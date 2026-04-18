#!/usr/bin/env python3

import argparse
import csv
import json
import math
import os
import re
import shlex
import statistics
import subprocess
import tempfile
import time
from pathlib import Path


SMT2_SUFFIXES = {".smt2"}
YICES_SUFFIXES = {".ys"}
TEST_SUFFIXES = SMT2_SUFFIXES | YICES_SUFFIXES


def parse_args():
    parser = argparse.ArgumentParser(
        description="Benchmark the MCSAT regression corpus for multiple worker counts."
    )
    parser.add_argument(
        "--tests-dir",
        type=Path,
        default=Path("tests/regress/mcsat"),
        help="Directory containing the MCSAT benchmark corpus.",
    )
    parser.add_argument(
        "--bin-dir",
        type=Path,
        required=True,
        help="Directory containing the yices binaries to benchmark.",
    )
    parser.add_argument(
        "--results-dir",
        type=Path,
        required=True,
        help="Directory where benchmark results and the cactus plot will be written.",
    )
    parser.add_argument(
        "--workers",
        type=int,
        nargs="+",
        required=True,
        help="Worker counts to benchmark.",
    )
    parser.add_argument(
        "--timeout",
        type=float,
        default=60.0,
        help="Wall-clock timeout in seconds per benchmark run.",
    )
    parser.add_argument(
        "--explicit-mcsat-only",
        action="store_true",
        help="Benchmark only tests that explicitly request --mcsat or use the Yices .ys MCSAT frontend.",
    )
    parser.add_argument(
        "--test-list",
        type=Path,
        help="Optional newline-separated list of benchmark file paths to run.",
    )
    return parser.parse_args()


def is_explicit_mcsat_test(path: Path):
    if path.suffix in YICES_SUFFIXES:
        return True
    options = load_options(path)
    return "--mcsat" in options


def discover_tests(tests_dir: Path, explicit_mcsat_only: bool):
    tests = []
    for path in tests_dir.rglob("*"):
        if path.suffix in TEST_SUFFIXES:
            if explicit_mcsat_only and not is_explicit_mcsat_test(path):
                continue
            tests.append(path)
    return sorted(tests)


def load_test_list(path: Path):
    tests = []
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        tests.append(Path(line))
    return tests


def binary_for_test(test: Path):
    if test.suffix in SMT2_SUFFIXES:
        return "yices_smt2"
    if test.suffix in YICES_SUFFIXES:
        return "yices"
    raise ValueError(f"unsupported test suffix: {test}")


def load_options(test: Path):
    options_path = Path(f"{test}.options")
    if not options_path.exists():
        return []
    return shlex.split(options_path.read_text(encoding="utf-8"))


def load_gold(test: Path):
    gold_path = Path(f"{test}.gold")
    if not gold_path.exists():
        raise FileNotFoundError(f"missing gold file for {test}")
    text = gold_path.read_text(encoding="utf-8")
    return {
        "normalized": normalize_output(text),
        "status_signature": extract_status_signature(text),
    }


def normalize_output(text: str):
    return " ".join(text.split())


def extract_status_signature(text: str):
    status_lines = []
    for line in text.splitlines():
        token = line.strip()
        if token in {"sat", "unsat", "unknown"}:
            status_lines.append(token)
    return tuple(status_lines)


def inject_worker_setting(test: Path, worker_count: int):
    text = test.read_text(encoding="utf-8")

    if test.suffix in SMT2_SUFFIXES:
        replacement = f"(set-option :yices-mcsat-parallel-workers {worker_count})"
        patterns = [
            r"\(set-option\s+:yices-mcsat-parallel-workers\s+\d+\)",
            r"\(set-option\s+:mcsat-parallel-workers\s+\d+\)",
        ]
    elif test.suffix in YICES_SUFFIXES:
        replacement = f"(set-param mcsat-parallel-workers {worker_count})"
        patterns = [
            r"\(set-param\s+mcsat-parallel-workers\s+\d+\)",
        ]
    else:
        raise ValueError(f"unsupported test suffix: {test}")

    updated = text
    replaced = False
    for pattern in patterns:
        updated, count = re.subn(pattern, replacement, updated)
        if count:
            replaced = True

    if not replaced:
        updated = replacement + "\n" + updated

    return updated


def run_single_test(test: Path, bin_dir: Path, worker_count: int, timeout_sec: float):
    binary = bin_dir / binary_for_test(test)
    options = load_options(test)
    expected = load_gold(test)
    payload = inject_worker_setting(test, worker_count)

    with tempfile.NamedTemporaryFile(
        mode="w",
        encoding="utf-8",
        suffix=test.suffix,
        prefix=".bench_",
        dir=test.parent,
        delete=False,
    ) as tmp:
        tmp.write(payload)
        tmp_path = Path(tmp.name)

    try:
        cmd = [str(binary)] + options + [str(tmp_path)]
        start = time.perf_counter()
        try:
            proc = subprocess.run(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                timeout=timeout_sec,
                check=False,
            )
            elapsed = time.perf_counter() - start
            output = normalize_output(proc.stdout)
            status_signature = extract_status_signature(proc.stdout)
            exact_match = output == expected["normalized"]
            status_match = (
                bool(expected["status_signature"])
                and status_signature == expected["status_signature"]
            )
            if proc.returncode == 0:
                if exact_match:
                    validation = "exact"
                elif status_match:
                    validation = "status"
                else:
                    validation = "exit_only"
                status = "ok"
            else:
                validation = "failed"
                status = "bad_output"
            return {
                "test": test.as_posix(),
                "worker_count": worker_count,
                "elapsed_sec": elapsed,
                "status": status,
                "returncode": proc.returncode,
                "output_ok": proc.returncode == 0,
                "exact_output_match": exact_match,
                "status_signature_match": status_match,
                "validation": validation,
            }
        except subprocess.TimeoutExpired:
            elapsed = time.perf_counter() - start
            return {
                "test": test.as_posix(),
                "worker_count": worker_count,
                "elapsed_sec": elapsed,
                "status": "timeout",
                "returncode": None,
                "output_ok": False,
                "exact_output_match": False,
                "status_signature_match": False,
                "validation": "timeout",
            }
    finally:
        try:
            tmp_path.unlink()
        except FileNotFoundError:
            pass


def geomean(values):
    if not values:
        return None
    return math.exp(sum(math.log(v) for v in values) / len(values))


def percentile(values, q):
    if not values:
        return None
    if len(values) == 1:
        return values[0]
    idx = (len(values) - 1) * q
    lo = math.floor(idx)
    hi = math.ceil(idx)
    if lo == hi:
        return values[lo]
    frac = idx - lo
    return values[lo] * (1 - frac) + values[hi] * frac


def summarize(results_by_worker):
    baseline = results_by_worker[min(results_by_worker)]
    baseline_ok = {
        entry["test"]: entry for entry in baseline if entry["status"] == "ok"
    }
    summary = {}

    for worker_count, results in results_by_worker.items():
        ok = [r for r in results if r["status"] == "ok"]
        ok_by_test = {entry["test"]: entry for entry in ok}
        runtimes = sorted(entry["elapsed_sec"] for entry in ok)
        status_counts = {}
        for entry in results:
            status_counts[entry["status"]] = status_counts.get(entry["status"], 0) + 1
        ratios_all = []
        ratios_hard = []
        for test, base in baseline_ok.items():
            cur = ok_by_test.get(test)
            if cur is None:
                continue
            ratio = base["elapsed_sec"] / cur["elapsed_sec"] if cur["elapsed_sec"] > 0 else float("inf")
            ratios_all.append(ratio)
            if base["elapsed_sec"] >= 0.1:
                ratios_hard.append(ratio)
        summary[worker_count] = {
            "count_ok": len(ok),
            "count_total": len(results),
            "status_counts": status_counts,
            "median_sec": statistics.median(runtimes) if runtimes else None,
            "p90_sec": percentile(runtimes, 0.90),
            "max_sec": max(runtimes) if runtimes else None,
            "geomean_speedup_vs_1": geomean(ratios_all),
            "geomean_speedup_vs_1_hard_0_1s": geomean(ratios_hard),
            "count_shared_with_1": len(ratios_all),
            "count_hard_shared_with_1": len(ratios_hard),
        }
    return summary


def write_csv(results_by_worker, out_path: Path):
    workers = sorted(results_by_worker)
    tests = sorted({entry["test"] for results in results_by_worker.values() for entry in results})
    by_key = {
        (entry["test"], entry["worker_count"]): entry
        for results in results_by_worker.values()
        for entry in results
    }
    with out_path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        header = ["test"]
        for worker in workers:
            header += [
                f"w{worker}_status",
                f"w{worker}_elapsed_sec",
            ]
        writer.writerow(header)
        for test in tests:
            row = [test]
            for worker in workers:
                entry = by_key[(test, worker)]
                row.extend([entry["status"], f"{entry['elapsed_sec']:.9f}"])
            writer.writerow(row)


def write_json(results_by_worker, summary, out_path: Path):
    payload = {
        "workers": sorted(results_by_worker),
        "summary": summary,
        "results": {
            str(worker): results for worker, results in sorted(results_by_worker.items())
        },
    }
    out_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")


def generate_cactus_svg(results_by_worker, out_path: Path):
    workers = sorted(results_by_worker)
    curves = {}
    max_x = 1
    positive_times = []
    for worker in workers:
        times = sorted(
            entry["elapsed_sec"]
            for entry in results_by_worker[worker]
            if entry["status"] == "ok"
        )
        curves[worker] = times
        max_x = max(max_x, len(times))
        positive_times.extend(t for t in times if t > 0)

    if not positive_times:
        raise RuntimeError("no successful benchmark runs available for cactus plot")

    min_y = min(max(t, 1e-4) for t in positive_times)
    max_y = max(positive_times)
    log_min = math.log10(min_y)
    log_max = math.log10(max_y)
    if log_min == log_max:
        log_max += 1.0

    width = 1200
    height = 760
    margin_left = 100
    margin_right = 40
    margin_top = 50
    margin_bottom = 90
    plot_width = width - margin_left - margin_right
    plot_height = height - margin_top - margin_bottom
    colors = {
        workers[0]: "#1f77b4",
        workers[1] if len(workers) > 1 else workers[0]: "#d62728",
        workers[2] if len(workers) > 2 else workers[0]: "#2ca02c",
    }

    def x_map(x):
        if max_x <= 1:
            return margin_left
        return margin_left + (x - 1) * plot_width / (max_x - 1)

    def y_map(value):
        v = max(value, 1e-4)
        return margin_top + (log_max - math.log10(v)) * plot_height / (log_max - log_min)

    y_ticks = []
    start_decade = math.floor(log_min)
    end_decade = math.ceil(log_max)
    for decade in range(start_decade, end_decade + 1):
        for mult in (1, 2, 5):
            value = mult * (10 ** decade)
            if min_y <= value <= max_y:
                y_ticks.append(value)
    y_ticks = sorted(set(y_ticks))

    x_ticks = []
    desired_ticks = min(10, max_x)
    for i in range(desired_ticks):
        x_ticks.append(1 + round(i * (max_x - 1) / max(desired_ticks - 1, 1)))
    x_ticks = sorted(set(x_ticks))

    lines = []
    lines.append('<?xml version="1.0" encoding="UTF-8"?>')
    lines.append(
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">'
    )
    lines.append('<rect width="100%" height="100%" fill="#ffffff"/>')
    lines.append(
        f'<text x="{width/2:.1f}" y="30" text-anchor="middle" font-family="Helvetica, Arial, sans-serif" font-size="24" fill="#111111">Yices2 Parallel MCSAT Cactus Plot</text>'
    )

    for tick in y_ticks:
        y = y_map(tick)
        lines.append(
            f'<line x1="{margin_left}" y1="{y:.2f}" x2="{width-margin_right}" y2="{y:.2f}" stroke="#e0e0e0" stroke-width="1"/>'
        )
        lines.append(
            f'<text x="{margin_left-12}" y="{y+4:.2f}" text-anchor="end" font-family="Helvetica, Arial, sans-serif" font-size="12" fill="#444444">{tick:.3g}</text>'
        )

    for tick in x_ticks:
        x = x_map(tick)
        lines.append(
            f'<line x1="{x:.2f}" y1="{margin_top}" x2="{x:.2f}" y2="{height-margin_bottom}" stroke="#f0f0f0" stroke-width="1"/>'
        )
        lines.append(
            f'<text x="{x:.2f}" y="{height-margin_bottom+24}" text-anchor="middle" font-family="Helvetica, Arial, sans-serif" font-size="12" fill="#444444">{tick}</text>'
        )

    lines.append(
        f'<line x1="{margin_left}" y1="{height-margin_bottom}" x2="{width-margin_right}" y2="{height-margin_bottom}" stroke="#222222" stroke-width="2"/>'
    )
    lines.append(
        f'<line x1="{margin_left}" y1="{margin_top}" x2="{margin_left}" y2="{height-margin_bottom}" stroke="#222222" stroke-width="2"/>'
    )

    for worker in workers:
        times = curves[worker]
        if not times:
            continue
        points = " ".join(
            f"{x_map(i+1):.2f},{y_map(t):.2f}" for i, t in enumerate(times)
        )
        color = colors[worker]
        lines.append(
            f'<polyline fill="none" stroke="{color}" stroke-width="3" points="{points}"/>'
        )

    legend_x = width - margin_right - 250
    legend_y = margin_top + 10
    lines.append(
        f'<rect x="{legend_x}" y="{legend_y}" width="220" height="{40 + 28 * len(workers)}" fill="#ffffff" stroke="#cccccc"/>'
    )
    lines.append(
        f'<text x="{legend_x + 12}" y="{legend_y + 22}" font-family="Helvetica, Arial, sans-serif" font-size="14" fill="#111111">Workers</text>'
    )
    for idx, worker in enumerate(workers):
        y = legend_y + 40 + idx * 28
        color = colors[worker]
        lines.append(
            f'<line x1="{legend_x + 12}" y1="{y}" x2="{legend_x + 42}" y2="{y}" stroke="{color}" stroke-width="3"/>'
        )
        lines.append(
            f'<text x="{legend_x + 52}" y="{y + 5}" font-family="Helvetica, Arial, sans-serif" font-size="13" fill="#111111">{worker} worker{"s" if worker != 1 else ""}</text>'
        )

    lines.append(
        f'<text x="{width/2:.1f}" y="{height-24}" text-anchor="middle" font-family="Helvetica, Arial, sans-serif" font-size="16" fill="#111111">Solved benchmarks (sorted by runtime)</text>'
    )
    lines.append(
        f'<text x="28" y="{height/2:.1f}" text-anchor="middle" transform="rotate(-90, 28, {height/2:.1f})" font-family="Helvetica, Arial, sans-serif" font-size="16" fill="#111111">Wall-clock time (seconds, log scale)</text>'
    )
    lines.append("</svg>")
    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def fmt_float(value):
    if value is None:
        return "n/a"
    return f"{value:.6f}"


def main():
    args = parse_args()
    if args.test_list is not None:
        tests = load_test_list(args.test_list)
    else:
        tests = discover_tests(args.tests_dir, args.explicit_mcsat_only)
    if not tests:
        raise RuntimeError(f"no benchmark tests found in {args.tests_dir}")

    args.results_dir.mkdir(parents=True, exist_ok=True)
    results_by_worker = {}

    print(f"Benchmarking {len(tests)} tests from {args.tests_dir}")
    for worker_count in args.workers:
        print(f"Running worker count {worker_count}...")
        worker_results = []
        for index, test in enumerate(tests, start=1):
            result = run_single_test(test, args.bin_dir, worker_count, args.timeout)
            worker_results.append(result)
            print(
                f"[w={worker_count}] {index}/{len(tests)} {result['status']:>10} {result['elapsed_sec']:.3f}s {result['test']}",
                flush=True,
            )
        results_by_worker[worker_count] = worker_results

    summary = summarize(results_by_worker)
    write_json(results_by_worker, summary, args.results_dir / "results.json")
    write_csv(results_by_worker, args.results_dir / "results.csv")
    generate_cactus_svg(results_by_worker, args.results_dir / "cactus.svg")

    print("Summary:")
    for worker_count in sorted(summary):
        entry = summary[worker_count]
        print(
            f"  w={worker_count}: ok={entry['count_ok']}/{entry['count_total']} "
            f"median={fmt_float(entry['median_sec'])}s "
            f"p90={fmt_float(entry['p90_sec'])}s "
            f"max={fmt_float(entry['max_sec'])}s "
            f"geomean_speedup_vs_1={fmt_float(entry['geomean_speedup_vs_1'])} "
            f"statuses={entry['status_counts']}"
        )


if __name__ == "__main__":
    main()
