#!/usr/bin/env python3
"""
Benchmark two Yices SMT2 binaries on the same SMT2 corpus and generate a cactus
plot as SVG.

The harness honors per-benchmark `.options` files, validates solver output
against `.gold` files using whitespace-insensitive comparison, alternates solver
order per benchmark to reduce cache bias, and emits both CSV data and a summary.
"""

from __future__ import annotations

import argparse
import csv
import math
import shlex
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


SVG_WIDTH = 1200
SVG_HEIGHT = 720
MARGIN_LEFT = 95
MARGIN_RIGHT = 35
MARGIN_TOP = 35
MARGIN_BOTTOM = 80
PLOT_WIDTH = SVG_WIDTH - MARGIN_LEFT - MARGIN_RIGHT
PLOT_HEIGHT = SVG_HEIGHT - MARGIN_TOP - MARGIN_BOTTOM
COLORS = ("#1f77b4", "#d62728")


@dataclass(frozen=True)
class SolverSpec:
    name: str
    binary: Path


@dataclass
class RunResult:
    benchmark: str
    solver: str
    seconds: float
    passed: bool
    returncode: int
    order_index: int
    first_line: str


def normalize_output(text: str) -> str:
    return " ".join(text.split())


def read_text_if_exists(path: Path) -> str | None:
    if path.is_file():
        return path.read_text(encoding="utf-8")
    return None


def load_benchmarks(list_file: Path, root: Path) -> list[Path]:
    result: list[Path] = []
    for raw in list_file.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if " [" in line:
            line = line.split(" [", 1)[0].rstrip()
        result.append((root / line).resolve())
    return result


def benchmark_options(benchmark: Path) -> list[str]:
    optfile = benchmark.with_name(benchmark.name + ".options")
    text = read_text_if_exists(optfile)
    if text is None:
        return []
    return shlex.split(text)


def benchmark_gold(benchmark: Path) -> str | None:
    gold = benchmark.with_name(benchmark.name + ".gold")
    text = read_text_if_exists(gold)
    if text is None:
        return None
    return normalize_output(text)


def run_solver(
    solver: SolverSpec,
    benchmark: Path,
    options: list[str],
    expected: str | None,
    timeout: float,
    order_index: int,
) -> RunResult:
    cmd = [str(solver.binary), *options, str(benchmark)]
    start = time.perf_counter()
    try:
        proc = subprocess.run(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=timeout,
            check=False,
        )
        elapsed = time.perf_counter() - start
        output = proc.stdout
        passed = proc.returncode == 0
        if expected is not None:
            passed = passed and normalize_output(output) == expected
        first_line = output.splitlines()[0] if output.splitlines() else ""
        return RunResult(
            benchmark=str(benchmark),
            solver=solver.name,
            seconds=elapsed,
            passed=passed,
            returncode=proc.returncode,
            order_index=order_index,
            first_line=first_line,
        )
    except subprocess.TimeoutExpired as exc:
        elapsed = time.perf_counter() - start
        output = exc.stdout or ""
        first_line = output.splitlines()[0] if output.splitlines() else "TIMEOUT"
        return RunResult(
            benchmark=str(benchmark),
            solver=solver.name,
            seconds=elapsed,
            passed=False,
            returncode=124,
            order_index=order_index,
            first_line=first_line,
        )


def write_csv(path: Path, rows: Iterable[RunResult]) -> None:
    with path.open("w", encoding="utf-8", newline="") as out:
        writer = csv.writer(out)
        writer.writerow(
            ["benchmark", "solver", "seconds", "passed", "returncode", "order_index", "first_line"]
        )
        for row in rows:
            writer.writerow(
                [
                    row.benchmark,
                    row.solver,
                    f"{row.seconds:.6f}",
                    int(row.passed),
                    row.returncode,
                    row.order_index,
                    row.first_line,
                ]
            )


def ticks_for_log_scale(max_time: float) -> list[float]:
    decade_min = -3
    decade_max = max(1, int(math.ceil(math.log10(max_time))))
    ticks: list[float] = []
    for decade in range(decade_min, decade_max + 1):
        value = 10**decade
        if value <= max_time * 1.001:
            ticks.append(value)
    if 60.0 <= max_time * 1.001 and 60.0 not in ticks:
        ticks.append(60.0)
    if 120.0 <= max_time * 1.001 and 120.0 not in ticks:
        ticks.append(120.0)
    ticks = sorted(set(ticks))
    return ticks


def format_tick(value: float) -> str:
    if value >= 1:
        if abs(value - round(value)) < 1e-9:
            return str(int(round(value)))
        return f"{value:g}"
    return f"{value:g}"


def svg_escape(text: str) -> str:
    return (
        text.replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
        .replace('"', "&quot;")
    )


def write_cactus_svg(path: Path, title: str, series: list[tuple[str, list[float]]]) -> None:
    all_times = [t for _, values in series for t in values]
    if not all_times:
        path.write_text(
            "\n".join(
                [
                    f'<svg xmlns="http://www.w3.org/2000/svg" width="{SVG_WIDTH}" height="{SVG_HEIGHT}" viewBox="0 0 {SVG_WIDTH} {SVG_HEIGHT}">',
                    '<rect width="100%" height="100%" fill="white"/>',
                    f'<text x="{SVG_WIDTH / 2:.1f}" y="24" text-anchor="middle" font-family="Helvetica, Arial, sans-serif" font-size="22">{svg_escape(title)}</text>',
                    f'<text x="{SVG_WIDTH / 2:.1f}" y="{SVG_HEIGHT / 2:.1f}" text-anchor="middle" font-family="Helvetica, Arial, sans-serif" font-size="20">No common passing benchmarks to plot</text>',
                    "</svg>",
                ]
            ),
            encoding="utf-8",
        )
        return

    min_time = min(all_times)
    max_time = max(all_times)
    min_time = max(min_time, 1e-3)
    max_time = max(max_time, min_time * 1.01)
    log_min = math.log10(min_time)
    log_max = math.log10(max_time)
    if abs(log_max - log_min) < 1e-9:
        log_min -= 0.5
        log_max += 0.5
    solved_max = max(len(values) for _, values in series)

    def x_scale(value: float) -> float:
        xpos = (math.log10(max(value, 1e-3)) - log_min) / (log_max - log_min)
        return MARGIN_LEFT + xpos * PLOT_WIDTH

    def y_scale(count: float) -> float:
        ypos = count / max(solved_max, 1)
        return MARGIN_TOP + PLOT_HEIGHT - ypos * PLOT_HEIGHT

    tick_values = ticks_for_log_scale(max_time)
    y_ticks = list(range(0, solved_max + 1, max(1, solved_max // 10 or 1)))
    if y_ticks[-1] != solved_max:
        y_ticks.append(solved_max)

    parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{SVG_WIDTH}" height="{SVG_HEIGHT}" viewBox="0 0 {SVG_WIDTH} {SVG_HEIGHT}">',
        '<rect width="100%" height="100%" fill="white"/>',
        f'<text x="{SVG_WIDTH / 2:.1f}" y="24" text-anchor="middle" font-family="Helvetica, Arial, sans-serif" font-size="22">{svg_escape(title)}</text>',
    ]

    for tick in tick_values:
        x = x_scale(tick)
        parts.append(
            f'<line x1="{x:.2f}" y1="{MARGIN_TOP}" x2="{x:.2f}" y2="{MARGIN_TOP + PLOT_HEIGHT}" stroke="#e6e6e6" stroke-width="1"/>'
        )
        parts.append(
            f'<text x="{x:.2f}" y="{SVG_HEIGHT - 42}" text-anchor="middle" font-family="Helvetica, Arial, sans-serif" font-size="12">{svg_escape(format_tick(tick))}</text>'
        )

    for tick in y_ticks:
        y = y_scale(tick)
        parts.append(
            f'<line x1="{MARGIN_LEFT}" y1="{y:.2f}" x2="{MARGIN_LEFT + PLOT_WIDTH}" y2="{y:.2f}" stroke="#efefef" stroke-width="1"/>'
        )
        parts.append(
            f'<text x="{MARGIN_LEFT - 12}" y="{y + 4:.2f}" text-anchor="end" font-family="Helvetica, Arial, sans-serif" font-size="12">{tick}</text>'
        )

    parts.append(
        f'<line x1="{MARGIN_LEFT}" y1="{MARGIN_TOP}" x2="{MARGIN_LEFT}" y2="{MARGIN_TOP + PLOT_HEIGHT}" stroke="black" stroke-width="1.5"/>'
    )
    parts.append(
        f'<line x1="{MARGIN_LEFT}" y1="{MARGIN_TOP + PLOT_HEIGHT}" x2="{MARGIN_LEFT + PLOT_WIDTH}" y2="{MARGIN_TOP + PLOT_HEIGHT}" stroke="black" stroke-width="1.5"/>'
    )

    for idx, (name, values) in enumerate(series):
        if not values:
            continue
        sorted_values = sorted(values)
        coords = [(x_scale(sorted_values[0]), y_scale(1))]
        for count, value in enumerate(sorted_values, start=1):
            coords.append((x_scale(value), y_scale(count)))
            if count < len(sorted_values):
                coords.append((x_scale(value), y_scale(count + 1)))
        polyline = " ".join(f"{x:.2f},{y:.2f}" for x, y in coords)
        parts.append(
            f'<polyline fill="none" stroke="{COLORS[idx % len(COLORS)]}" stroke-width="3" points="{polyline}"/>'
        )

    legend_x = MARGIN_LEFT + 20
    legend_y = MARGIN_TOP + 18
    for idx, (name, values) in enumerate(series):
        y = legend_y + idx * 24
        color = COLORS[idx % len(COLORS)]
        parts.append(
            f'<line x1="{legend_x}" y1="{y}" x2="{legend_x + 28}" y2="{y}" stroke="{color}" stroke-width="3"/>'
        )
        parts.append(
            f'<text x="{legend_x + 38}" y="{y + 4}" font-family="Helvetica, Arial, sans-serif" font-size="13">{svg_escape(name)} ({len(values)} solved)</text>'
        )

    parts.append(
        f'<text x="{SVG_WIDTH / 2:.1f}" y="{SVG_HEIGHT - 12}" text-anchor="middle" font-family="Helvetica, Arial, sans-serif" font-size="15">Wall-clock time (seconds, log scale)</text>'
    )
    parts.append(
        f'<text x="22" y="{SVG_HEIGHT / 2:.1f}" text-anchor="middle" transform="rotate(-90 22 {SVG_HEIGHT / 2:.1f})" font-family="Helvetica, Arial, sans-serif" font-size="15">Benchmarks solved</text>'
    )
    parts.append("</svg>")
    path.write_text("\n".join(parts), encoding="utf-8")


def summarize_common_passes(rows: list[RunResult], solver_names: tuple[str, str]) -> tuple[list[float], list[float], int]:
    by_benchmark: dict[str, dict[str, RunResult]] = {}
    for row in rows:
        by_benchmark.setdefault(row.benchmark, {})[row.solver] = row

    left_times: list[float] = []
    right_times: list[float] = []
    mismatches = 0

    for benchmark, result_map in by_benchmark.items():
        left = result_map.get(solver_names[0])
        right = result_map.get(solver_names[1])
        if left is None or right is None:
            continue
        if left.passed and right.passed:
            left_times.append(left.seconds)
            right_times.append(right.seconds)
        else:
            mismatches += 1

    return left_times, right_times, mismatches


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--list-file", required=True, type=Path)
    parser.add_argument("--solver-a-name", required=True)
    parser.add_argument("--solver-a-bin", required=True, type=Path)
    parser.add_argument("--solver-b-name", required=True)
    parser.add_argument("--solver-b-bin", required=True, type=Path)
    parser.add_argument("--output-dir", required=True, type=Path)
    parser.add_argument("--timeout", type=float, default=120.0)
    parser.add_argument("--root-dir", type=Path, default=Path.cwd())
    args = parser.parse_args()

    solver_a = SolverSpec(args.solver_a_name, args.solver_a_bin.resolve())
    solver_b = SolverSpec(args.solver_b_name, args.solver_b_bin.resolve())
    benchmarks = load_benchmarks(args.list_file.resolve(), args.root_dir.resolve())
    outdir = args.output_dir.resolve()
    outdir.mkdir(parents=True, exist_ok=True)

    rows: list[RunResult] = []

    print(f"Benchmarking {len(benchmarks)} SMT2 benchmarks", flush=True)
    for idx, benchmark in enumerate(benchmarks, start=1):
        options = benchmark_options(benchmark)
        expected = benchmark_gold(benchmark)
        pair = [solver_a, solver_b] if idx % 2 else [solver_b, solver_a]
        print(f"[{idx}/{len(benchmarks)}] {benchmark}", flush=True)
        for order_index, solver in enumerate(pair):
            row = run_solver(solver, benchmark, options, expected, args.timeout, order_index)
            rows.append(row)
            status = "PASS" if row.passed else f"FAIL(rc={row.returncode})"
            print(f"  {solver.name}: {row.seconds:.4f}s {status}", flush=True)

    csv_path = outdir / "results.csv"
    write_csv(csv_path, rows)

    names = (solver_a.name, solver_b.name)
    a_times, b_times, mismatches = summarize_common_passes(rows, names)
    summary_path = outdir / "summary.txt"
    with summary_path.open("w", encoding="utf-8") as out:
        out.write(f"solver_a={solver_a.name}\n")
        out.write(f"solver_b={solver_b.name}\n")
        out.write(f"benchmarks_total={len(benchmarks)}\n")
        out.write(f"common_passes={len(a_times)}\n")
        out.write(f"mismatches_or_failures={mismatches}\n")
        if a_times and b_times:
            a_wins = sum(1 for a, b in zip(a_times, b_times) if a < b)
            b_wins = sum(1 for a, b in zip(a_times, b_times) if b < a)
            ties = len(a_times) - a_wins - b_wins
            out.write(f"{solver_a.name}_wins={a_wins}\n")
            out.write(f"{solver_b.name}_wins={b_wins}\n")
            out.write(f"ties={ties}\n")
            out.write(f"{solver_a.name}_total_seconds={sum(a_times):.6f}\n")
            out.write(f"{solver_b.name}_total_seconds={sum(b_times):.6f}\n")

    plot_path = outdir / "cactus.svg"
    write_cactus_svg(
        plot_path,
        f"{solver_a.name} vs {solver_b.name} on SMT2 regression corpus",
        [(solver_a.name, a_times), (solver_b.name, b_times)],
    )

    print()
    print(f"CSV: {csv_path}")
    print(f"Summary: {summary_path}")
    print(f"Plot: {plot_path}")
    print(f"Common passing benchmarks: {len(a_times)}")
    print(f"Mismatches/failures: {mismatches}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
