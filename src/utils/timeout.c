/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
 */

/*
 * SUPPORT FOR A SINGLE TIMEOUT
 */

/*
 * Two implementations:
 * - POSIX systems use a dedicated timer thread
 * - Windows uses the timer queue API
 */

#include <assert.h>
#ifdef MINGW
// Use the oldest version of the Windows API.
#ifndef _WIN32_WINNT
#define _WIN32_WINNT 0x0500
#endif

#include <windows.h>
#else
#include <pthread.h>
#include <sys/time.h>
#endif

#include "utils/error.h"
#include "utils/memalloc.h"
#include "utils/timeout.h"
#include "yices_exit_codes.h"

/*
 * Timeout state:
 * - NOT_READY: initial state and after call to delete_timeout
 * - READY: ready to be started (state after init_timeout
 *          and after clear_timeout)
 * - ACTIVE: after a call to start_timeout, before the timer fires
 *           or the timeout is canceled
 * - CANCELED: used by clear_timeout
 * - FIRED: after the handler has been called
 */
typedef enum timeout_state {
  TIMEOUT_NOT_READY, // 0
  TIMEOUT_READY,
  TIMEOUT_ACTIVE,
  TIMEOUT_CANCELED,
  TIMEOUT_FIRED,
} timeout_state_t;


typedef struct timeout_s {
  timeout_state_t state;
  timeout_handler_t handler;
  void *param;
#ifdef MINGW
  HANDLE timer_queue;
  HANDLE timer;
#else
  struct timespec ts;
  pthread_t thread;
  pthread_mutex_t mutex;
  pthread_cond_t cond;
#endif
} timeout_t;

/* Initialize the timeout fields common to all implementations. */

static inline void init_base_timeout(timeout_t *timeout) {
  timeout->state = TIMEOUT_READY;
  timeout->handler = NULL;
  timeout->param = NULL;
}

#ifndef MINGW


/*****************************
 *  UNIX/C99 IMPLEMENTATION  *
 ****************************/

#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/errno.h>

static inline void check_thread_api(int expr, const char *msg) {
  if (expr) {
    perror_fatal_code(msg, expr);
  }
}

timeout_t *init_timeout(void) {
  timeout_t *timeout;

  timeout = (timeout_t *) safe_malloc(sizeof(timeout_t));

  init_base_timeout(timeout);
  timeout->ts.tv_sec = 0;
  timeout->ts.tv_nsec = 0;

  check_thread_api(pthread_mutex_init(&timeout->mutex, /*attr=*/NULL),
		   "start_timeout: pthread_mutex_init");
  check_thread_api(pthread_cond_init(&timeout->cond, /*attr=*/NULL),
		   "start_timeout: pthread_cond_init");
  
  return timeout;
}

void delete_timeout(timeout_t *timeout) {
  check_thread_api(pthread_cond_destroy(&timeout->cond),
		   "delete_timeout: pthread_cond_destroy");
  check_thread_api(pthread_mutex_destroy(&timeout->mutex),
		   "delete_timeout: pthread_mutex_destroy");
    
  safe_free(timeout);
}

static void *timer_thread(void *arg) {
  timeout_t *timeout;
  
  timeout = (timeout_t *) arg;

  /* Get exclusive access to the state. */
  check_thread_api(pthread_mutex_lock(&timeout->mutex),
		   "timer_thread: pthread_mutex_lock");
  /* It is theoretically possible that the timeout has already been
     canceled by a quick call to clear_timeout. If so, we do not need
     to wait. */
  if (timeout->state != TIMEOUT_CANCELED) {
    int ret = pthread_cond_timedwait(&timeout->cond, &timeout->mutex,
				     &timeout->ts);
    if (ret && ret != ETIMEDOUT)
      perror_fatal_code("timer_thread: pthread_cond_timedwait", ret);
  }

  /* If the timeout wasn't canceled, then the timeout expired. */
  if (timeout->state != TIMEOUT_CANCELED) {
    timeout->state = TIMEOUT_FIRED;
    timeout->handler(timeout->param);
  }

  check_thread_api(pthread_mutex_unlock(&timeout->mutex),
		   "timer_thread: pthread_mutex_unlock");
  
  return NULL;
}

void start_timeout(timeout_t *timeout, uint32_t delay, timeout_handler_t handler, void *param) {
  struct timeval tv;
  
  assert(delay > 0 && timeout->state == TIMEOUT_READY && handler != NULL);

  timeout->state = TIMEOUT_ACTIVE;
  timeout->handler = handler;
  timeout->param = param;

  /* Compute the desired stop time. */
  if (gettimeofday(&tv, /*tzp=*/NULL) == -1)
    perror_fatal("start_timeout: gettimeofday");
  timeout->ts.tv_sec = tv.tv_sec + delay;
  timeout->ts.tv_nsec = 1000 * tv.tv_usec;

  check_thread_api(pthread_create(&timeout->thread, /*attr=*/NULL,
				  timer_thread, timeout),
		   "start_timeout: pthread_create");
}

void clear_timeout(timeout_t *timeout) {
  void *value;
  
  /* Tell the thread to exit. */
  check_thread_api(pthread_mutex_lock(&timeout->mutex),
		   "clear_timeout: pthread_mutex_lock");
  timeout->state = TIMEOUT_CANCELED;
  check_thread_api(pthread_mutex_unlock(&timeout->mutex),
		   "clear_timeout: pthread_mutex_unlock");
  check_thread_api(pthread_cond_signal(&timeout->cond),
		   "clear_timeout: pthread_cond_signal");

  /* Wait for the thread to exit. */
  check_thread_api(pthread_join(timeout->thread, &value),
		   "clear_timeout: pthread_join");

  timeout->state = TIMEOUT_READY;
}

#else


/************************************
 *   WINDOWS/MINGW IMPLEMENTATION   *
 ***********************************/

#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>

/*
 * Callback function for the timer
 * - do nothing if the timeout is not active
 * - otherwise change the state to fired and
 *   call the handler.
 */
static VOID CALLBACK timer_callback(PVOID param, BOOLEAN timer_or_wait_fired) {
  timeout_t *timeout = (timeout_t *) param;
  
  if (timeout->state == TIMEOUT_ACTIVE) {
    timeout->state = TIMEOUT_FIRED;
    timeout->handler(timeout->param);
  }
}


/*
 * Initialization:
 * - create the timer queue
 */
timeout_t *init_timeout(void) {
  timeout_t *timeout = (timeout_t *) safe_malloc(sizeof(timeout_t));

  init_base_timeout(timeout);

  timeout->timer_queue = CreateTimerQueue();
  if (timeout->timer_queue == NULL) {
    fprintf(stderr, "Yices: CreateTimerQueue failed with error code %"PRIu32"\n", (uint32_t) GetLastError());
    fflush(stderr);
    exit(YICES_EXIT_INTERNAL_ERROR);
  }

  timeout->timer = NULL;

  return timeout;
}



/*
 * Activate:
 * - delay = timeout in seconds (must be positive)
 * - handler = handler to call if fired
 * - param = parameter for the handler
 */
void start_timeout(timeout_t *timeout, uint32_t delay, timeout_handler_t handler, void *param) {
  DWORD duetime;

  assert(delay > 0 && timeout->state == TIMEOUT_READY && handler != NULL);

  duetime = delay * 1000; // delay in milliseconds
  if (CreateTimerQueueTimer(&timeout->timer,
			    timeout->timer_queue,
			    (WAITORTIMERCALLBACK) timer_callback,
                            timeout, duetime,
			    /*Period=*/0,
			    /*Flags=*/WT_EXECUTEDEFAULT)) {
    // timer created
    timeout->state = TIMEOUT_ACTIVE;
    timeout->handler = handler;
    timeout->param = param;
  } else {
    fprintf(stderr, "Yices: CreateTimerQueueTimer failed with error code %"PRIu32"\n", (uint32_t) GetLastError());
    fflush(stderr);
    exit(YICES_EXIT_INTERNAL_ERROR);
  }
}



/*
 * Delete the timer
 */
void clear_timeout(timeout_t *timeout) {
  // GetLastError returns DWORD, which is an unsigned 32bit integer
  uint32_t error_code;

  if (timeout->state == TIMEOUT_ACTIVE || timeout->state == TIMEOUT_FIRED) {
    if (timeout->state == TIMEOUT_ACTIVE) {
      // active and not fired yet
      timeout->state = TIMEOUT_CANCELED; // will prevent call to handle
    }

    /*
     * We give NULL as CompletionEvent so timer_callback will complete
     * if the timer has fired. That's fine as the timeout state is not
     * active anymore so the timer_callback does nothing.
     *
     * Second try: give INVALID_HANDLE_VALUE?
     * This causes SEG FAULT in ntdll.dll
     */
    if (! DeleteTimerQueueTimer(timeout->timer_queue, timeout->timer,
				INVALID_HANDLE_VALUE)) {
      error_code = (uint32_t) GetLastError();
      // The Microsoft doc says we should try again
      // unless error code is ERROR_IO_PENDING??
      fprintf(stderr, "Yices: DeleteTimerQueueTimer failed with error code %"PRIu32"\n", error_code);
      fflush(stderr);
      exit(YICES_EXIT_INTERNAL_ERROR);
    }
  }

  timeout->state = TIMEOUT_READY;
}



/*
 * Final cleanup:
 * - delete the timer_queue
 */
void delete_timeout(timeout_t *timeout) {
  if (! DeleteTimerQueueEx(timeout->timer_queue, INVALID_HANDLE_VALUE)) {
    fprintf(stderr, "Yices: DeleteTimerQueueEx failed with error code %"PRIu32"\n", (uint32_t) GetLastError());
    fflush(stderr);
    exit(YICES_EXIT_INTERNAL_ERROR);
  }

  safe_free(timeout);
}




#endif /* MINGW */
