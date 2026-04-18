:tocdepth: 2

.. highlight:: c

.. _thread_safe:

Legacy Thread-Safety API
========================

The old global-lock thread-safety mode has been removed from this tree. Yices
no longer offers a separately configured re-entrant API build that serializes
term/type creation behind a single mutex.

The following function remains for compatibility.

.. c:function:: int32_t yices_is_thread_safe(void)

   Check whether the legacy global-lock API mode is enabled.

   This function now always returns 0. It is kept only for source and ABI
   compatibility with older callers.
