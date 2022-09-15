.. title:: clang-tidy - performance-unnecessary-copy-on-last-use

performance-unnecessary-copy-on-last-use
========================================

Finds variables of non-trivially-copyable types, that are used in a copy
construction on their last usage and suggest to wrap the usage in a
``std::move``. The usage just before an assignment is interpreted as last usage.

Many programmers tend to forget ``std::move`` for variables that can be moved.
Instead, the compiler creates implicit copies, which can significantly decrease
performance.

Example
--------

.. code-block:: c++

  void acceptor(std::vector<int> v);
  void Function() {
    std::vector<int> v;
    v.emplace_back(20);
    // The warning will suggest passing this as a rvalue-reference
    acceptor(v);
  }

Options
-------

.. option:: BlockedTypes

   A semicolon-separated list of names of types allowed to be copied on last
   usage. Regular expressions are accepted, e.g. `[Rr]ef(erence)?$` matches
   every type with suffix `Ref`, `ref`, `Reference` and `reference`.
   The default is empty. If a name in the list contains the sequence `::` it
   is matched against the qualified typename (i.e. `namespace::Type`,
   otherwise it is matched against only the type name (i.e. `Type`).

.. option:: BlockedFunctions

   A semicolon-separated list of names of functions who's parameters do not
   participate in the resolution.
   Regular expressions are accepted, e.g. `[Rr]ef(erence)?$` matches
   every type with suffix `Ref`, `ref`, `Reference` and `reference`.
   The default is empty. If a name in the list contains the sequence `::` it
   is matched against the qualified typename (i.e. `namespace::Type`,
   otherwise it is matched against only the type name (i.e. `Type`).

.. option:: IncludeStyle

   A string specifying which include-style is used, `llvm` or `google`. Default
   is `llvm`.

Limitations
-----------

This check does not implement a heuristic, if a variable is used as guard until
the end of it's scope. It also does not check, if a variable has any side 
effects in the destructor, which must be applied at the end of the scope.
Therefore, it will suggest to use ``std::move`` in the
following case, where `guard` protects `i`:

.. code-block:: cpp
    
  void acceptor(std::shared_ptr<std::unique_lock<std::mutex>>, int& i);

  void f(std::shared_ptr<std::unique_lock<std::mutex>> guard, int& i) {
    acceptor(guard, i);
    i++;
  }

This check is also unable to detect last usages for fields, if the parent 
class is destructed after the last usage.

Implicit copies in lambda-captures are detected, but no fixit is provided.
Also, the check will warn for c++11 even if it is not possible to fix it without
an language upgrade to at least c++14.
