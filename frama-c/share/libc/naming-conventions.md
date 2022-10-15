Naming conventions for ACSL specifications in the Frama-C libc
==============================================================

This file defines some naming conventions regarding the Frama-C standard library
specifications.

Note that most files were created before these conventions, so they may not
respect them.

1. ACSL names define an _interface_ for the predicates they name. For instance,
   they are the only visible part in error messages. Therefore, the chosen
   names should provide concise and self-explanatory information for the users.
   For instance, instead of the warning:

        [value] warning: function strtok_r: precondition
            '*saveptr != \null && \initialized(saveptr);' got status unknown.

    A more concise and informative message might be:

        [value] warning: function strtok_r: precondition
            'not_first_call' got status unknown.

    This gives some semantic information concerning the predicate. It also
    avoids changing oracles if the specification is improved in future versions.

    In some cases, the name is very similar to the actual implementation, but
    that is not an issue.
    For instance, in `valid_string_s1: valid_read_string(s1)`, the user will
    only see `valid_string_s1`; a name such as `s1` would not be informative
    enough. Note that `read` is absent from the name; in this case, it might
    be considered an implementation detail (there cannot be two preconditions
    `valid_read_string(s1)` and `valid_string(s1)` in the same function).
    However, `string` is present, since it is important to communicate to the
    user that `s1` must not only be a valid memory region, but also a valid,
    null-terminated string.

2. Some predefined ACSL names are used by plug-ins to automatically filter
   features they cannot handle. Here is a (non-exhaustive) list of such
   names, which are usually _nouns_ instead of _adjectives_:

   - `initialization`: used for `\initialized` predicates;
   - `danglingness`: used for `!\dangling` predicates;
   - `separation`: used for `\separated` predicates;
   - `allocation`: used for `ensures \fresh` postconditions.

    Note that ACSL names are not unique: several predicates can have
    the same name. In particular, if there are multiple preconditions and/or
    postconditions dealing with initialization, all of them must have the
    `initialization` name. A second name should be added for disambiguation,
    typically with the name of the affected variable(s).
    For instance, consider this specification for `memcmp`:

        requires initialization:s1: \initialized(((char*)s1)+(0..n - 1));
        requires initialization:s2: \initialized(((char*)s2)+(0..n - 1));

    It respects the `initialization` constraint, but also ensures unicity and
    readability by adding the variable name at the end.
    Note that we cannot simply add a suffix to `initialization`,
    such as `initialization_s1`, otherwise the plug-in filters will fail.

3. Behavior names are often adjectives, but more generally they correspond to
   the different states or situations which can arise in a given function.
   For instance, a function that searches for an element in a container will
   likely have behaviors names `found` and `not_found`.

4. The following clauses are _not_ named:
   `assigns`, `allocates`, `frees`, `terminates`.
   This is mostly due to the fact that they occur only once in most (if not all)
   specifications. For instance, in a given function contract, several
   `assigns` "sub"-clauses all form part of a single, canonical clause.
