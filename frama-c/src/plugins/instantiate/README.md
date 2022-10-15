# Instantiate plugin

## Description

The instantiate plugin is meant to build function specialization to C functions
in a project when the original specification (or prototype of the function)
cannot be efficiently used by some plugins.

For example, the specification of a function like `memcpy` cannot be efficiently
used by a plugin like `WP` because it involves `void*` pointers and requires to
deduce that bytes equality implies (typed) data equality. While for example it
is easy to produce a typed specification for a type `int`:

```c
/*@ requires valid_dest: \valid(dest + (0 .. len-1));
    requires valid_read_src: \valid_read(src + (0 .. len-1));
    requires separation: \separated(dest + (0 .. len-1), src + (0 .. len-1));
    ensures copied: ∀ ℤ j0; 0 ≤ j0 < len ⇒ *(dest + j0) ≡ *(src + j0);
    ensures result: \result ≡ dest;
    assigns *(dest + (0 .. len - 1)), \result;
    assigns *(dest + (0 .. len - 1)) \from *(src + (0 .. len - 1));
    assigns \result \from dest;
 */
int *memcpy_int(int *dest, int const *src, size_t len);
```

That can be easily used by WP.

The role of the Instantiate plugin is to find each call for which an
instantiation generator is available and if the call is well-typed according to
the generator (for example for `memcpy` if `dest` and `src` are both pointers to
integers), to replace this call with a call to an automatically generated
specialization corresponding to the call.

## Options

- `-instantiate` activate function replacement
- `-instantiate-fct=f,...` only replace calls in specified functions (default to all)
- `-instantiate-(no-)<function_name>` activate or deactivate a particular
  function, defaults to true.

## Available functions

### `string.h`

```c
int memcmp(void const* s1, void const* s2, size_t len);
```

The parameters `s1` and `s2` must have the same types, except that qualifiers
and typedefs are ignored. The type of `s1` or `s2` cannot be `void*`.

```c
void* memcpy(void * dest, void const* src, size_t len);
```

The parameters `dest` and `src` must have the same types, except that qualifiers
and typedefs are ignored. The type of `dest` or `src` cannot be `void*`.

```c
void* memmove(void * dest, void const* src, size_t len);
```

The parameters `dest` and `src` must have the same types, except that qualifiers
and typedefs are ignored. The type of `dest` or `src` cannot be `void*`.

```c
void* memset(void * ptr, int value, size_t len);
```

If `ptr` is of `char*` type (include signed and unsigned variants), `value` must
be a `char`.

If `ptr` is of any other pointer type (except `void*`), `value` must be a
constant that statically evaluates to `0x00` or `0xFF`.

### `stdlib.h`

```c
void* calloc(size_t num, size_t size);

{
  type* res = calloc(...) ;
}
```

`calloc` is typed according to the variable that receives its result. It must be
a pointer type different from `void*`. If the pointed type has a flexible array
member, `num` is assumed to evaluate to `1` (a precondition is created for this).

```c
void free(void* ptr);
```

The type of `ptr` must be different from `void*`.


```c
void* malloc(size_t num, size_t size);

{
  type* res = calloc(...) ;
}
```

`malloc` is typed according to the variable that receives its result. It must be
a pointer type different from `void*`.

## Adding a new instantiator

To add a new instantiator, one has to register a new module implementing the
`Instantiator_builder.Generator_sig` module type to the `Transform` module. The
lasts steps of the code should look like:

```ocaml
let () = Transform.register (module struct
    module Hashtbl = ...
    type override_key = ...

    let function_name = "my_function"
    let well_typed_call = ...
    let key_from_call = ...
    let retype_args = ...
    let generate_prototype = ...
    let generate_spec = ...
    let args_for_original = ...
  end)
```

The role and types of each function is documented in `Instantiator_builder.mli`.