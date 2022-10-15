Nonterm
=======

Nonterm (for "non-termination") is a small plug-in used to help identify issues
when running Eva.

It runs after Eva and outputs warnings when reachable but definitively
non-terminating functions/loops are detected, e.g. as in the code below:

    void f(int i) {
      while (i != 0)
            i--;
    }

    int main() {
        f(-1); // should be non-negative
        return 0;
    }

A warning is emitted when a function is reachable by Eva, but its return
statement is unreachable.

Note that normalized void functions have an implicit return statement before
their closing }.

Warnings are also emitted when reachable statements (e.g. calls to built-ins)
have unreachable post-states (i.e. their evaluation results in `Bottom`).


Usage
-----

Apply it after running Eva, as in:

    frama-c -eva file.c -then -nonterm
