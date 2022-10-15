/* run.config
 MODULE: pp_lines
   STDOPT:
*/

// Test locations when cabs2cil merges declarations and tentative definitions
// together. We should always favor the tentative definition.

extern int foo;

int foo;  // Better


int bar; // Better

extern int bar;


extern int baz;

extern int baz;

int z = (int) &baz;
