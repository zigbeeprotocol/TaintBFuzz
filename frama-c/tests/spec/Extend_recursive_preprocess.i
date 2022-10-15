/* run.config
 MODULE: @PTEST_NAME@
   OPT: -kernel-warn-key=annot-error=active -print
*/

/*@ gl_foo foo1 {
    gl_fooo must_replace(x);
    gl_fooo must_not_replace(x);
    gl_fooo must_replace(x);
}*/


/*@ gl_foo foo1 {
    gl_foo foo2 {
      gl_fooo must_replace(x);
      gl_fooo must_not_replace(x);
    }
}*/

/*@ gl_foo foo1 {
    gl_fooo must_replace(x);
    gl_foo foo2 {
      gl_fooo must_replace(x);
      gl_foo foo3 {
         gl_fooo must_replace(x);
	 gl_fooo must_not_replace(x);
      }
      gl_fooo must_replace(x);
    }
    gl_fooo must_not_replace(x);

}*/

//frama-c -no-autoload-plugins -kernel-warn-key=annot-error=active -print -load-script Extend_recursive_preprocess.ml Extend_recursive_preprocess.i
