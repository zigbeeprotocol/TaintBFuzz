/* run.config
   OPT: -wp-smoke-tests
*/

/* run.config_qualif
   OPT: -wp-smoke-tests
*/

//@ requires a < 0 && a > 0 ;
void requires(int a){}

/*@ requires a < 0 ;
    behavior B:
      assumes a > 0 ;
*/
void reqs_assumes(int a){}

/*@ requires a < 0 ;
    behavior B:
      assumes a > 0 ;
      assumes a > 1 ;
*/
void reqs_2_2_assumes(int a){}

/*@ requires a < 0 ;
    behavior B:
      assumes a > 0 ;
      assumes a < -42 ;
*/
void reqs_1_2_assumes(int a){}

/*@ requires a >= 0 ;
    behavior B:
      assumes a > 10 ;
      assumes a < 10 ;
*/
void reqs_combined_assumes(int a){}

/*@ behavior B:
      assumes a < 0 && a > 0 ; // not detected
*/
void only_assumes(int a){}

/*@ behavior B:
      assumes  a > 0 ;
      requires a < 0 ;
*/
void bhv_requires_assumes(int a){}

/*@ requires a < 0 ;
    behavior B1:
      assumes a > 0 ;
    behavior B2:
      assumes a > 1 ;
*/
void reqs_massumes(int a){}
