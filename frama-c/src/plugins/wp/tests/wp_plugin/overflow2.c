/* run.config
   OPT: -machdep x86_32
*/
/* run.config_qualif
   OPT: -machdep x86_32
*/

/* run with: frama-c-gui -wp -wp-rte strange_work_again.c */
// uproven: a04, a05, a09, a10
// note that when the type of distance is ushort, all is proven

typedef unsigned char uchar;
typedef unsigned short ushort;
typedef unsigned int uint;
typedef unsigned long ulong;

uint p1_off, p2_off;

/*@
  requires p1_off <= 10;
  assigns p2_off;
  ensures post: p2_off == p1_off + (ushort)distance; 	 
*/
void pointers_and_companions(short distance)
{
  p2_off = p1_off + (ushort)distance;	
  //@ assert a01: p2_off == (uint)(p1_off + (ushort)distance);
  //@ assert a02: (ushort)distance <= 65535;
  //@ assert a03: p1_off <= 10;
  //@ assert a04: p1_off + (ushort)distance <= 10 + 65535;
  //@ assert a05: p1_off + (ushort)distance == (uint)(p1_off + (ushort)distance);
}

// the same behavior for ulong

ulong p1_off_alt, p2_off_alt;

/*@
  requires p1_off_alt <= 10;
  assigns p2_off_alt;
  ensures postul: p2_off_alt == p1_off_alt + (ushort)distance; 	 
*/
void pointers_and_companions_ulong(short distance)
{
  p2_off_alt = p1_off_alt + (ushort)distance;
  //@ assert a06: p2_off_alt == (uint)(p1_off_alt + (ushort)distance);
  //@ assert a07: (ushort)distance <= 65535;
  //@ assert a08: p1_off_alt <= 10;
  //@ assert a09: p1_off_alt + (ushort)distance <= 10 + 65535;
  //@ assert a10: ((ulong)(p1_off_alt + (ushort)distance)) == (p1_off_alt + (ushort)distance);
}
