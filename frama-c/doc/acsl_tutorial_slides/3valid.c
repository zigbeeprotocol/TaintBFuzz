/* VALIDITY OF POINTERS 

It is always legal to write "*p" in the logic,
even when p is not valid. */

/* assert \valid(p) && *p == 10; */

/* assert *p == 10 && \valid(p); */

/* or, assuming that p is either valid or NULL: */

/* assert p != NULL && *p == 10; */

/* assert *p == 10 && p != NULL */


/* assert *p == *p;  */


