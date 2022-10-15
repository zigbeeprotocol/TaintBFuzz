// Missing stream parameter
extern int fprintf (const char *restrict __format, ...);

void main(void)
{
  fprintf("GCC compiles but crashes during execution");
}
