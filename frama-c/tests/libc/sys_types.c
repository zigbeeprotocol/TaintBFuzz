#include <sys/types.h>

int main() {
  dev_t dev = makedev(1, 42);
  return 0;
}
