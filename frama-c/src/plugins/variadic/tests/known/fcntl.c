#include <fcntl.h>

int main(){
  struct flock fl;
  volatile choice = 0;

  // Normal usage
  int flags = fcntl(0, F_GETFD);
  fcntl(0, F_SETFD, flags);
  fcntl(0, F_GETLK, &fl);

  switch (choice)
  {
  case 1:
    // Too many arguments
    fcntl(0, F_SETFD, flags, 5);

  case 2:
    // Not enough arguments
    fcntl(0, F_SETFD);

  case 3:
    // Wrong arguments
    fcntl(0, F_SETFD, &fl);

  case 4:
    // Unexpected argument type
    fcntl(0, F_SETFD, 0.5);
  }
}

