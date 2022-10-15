#include <netinet/in.h>
#include <stdio.h>

int main() {
  struct in_addr addr = {0};
  printf("%s", inet_ntoa(addr));
  struct sockaddr_in6 sockaddr6_any = {0, 0, 0, IN6ADDR_ANY_INIT, 0};
  struct sockaddr_in6 sockaddr6_loopback = {0, 0, 0, IN6ADDR_LOOPBACK_INIT, 0};
}
