#include <arpa/inet.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <stdlib.h>
volatile int v;
int main() {
  int sockfd = socket(AF_INET, SOCK_STREAM, 0);
  if (sockfd < 0) exit(1);
  struct sockaddr_in addr;
  addr.sin_family = AF_INET;
  addr.sin_addr.s_addr = inet_addr("127.0.0.1");
  addr.sin_port = htons(42);
  int rc = connect(sockfd, (struct sockaddr *)&addr, sizeof(addr));
  if (rc < 0) exit(2);

  int optval;
  socklen_t optlen = sizeof(optval);
  rc = getsockopt(sockfd, SOL_SOCKET, SO_ERROR, (void *)&optval, &optlen);
  struct sockaddr_in addr2;
  socklen_t socklen = sizeof(addr2);
  rc = getsockname(sockfd, (struct sockaddr *)&addr2, &socklen);

  char buf[40] = {'a', 'b', 'c'};
  ssize_t sent = sendto(sockfd, buf, 3, 0, (struct sockaddr *)&addr,
                        sizeof(addr));

  ssize_t sent2 = sendto(sockfd, buf, 3, 0, 0, 0);

  struct sockaddr_in recvfrom_addr;
  socklen_t recvfrom_addr_len = sizeof(recvfrom_addr);
  ssize_t received = recvfrom(sockfd, buf, sizeof(buf), 0,
                              (struct sockaddr *)&recvfrom_addr,
                              &recvfrom_addr_len);
  if (received != -1) {
    //@ assert \initialized(&recvfrom_addr);
  }
  ssize_t received2 = recvfrom(sockfd, buf, sizeof(buf), 0, 0, 0);
  return rc;
}
