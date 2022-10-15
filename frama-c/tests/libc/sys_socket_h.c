#include <sys/socket.h>
#include <netinet/in.h>
#include <string.h>

struct s1 {
  int a;
  char b;
};

struct s2 {
  int *p;
  double d;
};

volatile struct sockaddr_in dest;
volatile int v;

int main() {
  char *d1 = "message";
  struct s1 s1 = {42, 'A'};
  struct s2 s2 = {0, 3.125};
  int n = 501;
  double d = 5.5;
  struct iovec iov[5];
  iov[0].iov_base = d1;
  iov[0].iov_len = strlen(d1);
  iov[1].iov_base = &s1;
  iov[1].iov_len = sizeof(struct s1);
  iov[2].iov_base = &s2;
  iov[2].iov_len = sizeof(struct s2);
  iov[3].iov_base = &n;
  iov[3].iov_len = sizeof(int);
  iov[4].iov_base = &d;
  iov[4].iov_len = sizeof(double);
  struct msghdr msg;
   msg.msg_name = 0;
   msg.msg_namelen = 0;
   msg.msg_iov = iov;
   msg.msg_iovlen = 5;
   int sockfd = socket(AF_INET, SOCK_STREAM, 0);
   if (sockfd < 0) return 1;
   int r = sendmsg(sockfd, &msg, 0);
   //@ assert valid: r == -1 || r >= 0;

   msg.msg_iovlen = 6; // invalid length
   if (v) {
     sendmsg(sockfd, &msg, 0); // must fail
     //@ assert unreachable: \false;
   }
   return 0;
}
