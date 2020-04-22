#include <netinet/in.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <time.h>
#include <unistd.h>

void handle_error(const char *msg) {
  perror(msg);
  exit(EXIT_FAILURE);
}

struct sockaddr_in peer_addr;

void init() {
  srand(time(NULL));
  peer_addr.sin_family = AF_INET;
  char *port = getenv("PORT");
  if (port == NULL) port = "8000";
  peer_addr.sin_port = htons(atoi(port));
  peer_addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
}

int connect_socket() {
  int sfd = socket(AF_INET, SOCK_STREAM, 0);
  if (sfd == -1)
    handle_error("socket");
  usleep(1000);
  if (connect(sfd, (const struct sockaddr *) &peer_addr, sizeof peer_addr)
      == -1)
    handle_error("connect");
  return sfd;
}

void send_request(int *connection, char request) {
  *connection = connect_socket();
  if (send(*connection, &request, 1, 0) == -1)
    handle_error("send");
}

char recv_response(int connection) {
  char response;
  if (recv(connection, &response, 1, 0) == -1)
    handle_error("recv");
  close(connection);
  return response;
}

void fail(char *s) {
  fputs(s, stderr);
  exit(EXIT_FAILURE);
}

int main() {
  init();
  unsigned char is;
  bool known       = false;
  bool is_not[256] = {false};

  while (true) {
    int connection;
    unsigned char request = rand();
    send_request(&connection, request);
    printf("Send %x\n", request);
    char response = recv_response(connection);
    printf("Recv %c\n", response);
    switch(response) {
      case '1':
        if (is_not[request] || (known && is != request))
          fail("Wrong answer!");
        else { known = true; is = request; }
        break;
      case '0':
        if (known && is == request) fail("Wrong answer!");
        else is_not[request] = true;
        break;
      default: fail("Bad response!");
    }
  }
}
