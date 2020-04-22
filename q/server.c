#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <time.h>
#include <unistd.h>

void handle_error(const char *msg) {
  perror(msg);
  exit(EXIT_FAILURE);
}

int sock;

void init() {
  srand(time(NULL));

  struct sockaddr_in my_addr;
  my_addr.sin_family      = AF_INET;
  char *port = getenv("PORT");
  if (port == NULL) port = "8000";
  my_addr.sin_port        = htons(atoi(port));
  my_addr.sin_addr.s_addr = INADDR_ANY;

  sock = socket(AF_INET, SOCK_STREAM, 0);
  if (bind(sock, (struct sockaddr *) &my_addr, sizeof my_addr) == -1)
    handle_error("bind");
  if (listen(sock, SOMAXCONN) == -1)
    handle_error("listen");
}

int accept_connection(int sock) {
  struct sockaddr_in peer_addr;
  socklen_t peer_addr_size;
  int cfd = accept(sock, (struct sockaddr *) &peer_addr, &peer_addr_size);
  if (cfd == -1)
    handle_error("accept");
  return cfd;
}

int recv_request(int *connection) {
  *connection = accept_connection(sock);
  char buf;
  if (recv(*connection, &buf, 1, 0) == -1)
    handle_error("recv");
  return buf;
}

void send_response(int connection, char response) {
  if (send(connection, &response, 1, 0) == -1)
    handle_error("send");
  close(connection);
}

int main() {
  init();
  const int data = rand();

  while (true) {
    int  connection;
    int  request  = recv_request(&connection);
    char response = (request == data) ? '1' : '0';
    send_response(connection, response);
  }
}
