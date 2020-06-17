#include <stdio.h>
#include <stdlib.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <unistd.h>
#include <string.h>

#define BUFFER_SIZE 1024
#define on_error(...) { fprintf(stderr, __VA_ARGS__); fflush(stderr); exit(1); }

int main (int argc, char *argv[]) {
  if (argc < 2) on_error("Usage: %s [port]\n", argv[0]);

  int port = atoi(argv[1]);

  int server_fd, client_fd, err;
  struct sockaddr_in server, client;
  char buf[BUFFER_SIZE];
  char *text = "Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do"
"eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad"
"minim veniam, quis nostrud exercitation ullamco laboris nisi ut"
"aliquip ex ea commodo consequat. Duis aute irure dolor in"
"reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla"
"pariatur. Excepteur sint occaecat cupidatat non proident, sunt in"
"culpa qui officia deserunt mollit anim id est laborum."
"Curabitur pretium tincidunt lacus. Nulla gravida orci a odio. Nullam"
"varius, turpis et commodo pharetra, est eros bibendum elit, nec luctus"
"magna felis sollicitudin mauris. Integer in mauris eu nibh euismod"
"gravida. Duis ac tellus et risus vulputate vehicula. Donec lobortis"
"risus a elit. Etiam tempor. Ut ullamcorper, ligula eu tempor congue,"
"eros est euismod turpis, id tincidunt sapien risus a quam. Maecenas"
"fermentum consequat mi. Donec fermentum. Pellentesque malesuada nulla"
"a mi. Duis sapien sem, aliquet nec, commodo eget, consequat quis,"
"neque. Aliquam faucibus, elit ut dictum aliquet, felis nisl adipiscing"
"sapien, sed malesuada diam lacus eget erat. Cras mollis scelerisque"
"nunc. Nullam arcu. Aliquam consequat. Curabitur augue lorem, dapibus"
"quis, laoreet et, pretium ac, nisi. Aenean magna nisl, mollis quis,"
"molestie eu, feugiat in, orci. In hac habitasse platea dictumst."
"Sed ut perspiciatis, unde omnis iste natus error sit voluptatem"
"accusantium doloremque laudantium, totam rem aperiam eaque ipsa, quae"
"ab illo inventore veritatis et quasi architecto beatae vitae dicta"
"sunt, explicabo. Nemo enim ipsam voluptatem, quia voluptas sit,"
"aspernatur aut odit aut fugit, sed quia consequuntur magni dolores"
"eos, qui ratione voluptatem sequi nesciunt, neque porro quisquam"
;
  char *next;
  int len;
  while(1) {
      server_fd = socket(AF_INET, SOCK_STREAM, 0);
      if (server_fd < 0) on_error("Could not create socket\n");

      server.sin_family = AF_INET;
      server.sin_port = htons(port);
      server.sin_addr.s_addr = htonl(INADDR_ANY);

      int opt_val = 1;
      setsockopt(server_fd, SOL_SOCKET, SO_REUSEADDR, &opt_val, sizeof opt_val);

      err = bind(server_fd, (struct sockaddr *) &server, sizeof(server));
      if (err < 0) on_error("Could not bind socket\n");

      client.sin_family = AF_INET;
      client.sin_port = htons(1235);
      client.sin_addr.s_addr = htonl(0x0a000002);

      while (1) {
          err = connect(server_fd, (struct sockaddr *) &client, sizeof(client));
          if (err < 0) {
              printf("Could not connect to server\n");
              sleep(1);
          }
          else break;
      }

      printf("Connect to server on %d\n", port);
      if (err < 0) on_error("Connect failed\n");

      for (next = text; *next != 0; next += len) {
          len = strlen(next);
          if (len > 512) {len = 512;}
          err = send(server_fd, next, len, 0);
          if (err < 0) on_error("Send failed\n");
          sleep(1);
      }

      int read = recv(server_fd, buf, BUFFER_SIZE, 0);
      if (read < 0) on_error("Client read failed\n");
      write(1,buf,read);

      close(server_fd);
  }
  return 0;
}
