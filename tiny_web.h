#ifndef TINY_WEB_H
#define TINY_WEB_H

#include <sys/types.h>
extern int listenfd;
/* Simplifies calls to bind(), connect(), and accept() */
typedef struct sockaddr SA;

typedef struct {
    char filename[512];
    off_t offset; /* for support Range */
    size_t end;
} http_request;

void tiny_create(int argc, char **argv);

void parse_request(int fd, struct sockaddr_in *clientaddr, http_request *req);

#endif