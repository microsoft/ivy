#include "errno.h"
#include <stdlib.h>
#include <iostream>
#include "gnutls/gnutls.h"
#include <vector>

std::vector<char> client_input;
std::vector<char> server_input;


ssize_t client_push_func(gnutls_transport_ptr_t ptr, const void* data, size_t len) {
    char *d = (char *)data;
    for (size_t i = 0; i < len; i++) {
        server_input.push_back(d[i]);
    }
    return len;
}

ssize_t client_pull_func(gnutls_transport_ptr_t ptr, void* data, size_t len){
    errno = EAGAIN;
    return -1;
}

ssize_t server_push_func(gnutls_transport_ptr_t ptr, const void* data, size_t len) {
    return len;
}

ssize_t server_pull_func(gnutls_transport_ptr_t ptr, void* data, size_t len){
    size_t res;
    res = server_input.size();
    if (len < res)
        res = len;
    if (res == 0) {
        errno = EAGAIN;
        return -1;
    }
    char *d = (char *)data;
    for (size_t i = 0; i < res; i++) {
        d[i] = server_input[i];
    }
    server_input.erase(server_input.begin(),server_input.begin()+res);
    return res;
}

int main () {
    gnutls_session_t client;
    if (gnutls_init (& client, GNUTLS_CLIENT | GNUTLS_NONBLOCK) != GNUTLS_E_SUCCESS) {
        std::cout << "gnutls_init failed\n";
        exit(1);
    }
    gnutls_transport_ptr_t ptr;
    gnutls_transport_set_ptr (client, ptr);
    gnutls_transport_set_push_function (client, client_push_func);
    gnutls_transport_set_pull_function (client, client_pull_func);
    const char *errpos;
    int pres = gnutls_priority_set_direct (client,"NORMAL:+ANON-ECDH:+ANON-DH",&errpos);
    if (pres != GNUTLS_E_SUCCESS) {
        std::cerr << "set_default_priority returned error\n";
        exit(1);
    }
    gnutls_anon_client_credentials_t cred;
    int crres = gnutls_anon_allocate_client_credentials (&cred);
    if (crres != GNUTLS_E_SUCCESS) {
        std::cerr << "anon_allocate_client_credentials returned error\n";
        exit(1);
    }
    int cres = gnutls_credentials_set (client, GNUTLS_CRD_ANON, &cred);
    if (cres != GNUTLS_E_SUCCESS) {
        std::cerr << "gnutls_credentials_set returned error\n";
        exit(1);
    }
    int res = gnutls_handshake (client);
    if (res != GNUTLS_E_SUCCESS) {
        if (res == GNUTLS_E_AGAIN) {
            std::cerr << "gnutls_handshake returned EAGAIN\n";
        } else {
            std::cerr << "gnutls_handshake returned error\n";
            exit(1);
        }
    }

    gnutls_session_t server;
    if (gnutls_init (& server, GNUTLS_SERVER | GNUTLS_NONBLOCK) != GNUTLS_E_SUCCESS) {
        std::cout << "gnutls_init failed\n";
        exit(1);
    }
    gnutls_transport_set_ptr (server, ptr);
    gnutls_transport_set_push_function (server, server_push_func);
    gnutls_transport_set_pull_function (server, server_pull_func);
    pres = gnutls_priority_set_direct (server,"NORMAL:+ANON-ECDH:+ANON-DH",&errpos);
    if (pres != GNUTLS_E_SUCCESS) {
        std::cerr << "set_default_priority returned error\n";
        exit(1);
    }
    gnutls_anon_server_credentials_t scred;
     crres = gnutls_anon_allocate_server_credentials (&scred);
    if (crres != GNUTLS_E_SUCCESS) {
        std::cerr << "anon_allocate_server_credentials returned error\n";
        exit(1);
    }
    cres = gnutls_credentials_set (server, GNUTLS_CRD_ANON, &scred);
    if (cres != GNUTLS_E_SUCCESS) {
        std::cerr << "gnutls_credentials_set returned error\n";
        exit(1);
    }
    res = gnutls_handshake (server);
    if (res != GNUTLS_E_SUCCESS) {
        if (res == GNUTLS_E_AGAIN) {
            std::cerr << "gnutls_handshake returned EAGAIN\n";
        } else {
            std::cerr << "gnutls_handshake returned error\n";
            exit(1);
        }
    }

    return 0;
}
