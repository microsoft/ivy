#!/bin/sh

#export MINQ_LOG=connection
#export MINT_LOG=handshake

/usr/lib/go-1.10/bin/go run ${GOPATH}/src/github.com/kenmcmil/minq/bin/server/main.go --addr=10.0.0.1:4433 --server-name=10.0.0.1
