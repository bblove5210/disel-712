#!/usr/bin/env bash
# Interactive KV store client, talking to the servers started by
# scripts/kvstore-servers.sh.
#
#   ./scripts/kvstore-repl.sh [3|4] [extra KVStoreMain options, e.g. -v 1]
#
# Commands: GET k | PUT k v | DEL k | CAS k old|- new | CAD k old | help | quit
# Also works non-interactively:
#   printf 'PUT x 1\nGET x\n' | ./scripts/kvstore-repl.sh 3

cd "$(dirname "$0")/.."

kvstore=KVStoreMain.native

if ! [ -x ./$kvstore ]
then
    echo "$kvstore not found!"
    echo "Run 'make kvstore' first."
    exit 1
fi

NODE=${1:-3}
shift || true
case "$NODE" in
    3|4) ;;
    *) echo "client node must be 3 or 4 (the protocol's two client nodes)"; exit 1 ;;
esac

CLUSTER="1 127.0.0.1 9101 2 127.0.0.1 9102 3 127.0.0.1 9103 4 127.0.0.1 9104"

exec ./$kvstore -me "$NODE" -mode repl "$@" $CLUSTER
