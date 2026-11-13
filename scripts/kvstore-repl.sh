#!/usr/bin/env bash
# Interactive KV store client, talking to the servers started by
# scripts/kvstore-servers.sh.
#
#   ./scripts/kvstore-repl.sh [NODE] [extra KVStoreMain options, e.g. -v 1]
#
# NODE is a client node, 3 .. N+2 (default 3), where N is the number of
# clients the servers were started with (read from kvstore.clients).
#
# Commands: GET k | PUT k v | DEL k | CAS k old|- new | CAD k old | help | quit
# Also works non-interactively:
#   printf 'PUT x 1\nGET x\n' | ./scripts/kvstore-repl.sh 3

cd "$(dirname "$0")/.."
. scripts/kvstore-cluster.sh
kv_check_binary

if [ -f $KV_CLIENTS_FILE ]; then N=$(cat $KV_CLIENTS_FILE); else N=${CLIENTS:-2}; fi
kv_check_count "$N"

NODE=${1:-3}
shift || true
if ! [ "$NODE" -ge 3 ] 2>/dev/null || [ "$NODE" -gt $((N + 2)) ]; then
    echo "client node must be one of 3 .. $((N + 2)) (servers run with $N clients)"
    exit 1
fi

exec ./$kvstore -me "$NODE" -mode repl -clients "$N" "$@" $(kv_cluster "$N")
