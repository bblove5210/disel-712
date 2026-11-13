#!/usr/bin/env bash
# Start the KV store primary (node 1) and backup (node 2) on localhost for a
# system with N client nodes (3 .. N+2), and keep them running until Ctrl-C.
#
#   ./scripts/kvstore-servers.sh [N]        (default N: $CLIENTS, else 2)
#
# Then talk to them with ./scripts/kvstore-repl.sh <node> in other
# terminals. Logs: primary.log, backup.log (every protocol message;
# VERBOSE=2 also dumps the world on every send, VERBOSE=0 silences the shim).

cd "$(dirname "$0")/.."
. scripts/kvstore-cluster.sh
kv_check_binary

N=${1:-${CLIENTS:-2}}
kv_check_count "$N"
CLUSTER=$(kv_cluster "$N")
V=${VERBOSE:-1}
echo "$N" > $KV_CLIENTS_FILE

./$kvstore -me 2 -mode backup  -clients $N -v $V $CLUSTER >backup.log 2>&1 &
BACKUP=$!
./$kvstore -me 1 -mode primary -clients $N -v $V $CLUSTER >primary.log 2>&1 &
PRIMARY=$!
trap 'kill $PRIMARY $BACKUP 2>/dev/null' EXIT INT TERM

echo "primary pid $PRIMARY (node 1, port 9101), backup pid $BACKUP (node 2, port 9102)"
echo "$N client nodes: 3 .. $((N + 2))  ->  ./scripts/kvstore-repl.sh <node>"
echo "logs: primary.log backup.log; Ctrl-C to stop"
wait
