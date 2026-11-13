#!/usr/bin/env bash
# Run the KV store once with N batch clients (default 2): start the primary
# and backup, let every client run its fixed list of requests, print the
# results, and stop.
#
#   ./scripts/kvstore.sh [N]        (default N: $CLIENTS, else 2)

cd "$(dirname "$0")/.."
. scripts/kvstore-cluster.sh
kv_check_binary

N=${1:-${CLIENTS:-2}}
kv_check_count "$N"
CLUSTER=$(kv_cluster "$N")

./$kvstore -me 1 -mode primary -clients $N $CLUSTER >primary.log 2>&1 &
PRIMARY=$!
./$kvstore -me 2 -mode backup  -clients $N $CLUSTER >backup.log 2>&1 &
BACKUP=$!
sleep 1

CLIENT_PIDS=()
for ((c = 3; c < N + 3; c++)); do
    ./$kvstore -me $c -mode client -clients $N $CLUSTER >client$c.log 2>&1 &
    CLIENT_PIDS+=($!)
done

wait "${CLIENT_PIDS[@]}"
kill $PRIMARY $BACKUP 2>/dev/null

for ((c = 3; c < N + 3; c++)); do
    grep -A100 "^client" client$c.log
done
