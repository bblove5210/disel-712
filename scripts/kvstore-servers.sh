#!/usr/bin/env bash
# Start the KV store primary (node 1) and backup (node 2) on localhost and
# keep them running until Ctrl-C. Then talk to them with
#   ./scripts/kvstore-repl.sh 3      (and/or 4, in another terminal)
#
# Logs: primary.log, backup.log (every protocol message; VERBOSE=2 also
# dumps the world on every send, VERBOSE=0 silences the shim).

cd "$(dirname "$0")/.."

kvstore=KVStoreMain.native

if ! [ -x ./$kvstore ]
then
    echo "$kvstore not found!"
    echo "Run 'make kvstore' first."
    exit 1
fi

CLUSTER="1 127.0.0.1 9101 2 127.0.0.1 9102 3 127.0.0.1 9103 4 127.0.0.1 9104"
V=${VERBOSE:-1}

./$kvstore -me 2 -mode backup  -v $V $CLUSTER >backup.log 2>&1 &
BACKUP=$!
./$kvstore -me 1 -mode primary -v $V $CLUSTER >primary.log 2>&1 &
PRIMARY=$!
trap 'kill $PRIMARY $BACKUP 2>/dev/null' EXIT INT TERM

echo "primary pid $PRIMARY (node 1, port 9101), backup pid $BACKUP (node 2, port 9102)"
echo "logs: primary.log backup.log; Ctrl-C to stop"
echo "clients: ./scripts/kvstore-repl.sh 3   or   ./scripts/kvstore-repl.sh 4"
wait
