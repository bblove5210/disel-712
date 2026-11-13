#!/usr/bin/env bash

kvstore=KVStoreMain.native

if ! [ -x ./$kvstore ]
then
    echo "$kvstore not found!"
    echo "Run 'make $kvstore' first."
    exit 1
fi

CLUSTER="1 127.0.0.1 9101 2 127.0.0.1 9102 3 127.0.0.1 9103 4 127.0.0.1 9104"

./$kvstore -me 1 -mode primary $CLUSTER >primary.log 2>&1 &
PRIMARY=$!
./$kvstore -me 2 -mode backup  $CLUSTER >backup.log 2>&1 &
BACKUP=$!
sleep 1

./$kvstore -me 3 -mode client $CLUSTER >client3.log 2>&1 &
C3=$!
./$kvstore -me 4 -mode client $CLUSTER >client4.log 2>&1 &
C4=$!

wait $C3 $C4
kill $PRIMARY $BACKUP 2>/dev/null

grep -A100 "^client" client3.log
grep -A100 "^client" client4.log
