# Shared by the kvstore scripts (source it from the disel root).
#
# Nodes: primary 1, backup 2, clients 3 .. N+2, all on localhost; node i
# listens on port 9100+i.

kvstore=KVStoreMain.native

# File where kvstore-servers.sh records the number of clients, so that
# kvstore-repl.sh starts clients with the same -clients N as the servers.
KV_CLIENTS_FILE=kvstore.clients

kv_check_binary() {
    if ! [ -x ./$kvstore ]
    then
        echo "$kvstore not found!"
        echo "Run 'make kvstore' first."
        exit 1
    fi
}

kv_check_count() {
    case "$1" in
        ''|*[!0-9]*) echo "number of clients must be a non-negative integer, got '$1'"; exit 1 ;;
    esac
}

# kv_cluster N: the CLUSTER argument (ID IP PORT triples) for N clients
kv_cluster() {
    local s="1 127.0.0.1 9101 2 127.0.0.1 9102" i
    for ((i = 3; i < $1 + 3; i++)); do
        s="$s $i 127.0.0.1 $((9100 + i))"
    done
    echo "$s"
}
