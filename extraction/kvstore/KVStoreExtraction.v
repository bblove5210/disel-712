From DiSeL Require Import DiSeLExtraction.
From DiSeL Require Import SimpleKVStoreApp.

Cd "extraction".
  Cd "kvstore".
    Separate Extraction State.StateGetters.getStatelet
                        init_state p_runner b_runner client_of c_runner c_session.
  Cd "..".
Cd "..".
