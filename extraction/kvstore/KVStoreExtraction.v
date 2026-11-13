From DiSeL Require Import DiSeLExtraction.
From DiSeL Require Import SimpleKVStoreApp.

Cd "extraction".
  Cd "kvstore".
    Separate Extraction State.StateGetters.getStatelet
                        init_state p_runner b_runner c_runner1 c_runner2.
  Cd "..".
Cd "..".
