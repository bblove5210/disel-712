(******************************************************************************)
(* A simple application running the primary-backup VarD store on the shim.    *)
(*                                                                            *)
(* Nodes: primary 1, backup 2, and N clients 3 .. N+2, where N is chosen at   *)
(* launch time: the initial state, the world and every runnable program are   *)
(* functions of N. All programs run against the protocol strengthened with    *)
(* the inductive invariant (via [with_inv]), so each client's final state     *)
(* satisfies Verdi's VarD trace_correct.                                      *)
(*                                                                            *)
(* Check for [Run] tags to find the initial state and the runnable programs.  *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq path.
From Coq Require Import Eqdep Relation_Operators String.
From pcm Require Import pred prelude ordtype finmap pcm unionmap heap.
From DiSeL Require Import State Protocols Worlds NetworkSem Rely.
From DiSeL Require Import HoareTriples InferenceRules InductiveInv While.
From DiSeL Require Import KVStoreSpec KVStoreProtocol KVStoreInvariant KVStoreNodes.

Local Obligation Tactic := idtac.

Module SimpleKVStoreApp.

Definition l : Label := 0.

(* Primary and backup *)
Definition p : nid := 1.
Definition b : nid := 2.

Section App.

(* Number of clients *)
Variable N : nat.

(* Clients: 3, 4, ..., N+2 *)
Definition cls : seq nid := iota 3 N.

Lemma Huniq : uniq ([:: p; b] ++ cls).
Proof. by rewrite /= !inE !mem_iota iota_uniq /=. Qed.

Notation kv := (KVProtocol Huniq l).
Notation ii := (@kv_ii l p b cls Huniq).
Notation kvI := (@KVProtocolWithInv l p b cls Huniq).
Notation W := (mkWorld kvI).

(* A client node, together with the proof that it is one. *)
Definition client := sig (fun c : nid => c \in cls).

Definition client_of (n : nid) : option client :=
  (if n \in cls as t return (n \in cls = t -> option client)
   then fun H => Some (exist _ n H)
   else fun _ => None) (erefl _).

(****************************************************)
(***********        Initial state     ***************)
(****************************************************)

Notation lstate := (union_map [ordType of nid] heap).

Definition init_heap_p := st :-> init_pstate.
Definition init_heap_b := st :-> init_bstate.
Definition init_heap_c : heap := Unit.

Fixpoint clients_dstate (cs : seq nid) : lstate :=
  if cs is c :: cs' then c \\-> init_heap_c \+ clients_dstate cs' else Unit.

Definition init_dstate : lstate :=
  p \\-> init_heap_p \+ (b \\-> init_heap_b \+ clients_dstate cls).

(* Adding a fresh node keeps the local states valid, and extends the domain *)
Lemma ptUn_valid_dom k v {f : lstate} {ks} :
  valid f -> dom f =i ks -> k \notin ks ->
  valid (k \\-> v \+ f) /\ dom (k \\-> v \+ f) =i k :: ks.
Proof.
move=>V D Nk.
have Nk' : k \notin dom f by rewrite D.
have V' : valid (k \\-> v \+ f).
  by rewrite validPtUn; apply/and3P; split; [done | exact: V | exact: Nk'].
split=>// z; rewrite domPtUn inE V' /= inE -(D z).
by rewrite eq_sym.
Qed.

Lemma clients_valid_dom {cs} :
  uniq cs -> valid (clients_dstate cs) /\ dom (clients_dstate cs) =i cs.
Proof.
elim: cs=>[|c cs IH]/=; first by split=>[|z]; rewrite ?valid_unit ?dom0.
by case/andP=>Nc /IH[V D]; apply: ptUn_valid_dom.
Qed.

Lemma init_valid_dom :
  valid init_dstate /\ dom init_dstate =i [:: p; b] ++ cls.
Proof.
move: Huniq=>/= /and3P[Np Nb U].
case: (clients_valid_dom U)=>V D.
case: (ptUn_valid_dom b init_heap_b V D Nb)=>V' D'.
by apply: ptUn_valid_dom.
Qed.

Notation init_dstatelet := (DStatelet init_dstate Unit).

(* [Run] Initial state to run *)
Definition init_state : state := l \\-> init_dstatelet.

Lemma getPLoc : getLocal p init_dstatelet = init_heap_p.
Proof. by rewrite /getLocal/init_dstate/= findPtUn//; case: init_valid_dom. Qed.

Lemma getBLoc : getLocal b init_dstatelet = init_heap_b.
Proof.
case: init_valid_dom; rewrite /getLocal/init_dstate/= joinCA=>V _.
by rewrite findPtUn.
Qed.

Lemma init_kv_coh : KVCoh p b cls init_dstatelet.
Proof.
case: init_valid_dom=>V D.
split=>//=.
- by split; [rewrite valid_unit | move=>m ms; rewrite find0E].
move=>n _; case: (n =P p)=>[->|Np].
- by rewrite getPLoc; apply: localCoh_p.
case: (n =P b)=>[->|Nb].
- by rewrite getBLoc; apply: (localCoh_b Huniq).
by rewrite /localCoh/= (introF eqP Np) (introF eqP Nb).
Qed.

Lemma hook_complete_unit (c : context) : hook_complete (c, Unit).
Proof. by move=>????; rewrite dom0. Qed.

Lemma init_coh : init_state \In Coh W.
Proof.
split.
- apply/andP; split; last by rewrite valid_unit.
  by rewrite validPt.
- by rewrite/init_state validPt.
- by apply: hook_complete_unit.
- by move=>z; rewrite /init_state !domPt inE/=.
move=>k; case B: (l==k); last first.
- have X: (k \notin dom init_state) /\ (k \notin dom W.1).
    by rewrite /init_state/W/=!domPt !inE/=; move/negbT: B.
  rewrite /getProtocol /getStatelet/=.
  case: dom_find X=>//; last by move=>? _ _[].
  by move=>->[_]; case: dom_find=>//->.
move/eqP:B=>B; subst k; rewrite prEq/getStatelet/init_state findPt/=.
split; first by apply: init_kv_coh.
by apply: KVInv_init; rewrite ?getPLoc ?getBLoc.
Qed.

(****************************************************)
(***********    Runnable programs     ***************)
(****************************************************)

(* [Run] Primary *)
Program Definition run_primary (u : unit) :
  DHT [p, W] (fun i => network_rely W p init_state i,
              fun (_ : unit) m => False) :=
  Do (with_inv ii (@primary_loop l p b cls Huniq)).
Next Obligation.
move=>_ i/=R; by apply: with_inv_rule'; apply: call_rule.
Qed.

(* [Run] Backup *)
Program Definition run_backup (u : unit) :
  DHT [b, W] (fun i => network_rely W b init_state i,
              fun (_ : unit) m => False) :=
  Do (with_inv ii (@backup_loop l p b cls Huniq)).
Next Obligation.
move=>_ i/=R; by apply: with_inv_rule'; apply: call_rule.
Qed.

(* [Run] A client: issues the requests [xs] one at a time. Every response
   it gets is part of a global response trace that satisfies Verdi's
   VarD correctness predicate. *)
Program Definition run_client (c : nid) (Hc : c \in cls) (xs : seq input) :
  DHT [c, W] (fun i => network_rely W c init_state i,
              fun (res : seq (input * output)) m =>
                size res = size xs /\
                trace_correct (resp_trace (dsoup (getStatelet m l)))) :=
  Do (with_inv ii (@client_loop l p b cls Huniq c Hc xs)).
Next Obligation.
move=>c Hc xs i/=R; apply: with_inv_rule'; apply: call_rule=>// res m H _ I.
split=>//; case: I=>ps[bs][_ _ Sim _].
by apply: vard_step_1_star_trace_correct Sim.
Qed.

(* [Run] An interactive client: issues requests produced by [next] (see
   KVNodes.session) until it returns None. *)
Program Definition run_session (c : nid) (Hc : c \in cls)
        (next : option (input * output) -> option input) :
  DHT [c, W] (fun i => network_rely W c init_state i,
              fun (_ : option input) m =>
                trace_correct (resp_trace (dsoup (getStatelet m l)))) :=
  Do (with_inv ii (@session l p b cls Huniq c Hc next)).
Next Obligation.
move=>c Hc next i/=R; apply: with_inv_rule'; apply: call_rule=>// res m _ _ I _.
case: I=>ps[bs][_ _ Sim _].
by apply: vard_step_1_star_trace_correct Sim.
Qed.

End App.

End SimpleKVStoreApp.

(* [Run] Final programs to run with actual arguments supplied. The first
   argument of each is the number of clients N; a client is obtained from
   its node id with [client_of N n] (None unless 3 <= n <= N+2). *)

Definition init_state N := SimpleKVStoreApp.init_state N.
Definition p_runner N (u : unit) := SimpleKVStoreApp.run_primary N u.
Definition b_runner N (u : unit) := SimpleKVStoreApp.run_backup N u.
Definition client_of N n := SimpleKVStoreApp.client_of N n.
Definition c_runner N (c : SimpleKVStoreApp.client N) xs (u : unit) :=
  SimpleKVStoreApp.run_client N (proj1_sig c) (proj2_sig c) xs.
Definition c_session N (c : SimpleKVStoreApp.client N) next (u : unit) :=
  SimpleKVStoreApp.run_session N (proj1_sig c) (proj2_sig c) next.
