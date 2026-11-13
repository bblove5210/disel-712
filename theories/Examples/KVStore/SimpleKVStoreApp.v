(******************************************************************************)
(* A simple application running the primary-backup VarD store on the shim.    *)
(*                                                                            *)
(* Nodes: primary 1, backup 2, clients 3 and 4. All programs run against the  *)
(* protocol strengthened with the inductive invariant (via [with_inv]), so    *)
(* each client's final state satisfies Verdi's VarD trace_correct.            *)
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

(* Primary, backup and clients *)
Definition p : nid := 1.
Definition b : nid := 2.
Definition c1 : nid := 3.
Definition c2 : nid := 4.
Definition cls : seq nid := [:: c1; c2].

Fact Huniq : uniq ([:: p; b] ++ cls). Proof. by []. Qed.
Fact Hc1 : c1 \in cls. Proof. by []. Qed.
Fact Hc2 : c2 \in cls. Proof. by []. Qed.

Notation kv := (KVProtocol Huniq l).
Notation ii := (@kv_ii l p b cls Huniq).
Notation kvI := (@KVProtocolWithInv l p b cls Huniq).
Notation W := (mkWorld kvI).

(****************************************************)
(***********        Initial state     ***************)
(****************************************************)

Definition init_heap_p := st :-> init_pstate.
Definition init_heap_b := st :-> init_bstate.
Definition init_heap_c : heap := Unit.

Definition init_dstate :=
  p \\-> init_heap_p \+
  b \\-> init_heap_b \+
  c1 \\-> init_heap_c \+
  c2 \\-> init_heap_c.

Lemma valid_init_dstate : valid init_dstate.
Proof.
case: validUn=>//=;
do?[case: validUn=>//; do?[rewrite ?validPt/=//]|by rewrite validPt/=].
- by move=>k; rewrite !domPt !inE/==>/eqP<-/eqP.
- by move=>k; rewrite domUn!inE/==>/andP[_]/orP[]; rewrite !domPt!inE/==>/eqP=><-.
move=>k; rewrite domUn!inE/==>/andP[_]/orP[]; last by rewrite !domPt!inE/==>/eqP=><-.
by rewrite domUn!inE/==>/andP[_]/orP[]; rewrite !domPt!inE/==>/eqP=><-.
Qed.

Notation init_dstatelet := (DStatelet init_dstate Unit).

(* [Run] Initial state to run *)
Definition init_state : state := l \\-> init_dstatelet.

Lemma getPLoc : getLocal p init_dstatelet = init_heap_p.
Proof.
rewrite /getLocal/init_dstate -!joinA findPtUn//.
by rewrite !joinA valid_init_dstate.
Qed.

Lemma getBLoc : getLocal b init_dstatelet = init_heap_b.
Proof.
move: valid_init_dstate; rewrite /getLocal/init_dstate.
by rewrite -!joinA joinCA=>V; rewrite findPtUn//.
Qed.

Lemma init_kv_coh : KVCoh p b cls init_dstatelet.
Proof.
split=>//=; last first.
- move=>n; rewrite !inE=>/or4P[]/eqP->{n}.
  + by rewrite getPLoc; apply: localCoh_p.
  + by rewrite getBLoc; apply: (localCoh_b Huniq).
  + by rewrite /localCoh.
  by rewrite /localCoh.
- by apply: valid_init_dstate.
- move=>z; rewrite /init_dstate !domUn !inE valid_init_dstate/=.
  rewrite !domUn !inE (validL valid_init_dstate)/=.
  rewrite !domUn !inE (validL (validL valid_init_dstate))/=.
  rewrite !domPt!inE/= !(eq_sym z).
  by case:(p==z)(b==z)(c1==z)(c2==z);case;case;case.
by split; [rewrite valid_unit | move=>m ms; rewrite find0E].
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

Open Scope string_scope.

Definition inputs1 : seq input :=
  [:: VarD.Put "x" "1";
      VarD.Get "x";
      VarD.CAS "x" (Some "1") "2";
      VarD.CAS "x" (Some "1") "3";
      VarD.Get "x";
      VarD.Del "x";
      VarD.Get "x"].

Definition inputs2 : seq input :=
  [:: VarD.Put "y" "hello";
      VarD.CAD "y" "nope";
      VarD.Get "y";
      VarD.CAD "y" "hello";
      VarD.Get "y";
      VarD.CAS "y" None "world";
      VarD.Get "y"].

End SimpleKVStoreApp.

(* [Run] Final programs to run with actual arguments supplied *)

Definition init_state := SimpleKVStoreApp.init_state.
Definition p_runner (u : unit) := SimpleKVStoreApp.run_primary u.
Definition b_runner (u : unit) := SimpleKVStoreApp.run_backup u.
Definition c_runner1 (u : unit) :=
  SimpleKVStoreApp.run_client SimpleKVStoreApp.c1 SimpleKVStoreApp.Hc1 SimpleKVStoreApp.inputs1.
Definition c_runner2 (u : unit) :=
  SimpleKVStoreApp.run_client SimpleKVStoreApp.c2 SimpleKVStoreApp.Hc2 SimpleKVStoreApp.inputs2.
