(******************************************************************************)
(* Primary-backup replicated VarD key-value store as a Disel protocol.        *)
(*                                                                            *)
(* This is a transcription of Verdi's PrimaryBackup transformer               *)
(* (verdi/theories/Systems/PrimaryBackup.v) instantiated with VarD            *)
(* (verdi/theories/Systems/VarDPrimaryBackup.v).                              *)
(*                                                                            *)
(* Verdi PB, for reference:                                                   *)
(*   - Primary keeps a queue of inputs and a state.                           *)
(*   - Request r at Primary: if the queue is empty send BackItUp r to         *)
(*     Backup; append r to the queue.                                         *)
(*   - BackItUp i at Backup: apply i to the backup state, send Ack.           *)
(*   - Ack at Primary: pop the head x of the queue; send BackItUp for the     *)
(*     next element (if any); apply x to the primary state and output         *)
(*     RequestResponse x o.                                                   *)
(*                                                                            *)
(* Differences forced by Disel's model, none of which changes the protocol:   *)
(*                                                                            *)
(*  1. Verdi's inputs/outputs are external events at the Primary. Disel has   *)
(*     no external I/O, so clients are explicit nodes: a request is a [req]   *)
(*     message from a client to the primary, and the RequestResponse output   *)
(*     is a [resp] message from the primary back to that client.              *)
(*     The primary's queue therefore records the requesting client too.       *)
(*                                                                            *)
(*  2. A Disel receive transition cannot send. Each Verdi handler that        *)
(*     receives and then sends is split into a receive transition followed    *)
(*     by a send transition, with a phase/flag in local state recording that  *)
(*     the send is now due:                                                   *)
(*       - primary phase PIdle  : no BackItUp outstanding                     *)
(*                       PSent  : BackItUp for the queue head was sent        *)
(*                       PAcked : the backup acknowledged the queue head      *)
(*       - backup flag b_owe    : an Ack is due                               *)
(*     The primary applies the head of the queue and emits the response in a  *)
(*     single (atomic) send transition, which is the moment Verdi emits the   *)
(*     RequestResponse output.                                                *)
(*                                                                            *)
(*  3. Verdi's debugging [Read] input (which returns the raw state of a       *)
(*     node and is ignored by all of Verdi's PB/VarD theorems) is omitted.    *)
(*                                                                            *)
(* Because the Disel protocol allows sends to be delayed arbitrarily, its set *)
(* of executions is a superset of those of Verdi PB (modulo the split above); *)
(* the invariants proven in KVStoreInvariant.v hold for all of them.          *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq path.
From Coq Require Import Eqdep Relation_Operators.
From pcm Require Import axioms pred prelude ordtype finmap pcm unionmap heap.
From DiSeL Require Import Freshness State EqTypeX Protocols Worlds NetworkSem.
From DiSeL Require Import Rely Actions Injection Process Always.
From DiSeL Require Import HoareTriples InferenceRules.
From DiSeL Require Import KVStoreSpec.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module KVProtocol.

(****************************************************************)
(*                        Local states                           *)
(****************************************************************)

Inductive phase := PIdle | PSent | PAcked.

Record pstate := PState {
  p_queue : seq (nid * input);  (* pending requests: (client, request) *)
  p_store : data;               (* primary copy of the VarD store *)
  p_phase : phase               (* replication status of the queue head *)
}.

Record bstate := BState {
  b_store : data;               (* backup copy of the VarD store *)
  b_owe   : bool                (* an Ack is due to the primary *)
}.

Definition init_pstate := PState [::] init_data PIdle.
Definition init_bstate := BState init_data false.

(* All local state lives under a single pointer. *)
Definition st := ptr_nat 1.

(* Message tags *)
Definition t_req  : nat := 0.  (* client  -> primary : request          *)
Definition t_bak  : nat := 1.  (* primary -> backup  : BackItUp         *)
Definition t_ack  : nat := 2.  (* backup  -> primary : Ack              *)
Definition t_resp : nat := 3.  (* primary -> client  : RequestResponse  *)

Definition tags := [:: t_req; t_bak; t_ack; t_resp].

Section KVProtocol.

Variable p : nid.          (* primary *)
Variable b : nid.          (* backup  *)
Variable cls : seq nid.    (* clients *)

Notation nodes := ([:: p; b] ++ cls).
Hypothesis Huniq : uniq nodes.

(****************************************************************)
(*                     Node-identity lemmas                      *)
(****************************************************************)

Lemma p_in : p \in nodes. Proof. by rewrite inE eqxx. Qed.
Lemma b_in : b \in nodes. Proof. by rewrite !inE eqxx orbT. Qed.
Lemma cls_in n : n \in cls -> n \in nodes.
Proof. by rewrite mem_cat orbC=>->. Qed.

Lemma pb_neq : (p == b) = false.
Proof.
apply/negbTE/negP=>/eqP Z; subst b.
by move: Huniq; rewrite /= inE eqxx.
Qed.

Lemma bp_neq : (b == p) = false.
Proof. by rewrite eq_sym pb_neq. Qed.

Lemma cls_nodes_disj n : n \in cls -> n \notin [:: p; b].
Proof.
move=>H; move: Huniq; rewrite cat_uniq=>/and3P[_ N _].
by apply/negP=>X; move/negP: N; apply; apply/hasP; exists n.
Qed.

Lemma cls_neq_p n : n \in cls -> (n == p) = false.
Proof. by move/cls_nodes_disj; rewrite !inE negb_or=>/andP[/negbTE]. Qed.

Lemma cls_neq_b n : n \in cls -> (n == b) = false.
Proof. by move/cls_nodes_disj; rewrite !inE negb_or=>/andP[_ /negbTE]. Qed.

(****************************************************************)
(*                         Coherence                             *)
(****************************************************************)

(* Every queued request comes from a client. *)
Definition queue_wf (q : seq (nid * input)) := all (fun e => e.1 \in cls) q.

Definition localCoh (n : nid) : Pred heap :=
  [Pred h | if n == p then exists s : pstate, h = st :-> s /\ queue_wf (p_queue s)
            else if n == b then exists s : bstate, h = st :-> s
            else True].

(* Well-formed messages: right roles and decodable payloads. *)
Definition cohMsg (ms : msg TaggedMessage) : Prop :=
  let: body := content ms in
  if tag body == t_req then
    [/\ from ms \in cls, to ms == p & isSome (dec_input (tms_cont body))]
  else if tag body == t_bak then
    [/\ from ms == p, to ms == b & isSome (dec_input (tms_cont body))]
  else if tag body == t_ack then
    [/\ from ms == b, to ms == p & tms_cont body == [::]]
  else
    [/\ tag body == t_resp, from ms == p, to ms \in cls &
        isSome (dec_resp (tms_cont body))].

Definition soupCoh : Pred soup :=
  [Pred s | valid s /\ forall m ms, find m s = Some ms -> cohMsg ms].

Definition kv_coh d : Prop :=
  let: dl := dstate d in
  let: ds := dsoup d in
  [/\ soupCoh ds, dom dl =i nodes, valid dl &
      forall n, n \in nodes -> localCoh n (getLocal n d)].

Lemma l1 d : kv_coh d -> valid (dstate d).
Proof. by case. Qed.

Lemma l2 d : kv_coh d -> valid (dsoup d).
Proof. by case; case. Qed.

Lemma l3 d : kv_coh d -> dom (dstate d) =i nodes.
Proof. by case. Qed.

Definition KVCoh := CohPred (CohPredMixin l1 l2 l3).

Notation coh := KVCoh.

(****************************************************************)
(*                Generic coherence-preservation                 *)
(****************************************************************)

Lemma trans_updDom this d s :
  this \in nodes -> coh d -> dom (upd this s (dstate d)) =i nodes.
Proof.
move=>D C z; rewrite -(cohDom C) domU inE/=.
by case: ifP=>///eqP->{z}; rewrite (cohDom C) D; apply: cohVl C.
Qed.

Lemma getLocal_upd d this n loc' s' :
  valid (dstate d) ->
  getLocal n (DStatelet (upd this loc' (dstate d)) s') =
  if n == this then loc' else getLocal n d.
Proof. by move=>V; rewrite /getLocal/= findU; case: ifP=>//=; rewrite V. Qed.

Lemma send_coh d this to t msg loc' :
  coh d -> this \in nodes ->
  cohMsg (Msg (TMsg t msg) this to true) -> localCoh this loc' ->
  coh (DStatelet (upd this loc' (dstate d))
                 (post_msg (dsoup d) (Msg (TMsg t msg) this to true)).1).
Proof.
move=>C D M L; split=>/=.
- split=>[|i ms]; first by rewrite valid_fresh (cohVs C).
  rewrite findUnL ?valid_fresh ?(cohVs C)//; case: ifP=>_.
  + by case: C=>[[_ H]] _ _ _; apply: H.
  by move/findPt_inv=>[_ <-].
- by apply: trans_updDom.
- by rewrite validU; apply: cohVl C.
move=>n Ni; rewrite getLocal_upd ?(cohVl C)//.
by case: ifP=>[/eqP->|_]//; case: C=>_ _ _ /(_ n Ni).
Qed.

Lemma consume_coh d i : coh d -> soupCoh (consume_msg (dsoup d) i).
Proof.
move=>C; split=>[|m' msg]; first by apply: consume_valid; rewrite (cohVs C).
case X: (i == m');[move/eqP: X=><-{m'}|].
- case/(find_mark (cohVs C))=>tms[E]->{msg}.
  by case:(C); case=>_/(_ i tms E).
rewrite eq_sym in X.
rewrite (mark_other (cohVs C) X)=>E.
by case:(C); case=>_; move/(_ m' msg E).
Qed.

Lemma recv_coh d this i loc' :
  coh d -> this \in nodes -> localCoh this loc' ->
  coh (DStatelet (upd this loc' (dstate d)) (consume_msg (dsoup d) i)).
Proof.
move=>C D L; split=>/=; first by apply: consume_coh.
- by apply: trans_updDom.
- by rewrite validU; apply: cohVl C.
move=>n Ni; rewrite getLocal_upd ?(cohVl C)//.
by case: ifP=>[/eqP->|_]//; case: C=>_ _ _ /(_ n Ni).
Qed.

(* Coherence of the message found in the soup *)
Lemma coh_msg d (C : coh d) i ms :
  find i (dsoup d) = Some ms -> cohMsg ms.
Proof. by case: C=>[[_ H]] _ _ _; apply: H. Qed.

(****************************************************************)
(*                 Getters for typed local states                *)
(****************************************************************)

Lemma locP_ex d (C : coh d) :
  exists s : pstate, getLocal p d = st :-> s /\ queue_wf (p_queue s).
Proof. by case: C=>_ _ _ /(_ p p_in); rewrite /localCoh/= eqxx. Qed.

Lemma locB_ex d (C : coh d) : exists s : bstate, getLocal b d = st :-> s.
Proof. by case: C=>_ _ _ /(_ b b_in); rewrite /localCoh/= bp_neq eqxx. Qed.

Lemma cohStP d (C : coh d) v :
  find st (getLocal p d) = Some v -> dyn_tp v = pstate.
Proof. by case: (locP_ex C)=>s[->] _; rewrite findPt; case=><-. Qed.

Lemma cohStB d (C : coh d) v :
  find st (getLocal b d) = Some v -> dyn_tp v = bstate.
Proof. by case: (locB_ex C)=>s->; rewrite findPt; case=><-. Qed.

Definition getP d (C : coh d) : pstate :=
  match find st (getLocal p d) as f return _ = f -> _ with
    Some v => fun epf => icast (sym_eq (cohStP C epf)) (dyn_val v)
  | _ => fun epf => init_pstate
  end (erefl _).

Definition getB d (C : coh d) : bstate :=
  match find st (getLocal b d) as f return _ = f -> _ with
    Some v => fun epf => icast (sym_eq (cohStB C epf)) (dyn_val v)
  | _ => fun epf => init_bstate
  end (erefl _).

Lemma getPK d (C : coh d) s : getLocal p d = st :-> s -> getP C = s.
Proof.
move=>E; rewrite /getP/=.
by move: (cohStP C); rewrite !E/==>H; apply: eqc.
Qed.

Lemma getBK d (C : coh d) s : getLocal b d = st :-> s -> getB C = s.
Proof.
move=>E; rewrite /getB/=.
by move: (cohStB C); rewrite !E/==>H; apply: eqc.
Qed.

Lemma locP d (C : coh d) :
  getLocal p d = st :-> getP C /\ queue_wf (p_queue (getP C)).
Proof. by case: (locP_ex C)=>s[E W]; rewrite (getPK C E). Qed.

Lemma locB d (C : coh d) : getLocal b d = st :-> getB C.
Proof. by case: (locB_ex C)=>s E; rewrite (getBK C E). Qed.

Lemma getPE d d' (C : coh d) (C' : coh d') :
  getLocal p d = getLocal p d' -> getP C = getP C'.
Proof. by move=>E; apply: getPK; rewrite E; case: (locP C'). Qed.

Lemma getBE d d' (C : coh d) (C' : coh d') :
  getLocal b d = getLocal b d' -> getB C = getB C'.
Proof. by move=>E; apply: getBK; rewrite E; apply: locB. Qed.

Lemma localCoh_p s : queue_wf (p_queue s) -> localCoh p (st :-> s).
Proof. by move=>W; rewrite /localCoh/= eqxx; exists s. Qed.

Lemma localCoh_b (s : bstate) : localCoh b (st :-> s).
Proof. by rewrite /localCoh/= bp_neq eqxx; exists s. Qed.

Lemma localCoh_same d (C : coh d) n : n \in nodes -> localCoh n (getLocal n d).
Proof. by case: C=>_ _ _ /(_ n). Qed.

(****************************************************************)
(*                      Send transitions                         *)
(****************************************************************)

(* [1] Client sends a request to the primary. *)
Section ClientSendReq.

Definition creq_safe (this to : nid) (d : dstatelet) (msg : seq nat) :=
  [/\ this \in cls, to == p, coh d & isSome (dec_input msg)].

Lemma creq_safe_coh this to d m : creq_safe this to d m -> coh d.
Proof. by case. Qed.

Lemma creq_safe_in this to d m :
  creq_safe this to d m -> this \in nodes /\ to \in nodes.
Proof. by case=>H/eqP-> _ _; rewrite p_in cls_in. Qed.

Definition creq_step (this to : nid) (d : dstatelet) (msg : seq nat)
           (pf : creq_safe this to d msg) :=
  Some (getLocal this d).

Lemma creq_step_coh : s_step_coh_t coh t_req creq_step.
Proof.
move=>this to d msg pf h[]->{h}; case: (pf)=>H/eqP Z C M; subst to.
apply: send_coh=>//; first by apply: cls_in.
by apply: localCoh_same=>//; apply: cls_in.
Qed.

Lemma creq_safe_def this to d msg :
  creq_safe this to d msg <->
  exists b pf, @creq_step this to d msg pf = Some b.
Proof. by split=>[pf|]; [exists (getLocal this d), pf | case=>?[]]. Qed.

Definition client_send_req_trans :=
  SendTrans creq_safe_coh creq_safe_in creq_safe_def creq_step_coh.

End ClientSendReq.

(* [2] Primary sends BackItUp for the head of its queue. *)
Section PrimarySendBackup.

Definition pbak_safe (this to : nid) (d : dstatelet) (msg : seq nat) :=
  [/\ this == p, to == b &
      exists C : coh d,
        let: s := getP C in
        p_phase s = PIdle /\
        exists c i rest, p_queue s = (c, i) :: rest /\ msg = enc_input i].

Lemma pbak_safe_coh this to d m : pbak_safe this to d m -> coh d.
Proof. by case=>_ _[]. Qed.

Lemma pbak_safe_in this to d m :
  pbak_safe this to d m -> this \in nodes /\ to \in nodes.
Proof. by case=>/eqP->/eqP-> _; rewrite p_in b_in. Qed.

Definition pbak_step (this to : nid) (d : dstatelet) (msg : seq nat)
           (pf : pbak_safe this to d msg) :=
  let: C := pbak_safe_coh pf in
  let: s := getP C in
  Some (st :-> PState (p_queue s) (p_store s) PSent).

Lemma pbak_step_coh : s_step_coh_t coh t_bak pbak_step.
Proof.
move=>this to d msg pf h[]->{h}; have [/eqP Z1 /eqP Z2 [C][_][c][i][rest][_ E]] := pf.
subst this to msg; apply: (send_coh (pbak_safe_coh pf) p_in).
- by rewrite /cohMsg/= !eqxx dec_enc_input.
by apply: localCoh_p; case: (locP (pbak_safe_coh pf)).
Qed.

Lemma pbak_safe_def this to d msg :
  pbak_safe this to d msg <->
  exists b pf, @pbak_step this to d msg pf = Some b.
Proof. by split=>[pf|]; [eexists _, pf | case=>?[]]. Qed.

Definition primary_send_backup_trans :=
  SendTrans pbak_safe_coh pbak_safe_in pbak_safe_def pbak_step_coh.

End PrimarySendBackup.

(* [3] Backup acknowledges a BackItUp. *)
Section BackupSendAck.

Definition back_safe (this to : nid) (d : dstatelet) (msg : seq nat) :=
  [/\ this == b, to == p, msg = [::] &
      exists C : coh d, b_owe (getB C)].

Lemma back_safe_coh this to d m : back_safe this to d m -> coh d.
Proof. by case=>_ _ _[]. Qed.

Lemma back_safe_in this to d m :
  back_safe this to d m -> this \in nodes /\ to \in nodes.
Proof. by case=>/eqP->/eqP-> _ _; rewrite p_in b_in. Qed.

Definition back_step (this to : nid) (d : dstatelet) (msg : seq nat)
           (pf : back_safe this to d msg) :=
  let: C := back_safe_coh pf in
  Some (st :-> BState (b_store (getB C)) false).

Lemma back_step_coh : s_step_coh_t coh t_ack back_step.
Proof.
move=>this to d msg pf h[]->{h}; have [/eqP Z1 /eqP Z2 Z3 _] := pf.
subst this to msg; apply: (send_coh (back_safe_coh pf) b_in).
- by rewrite /cohMsg/= !eqxx.
by apply: localCoh_b.
Qed.

Lemma back_safe_def this to d msg :
  back_safe this to d msg <->
  exists b pf, @back_step this to d msg pf = Some b.
Proof. by split=>[pf|]; [eexists _, pf | case=>?[]]. Qed.

Definition backup_send_ack_trans :=
  SendTrans back_safe_coh back_safe_in back_safe_def back_step_coh.

End BackupSendAck.

(* [4] Primary applies the acknowledged head of its queue and responds. *)
Section PrimarySendResp.

Definition presp_safe (this to : nid) (d : dstatelet) (msg : seq nat) :=
  [/\ this == p, to \in cls &
      exists C : coh d,
        let: s := getP C in
        p_phase s = PAcked /\
        exists i rest, p_queue s = (to, i) :: rest /\
                       msg = enc_resp i (vard_step i (p_store s)).1].

Lemma presp_safe_coh this to d m : presp_safe this to d m -> coh d.
Proof. by case=>_ _[]. Qed.

Lemma presp_safe_in this to d m :
  presp_safe this to d m -> this \in nodes /\ to \in nodes.
Proof. by case=>/eqP-> H _; rewrite p_in cls_in. Qed.

(* Pop the head of the queue and apply it to the store. *)
Definition apply_head (s : pstate) : pstate :=
  if p_queue s is (_, i) :: rest
  then PState rest (vard_step i (p_store s)).2 PIdle
  else s.

Definition presp_step (this to : nid) (d : dstatelet) (msg : seq nat)
           (pf : presp_safe this to d msg) :=
  let: C := presp_safe_coh pf in
  Some (st :-> apply_head (getP C)).

Lemma presp_step_coh : s_step_coh_t coh t_resp presp_step.
Proof.
move=>this to d msg pf h[]->{h}; have [/eqP Z1 H [C][_][i][rest][Q E]] := pf.
subst this msg; apply: (send_coh (presp_safe_coh pf) p_in).
- by rewrite /cohMsg/= eqxx H dec_enc_resp.
apply: localCoh_p; case: (locP (presp_safe_coh pf))=>_.
case: (getP _)=>q st0 ph; rewrite /apply_head/=.
by case: q=>[|[c' i'] rest']//= /andP[].
Qed.

Lemma presp_safe_def this to d msg :
  presp_safe this to d msg <->
  exists b pf, @presp_step this to d msg pf = Some b.
Proof. by split=>[pf|]; [eexists _, pf | case=>?[]]. Qed.

Definition primary_send_resp_trans :=
  SendTrans presp_safe_coh presp_safe_in presp_safe_def presp_step_coh.

End PrimarySendResp.

(****************************************************************)
(*                     Receive transitions                       *)
(****************************************************************)

(* [5] Primary receives a request and enqueues it. *)
Section PrimaryRecvReq.

Definition preq_wf d (_ : coh d) (this from : nid) (m : TaggedMessage) :=
  isSome (dec_input m).

Definition enqueue (s : pstate) (e : nid * input) : pstate :=
  PState (rcons (p_queue s) e) (p_store s) (p_phase s).

Definition preq_step : receive_step_t coh :=
  fun this (from : nid) (m : seq nat) d (C : coh d) (pt : this \in nodes) =>
    if this == p then
      if dec_input m is Some i
      then st :-> enqueue (getP C) (from, i)
      else getLocal this d
    else getLocal this d.

Lemma preq_step_coh : r_step_coh_t preq_wf t_req preq_step.
Proof.
move=>d from this i C pf tms D F Wf T/=.
apply: recv_coh=>//; rewrite /preq_step; case: ifP=>[/eqP Z|_];
  last by apply: localCoh_same.
subst this; case: (dec_input tms)=>[r|]; last by apply: localCoh_same.
apply: localCoh_p; case: (locP C)=>_ W.
move: (coh_msg C F); rewrite /cohMsg/= T eqxx; case=>H _ _.
by rewrite /queue_wf/= all_rcons/= H.
Qed.

Definition primary_recv_req_trans := ReceiveTrans preq_step_coh.

End PrimaryRecvReq.

(* [6] Backup receives BackItUp, applies it, and owes an Ack. *)
Section BackupRecvBackup.

Definition bbak_wf d (_ : coh d) (this from : nid) (m : TaggedMessage) :=
  isSome (dec_input m).

Definition bbak_step : receive_step_t coh :=
  fun this (from : nid) (m : seq nat) d (C : coh d) (pt : this \in nodes) =>
    if this == b then
      if dec_input m is Some i
      then st :-> BState (vard_step i (b_store (getB C))).2 true
      else getLocal this d
    else getLocal this d.

Lemma bbak_step_coh : r_step_coh_t bbak_wf t_bak bbak_step.
Proof.
move=>d from this i C pf tms D F Wf T/=.
apply: recv_coh=>//; rewrite /bbak_step; case: ifP=>[/eqP Z|_];
  last by apply: localCoh_same.
subst this; case: (dec_input tms)=>[r|]; last by apply: localCoh_same.
by apply: localCoh_b.
Qed.

Definition backup_recv_backup_trans := ReceiveTrans bbak_step_coh.

End BackupRecvBackup.

(* [7] Primary receives the Ack for the queue head. *)
Section PrimaryRecvAck.

Definition pack_wf d (_ : coh d) (this from : nid) (m : TaggedMessage) := true.

Definition pack_step : receive_step_t coh :=
  fun this (from : nid) (m : seq nat) d (C : coh d) (pt : this \in nodes) =>
    if this == p then
      let: s := getP C in st :-> PState (p_queue s) (p_store s) PAcked
    else getLocal this d.

Lemma pack_step_coh : r_step_coh_t pack_wf t_ack pack_step.
Proof.
move=>d from this i C pf tms D F Wf T/=.
apply: recv_coh=>//; rewrite /pack_step; case: ifP=>[/eqP Z|_];
  last by apply: localCoh_same.
by subst this; apply: localCoh_p; case: (locP C).
Qed.

Definition primary_recv_ack_trans := ReceiveTrans pack_step_coh.

End PrimaryRecvAck.

(* [8] Client receives a response. *)
Section ClientRecvResp.

Definition cresp_wf d (_ : coh d) (this from : nid) (m : TaggedMessage) :=
  isSome (dec_resp m).

Definition cresp_step : receive_step_t coh :=
  fun this (from : nid) (m : seq nat) d (C : coh d) (pt : this \in nodes) =>
    getLocal this d.

Lemma cresp_step_coh : r_step_coh_t cresp_wf t_resp cresp_step.
Proof.
move=>d from this i C pf tms D F Wf T/=.
by apply: recv_coh=>//; apply: localCoh_same.
Qed.

Definition client_recv_resp_trans := ReceiveTrans cresp_step_coh.

End ClientRecvResp.

(****************************************************************)
(*                        The protocol                           *)
(****************************************************************)

Section Protocol.

Variable l : Label.

Definition kv_sends :=
  [:: client_send_req_trans; primary_send_backup_trans;
      backup_send_ack_trans; primary_send_resp_trans].

Definition kv_receives :=
  [:: primary_recv_req_trans; backup_recv_backup_trans;
      primary_recv_ack_trans; client_recv_resp_trans].

Program Definition KVProtocol : protocol :=
  @Protocol _ l _ kv_sends kv_receives _ _.

End Protocol.
End KVProtocol.

End KVProtocol.

Export KVProtocol.
