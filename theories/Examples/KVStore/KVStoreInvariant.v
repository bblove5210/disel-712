(******************************************************************************)
(* Correctness of the primary-backup VarD store in Disel.                     *)
(*                                                                            *)
(* We strengthen the protocol's coherence with an inductive invariant         *)
(* [KVInv], made of two parts that mirror Verdi's proof of                    *)
(* VarDPrimaryBackup:                                                         *)
(*                                                                            *)
(*  (1) Simulation (Verdi: PrimaryBackup.simulation)                          *)
(*        vard_step_1_star init_data (primary store) (resp_trace soup)        *)
(*      i.e. the sequence of responses emitted so far, in emission order, is  *)
(*      a trace of Verdi's single-node VarD semantics ending in the primary's *)
(*      current store.                                                        *)
(*                                                                            *)
(*  (2) Replication (Verdi: PrimaryBackup.network_invariant)                  *)
(*      relates the primary's phase/queue, the backup's state and the         *)
(*      in-flight BackItUp/Ack messages, exactly like Verdi's three cases.    *)
(*                                                                            *)
(* The headline theorem [kv_trace_correct] is Verdi's correctness statement   *)
(* for VarD (VarD.VarD.trace_correct, the same predicate that Verdi proves    *)
(* for VarDPrimaryBackup in [lifting_applied]) about the trace of all         *)
(* responses ever emitted. Since the soup never forgets a message (receiving  *)
(* only marks it inactive) and message ids are allocated in increasing order, *)
(* [resp_trace] is precisely the sequence of RequestResponse outputs, in      *)
(* order -- the Disel counterpart of Verdi's [revert_trace].                  *)
(*                                                                            *)
(* Every state reachable by programs running against                          *)
(* [KVProtocolWithInv] satisfies the invariant (Disel's coherence is          *)
(* preserved by every protocol transition and assumed by every program).      *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq path.
From Coq Require Import Eqdep Relation_Operators.
From pcm Require Import axioms pred prelude ordtype finmap pcm unionmap heap.
From DiSeL Require Import Freshness State EqTypeX Protocols Worlds NetworkSem.
From DiSeL Require Import Rely Actions Injection Process Always HoareTriples.
From DiSeL Require Import InferenceRules InductiveInv StatePredicates.
From DiSeL Require Import KVStoreSpec KVStoreProtocol.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(****************************************************************)
(*        The trace of responses, read off the message soup      *)
(****************************************************************)

Section RespTrace.

(* The (input, output) event carried by a message, if it is a response. *)
Definition resp_of (ms : msg TaggedMessage) : option (input * output) :=
  if tag (content ms) == t_resp then dec_resp (tms_cont (content ms)) else None.

(* All responses ever sent, ordered by message id, i.e. by emission time. *)
Definition resp_trace (s : soup) : seq (input * output) :=
  pmap (fun i => if find i s is Some ms then resp_of ms else None) (dom s).

Lemma resp_trace0 : resp_trace Unit = [::].
Proof. by rewrite /resp_trace dom0. Qed.

(* Receiving a message does not change the trace. *)
Lemma resp_trace_consume s i :
  valid s -> resp_trace (consume_msg s i) = resp_trace s.
Proof.
move=>V; rewrite /consume_msg; case E: (find i s)=>[m|]//.
rewrite /resp_trace (domUE _ (find_some E)).
apply: eq_in_pmap=>j _; rewrite findU/= V.
by case: ifP=>//=/eqP->; rewrite E.
Qed.

(* Sending a message appends its event (if any) to the trace. *)
Lemma resp_trace_post s m :
  valid s ->
  resp_trace (post_msg s m).1 =
  resp_trace s ++ (if resp_of m is Some e then [:: e] else [::]).
Proof.
move=>V; rewrite /resp_trace/=.
have V': valid (s \+ fresh s \\-> m) by rewrite valid_fresh.
rewrite (domUnPtK V'); last by apply/allP=>x /dom_ordfresh.
rewrite -cats1 pmap_cat; congr (_ ++ _).
- apply: eq_in_pmap=>j D.
  by rewrite findUnL // D.
rewrite /= findUnR // domPt inE eqxx findPt/=.
by case: (resp_of m).
Qed.

Lemma resp_trace_post_other s m :
  valid s -> tag (content m) != t_resp ->
  resp_trace (post_msg s m).1 = resp_trace s.
Proof.
by move=>V N; rewrite resp_trace_post // /resp_of (negbTE N) cats0.
Qed.

End RespTrace.

(****************************************************************)
(*                     The inductive invariant                   *)
(****************************************************************)

Section KVInvariant.

Variable l : Label.
Variables (p b : nid) (cls : seq nid).
Notation nodes := ([:: p; b] ++ cls).
Hypothesis Huniq : uniq nodes.

Notation kv := (KVProtocol Huniq l).
Notation kcoh := (KVCoh p b cls).
Notation getP := (@getP p b cls _).
Notation getB := (@getB p b cls Huniq _).

(* Replication invariant: Verdi's [network_invariant], phase by phase. *)
Definition net_inv (ps : pstate) (bs : bstate) (s : soup) : Prop :=
  match p_phase ps with
  | PIdle =>
    (* nothing in flight; replicas agree *)
    [/\ no_msg_from_to p b s, no_msg_from_to b p s,
        b_owe bs = false & b_store bs = p_store ps]
  | PSent =>
    exists c i rest, p_queue ps = (c, i) :: rest /\
    [\/ (* BackItUp i in flight; replicas agree *)
        [/\ msg_spec p b t_bak (enc_input i) s, no_msg_from_to b p s,
            b_owe bs = false & b_store bs = p_store ps],
        (* backup applied i and owes an Ack *)
        [/\ no_msg_from_to p b s, no_msg_from_to b p s,
            b_owe bs = true & b_store bs = (vard_step i (p_store ps)).2]
      | (* Ack in flight; backup is one step ahead *)
        [/\ no_msg_from_to p b s, msg_spec b p t_ack [::] s,
            b_owe bs = false & b_store bs = (vard_step i (p_store ps)).2]]
  | PAcked =>
    (* backup is one step ahead; primary may now apply the head *)
    exists c i rest, p_queue ps = (c, i) :: rest /\
    [/\ no_msg_from_to p b s, no_msg_from_to b p s,
        b_owe bs = false & b_store bs = (vard_step i (p_store ps)).2]
  end.

Definition KVInv (d : dstatelet) : Prop :=
  exists (ps : pstate) (bs : bstate),
    [/\ getLocal p d = st :-> ps,
        getLocal b d = st :-> bs,
        vard_step_1_star init_data (p_store ps) (resp_trace (dsoup d)) &
        net_inv ps bs (dsoup d)].

(****************************************************************)
(*                        Auxiliary lemmas                       *)
(****************************************************************)

Lemma no_msg_contra from to s i m :
  no_msg_from_to from to s ->
  find i s = Some (Msg m from to true) -> False.
Proof. by move=>H /H. Qed.

Lemma msg_spec_content from to tg cnt s i t c :
  msg_spec from to tg cnt s ->
  find i s = Some (Msg (TMsg t c) from to true) -> t = tg /\ c = cnt.
Proof. by case=>_ H /H/andP[/eqP->/eqP->]. Qed.

(* Sending a message that is neither p->b nor b->p preserves [net_inv]. *)
Lemma net_inv_post ps bs s tms from to :
  valid s ->
  ((from == p) && (to == b)) = false ->
  ((from == b) && (to == p)) = false ->
  net_inv ps bs s -> net_inv ps bs (post_msg s (Msg tms from to true)).1.
Proof.
move=>V N1 N2.
have Hpb: no_msg_from_to p b s -> no_msg_from_to p b (post_msg s (Msg tms from to true)).1.
- move=>H; case X: (from == p); last by apply: no_msg_from_toE'.
  move/eqP: X=>X; subst from; rewrite eqxx/= in N1.
  by apply: no_msg_from_toE=>//; rewrite eq_sym.
have Hbp: no_msg_from_to b p s -> no_msg_from_to b p (post_msg s (Msg tms from to true)).1.
- move=>H; case X: (from == b); last by apply: no_msg_from_toE'.
  move/eqP: X=>X; subst from; rewrite eqxx/= in N2.
  by apply: no_msg_from_toE=>//; rewrite eq_sym.
have Spb: forall cnt, msg_spec p b t_bak cnt s ->
                      msg_spec p b t_bak cnt (post_msg s (Msg tms from to true)).1.
- move=>cnt H; case X: (from == p); last by apply: msg_specE''=>//; rewrite eq_sym.
  move/eqP: X=>X; subst from; rewrite eqxx/= in N1.
  by apply: msg_specE'=>//; rewrite eq_sym.
have Sbp: forall cnt, msg_spec b p t_ack cnt s ->
                      msg_spec b p t_ack cnt (post_msg s (Msg tms from to true)).1.
- move=>cnt H; case X: (from == b); last by apply: msg_specE''=>//; rewrite eq_sym.
  move/eqP: X=>X; subst from; rewrite eqxx/= in N2.
  by apply: msg_specE'=>//; rewrite eq_sym.
rewrite /net_inv; case: (p_phase ps).
- by case=>H1 H2 H3 H4; split=>//; [apply: Hpb | apply: Hbp].
- case=>c[i][rest][Q]; case=>[[H1 H2 H3 H4]|[H1 H2 H3 H4]|[H1 H2 H3 H4]];
  exists c, i, rest; split=>//.
  + by constructor 1; split=>//; [apply: Spb | apply: Hbp].
  + by constructor 2; split=>//; [apply: Hpb | apply: Hbp].
  by constructor 3; split=>//; [apply: Hpb | apply: Sbp].
case=>c[i][rest][Q][H1 H2 H3 H4]; exists c, i, rest; split=>//.
by split=>//; [apply: Hpb | apply: Hbp].
Qed.

(* Receiving a message that is neither p->b nor b->p preserves [net_inv]. *)
Lemma net_inv_consume ps bs s i m from to :
  valid s ->
  find i s = Some (Msg m from to true) ->
  ((from == p) && (to == b)) = false ->
  ((from == b) && (to == p)) = false ->
  net_inv ps bs s -> net_inv ps bs (consume_msg s i).
Proof.
move=>V F N1 N2.
have Hn: forall x y, no_msg_from_to x y s -> no_msg_from_to x y (consume_msg s i).
- by move=>x y; apply: no_msg_from_to_consume.
have Spb: forall cnt, msg_spec p b t_bak cnt s ->
                      msg_spec p b t_bak cnt (consume_msg s i).
- move=>cnt; apply: (msg_specE_consume (to':=to) V F).
  by move: N1; rewrite (eq_sym from) (eq_sym to); case: (p == from); case: (b == to).
have Sbp: forall cnt, msg_spec b p t_ack cnt s ->
                      msg_spec b p t_ack cnt (consume_msg s i).
- move=>cnt; apply: (msg_specE_consume (to':=to) V F).
  by move: N2; rewrite (eq_sym from) (eq_sym to); case: (b == from); case: (p == to).
rewrite /net_inv; case: (p_phase ps).
- by case=>H1 H2 H3 H4; split=>//; apply: Hn.
- case=>c[j][rest][Q]; case=>[[H1 H2 H3 H4]|[H1 H2 H3 H4]|[H1 H2 H3 H4]];
  exists c, j, rest; split=>//.
  + by constructor 1; split=>//; [apply: Spb | apply: Hn].
  + by constructor 2; split=>//; apply: Hn.
  by constructor 3; split=>//; [apply: Hn | apply: Sbp].
case=>c[j][rest][Q][H1 H2 H3 H4]; exists c, j, rest; split=>//.
by split=>//; apply: Hn.
Qed.

(* Enqueueing a request does not disturb the replication invariant. *)
Lemma net_inv_enqueue ps bs s e :
  net_inv ps bs s -> net_inv (enqueue ps e) bs s.
Proof.
rewrite /net_inv /enqueue/=; case: (p_phase ps)=>//.
- by case=>c[i][rest][Q] H; exists c, i, (rcons rest e); rewrite Q.
by case=>c[i][rest][Q] H; exists c, i, (rcons rest e); rewrite Q.
Qed.

Lemma pb_neq' : (p == b) = false. Proof. exact: pb_neq Huniq. Qed.
Lemma bp_neq' : (b == p) = false. Proof. exact: bp_neq Huniq. Qed.

(* Unfolding the post-state of a transition. *)
Lemma loc_post d this loc' s' n :
  valid (dstate d) ->
  getLocal n (DStatelet (upd this loc' (dstate d)) s') =
  if n == this then loc' else getLocal n d.
Proof. by apply: getLocal_upd. Qed.

(****************************************************************)
(*                 Send transitions preserve KVInv               *)
(****************************************************************)

Notation Sinv := (@S_inv kv (fun d _ => KVInv d)).
Notation Rinv := (@R_inv kv (fun d _ => KVInv d)).

(* [1] client request *)
Program Definition s_creq : Sinv (client_send_req_trans p b cls).
Proof.
move=>this to d msg S h [ps][bs][Lp Lb Sim Net] E _ /=.
case: (S)=>H/eqP Z C M; subst to; rewrite /= /creq_step in E; case: E=>E; subst h.
have V := cohVl C; have Vs := cohVs C.
exists ps, bs; rewrite /= !loc_post //.
rewrite (eq_sym p) (eq_sym b) (cls_neq_p Huniq H) (cls_neq_b Huniq H); split=>//.
- by rewrite resp_trace_post_other.
apply: net_inv_post=>//; first by rewrite (cls_neq_p Huniq H).
by rewrite (cls_neq_b Huniq H).
Qed.

(* [2] primary sends BackItUp *)
Program Definition s_pbak : Sinv (primary_send_backup_trans p b cls).
Proof.
move=>this to d msg S h [ps][bs][Lp Lb Sim Net] E _ /=.
have [/eqP Z1 /eqP Z2 [C][Ph][c][i][rest][Q Em]] := S; subst this to.
rewrite /= /pbak_step in E; case: E=>E; subst h.
have C' := pbak_safe_coh S.
have V := cohVl C'; have Vs := cohVs C'.
rewrite (getPK (pbak_safe_coh S) Lp) (getPK C Lp) in Ph Q Em *; subst msg.
exists (PState (p_queue ps) (p_store ps) PSent), bs.
rewrite /= !loc_post // eqxx bp_neq'; split=>//.
- by rewrite resp_trace_post_other.
move: Net; rewrite /net_inv Ph Q=>[[H1 H2 H3 H4]].
exists c, i, rest; split=>//; constructor 1; split=>//.
- by apply: msg_specE.
by apply: no_msg_from_toE'=>//; rewrite pb_neq'.
Qed.

(* [3] backup sends Ack *)
Program Definition s_back : Sinv (backup_send_ack_trans Huniq).
Proof.
move=>this to d msg S h [ps][bs][Lp Lb Sim Net] E _ /=.
have [/eqP Z1 /eqP Z2 Z3 [C Ow]] := S; subst this to msg.
rewrite /= /back_step in E; case: E=>E; subst h.
have C' := back_safe_coh S.
have V := cohVl C'; have Vs := cohVs C'.
rewrite (getBK Huniq (back_safe_coh S) Lb) (getBK Huniq C Lb) in Ow *.
exists ps, (BState (b_store bs) false).
rewrite /= !loc_post // eqxx pb_neq'; split=>//.
- by rewrite resp_trace_post_other.
move: Net; rewrite /net_inv; case: (p_phase ps).
- by case=>_ _; rewrite Ow.
- case=>c[i][rest][Q]; case=>[[_ _]|[H1 H2 _ H4]|[_ _]]; rewrite ?Ow//.
  exists c, i, rest; split=>//; constructor 3; split=>//.
  + by apply: no_msg_from_toE'=>//; rewrite bp_neq'.
  by apply: msg_specE.
by case=>c[i][rest][Q][_ _]; rewrite Ow.
Qed.

(* [4] primary applies the head of its queue and responds *)
Program Definition s_presp : Sinv (primary_send_resp_trans p b cls).
Proof.
move=>this to d msg S h [ps][bs][Lp Lb Sim Net] E _ /=.
have [/eqP Z1 Hc [C][Ph][i][rest][Q Em]] := S; subst this.
rewrite /= /presp_step in E; case: E=>E; subst h.
have C' := presp_safe_coh S.
have V := cohVl C'; have Vs := cohVs C'.
rewrite (getPK (presp_safe_coh S) Lp) (getPK C Lp) in Ph Q Em *; subst msg.
exists (apply_head ps), bs.
rewrite /= !loc_post // eqxx bp_neq'; split=>//.
- rewrite resp_trace_post // /resp_of/= dec_enc_resp /apply_head Q/=.
  by apply: vard_step_1_star_snoc.
move: Net; rewrite /net_inv Ph /apply_head Q/==>[[c][i'][rest'][[Zc Zi Zr]]].
subst c i' rest'=>[[H1 H2 H3 H4]]; split=>//.
- by apply: no_msg_from_toE=>//; rewrite eq_sym (cls_neq_b Huniq Hc).
by apply: no_msg_from_toE'=>//; rewrite pb_neq'.
Qed.

(****************************************************************)
(*               Receive transitions preserve KVInv              *)
(****************************************************************)

(* [5] primary receives a request *)
Program Definition r_preq : Rinv (primary_recv_req_trans p b cls).
Proof.
move=>d from this i C m pf [ps][bs][Lp Lb Sim Net] F D Wf T _ /=.
have V := cohVl C; have Vs := cohVs C.
move: (coh_msg C F); rewrite /cohMsg/= T eqxx=>[[Hf /eqP Zt _]]; subst this.
rewrite /preq_step eqxx (getPK C Lp).
rewrite /= /preq_wf in Wf; case: (dec_input m) Wf=>[r|]// _.
exists (enqueue ps (from, r)), bs; rewrite /= !loc_post // eqxx bp_neq'.
split=>//; first by rewrite resp_trace_consume.
apply: net_inv_enqueue; apply: (net_inv_consume Vs F)=>//.
- by rewrite (cls_neq_p Huniq Hf).
by rewrite (cls_neq_b Huniq Hf).
Qed.

(* [6] backup receives BackItUp *)
Program Definition r_bbak : Rinv (backup_recv_backup_trans Huniq).
Proof.
move=>d from this i C m pf [ps][bs][Lp Lb Sim Net] F D Wf T _ /=.
have V := cohVl C; have Vs := cohVs C.
move: (coh_msg C F); rewrite /cohMsg/= T/==>[[/eqP Zf /eqP Zt _]]; subst from this.
case: m F Wf T=>t c F Wf /= T; subst t.
rewrite /bbak_step eqxx (getBK Huniq C Lb).
(* Only the "BackItUp in flight" case is possible. *)
move: Net Sim; rewrite /net_inv; case Ph: (p_phase ps).
- by case=>H1; move: (no_msg_contra H1 F).
- case=>c'[i'][rest][Q]; case=>[[H1 H2 H3 H4]|[H1 _ _ _]|[H1 _ _ _]];
  last 2 first; [by move: (no_msg_contra H1 F) | by move: (no_msg_contra H1 F)|].
  case: (msg_spec_content H1 F)=>_ Zc; subst c.
  rewrite dec_enc_input=>Sim.
  exists ps, (BState (vard_step i' (b_store bs)).2 true).
  rewrite /= !loc_post // eqxx pb_neq'; split=>//.
  + by rewrite resp_trace_consume.
  rewrite /net_inv Ph; exists c', i', rest; split=>//; constructor 2; split=>//.
  + by apply: (msg_spec_consume Vs F H1).
  + by apply: no_msg_from_to_consume.
  by rewrite H4.
by case=>c'[i'][rest][Q][H1]; move: (no_msg_contra H1 F).
Qed.

(* [7] primary receives Ack *)
Program Definition r_pack : Rinv (primary_recv_ack_trans p b cls).
Proof.
move=>d from this i C m pf [ps][bs][Lp Lb Sim Net] F D Wf T _ /=.
have V := cohVl C; have Vs := cohVs C.
move: (coh_msg C F); rewrite /cohMsg/= T/==>[[/eqP Zf /eqP Zt _]]; subst from this.
case: m F Wf T=>t c F Wf /= T; subst t.
rewrite /pack_step eqxx (getPK C Lp).
exists (PState (p_queue ps) (p_store ps) PAcked), bs.
rewrite /= !loc_post // eqxx bp_neq'; split=>//; first by rewrite resp_trace_consume.
(* Only the "Ack in flight" case is possible. *)
move: Net; rewrite /net_inv; case Ph: (p_phase ps).
- by case=>_ H2; move: (no_msg_contra H2 F).
- case=>c'[i'][rest][Q]; case=>[[_ H2 _ _]|[_ H2 _ _]|[H1 H2 H3 H4]];
  try by move: (no_msg_contra H2 F).
  rewrite /=; exists c', i', rest; split=>//; split=>//.
  + by apply: no_msg_from_to_consume.
  by apply: (msg_spec_consume Vs F H2).
by case=>c'[i'][rest][Q][_ H2]; move: (no_msg_contra H2 F).
Qed.

(* [8] client receives a response *)
Program Definition r_cresp : Rinv (client_recv_resp_trans p b cls).
Proof.
move=>d from this i C m pf [ps][bs][Lp Lb Sim Net] F D Wf T _ /=.
have V := cohVl C; have Vs := cohVs C.
move: (coh_msg C F); rewrite /cohMsg/= T/==>[[_ /eqP Zf Ht _]]; subst from.
rewrite /cresp_step.
exists ps, bs; rewrite /= !loc_post //.
rewrite (eq_sym p) (eq_sym b) (cls_neq_p Huniq Ht) (cls_neq_b Huniq Ht).
split=>//; first by rewrite resp_trace_consume.
apply: (net_inv_consume Vs F)=>//; first by rewrite (cls_neq_b Huniq Ht) andbF.
by rewrite pb_neq'.
Qed.

(****************************************************************)
(*                  Protocol with the invariant                  *)
(****************************************************************)

Definition sts' := [:: SI s_creq; SI s_pbak; SI s_back; SI s_presp].
Definition rts' := [:: RI r_preq; RI r_bbak; RI r_pack; RI r_cresp].

Program Definition kv_ii := @ProtocolWithInvariant.II _ _ sts' rts' _ _.

Definition KVProtocolWithInv := ProtocolWithIndInv kv_ii.

(****************************************************************)
(*                         Main theorems                         *)
(****************************************************************)

Notation cohI := (coh KVProtocolWithInv).

Lemma cohI_inv d : cohI d -> KVInv d.
Proof. by case. Qed.

(* Simulation: the responses emitted so far form a run of Verdi's
   single-node VarD that ends in the primary's store.
   (Verdi: PrimaryBackup.simulation) *)
Theorem kv_simulation d (C : cohI d) :
  vard_step_1_star init_data (p_store (getP (proj1 C))) (resp_trace (dsoup d)).
Proof.
have [C0 [ps][bs][Lp _ Sim _]] := C.
by rewrite (getPK (proj1 C) Lp).
Qed.

(* Correctness: every reachable state's response trace satisfies Verdi's
   VarD correctness predicate.
   (Verdi: VarDPrimaryBackup.lifting_applied) *)
Theorem kv_trace_correct d :
  cohI d -> trace_correct (resp_trace (dsoup d)).
Proof.
by case=>_ [ps][bs][_ _ Sim _]; apply: vard_step_1_star_trace_correct Sim.
Qed.

(* Replication: the backup is always either in sync with the primary or
   exactly one (acknowledged or in-flight) step ahead of it.
   (Verdi: PrimaryBackup.network_invariant) *)
Theorem kv_replication d (C : cohI d) :
  net_inv (getP (proj1 C)) (getB (proj1 C)) (dsoup d).
Proof.
have [C0 [ps][bs][Lp Lb _ Net]] := C.
by rewrite (getPK (proj1 C) Lp) (getBK Huniq (proj1 C) Lb).
Qed.

(* Only the primary ever emits responses (Verdi: pbj_NOABT). *)
Theorem kv_resp_from_primary d (C : cohI d) i ms :
  find i (dsoup d) = Some ms -> tag (content ms) = t_resp ->
  from ms = p /\ to ms \in cls.
Proof.
move=>F T; move: (coh_msg (proj1 C) F); rewrite /cohMsg T/=.
by case=>_ /eqP-> H _.
Qed.

(* The initial state satisfies the invariant. *)
Lemma KVInv_init d :
  getLocal p d = st :-> init_pstate ->
  getLocal b d = st :-> init_bstate ->
  dsoup d = Unit -> KVInv d.
Proof.
move=>Lp Lb S; exists init_pstate, init_bstate; rewrite S resp_trace0.
split=>//; first by apply: vard_step_1_star_init.
by split=>//= j tms bb; rewrite find0E.
Qed.

End KVInvariant.
