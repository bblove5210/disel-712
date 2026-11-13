(******************************************************************************)
(* Runnable node programs for the primary-backup VarD store.                  *)
(*                                                                            *)
(*  - [primary_loop] : forever: receive a request/ack (if any), then, if the  *)
(*                     queue head is not yet replicated send BackItUp, and if *)
(*                     it was acknowledged apply it and send the response.    *)
(*  - [backup_loop]  : forever: receive a BackItUp (if any), then send the    *)
(*                     Ack if one is owed.                                    *)
(*  - [client_loop]  : for each input, send a request to the primary and      *)
(*                     block until a response arrives; returns all responses. *)
(*                                                                            *)
(* The programs are verified against the protocol's coherence. Combined with  *)
(* [with_inv kv_ii] (see SimpleKVStoreApp.v), every state they reach also     *)
(* satisfies the inductive invariant, and thus Verdi's VarD correctness.      *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq path.
From Coq Require Import Eqdep Relation_Operators String.
From pcm Require Import axioms pred prelude ordtype finmap pcm unionmap heap.
From DiSeL Require Import Freshness State EqTypeX Protocols Worlds NetworkSem.
From DiSeL Require Import Rely Actions Injection Process Always HoareTriples.
From DiSeL Require Import InferenceRules InductiveInv While.
From DiSeL Require Import KVStoreSpec KVStoreProtocol.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Plain (non-dependent) matches inside programs; all reasoning is done
   in the verification obligations. *)
Local Unset Program Cases.
Local Obligation Tactic := idtac.

Module KVNodes.
Section KVNodes.

Variable l : Label.
Variables (p b : nid) (cls : seq nid).
Hypothesis Huniq : uniq ([:: p; b] ++ cls).

Notation kv := (KVProtocol Huniq l).
Notation W := (mkWorld kv).
Notation getS s := (getStatelet s l).
Notation loc n s := (getLocal n (getStatelet s l)).

(****************************************************************)
(*                       Generic helpers                         *)
(****************************************************************)

Lemma coh_kv s : s \In Coh W -> KVCoh p b cls (getS s).
Proof. by case=>_ _ _ _ /(_ l); rewrite prEq. Qed.

Lemma send_act_safe_kv this (t : send_trans (KVCoh p b cls)) msg to s :
  s \In Coh W -> this \in [:: p; b] ++ cls ->
  send_safe t this to (getS s) msg ->
  Actions.send_act_safe W (p:=kv) this l t msg to s.
Proof.
move=>C N S; split=>//.
- rewrite /Actions.can_send; apply/andP; split; last by exact: N.
  by rewrite -(cohD C)/= domPt inE eqxx.
rewrite /Actions.filter_hooks umfilt0=>???.
by move/esym/find_some; rewrite dom0.
Qed.

Definition always_true {B : Type} (_ : B) := true.

(****************************************************************)
(*                           Primary                             *)
(****************************************************************)

Section Primary.

Program Definition read_p_act :=
  act (@skip_action_wrapper W p l kv (prEq kv) _
         (fun s (pf : KVCoh p b cls (getS s)) => getP pf)).

Program Definition read_p :
  DHT [p, W] (fun _ => True, fun (r : pstate) m => loc p m = st :-> r) :=
  Do read_p_act.
Next Obligation.
move=>i _; apply: act_rule=>j R; split=>[|r k m]; first by case: (rely_coh R).
case=>/=H1[Cj]Z; subst j=>->R'.
by rewrite (rely_loc' l R'); case: (locP (Actions.safe_local (prEq kv) H1)).
Qed.

Program Definition tryrecv_p_act :=
  act (@tryrecv_action_wrapper W p
         (fun k _ t _ => (k == l) && ((t == t_req) || (t == t_ack))) _).
Next Obligation. by move=>????/andP[/eqP->_]; rewrite domPt inE eqxx. Qed.

Program Definition tryrecv_p :
  DHT [p, W] (fun _ => True,
              fun (_ : option (nid * nat * seq nat)) _ => True) :=
  Do tryrecv_p_act.
Next Obligation.
by move=>i _; apply: act_rule=>j R; split=>//; case: (rely_coh R).
Qed.

Program Definition send_bak_act (msg : seq nat) :=
  act (@send_action_wrapper W kv p l (prEq kv)
         (primary_send_backup_trans p b cls) _ msg b).
Next Obligation. by move=>?; rewrite !InE; do ?[by left | right]. Qed.

(* Replicate the head of the queue to the backup. *)
Program Definition send_backup (i : input) :
  DHT [p, W]
  (fun s => exists c rest d,
     loc p s = st :-> PState ((c, i) :: rest) d PIdle,
   fun (_ : seq nat) _ => True) :=
  Do (send_bak_act (enc_input i)).
Next Obligation.
move=>i s0 [c][rest][d] L; apply: act_rule=>j R; split=>//.
have Cj := proj2 (rely_coh R); have C := coh_kv Cj.
apply: send_act_safe_kv=>//; first by rewrite inE eqxx.
split=>//; exists C; rewrite -(rely_loc' _ R) in L.
by rewrite (getPK C L); split=>//; exists c, i, rest.
Qed.

Program Definition send_resp_act (to : nid) (msg : seq nat) :=
  act (@send_action_wrapper W kv p l (prEq kv)
         (primary_send_resp_trans p b cls) _ msg to).
Next Obligation. by move=>??; rewrite !InE; do ?[by left | right]. Qed.

(* Apply the acknowledged head of the queue and answer the client. *)
Program Definition send_response (c : nid) (i : input) (d : data) :
  DHT [p, W]
  (fun s => exists rest,
     loc p s = st :-> PState ((c, i) :: rest) d PAcked,
   fun (_ : seq nat) _ => True) :=
  Do (send_resp_act c (enc_resp i (vard_step i d).1)).
Next Obligation.
move=>c i d s0 [rest] L; apply: act_rule=>j R; split=>//.
have Cj := proj2 (rely_coh R); have C := coh_kv Cj.
apply: send_act_safe_kv=>//; first by rewrite inE eqxx.
rewrite -(rely_loc' _ R) in L.
have Hc: c \in cls.
- by case: (locP C)=>_; rewrite (getPK C L)/queue_wf/==>/andP[].
split=>//; exists C; rewrite (getPK C L); split=>//.
by exists i, rest.
Qed.

(* One iteration of the primary *)
Program Definition primary_body (u : unit) :
  DHT [p, W] (fun _ => True, fun (_ : unit) _ => True) :=
  Do (_ <-- tryrecv_p;
      s <-- read_p;
      match s with
      | PState ((c, i) :: _) d PIdle  => send_backup i;; ret _ _ tt
      | PState ((c, i) :: _) d PAcked => send_response c i d;; ret _ _ tt
      | _ => ret _ _ tt
      end).
Next Obligation.
move=>_ i _; apply: step; apply: call_rule=>// _ j _ _.
apply: step; apply: call_rule=>// s k L _.
case: s L=>[[|[c i'] rest] d ph] L;
  try by apply: ret_rule.
case: ph L=>L; try by apply: ret_rule.
- apply: step; apply: call_rule; first by move=>_; exists c, rest, d.
  by move=>_ m _ _; apply: ret_rule.
apply: step; apply: call_rule; first by move=>_; exists rest.
by move=>_ m _ _; apply: ret_rule.
Qed.

Definition loop_inv (_ : unit) (_ : unit) (_ : state) := True.

Program Definition primary_loop_body (u : unit) :
  {a : unit}, DHT [p, W]
  (fun s => always_true u /\ loop_inv a u s,
   fun u' s1 => loop_inv a u' s1) :=
  Do (primary_body u).
Next Obligation.
by move=>u; apply: ghC=>i a _ C; apply: call_rule.
Qed.

(* [Run] the primary runs forever *)
Program Definition primary_loop :
  DHT [p, W] (fun _ => True, fun (_ : unit) _ => False) :=
  Do (@while p W _ _ always_true loop_inv _ primary_loop_body tt).
Next Obligation. by []. Qed.
Next Obligation.
move=>i _; apply: (gh_ex (g:=tt)); apply: call_rule=>//.
by move=>x m [H _]; move: H; rewrite /always_true.
Qed.

End Primary.

(****************************************************************)
(*                            Backup                             *)
(****************************************************************)

Section Backup.

Program Definition read_b_act :=
  act (@skip_action_wrapper W b l kv (prEq kv) _
         (fun s (pf : KVCoh p b cls (getS s)) => getB Huniq pf)).

Program Definition read_b :
  DHT [b, W] (fun _ => True, fun (r : bstate) m => loc b m = st :-> r) :=
  Do read_b_act.
Next Obligation.
move=>i _; apply: act_rule=>j R; split=>[|r k m]; first by case: (rely_coh R).
case=>/=H1[Cj]Z; subst j=>->R'.
by rewrite (rely_loc' l R') (locB Huniq (Actions.safe_local (prEq kv) H1)).
Qed.

Program Definition tryrecv_b_act :=
  act (@tryrecv_action_wrapper W b
         (fun k _ t _ => (k == l) && (t == t_bak)) _).
Next Obligation. by move=>????/andP[/eqP->_]; rewrite domPt inE eqxx. Qed.

Program Definition tryrecv_b :
  DHT [b, W] (fun _ => True,
              fun (_ : option (nid * nat * seq nat)) _ => True) :=
  Do tryrecv_b_act.
Next Obligation.
by move=>i _; apply: act_rule=>j R; split=>//; case: (rely_coh R).
Qed.

Program Definition send_ack_act :=
  act (@send_action_wrapper W kv b l (prEq kv)
         (backup_send_ack_trans Huniq) _ [::] p).
Next Obligation. by rewrite !InE; do ?[by left | right]. Qed.

Program Definition send_ack :
  DHT [b, W]
  (fun s => exists d, loc b s = st :-> BState d true,
   fun (_ : seq nat) _ => True) :=
  Do send_ack_act.
Next Obligation.
move=>s0 [d] L; apply: act_rule=>j R; split=>//.
have Cj := proj2 (rely_coh R); have C := coh_kv Cj.
apply: send_act_safe_kv=>//; first by rewrite !inE eqxx orbT.
split=>//; exists C; rewrite -(rely_loc' _ R) in L.
by rewrite (getBK Huniq C L).
Qed.

(* One iteration of the backup *)
Program Definition backup_body (u : unit) :
  DHT [b, W] (fun _ => True, fun (_ : unit) _ => True) :=
  Do (_ <-- tryrecv_b;
      s <-- read_b;
      if b_owe s then send_ack;; ret _ _ tt else ret _ _ tt).
Next Obligation.
move=>_ i _; apply: step; apply: call_rule=>// _ j _ _.
apply: step; apply: call_rule=>// s k L _.
case: s L=>d [] L; last by apply: ret_rule.
apply: step; apply: call_rule; first by move=>_; exists d.
by move=>_ m _ _; apply: ret_rule.
Qed.

Program Definition backup_loop_body (u : unit) :
  {a : unit}, DHT [b, W]
  (fun s => always_true u /\ loop_inv a u s,
   fun u' s1 => loop_inv a u' s1) :=
  Do (backup_body u).
Next Obligation.
by move=>u; apply: ghC=>i a _ C; apply: call_rule.
Qed.

(* [Run] the backup runs forever *)
Program Definition backup_loop :
  DHT [b, W] (fun _ => True, fun (_ : unit) _ => False) :=
  Do (@while b W _ _ always_true loop_inv _ backup_loop_body tt).
Next Obligation. by []. Qed.
Next Obligation.
move=>i _; apply: (gh_ex (g:=tt)); apply: call_rule=>//.
by move=>x m [H _]; move: H; rewrite /always_true.
Qed.

End Backup.

(****************************************************************)
(*                            Client                             *)
(****************************************************************)

Section Client.

Variable cl : nid.
Hypothesis Hc : cl \in cls.

Program Definition send_req_act (msg : seq nat) :=
  act (@send_action_wrapper W kv cl l (prEq kv)
         (client_send_req_trans p b cls) _ msg p).
Next Obligation. by move=>?; rewrite !InE; do ?[by left | right]. Qed.

Program Definition send_request (i : input) :
  DHT [cl, W] (fun _ => True, fun (_ : seq nat) _ => True) :=
  Do (send_req_act (enc_input i)).
Next Obligation.
move=>i s0 _; apply: act_rule=>j R; split=>//.
have Cj := proj2 (rely_coh R); have C := coh_kv Cj.
apply: send_act_safe_kv=>//; first by rewrite mem_cat Hc orbT.
by split=>//; rewrite dec_enc_input.
Qed.

Program Definition tryrecv_c_act :=
  act (@tryrecv_action_wrapper W cl
         (fun k _ t _ => (k == l) && (t == t_resp)) _).
Next Obligation. by move=>????/andP[/eqP->_]; rewrite domPt inE eqxx. Qed.

Program Definition tryrecv_c :
  DHT [cl, W] (fun _ => True,
               fun (_ : option (nid * nat * seq nat)) _ => True) :=
  Do tryrecv_c_act.
Next Obligation.
by move=>i _; apply: act_rule=>j R; split=>//; case: (rely_coh R).
Qed.

(* Polling for a response *)
Definition waiting (r : option (input * output)) :=
  if r is None then true else false.

Definition wait_inv (_ : unit) (_ : option (input * output)) (_ : state) := True.

Program Definition recv_resp_body (r : option (input * output)) :
  {a : unit}, DHT [cl, W]
  (fun s => waiting r /\ wait_inv a r s,
   fun r' s1 => wait_inv a r' s1) :=
  Do (m <-- tryrecv_c;
      match m with
      | Some (_, _, msg) => ret _ _ (dec_resp msg)
      | None => ret _ _ None
      end).
Next Obligation.
move=>r; apply: ghC=>i a _ C; apply: step; apply: call_rule=>// m j _ _.
by case: m=>[[[]]|]*; apply: ret_rule.
Qed.

Program Definition recv_resp :
  DHT [cl, W] (fun _ => True,
               fun (r : option (input * output)) _ => True) :=
  Do (@while cl W _ _ waiting wait_inv _ recv_resp_body None).
Next Obligation. by []. Qed.
Next Obligation.
by move=>i _; apply: (gh_ex (g:=tt)); apply: call_rule.
Qed.

(* One request/response round trip. The fallback can never be returned:
   [recv_resp] only terminates on [Some _]. *)
Program Definition request (i : input) :
  DHT [cl, W] (fun _ => True, fun (_ : input * output) _ => True) :=
  Do (send_request i;;
      r <-- recv_resp;
      ret _ _ (if r is Some e then e
               else (i, VarD.Response EmptyString None None))).
Next Obligation.
move=>i s _; apply: step; apply: call_rule=>// _ j _ _.
apply: step; apply: call_rule=>// r k _ _.
by apply: ret_rule.
Qed.

(* Client loop over the inputs: (inputs still to send, responses so far) *)
Definition cstate := (seq input * seq (input * output))%type.

Definition c_cond (x : cstate) := if x.1 is _ :: _ then true else false.

Definition c_inv (xs : seq input) (_ : unit) (x : cstate) (_ : state) :=
  size x.1 + size x.2 = size xs.

Program Definition client_body (xs : seq input) (x : cstate) :
  {a : unit}, DHT [cl, W]
  (fun s => c_cond x /\ c_inv xs a x s,
   fun x' s1 => c_inv xs a x' s1) :=
  Do (match x with
      | (i :: rest, acc) => r <-- request i; ret _ _ (rest, rcons acc r)
      | _ => ret _ _ x
      end).
Next Obligation.
move=>xs x; apply: ghC=>s a [] Hc' HI C.
case: x Hc' HI=>[[|i rest] acc]//= _ HI.
apply: step; apply: call_rule=>// r j _ _.
apply: ret_rule=>m _.
by rewrite /c_inv/= size_rcons addnS -addSn.
Qed.

(* [Run] the client sends each input in turn and collects the responses *)
Program Definition client_loop (xs : seq input) :
  DHT [cl, W] (fun _ => True,
               fun (res : seq (input * output)) _ => size res = size xs) :=
  Do (r <-- @while cl W _ _ c_cond (c_inv xs) _ (client_body xs) (xs, [::]);
      ret _ _ r.2).
Next Obligation. by []. Qed.
Next Obligation.
move=>xs s _; apply: step; apply: (gh_ex (g:=tt)).
apply: call_rule; first by move=>_; rewrite /c_inv/= addn0.
move=>[todo acc] m [] Hc' HI _; apply: ret_rule=>m' _.
case: todo Hc' HI=>[|i rest] H HI; last by move: H.
by rewrite /c_inv/= add0n in HI.
Qed.

(* Interactive session. Inputs are produced on demand by [next], which is
   handed the previous round trip (None at the start) and returns the next
   request, or None to stop. The spec holds for every [next], so the
   extracted program may implement it with real I/O (read a command, print
   the last response). *)
Definition sess_cond (x : option input) := if x is Some _ then true else false.

Definition sess_inv (_ : unit) (_ : option input) (_ : state) := True.

Program Definition session_body
        (next : option (input * output) -> option input) (x : option input) :
  {a : unit}, DHT [cl, W]
  (fun s => sess_cond x /\ sess_inv a x s,
   fun x' s1 => sess_inv a x' s1) :=
  Do (match x with
      | Some i => r <-- request i; ret _ _ (next (Some r))
      | None => ret _ _ None
      end).
Next Obligation.
move=>next x; apply: ghC=>s a [] Hc' _ C.
case: x Hc'=>[i|]//= _.
apply: step; apply: call_rule=>// r j _ _.
by apply: ret_rule=>m _.
Qed.

(* [Run] the client serves requests from [next] until it returns None *)
Program Definition session (next : option (input * output) -> option input) :
  DHT [cl, W] (fun _ => True, fun (_ : option input) _ => True) :=
  Do (@while cl W _ _ sess_cond sess_inv _ (session_body next) (next None)).
Next Obligation. by []. Qed.
Next Obligation.
by move=>next i _; apply: (gh_ex (g:=tt)); apply: call_rule.
Qed.

End Client.

End KVNodes.
End KVNodes.

Export KVNodes.
