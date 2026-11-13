(******************************************************************************)
(* Specification layer for the Disel key-value store.                         *)
(*                                                                            *)
(* Everything that defines *what* the store computes and *what it means to be *)
(* correct* is Verdi's VarD, via the standalone transcription in VarD.v       *)
(* (copied from verdi/theories/Systems/VarD.v; no Verdi dependency):          *)
(*                                                                            *)
(*   - the request/response types           VarD.input / VarD.output          *)
(*   - the state machine (handler + store)  VarD.VarD.VarDHandler / data      *)
(*   - the single-node semantics            VarD.VarD.step_1_star             *)
(*   - the correctness predicate            VarD.VarD.trace_correct           *)
(*                                                                            *)
(* VarD.VarD is Verdi's LogTimeVarD, i.e. the store is a PositiveMap indexed  *)
(* by an injective string -> positive encoding, exactly as in Verdi.          *)
(*                                                                            *)
(* Disel messages carry a payload of type [seq nat], so this file also        *)
(* defines an encoding of inputs and outputs into [seq nat] together with     *)
(* decoders and round-trip lemmas.                                            *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From Coq Require Import String Ascii.
From DiSeL Require VarD.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module KVStoreSpec.

(****************************************************************)
(*              VarD types and state machine (reused)            *)
(****************************************************************)

Definition key    := VarD.key.
Definition value  := VarD.value.
Definition input  := VarD.input.
Definition output := VarD.output.

(* The replicated state: Verdi's VarD store. *)
Definition data := VarD.VarD.data.

(* Initial store, as in Verdi. *)
Definition init_data : data := VarD.VarD.init_map.

(* One step of the VarD state machine: Verdi's handler, unchanged. *)
Definition vard_step : input -> data -> output * data := VarD.VarD.VarDHandler.

(* Verdi's single-node semantics for VarD. *)
Definition vard_step_1_star : data -> data -> seq (input * output) -> Prop :=
  VarD.VarD.step_1_star.

(* Verdi's correctness predicate for VarD traces. *)
Definition trace_correct : seq (input * output) -> Prop :=
  VarD.VarD.trace_correct.

(* Taking one handler step extends a single-node execution by one event. *)
Lemma vard_step_1_star_snoc st t i :
  vard_step_1_star init_data st t ->
  vard_step_1_star init_data (vard_step i st).2 (t ++ [:: (i, (vard_step i st).1)]).
Proof.
move=>H; apply: (VarD.VarD.refl_trans_1n_trace_trans H).
rewrite -[[:: (i, _)]]cats0.
econstructor; first by apply: VarD.VarD.S1T_deliver; apply: surjective_pairing.
by apply: VarD.VarD.RT1nTBase.
Qed.

Lemma vard_step_1_star_init : vard_step_1_star init_data init_data [::].
Proof. by apply: VarD.VarD.RT1nTBase. Qed.

(* Verdi's VarD correctness theorem, specialised to our names. *)
Theorem vard_step_1_star_trace_correct st t :
  vard_step_1_star init_data st t -> trace_correct t.
Proof. by apply: VarD.VarD.step_1_star_trace_correct. Qed.

(****************************************************************)
(*          Encoding inputs/outputs as Disel payloads             *)
(****************************************************************)

(* Strings are encoded as their length followed by character codes. *)

Fixpoint enc_chars (s : string) : seq nat :=
  match s with
  | EmptyString => [::]
  | String a s' => nat_of_ascii a :: enc_chars s'
  end.

Definition enc_string (s : string) : seq nat := String.length s :: enc_chars s.

Fixpoint dec_chars (n : nat) (l : seq nat) : option (string * seq nat) :=
  match n with
  | 0 => Some (EmptyString, l)
  | n'.+1 =>
    match l with
    | [::] => None
    | c :: l' =>
      match dec_chars n' l' with
      | Some (s, r) => Some (String (ascii_of_nat c) s, r)
      | None => None
      end
    end
  end.

Definition dec_string (l : seq nat) : option (string * seq nat) :=
  match l with
  | [::] => None
  | n :: l' => dec_chars n l'
  end.

Lemma dec_enc_string s r : dec_string (enc_string s ++ r) = Some (s, r).
Proof.
rewrite /dec_string /enc_string /=.
elim: s=>//= a s ->.
by rewrite ascii_nat_embedding.
Qed.

Arguments enc_string : simpl never.
Arguments dec_string : simpl never.

(* Optional values: 0 for None, 1 followed by the value for Some. *)

Definition enc_opt (o : option value) : seq nat :=
  match o with
  | None => [:: 0]
  | Some v => 1 :: enc_string v
  end.

Definition dec_opt (l : seq nat) : option (option value * seq nat) :=
  match l with
  | 0 :: r => Some (None, r)
  | 1 :: r =>
    match dec_string r with
    | Some (v, r') => Some (Some v, r')
    | None => None
    end
  | _ => None
  end.

Lemma dec_enc_opt o r : dec_opt (enc_opt o ++ r) = Some (o, r).
Proof. by case: o=>[v|]//=; rewrite dec_enc_string. Qed.

Arguments enc_opt : simpl never.
Arguments dec_opt : simpl never.

(* Inputs: a constructor code followed by the arguments. *)

Definition enc_input (i : input) : seq nat :=
  match i with
  | VarD.Put k v     => 0 :: enc_string k ++ enc_string v
  | VarD.Get k       => 1 :: enc_string k
  | VarD.Del k       => 2 :: enc_string k
  | VarD.CAS k ov v  => 3 :: enc_string k ++ enc_opt ov ++ enc_string v
  | VarD.CAD k v     => 4 :: enc_string k ++ enc_string v
  end.

Definition dec_input_rest (l : seq nat) : option (input * seq nat) :=
  match l with
  | 0 :: r =>
    match dec_string r with
    | Some (k, r1) =>
      match dec_string r1 with
      | Some (v, r2) => Some (VarD.Put k v, r2)
      | None => None
      end
    | None => None
    end
  | 1 :: r =>
    match dec_string r with
    | Some (k, r1) => Some (VarD.Get k, r1)
    | None => None
    end
  | 2 :: r =>
    match dec_string r with
    | Some (k, r1) => Some (VarD.Del k, r1)
    | None => None
    end
  | 3 :: r =>
    match dec_string r with
    | Some (k, r1) =>
      match dec_opt r1 with
      | Some (ov, r2) =>
        match dec_string r2 with
        | Some (v, r3) => Some (VarD.CAS k ov v, r3)
        | None => None
        end
      | None => None
      end
    | None => None
    end
  | 4 :: r =>
    match dec_string r with
    | Some (k, r1) =>
      match dec_string r1 with
      | Some (v, r2) => Some (VarD.CAD k v, r2)
      | None => None
      end
    | None => None
    end
  | _ => None
  end.

Lemma dec_enc_input_rest i r : dec_input_rest (enc_input i ++ r) = Some (i, r).
Proof.
case: i=>[k v|k|k|k ov v|k v]/=; rewrite -?catA ?dec_enc_string //.
- by rewrite dec_enc_opt dec_enc_string.
Qed.

Definition dec_input (l : seq nat) : option input :=
  match dec_input_rest l with
  | Some (i, [::]) => Some i
  | _ => None
  end.

Lemma dec_enc_input i : dec_input (enc_input i) = Some i.
Proof. by rewrite /dec_input -[enc_input i]cats0 dec_enc_input_rest. Qed.

(* Outputs: VarD has a single, uniform response constructor. *)

Definition enc_output (o : output) : seq nat :=
  match o with
  | VarD.Response k v old => enc_string k ++ enc_opt v ++ enc_opt old
  end.

Definition dec_output_rest (l : seq nat) : option (output * seq nat) :=
  match dec_string l with
  | Some (k, r1) =>
    match dec_opt r1 with
    | Some (v, r2) =>
      match dec_opt r2 with
      | Some (old, r3) => Some (VarD.Response k v old, r3)
      | None => None
      end
    | None => None
    end
  | None => None
  end.

Lemma dec_enc_output_rest o r : dec_output_rest (enc_output o ++ r) = Some (o, r).
Proof.
case: o=>k v old/=; rewrite /dec_output_rest -!catA.
by rewrite dec_enc_string dec_enc_opt dec_enc_opt.
Qed.

(* A response message carries the request it answers and the VarD
   output, i.e. exactly one (input, output) event of a VarD trace. This
   mirrors RequestResponse in Verdi's PrimaryBackup. *)

Definition enc_resp (i : input) (o : output) : seq nat :=
  enc_input i ++ enc_output o.

Definition dec_resp (l : seq nat) : option (input * output) :=
  match dec_input_rest l with
  | Some (i, r) =>
    match dec_output_rest r with
    | Some (o, [::]) => Some (i, o)
    | _ => None
    end
  | None => None
  end.

Lemma dec_enc_resp i o : dec_resp (enc_resp i o) = Some (i, o).
Proof.
rewrite /dec_resp /enc_resp dec_enc_input_rest.
by rewrite -[enc_output o]cats0 dec_enc_output_rest.
Qed.

End KVStoreSpec.

Export KVStoreSpec.
