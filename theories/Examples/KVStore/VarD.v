(******************************************************************************)
(* A standalone transcription of Verdi's VarD key-value store                *)
(* (verdi/theories/Systems/VarD.v), so that the Disel KV store builds        *)
(* without depending on the Verdi library.                                    *)
(*                                                                            *)
(* What is copied, and from where:                                            *)
(*   - input / output types, the handler, input_key, operate, interpret,     *)
(*     inputs_with_key, trace_correct           Verdi Systems/VarD.v          *)
(*   - the store: Verdi's LogTimeVarD, i.e. a PositiveMap indexed by the     *)
(*     injective string -> positive encoding    Verdi Lib/FMapVeryWeak.v      *)
(*   - the handler monad (GenHandler1)          Verdi Core/StateMachineHandlerMonad.v *)
(*   - single-node semantics step_1 / step_1_star                            *)
(*                                              Verdi Core/Net.v              *)
(*                                                                            *)
(* Definitions keep Verdi's names, layout and argument order. The only        *)
(* differences are that the map is used directly rather than through Verdi's *)
(* VWS functor, and the proof of [step_1_star_trace_correct] is re-done       *)
(* (Verdi's proof relies on StructTact tactics).                              *)
(*                                                                            *)
(* As in Verdi, [VarD.input] etc. live at top level and the store, handler   *)
(* and correctness theorem live in the inner module [VarD.VarD].             *)
(******************************************************************************)

From Coq Require Import String Ascii List PArith FMapPositive.
Import ListNotations.

Definition key := string.
Definition value := string.

Inductive input : Set :=
| Put : key -> value -> input
| Get : key -> input
| Del : key -> input
| CAS : key -> option value -> value -> input
| CAD : key -> value -> input.

Inductive output : Set :=
| Response : key -> option value -> option value -> output. (* uniform response *)

(****************************************************************)
(*   Verdi's IndexedString: an injective string -> positive map  *)
(****************************************************************)

Fixpoint positive_of_digits (l : list bool) (p : positive) : positive :=
  match l with
  | [] => p
  | b :: l' => if b then xI (positive_of_digits l' p) else xO (positive_of_digits l' p)
  end.

Definition list_bool_of_ascii (a : ascii) : list bool :=
  let (a0,a1,a2,a3,a4,a5,a6,a7) := a in
  [a0; a1; a2; a3; a4; a5; a6; a7].

Fixpoint index (s : string) : positive :=
  match s with
  | EmptyString => 1
  | String a s' => positive_of_digits (list_bool_of_ascii a) (index s')
  end.

Lemma positive_of_digits_inj :
  forall l l' p p',
    List.length l = List.length l' ->
    positive_of_digits l p = positive_of_digits l' p' ->
    l = l' /\ p = p'.
Proof.
  induction l as [|a l IH]; destruct l' as [|a' l']; simpl;
    intros p p' Hlen Heq; try discriminate.
  - split; auto.
  - injection Hlen as Hlen.
    destruct a, a'; try discriminate; injection Heq as Heq;
      destruct (IH _ _ _ Hlen Heq) as [-> ->]; auto.
Qed.

Theorem index_inj : forall x y, index x = index y -> x = y.
Proof.
  induction x as [|a x IH]; destruct y as [|b y]; intros H.
  - reflexivity.
  - destruct b as [[] ? ? ? ? ? ? ?]; simpl in H; discriminate.
  - destruct a as [[] ? ? ? ? ? ? ?]; simpl in H; discriminate.
  - cbn [index] in H.
    assert (Hlen : List.length (list_bool_of_ascii a) =
                   List.length (list_bool_of_ascii b)) by (destruct a, b; reflexivity).
    destruct (positive_of_digits_inj _ _ _ _ Hlen H) as [Hl Hp].
    rewrite (IH _ Hp).
    destruct a, b; cbv [list_bool_of_ascii] in Hl; inversion Hl; reflexivity.
Qed.

Module VarD.

(****************************************************************)
(*        The store (Verdi's LogTimeStringMap, unfolded)         *)
(****************************************************************)

Definition key_eq_dec := string_dec.
Definition value_eq_dec := string_dec.

Definition val_eq_dec : forall v v' : option value, {v = v'} + {v <> v'}.
  decide equality.
  auto using value_eq_dec.
Defined.

Theorem input_eq_dec : forall x y: input, {x = y} + {x <> y}.
Proof.
  decide equality;
  auto using key_eq_dec, value_eq_dec, val_eq_dec.
Defined.

Theorem output_eq_dec : forall x y: output, {x = y} + {x <> y}.
Proof.
  decide equality;
  auto using key_eq_dec, value_eq_dec, val_eq_dec.
Defined.

Definition data := PositiveMap.t string.

Definition find (k : key) (m : data) : option value := PositiveMap.find (index k) m.
Definition add (k : key) (v : value) (m : data) : data := PositiveMap.add (index k) v m.
Definition remove (k : key) (m : data) : data := PositiveMap.remove (index k) m.

Lemma find_empty k : find k (PositiveMap.empty string) = None.
Proof. apply PositiveMap.gempty. Qed.

Lemma find_add_eq k v m : find k (add k v m) = Some v.
Proof. apply PositiveMap.gss. Qed.

Lemma find_add_neq k k' v m : k <> k' -> find k (add k' v m) = find k m.
Proof. intro H; apply PositiveMap.gso; intro E; apply H, index_inj, E. Qed.

Lemma find_remove_eq k m : find k (remove k m) = None.
Proof. apply PositiveMap.grs. Qed.

Lemma find_remove_neq k k' m : k <> k' -> find k (remove k' m) = find k m.
Proof. intro H; apply PositiveMap.gro; intro E; apply H, index_inj, E. Qed.

(****************************************************************)
(*          Verdi's handler monad (StateMachineHandlerMonad)     *)
(****************************************************************)

Definition GenHandler1 (S A : Type) : Type := S -> A * S % type.

Definition ret {S A : Type} (a : A) : GenHandler1 S A := fun s => (a, s).

Definition bind {S A B : Type} (m : GenHandler1 S A) (f : A -> GenHandler1 S B) :
  GenHandler1 S B :=
  fun s =>
    let '(a, s') := m s in
    let '(b, s'') := f a s' in
    (b, s'').

Definition write_output {S O} (o : O) : GenHandler1 S O := ret o.

Definition modify {S} (f : S -> S) : GenHandler1 S unit := fun s => (tt, f s).

Definition get {S} : GenHandler1 S S := fun s => (s, s).

Definition runGenHandler1 {S A} (s : S) (h : GenHandler1 S A) : A * S % type := h s.

Local Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2))
  (at level 100, c1 at next level, right associativity).
Local Notation "e1 ;; e2" := (bind e1 (fun _ => e2))
  (at level 100, right associativity).

(****************************************************************)
(*                   The VarD state machine                      *)
(****************************************************************)

Definition getk k : GenHandler1 data (option value) :=
  db <- get ;;
  ret (find k db).

Definition setk k v : GenHandler1 data unit := modify (fun db => add k v db).

Definition delk k : GenHandler1 data unit := modify (fun db => remove k db).

Definition resp k v old : GenHandler1 data output :=
  write_output (Response k v old).

Definition VarDHandler' (inp : input) : GenHandler1 data output :=
  match inp with
    | Get k => v <- getk k ;; resp k v v
    | Put k v => old <- getk k ;; setk k v ;; resp k (Some v) old
    | Del k => old <- getk k ;; delk k ;; resp k None old
    | CAS k v v' =>
      old <- getk k ;;
          if (val_eq_dec old v) then
            (setk k v' ;; resp k (Some v') old)
          else
            resp k old old
    | CAD k v =>
      old <- getk k ;;
          if (val_eq_dec old (Some v)) then
            (delk k ;; resp k None old)
          else
            resp k old old
  end.

Definition runHandler (h : input -> GenHandler1 data output)
           (inp : input) (d : data) : output * data :=
  runGenHandler1 d (h inp).

Definition VarDHandler := runHandler VarDHandler'.

Definition init_map : data := PositiveMap.empty string.

(****************************************************************)
(*        Single-node semantics (Verdi's Net.step_1_star)        *)
(****************************************************************)

Inductive step_1 : data -> data -> list (input * output) -> Prop :=
| S1T_deliver : forall (i : input) s s' (out : output),
    VarDHandler i s = (out, s') ->
    step_1 s s' [(i, out)].

Inductive refl_trans_1n_trace {A L} (step : A -> A -> list L -> Prop) :
  A -> A -> list L -> Prop :=
| RT1nTBase : forall x, refl_trans_1n_trace step x x []
| RT1nTStep : forall x x' x'' cs cs',
    step x x' cs ->
    refl_trans_1n_trace step x' x'' cs' ->
    refl_trans_1n_trace step x x'' (cs ++ cs').

Arguments RT1nTBase {A L step x}.

Definition step_1_star := refl_trans_1n_trace step_1.

Lemma refl_trans_1n_trace_trans {A L} {step : A -> A -> list L -> Prop} {x y z cs cs'} :
  refl_trans_1n_trace step x y cs ->
  refl_trans_1n_trace step y z cs' ->
  refl_trans_1n_trace step x z (cs ++ cs').
Proof.
  intros H; revert z cs'; induction H; intros z cs'' H'; simpl; auto.
  rewrite <- app_assoc; econstructor; eauto.
Qed.

(****************************************************************)
(*                 Verdi's correctness predicate                 *)
(****************************************************************)

Definition input_key (i : input) : key :=
  match i with
    | Get k => k
    | Put k _ => k
    | Del k => k
    | CAS k _ _ => k
    | CAD k _ => k
  end.

Definition operate (op : input) (curr : option value) :=
  match op with
    | Get _ => (curr, curr)
    | Put _ v => (Some v, curr)
    | Del _ => (None, curr)
    | CAS _ v v' => if val_eq_dec curr v then (Some v', curr) else (curr, curr)
    | CAD _ v => if val_eq_dec curr (Some v) then (None, curr) else (curr, curr)
  end.

Fixpoint interpret (k : key) (ops : list input) (init : option value) :=
  match ops with
    | [] => (init, init)
    | op :: ops =>
      (operate op (fst (interpret k ops init)))
  end.

(* StructTact's filterMap *)
Fixpoint filterMap {A B} (f : A -> option B) (l : list A) : list B :=
  match l with
  | [] => []
  | x :: xs => match f x with
              | None => filterMap f xs
              | Some y => y :: filterMap f xs
              end
  end.

Definition inputs_with_key (trace : list (input * output)) (k : key) : list input :=
  filterMap (fun ev => if key_eq_dec k (input_key (fst ev)) then
                            Some (fst ev)
                          else
                            None)
            trace.

Inductive trace_correct : list (input * output) -> Prop :=
| TCnil : trace_correct []
| TCApp : forall t i v o, trace_correct t ->
                     interpret (input_key i)
                               (i :: (rev (inputs_with_key t (input_key i))))
                               None = (v, o) ->
                     trace_correct (t ++ [(i, Response (input_key i) v o)]).

(****************************************************************)
(*        VarD's correctness theorem (proof re-done here)        *)
(****************************************************************)

(* Running the handler on input i responds with [operate] applied to
   the current value of i's key... *)
Lemma handler_out i s :
  fst (VarDHandler i s) =
  Response (input_key i) (fst (operate i (find (input_key i) s)))
                         (snd (operate i (find (input_key i) s))).
Proof.
  unfold VarDHandler, runHandler, runGenHandler1, VarDHandler',
         getk, setk, delk, resp, bind, write_output, ret, get, modify.
  destruct i; simpl; try destruct (val_eq_dec _ _); reflexivity.
Qed.

(* ... and updates that key with [operate], leaving all others alone. *)
Lemma handler_state i s k :
  find k (snd (VarDHandler i s)) =
  if key_eq_dec k (input_key i) then fst (operate i (find k s)) else find k s.
Proof.
  unfold VarDHandler, runHandler, runGenHandler1, VarDHandler',
         getk, setk, delk, resp, bind, write_output, ret, get, modify.
  destruct i as [k0 v|k0|k0|k0 ov v|k0 v]; simpl;
    destruct (key_eq_dec k k0) as [<-|Hne];
    try destruct (val_eq_dec _ _); simpl;
    try rewrite find_add_eq; try rewrite find_remove_eq;
    try (rewrite find_add_neq by exact Hne);
    try (rewrite find_remove_neq by exact Hne);
    reflexivity.
Qed.

Lemma filterMap_app {A B} (f : A -> option B) l1 l2 :
  filterMap f (l1 ++ l2) = filterMap f l1 ++ filterMap f l2.
Proof.
  induction l1 as [|a l1 IH]; simpl; auto.
  destruct (f a); simpl; rewrite IH; reflexivity.
Qed.

Lemma inputs_with_key_snoc t k i o :
  inputs_with_key (t ++ [(i, o)]) k =
  inputs_with_key t k ++ (if key_eq_dec k (input_key i) then [i] else []).
Proof.
  unfold inputs_with_key; rewrite filterMap_app; simpl.
  destruct (key_eq_dec k (input_key i)); reflexivity.
Qed.

(* Induction over executions, adding one handler step at the end. *)
Lemma step_1_star_snoc_ind s0 s t :
  step_1_star s0 s t ->
  forall P : data -> list (input * output) -> Prop,
    (forall s t i, P s t ->
              P (snd (VarDHandler i s)) (t ++ [(i, fst (VarDHandler i s))])) ->
    P s0 [] -> P s t.
Proof.
  induction 1 as [x|x x' x'' cs cs' Hs Hrest IH]; intros P HP H0; auto.
  inversion Hs; subst; simpl.
  match goal with Hh : VarDHandler ?i ?y = (?o, ?y') |- _ =>
    apply (IH (fun s u => P s ((i, o) :: u)));
    [ intros s3 u i' Hu; exact (HP _ _ i' Hu)
    | pose proof (HP y [] i H0) as H1; rewrite Hh in H1; exact H1 ]
  end.
Qed.

Theorem step_1_star_trace_correct :
  forall st trace,
    step_1_star init_map st trace ->
    trace_correct trace.
Proof.
  intros st trace H.
  cut (trace_correct trace /\
       forall k, fst (interpret k (rev (inputs_with_key trace k)) None) = find k st);
    [tauto|].
  apply (step_1_star_snoc_ind _ _ _ H
           (fun s t => trace_correct t /\
                    forall k, fst (interpret k (rev (inputs_with_key t k)) None) =
                         find k s)).
  - intros s t i [Htc Hst]; cbv beta; split.
    + rewrite handler_out; apply TCApp; [exact Htc|].
      cbn [interpret]; rewrite Hst; apply surjective_pairing.
    + intros k; rewrite handler_state, inputs_with_key_snoc.
      destruct (key_eq_dec k (input_key i)).
      * rewrite rev_unit; cbn [interpret]; rewrite Hst; reflexivity.
      * rewrite app_nil_r; apply Hst.
  - split; [constructor|]; intros k; rewrite find_empty; reflexivity.
Qed.

End VarD.
