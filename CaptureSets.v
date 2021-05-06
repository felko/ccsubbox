(** Support here for Capture Sets, a.k.a a record
    of free and bound variables tracking which variables
    are captured by a particualar type. *)

Require Import Metatheory.
Require Import Tactics.
Require Import OrderedTypeEx.
Require Import OrderedType.
Require Import FSetFacts.
Require Import Atom.
Require Import Nat.
Require Export Bool.

Create HintDb csets.


(** ************************************************** *)
(** Definition of Capture Sets *)
(** ************************************************** *)

(** A captureset -- a pair of triple of free variables,
    bound variables, and if we contain the special
    `universal` variable. *)
Inductive cap : Type :=
  | cset_set : atoms -> nats -> bool -> cap.


(** ************************************************** *)
(** Constructors *)
(** ************************************************** *)

Definition empty_cset := cset_set {} {}N false.

(** The empty set may be written similarly to informal practice. *)
Notation "{}C" :=
  empty_cset : metatheory_scope.

(** Singletons *)
Definition cset_fvar (a : atom) :=
  (cset_set (AtomSet.F.singleton a) NatSet.F.empty false).
  
Definition cset_bvar (k : nat) :=
  (cset_set AtomSet.F.empty (NatSet.F.singleton k) false).

Definition cset_universal :=
  (cset_set AtomSet.F.empty NatSet.F.empty true).

(** ************************************************** *)
(** Selectors *)
(** ************************************************** *)

Definition cset_fvars (c : cap) : atoms :=
  match c with
  | cset_set A _ _ => A
  end.

Definition cset_bvars (c : cap) : nats :=
  match c with
  | cset_set _ N _ => N
  end.

Definition cset_has_universal (c : cap) : bool :=
  match c with
  | cset_set _ _ R => R
  end.



(** ************************************************** *)
(** Operations *)
(** ************************************************** *)

(* Definition cset_lvar (l : atom) :=
  (cset_set AtomSet.F.empty NatSet.F.empty (AtomSet.F.singleton l)). *)

(** Predicates for determining if a capture set explicity references
    a variable -- used for determining if a capture set is well formed.
    Don't use these predicates for determining if a capture set
    captures a variable, as one needs to also test cset_universal. *)
Definition cset_references_bvar (k : nat) (c : cap) :=
  NatSet.F.In k (cset_bvars c).

Definition cset_references_fvar (a : atom) (c : cap) :=
  AtomSet.F.In a (cset_fvars c).

Definition cset_references_bvar_dec (k : nat) (c : cap) :=
  NatSet.F.mem k (cset_bvars c).

Definition cset_references_fvar_dec (a : atom) (c : cap) :=
  AtomSet.F.mem a (cset_fvars c).

Definition cset_remove_bvar (k : nat) (c : cap) : cap :=
  cset_set (cset_fvars c) (NatSet.F.remove k (cset_bvars c)) (cset_has_universal c).

Definition cset_remove_fvar (a : atom) (c : cap) : cap :=
  cset_set (AtomSet.F.remove a (cset_fvars c)) (cset_bvars c) (cset_has_universal c).

Definition cset_references_univ_dec := cset_has_universal.
Definition cset_references_univ (c : cap) :=
    cset_references_univ_dec c = true.

(** Capture set unions are what you'd expect. *)
Definition cset_union (c1 c2 : cap) : cap :=
  cset_set 
    (AtomSet.F.union (cset_fvars c1) (cset_fvars c2))
    (NatSet.F.union (cset_bvars c1) (cset_bvars c2))
    ((cset_has_universal c1) || (cset_has_universal c2)).

Definition cset_subset_dec (C D : cap) :=
  AtomSet.F.subset (cset_fvars C) (cset_fvars D) 
    && NatSet.F.subset (cset_bvars C) (cset_bvars D)
    && (implb (cset_has_universal C) (cset_has_universal D)).

(** ************************************************** *)
(** Logical Predicates *)
(** ************************************************** *)

Definition cset_empty (c : cap) : Prop :=
  AtomSet.F.Empty (cset_fvars c) /\ NatSet.F.Empty (cset_bvars c) /\ 
    ((cset_has_universal c) = false). 

Definition cset_subset_prop (c : cap) (d : cap) : Prop :=
  AtomSet.F.Subset (cset_fvars c) (cset_fvars d) 
    /\ NatSet.F.Subset (cset_bvars c) (cset_bvars d) 
    /\  (leb (cset_has_universal c) (cset_has_universal d)).


(** ************************************************** *)
(** Properties *)
(** ************************************************** *)

Section Props.

  Variable x y a f : atom.
  Variable l m R : bool.
  Variable A A1 A2 : atoms.
  Variable k n : nat.
  Variable N N1 N2 : nats.
  Variable C D C1 C2 C3 : cap.

  Lemma cset_bvar_mem_iff : 
    cset_references_bvar k C <-> cset_references_bvar_dec k C = true.
  Proof.  
    destruct C ;
      unfold cset_references_bvar, cset_references_bvar_dec in *; 
      simpl in *; intuition.
  Qed.

  Lemma cset_fvar_mem_iff :
    cset_references_fvar a C <-> cset_references_fvar_dec a C = true.
  Proof.  
    destruct C ;
      unfold cset_references_fvar, cset_references_fvar_dec in *; 
      simpl in *; intuition.
  Qed.

  Lemma cset_univ_mem_iff :
    cset_references_univ C <-> cset_references_univ_dec C = true.
  Proof.  
    destruct C; unfold cset_references_univ, cset_references_univ_dec in *.
    reflexivity.
  Qed.

  Lemma cset_bvar_not_mem_iff : 
    ~ cset_references_bvar k C <-> cset_references_bvar_dec k C = false.
  Proof.  
    destruct C ;
      unfold cset_references_bvar, cset_references_bvar_dec in *; split; intros; simpl in *; intuition.
      rewrite <- NatSetFacts.not_mem_iff; fnsetdec.
      rewrite <- NatSetFacts.not_mem_iff in H; fnsetdec.
  Qed.

  Lemma cset_fvar_not_mem_iff :
    ~ cset_references_fvar a C <-> cset_references_fvar_dec a C = false.
  Proof.  
    destruct C ;
      unfold cset_references_fvar, cset_references_fvar_dec in *; split; intros; simpl in *; intuition.
      rewrite <- AtomSetFacts.not_mem_iff; fsetdec.
      rewrite <- AtomSetFacts.not_mem_iff in H; fsetdec.
  Qed.

  Lemma cset_univ_not_mem_iff :
    ~ cset_references_univ C <-> cset_references_univ_dec C = false.
  Proof.  
    destruct C; unfold cset_references_univ, cset_references_univ_dec, cset_has_universal in *; 
      split.
    intro; destruct b; auto*.
    intro; subst; auto.
  Qed.

  Lemma fvars_1 : cset_fvars (cset_set A N R) = A.
  Proof. unfold cset_fvars. trivial. Qed.

  Lemma bvars_1 : cset_bvars (cset_set A N R) = N.
  Proof. unfold cset_bvars. trivial. Qed.

  Lemma lvars_1 : cset_has_universal (cset_set A N R) = R.
  Proof. unfold cset_has_universal. trivial. Qed.

  Lemma fvars_union_1 : cset_fvars (cset_union C D) = AtomSet.F.union (cset_fvars C) (cset_fvars D).
  Proof. unfold cset_fvars. trivial. Qed.

  Lemma bvars_union_1 : cset_bvars (cset_union C D) = NatSet.F.union (cset_bvars C) (cset_bvars D).
  Proof. unfold cset_bvars. trivial. Qed.

  Lemma lvars_union_1 : cset_has_universal (cset_union C D) = orb (cset_has_universal C) (cset_has_universal D).
  Proof. unfold cset_has_universal. trivial. Qed.

  Lemma remove_fvar_1 : cset_remove_fvar x (cset_set A N R) = (cset_set (AtomSet.F.remove x A) N R).
  Proof. intros. unfold cset_remove_fvar in *; simpl in *. trivial. Qed.

  Lemma remove_bvar_1 : cset_remove_bvar k (cset_set A N R) = (cset_set A (NatSet.F.remove k N) R).
  Proof. intros. unfold cset_remove_bvar in *; simpl in *. trivial. Qed.

  Lemma mem_bvar_1 : cset_references_bvar k C -> cset_references_bvar_dec k C = true.
  Proof. rewrite cset_bvar_mem_iff; trivial. Qed.

  Lemma mem_bvar_2 : cset_references_bvar_dec k C = true -> cset_references_bvar k C.
  Proof. rewrite <- cset_bvar_mem_iff; trivial. Qed.

  Lemma mem_fvar_1 : cset_references_fvar a C -> cset_references_fvar_dec a C = true.
  Proof. rewrite cset_fvar_mem_iff; trivial. Qed.

  Lemma mem_fvar_2 : cset_references_fvar_dec a C = true -> cset_references_fvar a C.
  Proof. rewrite <- cset_fvar_mem_iff; trivial. Qed.

  Lemma mem_lvar_1 : cset_references_univ C -> cset_references_univ_dec C = true.
  Proof. rewrite cset_univ_mem_iff; trivial. Qed.

  Lemma mem_lvar_2 : cset_references_univ_dec C = true -> cset_references_univ C.
  Proof. rewrite <- cset_univ_mem_iff; trivial. Qed.

  Lemma In_bvar_1 : k = n -> cset_references_bvar k C -> cset_references_bvar n C.
  Proof. intros; subst; trivial. Qed.

  Lemma In_fvar_1 : a = f -> cset_references_fvar a C -> cset_references_fvar f C.
  Proof. intros; subst; trivial. Qed.

  Lemma Is_empty : cset_empty empty_cset.
  Proof. repeat split. fsetdec. fnsetdec. Qed.

  Lemma union_fvar_1 : cset_references_fvar x (cset_union C D) -> cset_references_fvar x C \/ cset_references_fvar x D.
  Proof. intros. unfold cset_union, cset_references_fvar in *; simpl in *. fsetdec. Qed.

  Lemma union_fvar_2 : cset_references_fvar x C -> cset_references_fvar x (cset_union C D).
  Proof. unfold cset_union, cset_references_fvar in *; simpl in *. fsetdec. Qed.

  Lemma union_fvar_3 : cset_references_fvar x D -> cset_references_fvar x (cset_union C D).
  Proof. unfold cset_union, cset_references_fvar in *; simpl in *. fsetdec. Qed.

  Lemma union_bvar_1 : cset_references_bvar k (cset_union C D) -> cset_references_bvar k C \/ cset_references_bvar k D.
  Proof. intros. unfold cset_union, cset_references_bvar in *; simpl in *. fnsetdec. Qed.

  Lemma union_bvar_2 : cset_references_bvar k C -> cset_references_bvar k (cset_union C D).
  Proof. unfold cset_union, cset_references_bvar in *; simpl in *. fnsetdec. Qed.

  Lemma union_bvar_3 : cset_references_bvar k D -> cset_references_bvar k (cset_union C D).
  Proof. unfold cset_union, cset_references_bvar in *; simpl in *. fnsetdec. Qed.

  Lemma union_lvar_1 : cset_references_univ (cset_union C D) -> 
    cset_references_univ C \/ cset_references_univ D.
  Proof. intros. unfold cset_union, cset_references_univ in *; simpl in *.
    rewrite orb_true_iff in H; auto*.
  Qed.

  Lemma union_lvar_2 : cset_references_univ C -> cset_references_univ (cset_union C D).
  Proof. unfold cset_union, cset_references_univ in *; simpl in *. intro.
    rewrite orb_true_iff. auto. Qed.

  Lemma union_lvar_3 : cset_references_univ D -> cset_references_univ (cset_union C D).
  Proof. unfold cset_union, cset_references_univ in *; simpl in *. intro.
    rewrite orb_true_iff. auto. Qed.

  Lemma union_sub_1 : cset_subset_prop C D -> cset_union D C = D.
  Proof. 
    unfold cset_union, cset_subset_prop, cset_fvars, cset_bvars, cset_has_universal. 
    intros. destruct C; destruct D; simpl; f_equal.
    fsetdec. fnsetdec.
      destruct b; destruct b0; auto*.
  Qed.
  
  Lemma union_sub_2 : cset_subset_prop C D -> D = cset_union D C.
  Proof. 
    unfold cset_union, cset_subset_prop, cset_fvars, cset_bvars, cset_has_universal. 
    intros. destruct C; destruct D; simpl; f_equal.
    fsetdec. fnsetdec.
      destruct b; destruct b0; auto*.
  Qed.

  Lemma union_subset_distribute_1 : cset_subset_prop C1 C2 -> cset_subset_prop (cset_union C1 D) (cset_union C2 D).
  Proof. 
    intros. unfold cset_subset_prop in *; inversion H as [Sub_F [Sub_B Sub_A]];
    unfold cset_union, cset_fvars, cset_bvars, cset_has_universal, cset_fvar in *; destruct C1; destruct C2.
    repeat split; try fsetdec; try fnsetdec.
      destruct b; destruct b0; unfold leb in *; simpl in *; destruct D; destruct b; auto*.
  Qed.

End Props.

(* TODO defined here to avoid all the implicit arguments *)
Lemma subset_univ_1 : forall R C, 
  cset_subset_prop R C -> cset_references_univ R -> cset_references_univ C.
Proof. unfold cset_references_univ, cset_subset_prop; intros.
  destruct H as [_ [_ H]]. unfold cset_has_universal, cset_references_univ_dec in *; destruct R;
    destruct C; unfold cset_has_universal, leb in *; destruct b; destruct b0; auto*. Qed.

Hint Rewrite 
  fvars_1 bvars_1 lvars_1 
  fvars_union_1 bvars_union_1 lvars_union_1 
  remove_fvar_1 remove_bvar_1 
: csets.


Hint Resolve 
  mem_bvar_1 mem_fvar_1 Is_empty 
  union_fvar_1 union_fvar_2 union_fvar_3 
  union_bvar_1 union_bvar_2 union_bvar_3
  union_lvar_1 union_lvar_2 union_lvar_3 
  union_sub_1 union_sub_2 union_subset_distribute_1
  subset_univ_1
: core.

Hint Immediate In_bvar_1 In_fvar_1 mem_bvar_2 mem_fvar_2 mem_lvar_2 : core.

(* Some subset properties *)
Lemma subset_refl : forall C,
  cset_subset_prop C C.
Proof.
  intros. unfold cset_subset_prop. repeat split. fsetdec. fnsetdec.
    unfold leb; destruct C; unfold cset_has_universal; destruct b; auto*.
Qed.

Lemma subset_union_left : forall C1 C2,
  cset_subset_prop C1 (cset_union C1 C2).
Proof.
  intros. destruct C1. destruct C2. unfold cset_subset_prop, cset_union, cset_fvars,
    cset_bvars, cset_has_universal. repeat split. fsetdec. fnsetdec.
    destr_bool.
Qed.

Lemma subset_union_right : forall C1 C2,
  cset_subset_prop C2 (cset_union C1 C2).
Proof.
  intros. destruct C1. destruct C2. unfold cset_subset_prop, cset_union, cset_fvars,
    cset_bvars, cset_has_universal. repeat split. fsetdec. fnsetdec.
    destr_bool.
Qed.

Lemma subset_trans : forall A B C,
  cset_subset_prop A B -> cset_subset_prop B C -> cset_subset_prop A C.
Proof.
  intros * AB BC.
  inversion AB as [ABF [ABN ABL]]; subst; inversion BC as [BCF [BCN BCL]]; subst...
  repeat (econstructor; try fsetdec; try fnsetdec)...
  destruct A; destruct B; destruct C; unfold cset_has_universal in *; destr_bool.
Qed.

Hint Immediate subset_union_left subset_union_right  subset_refl: core.


(***********)
(* Tactics *)
(***********)

Ltac rewrite_set_facts_in H :=
  match type of H with
  | true = _ => symmetry in H
  | false = _ => symmetry in H
  | _ => idtac
  end;
  match type of H with
  | NatSet.F.mem _ _ = true => rewrite <- NatSetFacts.mem_iff in H
  | NatSet.F.mem _ _ = false => rewrite <- NatSetFacts.not_mem_iff in H
  | AtomSet.F.mem _ _ = true => rewrite <- AtomSetFacts.mem_iff in H
  | AtomSet.F.mem _ _ = false => rewrite <- AtomSetFacts.not_mem_iff in H
  | cset_references_bvar_dec _ _ = true => rewrite <- cset_bvar_mem_iff in H
  | cset_references_fvar_dec _ _ = true => rewrite <- cset_fvar_mem_iff in H
  | cset_references_univ_dec _ _ = true => rewrite <- cset_univ_mem_iff in H
  | cset_references_bvar_dec _ _ = false => rewrite <- cset_bvar_not_mem_iff in H
  | cset_references_fvar_dec _ _ = false => rewrite <- cset_fvar_not_mem_iff in H
  | cset_references_univ_dec _ _ = false => rewrite <- cset_univ_not_mem_iff in H
  end.

Ltac rewrite_set_facts_back_in H :=
  match type of H with
  | true = _ => symmetry in H
  | false = _ => symmetry in H
  | _ => idtac
  end;
  match type of H with
  | NatSet.F.In _ _          => rewrite -> NatSetFacts.mem_iff in H
  | (~ NatSet.F.In _ _)      => rewrite -> NatSetFacts.not_mem_iff in H
  | AtomSet.F.In _ _         => rewrite -> AtomSetFacts.mem_iff in H
  | (~ AtomSet.F.In _ _)     => rewrite -> AtomSetFacts.not_mem_iff in H
  | cset_references_bvar _ _ => rewrite -> cset_bvar_mem_iff in H
  | cset_references_fvar _ _ => rewrite -> cset_fvar_mem_iff in H
  | cset_references_univ _ _ => rewrite -> cset_univ_mem_iff in H
  | (~ cset_references_bvar _ _) => rewrite -> cset_bvar_not_mem_iff in H
  | (~ cset_references_fvar _ _) => rewrite -> cset_fvar_not_mem_iff in H
  | (~ cset_references_univ _ _) => rewrite -> cset_univ_not_mem_iff in H
  end.


Ltac simpl_in_cset :=
  let go H := rewrite_set_facts_back_in H; try rewrite H in *; rewrite_set_facts_in H in
  match goal with
  | H: cset_references_bvar_dec ?I ?C = ?B |- _ => try rewrite H in *
  | H: ~ (cset_references_bvar _ _) |- _ => go H
  | H: (cset_references_bvar _ _)   |- _ => go H
  | H: ~ (cset_references_fvar _ _) |- _ => go H
  | H: (cset_references_fvar _ _)   |- _ => go H
  | H: ~ (cset_references_univ _ _) |- _ => go H
  | H: (cset_references_univ _ _)   |- _ => go H
  end.

Ltac destruct_set_mem a bs :=
  match type of bs with
  | AtomSet.F.t =>
    let H := fresh a "In" in
    destruct (AtomSet.F.mem a bs) eqn:H; rewrite_set_facts_in H
  | NatSet.F.t =>
    let H := fresh a "In" in
    destruct (NatSet.F.mem a bs) eqn:H; rewrite_set_facts_in H
  | cap =>
    match type of a with
    | atom => 
      let H := fresh a "In" in
      destruct (cset_references_fvar_dec a bs) eqn:H; rewrite_set_facts_in H; trivial
    | nat =>
      let H := fresh a "In" in
      destruct (cset_references_bvar_dec a bs) eqn:H; rewrite_set_facts_in H; trivial
    end
  end.


Lemma funion_empty_idempotent : forall xs,
    NatSet.F.union xs {}N = xs.
Proof. intros. fnsetdec. Qed.

Lemma empty_funion_idempotent : forall xs,
    NatSet.F.union {}N xs = xs.
Proof. intros. fnsetdec. Qed.

Lemma union_empty_idempotent : forall xs,
    AtomSet.F.union xs {} = xs.
Proof. intros. fsetdec. Qed.

Lemma empty_union_idempotent : forall xs,
    AtomSet.F.union {} xs = xs.
Proof. intros. fsetdec. Qed.

Lemma false_or_idempotent : forall xs,
    false || xs = xs.
Proof. destr_bool. Qed.

Lemma or_false_idempotent : forall xs,
    xs || false = xs.
Proof. destr_bool. Qed.

Lemma true_or_true : forall xs,
    true || xs = true.
Proof. destr_bool. Qed.

Lemma or_true_true : forall xs,
    xs || true = true.
Proof. destr_bool. Qed.

Hint Rewrite 
  funion_empty_idempotent empty_funion_idempotent 
  union_empty_idempotent empty_union_idempotent 
  or_false_idempotent false_or_idempotent
  true_or_true or_true_true
: csets.

Lemma cunion_empty_idempotent : forall xs,
    cset_union xs {}C = xs.
Proof. intros. destruct xs. unfold cset_union. autorewrite with csets; trivial. Qed.

Lemma empty_cunion_idempotent : forall xs,
    cset_union {}C xs = xs.
Proof. intros. destruct xs. unfold cset_union. autorewrite with csets; trivial. Qed.

Hint Rewrite cunion_empty_idempotent empty_cunion_idempotent : csets.

Ltac csetsimpl :=
  try (progress (simpl; autorewrite with csets in *); intuition csetsimpl).

Ltac csetsimplIn H :=
  try (progress (simpl in H; autorewrite with csets in H); intuition (csetsimplIn H)).

Tactic Notation "csetsimpl" "in" hyp(H) := csetsimplIn H.

Ltac csetdec := csetsimpl; try fsetdec; try fnsetdec.

(** Some more facts about Bool *)
Lemma leb_reflexive : forall xs,
  leb xs xs.
Proof. destr_bool. Qed.

Lemma leb_true : forall xs,
  leb xs true.
Proof. destr_bool. Qed.

Lemma false_leb : forall xs,
  leb false xs.
Proof. destr_bool. Qed.

Lemma andb_false_false : forall xs,
  andb xs false = false.
Proof. destr_bool. Qed.

Lemma false_andb_false : forall xs,
  andb false xs = false.
Proof. destr_bool. Qed.

Hint Resolve leb_reflexive leb_true false_leb andb_false_false false_andb_false : core.

(** ************************************************** *)
(** Locally Namelesss *)
(** ************************************************** *)


Definition capt (c : cap) : Prop := NatSet.F.Empty (cset_bvars c).

Lemma singleton_closed : forall f,
  capt (cset_fvar f).
Proof.
  unfold capt, cset_fvar; fnsetdec. 
Qed.

Lemma capt_empty_bvar : forall A N R,
  capt (cset_set A N R) ->
  N = {}N.
Proof.
  intros. unfold capt, cset_fvar in *. fnsetdec. 
Qed.

Lemma capt_concrete_cset : forall xs b,
  capt (cset_set xs {}N b).
Proof.
  intros. unfold capt, cset_bvars. fnsetdec.
Qed.
Hint Unfold capt : core.
Hint Resolve capt_empty_bvar capt_concrete_cset : core.


(** Opening a capture set with a bound variable d[k -> c] *)
Definition open_cset (k : nat) (c : cap) (d : cap) : cap :=
  if cset_references_bvar_dec k d then 
    cset_union c (cset_remove_bvar k d)
  else 
    d.

(** Substituting a capture set with a free variable d[a -> c] *)
Definition subst_cset (a : atom) (c : cap) (d: cap) : cap :=
  if cset_references_fvar_dec a d then
    cset_union c (cset_remove_fvar a d)
  else
    d.

Lemma subst_over_subset : forall C1 C2 D x,
  cset_subset_prop C1 C2 -> 
  cset_subset_prop (subst_cset x D C1) (subst_cset x D C2).
Proof.
  intros.
  unfold cset_subset_prop in *.
  destruct H as [HF [HB HL]].
  unfold subst_cset, cset_references_fvar_dec; destruct C1; destruct C2; simpl in *.
    destruct_set_mem x t; destruct_set_mem x t1; simpl in *; repeat split;
    try fsetdec; try fnsetdec; try (repeat destr_bool; autorewrite with csets); 
    try solve [exfalso; fsetdec]; eauto*.
Qed.

Lemma subst_subset_intro : forall C1 C2 x,
  (* C1 is closed *)
  capt C1 ->
  cset_subset_prop (cset_fvar x) C2 ->
  cset_subset_prop C1 (subst_cset x C1 C2).
Proof.
  intros.
  destruct C2.
  (* TODO what can we do to prevent having to unfold? *)
  unfold capt in H.
  unfold cset_subset_prop, subst_cset, cset_references_fvar_dec in *.
  destruct H0 as [HF [HB HL]]; simpl in *; csetsimpl; destruct_set_mem x t; csetsimpl;
    try fsetdec;
    try fnsetdec;
    try (repeat destr_bool; autorewrite with csets);
    eauto.
  exfalso. specialize (HF x). fsetdec.
Qed.

Lemma subst_cset_union : forall x D C1 C2,
  subst_cset x D (cset_union C1 C2) = (cset_union (subst_cset x D C1) (subst_cset x D C2)).
Proof with eauto.
  intros.
  unfold subst_cset, cset_fvars, cset_union, cset_fvar, cset_references_fvar_dec, cset_remove_fvar; simpl in *.
  destruct C1; destruct C2; destruct D; simpl.
  destruct_set_mem x (t `union` t1); destruct_set_mem x t; destruct_set_mem x t1;
    unfold cset_bvars, cset_fvars; f_equal; try fsetdec; try fnsetdec; 
    try (repeat destr_bool; autorewrite with csets)...
Qed.

Lemma subst_cset_singleton : forall x C,
  subst_cset x C (cset_fvar x) = C.
Proof.
  unfold subst_cset, cset_fvar, cset_fvars, cset_references_fvar_dec, cset_remove_fvar in *; simpl.
  intros.
  destruct_set_mem x (singleton x).
  replace (singleton x `remove` x) with {}; try fsetdec.
  destruct C; unfold cset_union; simpl; autorewrite with csets; trivial.
  fsetdec.
Qed.

Lemma subst_cset_fresh : forall x C1 C2,
  x `notin` (cset_fvars C1) ->
  C1 = subst_cset x C2 C1.
Proof with eauto.
  intros.
  unfold subst_cset, cset_references_fvar_dec, cset_union, cset_remove_fvar, cset_fvars in *.
  destruct C1 eqn:HC; destruct C2 eqn:HC2;
  destruct_set_mem x t...
  notin_solve.
Qed.

Lemma singleton_univ :
  cset_references_univ (cset_universal).
Proof with eauto.
  autorewrite with csets...
Qed.

Lemma subst_cset_fresh_id : forall x X C,
  x <> X ->
  (subst_cset X C (cset_fvar x)) = (cset_fvar x).
Proof.
  intros. unfold cset_fvar, subst_cset, cset_references_fvar_dec, cset_fvars.
  destruct_set_mem X (singleton x); auto.
  assert (x = X) by fsetdec; fsetdec.
Qed.

Lemma subst_cset_union_id : forall x y D C1,
  x <> y ->
  subst_cset x D (cset_union C1 (cset_fvar y)) = (cset_union (subst_cset x D C1) (cset_fvar y)).
Proof with eauto.
  intros.
  rewrite <- (subst_cset_fresh_id y x D) at 2...
  apply subst_cset_union.
Qed.

Lemma subst_cset_univ : forall x C R,
  cset_references_univ R ->
  cset_references_univ (subst_cset x C R).
Proof with eauto.
  destruct R; unfold cset_has_universal, subst_cset, cset_references_univ, cset_references_fvar_dec, cset_remove_fvar, cset_union in *; simpl.
  destruct_set_mem x t; intro; subst; autorewrite with csets...
Qed.

Lemma open_cset_capt : forall i C c,
  capt C ->
  C = open_cset i c C.
Proof with eauto*.
  intros i C c H.  
  unfold open_cset in *.
  destruct_set_mem i C. 
  exfalso. unfold capt, cset_references_bvar in *. 
  assert (~ NatSet.F.In i (cset_bvars C)) by nnotin_solve...
Qed.

Lemma subst_cc_intro_rec : forall X (C : cap) U k,
  X `notin` (cset_fvars C) ->
  open_cset k U C = subst_cset X U (open_cset k (cset_fvar X) C).
Proof with auto*.
  intros * NotIn.
  destruct C. destruct U. 
  unfold open_cset, cset_references_bvar_dec, 
    subst_cset, cset_bvars, cset_remove_bvar, cset_remove_fvar, cset_references_fvar_dec, cset_fvars in *; simpl.

  destruct_set_mem k t0; simpl. autorewrite with csets.
  unfold cset_union, cset_fvars.
  destruct_set_mem X (singleton X `union` t); simpl; autorewrite with csets; f_equal;
    try fsetdec; try (repeat destr_bool; autorewrite with csets).
  
  destruct_set_mem X t; auto.
  fsetdec.
Qed.


Hint Resolve singleton_closed open_cset_capt : core.
Hint Rewrite subst_cset_singleton subst_cset_union : csets.


(* unfold subst_cb, subst_cset, cset_references_fvar_dec, cset_fvar, cset_remove_fvar, cset_union.  
  destruct C1; destruct_set_mem X (singleton x)... fsetdec. *)
  
Lemma open_cset_rec_capt_aux : forall c j V i U,
  i <> j ->
  capt V ->
  (* TODO probably, we also want disjointness of labels here?, and that V
      and U do not both contain universal*)
  (andb (cset_has_universal V) (cset_has_universal U)) = false ->
  AtomSet.F.Empty (AtomSet.F.inter (cset_fvars V) (cset_fvars U)) ->
  open_cset j V c = open_cset i U (open_cset j V c) ->
  c = open_cset i U c.
Proof with eauto.
  intros * Hfresh Hempty HdisjointUniv HdisjointV HdisjointL.
  unfold cset_fvars, capt, open_cset, cset_remove_bvar, cset_references_bvar_dec, cset_union,
    cset_bvars in *.
  destruct c eqn:Hc; destruct U eqn:HU; destruct V eqn:HV; destruct_set_mem j t0; unfold cset_fvars in *;
    destruct_set_mem i t0;
    destruct (NatSet.F.mem i (NatSet.F.union t4 (NatSet.F.remove j t0))) eqn:iInUnion;
    rewrite_set_facts_in iInUnion; f_equal; autorewrite with csets in *;
      (* try (repeat destr_bool;autorewrite with csets)...*)
    inversion HdisjointL; autorewrite with csets;  try fsetdec; try fnsetdec.
  * assert (t1 `subset` t). {
      intros e Het1.
      assert (e `in` (t1 `union` t3 `union` t)) by fsetdec.
      assert (e `notin` t3) by fsetdec.
      rewrite <- H0 in H. fsetdec.
    }
    fsetdec.
  * assert (NatSet.F.In i (NatSet.F.remove j t0)) by fnsetdec.
    assert (~NatSet.F.In i (NatSet.F.remove i (NatSet.F.remove j t0))) by fnsetdec.
    assert (NatSet.F.In i t2). {
      destruct_set_mem i t2...
      exfalso.
      assert (~ NatSet.F.In i (NatSet.F.union t2 (NatSet.F.remove i (NatSet.F.union t4 (NatSet.F.remove j t0)))))
         by fnsetdec.
      rewrite <- H1 in H4. fnsetdec.
    }
    assert (NatSet.F.Subset t2 t0). {
      intros e Het3.
      destruct (e === i); subst...
      assert (NatSet.F.In e (NatSet.F.union t2 (NatSet.F.remove i (NatSet.F.union t4  (NatSet.F.remove j t0)))))
        by fnsetdec.
      rewrite <- H1 in H5...
      assert (e <> j) by fnsetdec.
      fnsetdec.
    }
    fnsetdec.
  * destr_bool...
  * destr_bool...
Qed.

Lemma subst_cset_open_cset_rec : forall x k C1 C2 D,
  capt C1 ->
  subst_cset x C1 (open_cset k C2 D) = open_cset k (subst_cset x C1 C2) (subst_cset x C1 D).
Proof with eauto*.
  intros x k C1 C2 D Closed.
  destruct D eqn:Hc; destruct C1 eqn:HC1; destruct C2 eqn:HC2;
  unfold capt, subst_cset, open_cset, cset_references_fvar_dec,
    cset_references_bvar_dec, cset_remove_bvar, cset_remove_fvar, cset_union, cset_fvars, cset_bvars in *; subst; csetsimpl.

    assert (t2 = {}N) by fnsetdec; subst.

    autorewrite with csets.

    destruct (NatSet.F.mem k t0) eqn:kT0;
    destruct (AtomSet.F.mem x t) eqn:xT;
    destruct (AtomSet.F.mem x t3) eqn:xT3;
    destruct (AtomSet.F.mem x (t3 `union` t)) eqn:xUnion;
    f_equal;
    rewrite_set_facts_in kT0;
    rewrite_set_facts_in xT;
    rewrite_set_facts_in xT3;
    rewrite_set_facts_in xUnion;
    try fsetdec; try fnsetdec;
    rewrite_set_facts_back_in kT0;
    try rewrite kT0;
    rewrite_set_facts_in kT0; f_equal; try fsetdec; try fnsetdec; try destr_bool.
Qed.

Lemma subst_cset_useless_repetition : forall x C1 C2 D,
  x `notin` cset_fvars C2 ->
  subst_cset x C1 (subst_cset x C2 D) = (subst_cset x C2 D).
Proof.
  intros.
  symmetry.
  eapply subst_cset_fresh with (C1 := subst_cset x C2 D)...
  destruct D; destruct C2.
  cbv [cset_fvars subst_cset cset_references_fvar_dec
        cset_union cset_remove_fvar cset_bvars cset_has_universal].
  destruct_set_mem x t...
  fsetdec.
  fsetdec.
Qed.