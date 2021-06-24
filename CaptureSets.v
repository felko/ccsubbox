(** Support here for Capture Sets, a.k.a a record
    of free and bound variables tracking which variables
    are captured by a particualar type. *)

Require Import Metatheory.
Require Import Tactics.
Require Import TaktikZ.

Require Import OrderedTypeEx.
Require Import OrderedType.
Require Import FSetFacts.
Require Import Atom.
Require Import Nat.
Require Export Bool.
Require Import Label.

Create HintDb csets.

(** ************************************************** *)
(** Definition of Capture Sets *)
(** ************************************************** *)

(** A captureset -- a pair of triple of free variables,
    bound variables, and if we contain the special
    `universal` variable. *)
Inductive cap : Type :=
  | cset_set : atoms -> nats -> bool -> labels -> cap.

(** ************************************************** *)
(** Constructors *)
(** ************************************************** *)

Declare Scope cset_shorthand.

Notation "`cset_fvar` a" := (cset_set {a}A {}N false {}L)
                              (at level 10, a at level 9) : cset_shorthand.

Notation "`cset_bvar` k" := (cset_set {}A {k}N false {}L)
                              (at level 10, k at level 9) : cset_shorthand.

Notation "{}" := (cset_set {}A {}N false {}L) : cset_shorthand.
Notation "{*}" := (cset_set {}A {}N true {}L) : cset_shorthand.

(** ************************************************** *)
(** Selectors *)
(** ************************************************** *)

Notation "`cset_fvars` C" := (match C with cset_set xs _ _ _ => xs end)
                                (at level 10, C at level 9) : cset_shorthand.

Notation "`cset_bvars` C" := (match C with cset_set _ ks _ _ => ks end)
                                (at level 10, C at level 9) : cset_shorthand.

Notation "`cset_uvar` C" := (match C with cset_set _ _ u _ => u end)
                                (at level 10, C at level 9) : cset_shorthand.

Notation "`cset_lvars` C" := (match C with cset_set _ _ _ l => l end)
                                (at level 10, C at level 9) : cset_shorthand.

(** ************************************************** *)
(** Operations *)
(** ************************************************** *)

(* Definition cset_lvar (l : atom) :=
  (cset_set AtomSet.F.empty NatSet.F.empty (AtomSet.F.singleton l)). *)

(** Predicates for determining if a capture set explicity references
    a variable -- used for determining if a capture set is well formed.
    Don't use these predicates for determining if a capture set
    captures a variable, as one needs to also test cset_universal. *)

Open Scope cset_shorthand.

(** Capture set unions are what you'd expect. *)
Definition cset_union (c1 c2 : cap) : cap :=
  cset_set
    (AtomSet.F.union (`cset_fvars` c1) (`cset_fvars` c2))
    (NatSet.F.union (`cset_bvars` c1) (`cset_bvars` c2))
    ((`cset_uvar` c1) || (`cset_uvar` c2))
    (LabelSet.F.union (`cset_lvars` c1) (`cset_lvars` c2)).

Definition cset_subset_dec (C D : cap) :=
  AtomSet.F.subset (`cset_fvars` C) (`cset_fvars` D)
    && NatSet.F.subset (`cset_bvars` C) (`cset_bvars` D)
    && (implb (`cset_uvar` C) (`cset_uvar` D))
    && LabelSet.F.subset (`cset_lvars` C) (`cset_lvars` D).

Notation "C `u` D" := (cset_union C D) (at level 69) : cset_shorthand.
Notation "C A`\` x" := (cset_set ((`cset_fvars` C) `\`A x) (`cset_bvars` C) (`cset_uvar` C) (`cset_lvars` C))
                         (at level 69) : cset_shorthand.
Notation "x A`in` C" := (AtomSet.F.In x (`cset_fvars` C))
                          (at level 69) : cset_shorthand.
Notation "x A`mem` C" := (AtomSet.F.mem x (`cset_fvars` C)) (at level 69) : cset_shorthand.

Notation "C N`\` k" := (cset_set ((`cset_fvars` C) ) ((`cset_bvars` C) `\`N k) (`cset_uvar` C) (`cset_lvars` C))
                         (at level 69) : cset_shorthand.
Notation "k N`in` C" := (NatSet.F.In k (`cset_bvars` C))
                          (at level 69) : cset_shorthand.
Notation "k N`mem` C" := (NatSet.F.mem k (`cset_bvars` C))
                           (at level 69) : cset_shorthand.
                      

Notation "C L`\` k" := (cset_set ((`cset_fvars` C) ) ((`cset_bvars` C)) ((`cset_uvar` C)) ((`cset_lvars` C) `\`L k))
                          (at level 69) : cset_shorthand.
Notation "k L`in` C" := (LabelSet.F.In k (`cset_lvars` C))
                            (at level 69) : cset_shorthand.
Notation "k L`mem` C" := (LabelSet.F.mem k (`cset_lvars` C))
                            (at level 69) : cset_shorthand.

Notation "`* mem` C" := (`cset_uvar` C)
                           (at level 10, only parsing) : cset_shorthand.
Notation "`* in` C" := (`cset_uvar` C = true)
                           (at level 10) : cset_shorthand.
                  


Notation "`cset_references_bvar` k c" :=
  (k N`in` c)
    (at level 10, k at level 9, c at level 9, only parsing) : cset_shorthand.
Notation "`cset_references_bvar_dec` k c" :=
  (k N`mem` c)
    (at level 10, k at level 9, c at level 9, only parsing) : cset_shorthand.
Notation "`cset_remove_bvar` k c" :=
  (c N`\` k)
    (at level 10, k at level 9, c at level 9, only parsing) : cset_shorthand.

Notation "`cset_references_fvar` a c" :=
  (a A`in` c)
    (at level 10, a at level 9, c at level 9, only parsing) : cset_shorthand.
Notation "`cset_references_fvar_dec` a c" :=
  (a A`mem` c)
    (at level 10, a at level 9, c at level 9, only parsing) : cset_shorthand.
Notation "`cset_remove_fvar` a c" :=
  (c A`\` a)
    (at level 10, a at level 9, c at level 9, only parsing) : cset_shorthand.

Notation "`cset_references_univ_dec` c" :=
  (`cset_uvar` c)
    (at level 10, c at level 9, only parsing) : cset_shorthand.
Notation "`cset_references_univ` c" :=
  (`* in` c)
    (at level 10, only parsing) : cset_shorthand.

Notation "`cset_references_lvar` a c" :=
  (a L`in` c)
    (at level 10, a at level 9, c at level 9, only parsing) : cset_shorthand.
Notation "`cset_references_lvar_dec` a c" :=
  (a L`mem` c)
    (at level 10, a at level 9, c at level 9, only parsing) : cset_shorthand.
Notation "`cset_remove_lvar` a c" :=
  (c L`\` a)
    (at level 10, a at level 9, c at level 9, only parsing) : cset_shorthand.
    

(* Check (fun x =>  fun N => x N`in` N). *)
(* Check (fun C D x => (cset_union D (cset_remove_fvar x C))). *)

Declare Scope experimental_set_scope.

Notation "{ x 'as' A}" := (`cset_fvar` x) : experimental_set_scope.
Notation "{ x 'as' N}" := (`cset_bvar` x) : experimental_set_scope.

(** ************************************************** *)
(** Logical Predicates *)
(** ************************************************** *)

Definition cset_empty (c : cap) : Prop :=
  AtomSet.F.Empty (`cset_fvars` c) /\ NatSet.F.Empty (`cset_bvars` c) /\
    ((`cset_uvar` c) = false) /\ LabelSet.F.Empty (`cset_lvars` c).

Definition cset_subset_prop (c : cap) (d : cap) : Prop :=
  AtomSet.F.Subset (`cset_fvars` c) (`cset_fvars` d)
    /\ NatSet.F.Subset (`cset_bvars` c) (`cset_bvars` d)
    /\  (leb (`cset_uvar` c) (`cset_uvar` d))
    /\ LabelSet.F.Subset (`cset_lvars` c) (`cset_lvars` d).


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
  Variable x1 x2 x3 x4 : label.
  Variable L X1 X2 X3 X4 : labels.

  Lemma cset_bvar_mem_iff :
    `cset_references_bvar` k C <-> `cset_references_bvar_dec` k C = true.
  Proof.
    destruct C ;
      simpl in *; intuition.
  Qed.

  Lemma cset_fvar_mem_iff :
    `cset_references_fvar` a C <-> `cset_references_fvar_dec` a C = true.
  Proof.
    destruct C ;
      simpl in *; intuition.
  Qed.

  Lemma cset_univ_mem_iff :
    `cset_references_univ` C <-> `cset_references_univ_dec` C = true.
  Proof.
    destruct C;
    reflexivity.
  Qed.

  Lemma cset_lvar_mem_iff :
    `cset_references_lvar` x1 C <-> `cset_references_lvar_dec` x1 C = true.
  Proof.
    destruct C ;
      simpl in *; intuition.
  Qed.

  Lemma cset_bvar_not_mem_iff :
    ~ `cset_references_bvar` k C <-> `cset_references_bvar_dec` k C = false.
  Proof.
    destruct C ; rewrite <- NatSetFacts.not_mem_iff; fnsetdec.
  Qed.

  Lemma cset_fvar_not_mem_iff :
    ~ `cset_references_fvar` a C <-> `cset_references_fvar_dec` a C = false.
  Proof.
    destruct C ;
      split; intros; simpl in *; intuition.
      rewrite <- AtomSetFacts.not_mem_iff; fsetdec.
      rewrite <- AtomSetFacts.not_mem_iff in H; fsetdec.
  Qed.

  Lemma cset_univ_not_mem_iff :
    ~ `cset_references_univ` C <-> `cset_references_univ_dec` C = false.
  Proof.
    destruct C;
      split.
    intro; destruct b; auto*.
    intro; subst; auto.
  Qed.

  Lemma cset_lvar_not_mem_iff :
    ~ `cset_references_lvar` x1 C <-> `cset_references_lvar_dec` x1 C = false.
  Proof.
    destruct C ; rewrite <- LabelSetFacts.not_mem_iff; fnsetdec.
  Qed.

  Lemma fvars_1 : `cset_fvars` (cset_set A N R L) = A.
  Proof. trivial. Qed.

  Lemma bvars_1 : `cset_bvars` (cset_set A N R L) = N.
  Proof. trivial. Qed.

  Lemma uvars_1 : `cset_uvar` (cset_set A N R L) = R.
  Proof. trivial. Qed.

  Lemma lvars_1 : `cset_lvars` (cset_set A N R L) = L.
  Proof. trivial. Qed.

  Lemma fvars_union_1 : `cset_fvars` (cset_union C D) = AtomSet.F.union (`cset_fvars` C) (`cset_fvars` D).
  Proof. trivial. Qed.

  Lemma bvars_union_1 : `cset_bvars` (cset_union C D) = NatSet.F.union (`cset_bvars` C) (`cset_bvars` D).
  Proof. trivial. Qed.

  Lemma uvar_union_1 : `cset_uvar` (cset_union C D) = orb (`cset_uvar` C) (`cset_uvar` D).
  Proof. trivial. Qed.
  
  Lemma lvars_union_1 : `cset_lvars` (cset_union C D) = LabelSet.F.union (`cset_lvars` C) (`cset_lvars` D).
  Proof. trivial. Qed.

  Lemma remove_fvar_1 : `cset_remove_fvar` x (cset_set A N R L) = (cset_set (AtomSet.F.remove x A) N R L).
  Proof. intros. simpl in *. trivial. Qed.

  Lemma remove_bvar_1 : `cset_remove_bvar` k (cset_set A N R L) = (cset_set A (NatSet.F.remove k N) R L).
  Proof. intros. simpl in *. trivial. Qed.

  Lemma remove_lvar_1 : `cset_remove_lvar` x1 (cset_set A N R L) = (cset_set A N R (LabelSet.F.remove x1 L)).
  Proof. intros. simpl in *. trivial. Qed.

  Lemma mem_bvar_1 : `cset_references_bvar` k C -> `cset_references_bvar_dec` k C = true.
  Proof. rewrite cset_bvar_mem_iff; trivial. Qed.

  Lemma mem_bvar_2 : `cset_references_bvar_dec` k C = true -> `cset_references_bvar` k C.
  Proof. rewrite <- cset_bvar_mem_iff; trivial. Qed.

  Lemma mem_fvar_1 : `cset_references_fvar` a C -> `cset_references_fvar_dec` a C = true.
  Proof. rewrite cset_fvar_mem_iff; trivial. Qed.

  Lemma mem_fvar_2 : `cset_references_fvar_dec` a C = true -> `cset_references_fvar` a C.
  Proof. rewrite <- cset_fvar_mem_iff; trivial. Qed.

  Lemma mem_uvar_1 : `cset_references_univ` C -> `cset_references_univ_dec` C = true.
  Proof. trivial. Qed.

  Lemma mem_uvar_2 : `cset_references_univ_dec` C = true -> `cset_references_univ` C.
  Proof. trivial. Qed.

  Lemma mem_lvar_1 : `cset_references_lvar` x1 C -> `cset_references_lvar_dec` x1 C = true.
  Proof. rewrite cset_lvar_mem_iff; trivial. Qed.

  Lemma mem_lvar_2 : `cset_references_lvar_dec` x1 C = true -> `cset_references_lvar` x1 C.
  Proof. rewrite <- cset_lvar_mem_iff; trivial. Qed.

  Lemma In_bvar_1 : k = n -> `cset_references_bvar` k C -> `cset_references_bvar` n C.
  Proof. intros; subst; trivial. Qed.

  Lemma In_fvar_1 : a = f -> `cset_references_fvar` a C -> `cset_references_fvar` f C.
  Proof. intros; subst; trivial. Qed.

  Lemma In_lvar_1 : x1 = x2 -> `cset_references_lvar` x1 C -> `cset_references_lvar` x2 C.
  Proof. intros; subst; trivial. Qed.

  Lemma Is_empty : cset_empty {}.
  Proof. repeat split. fsetdec. fnsetdec. lsetdec. Qed.

  Lemma union_fvar_1 : `cset_references_fvar` x (cset_union C D) -> `cset_references_fvar` x C \/ `cset_references_fvar` x D.
  Proof. intros. unfold cset_union in *; simpl in *. fsetdec. Qed.

  Lemma union_fvar_2 : `cset_references_fvar` x C -> `cset_references_fvar` x (cset_union C D).
  Proof. unfold cset_union in *; simpl in *. fsetdec. Qed.

  Lemma union_fvar_3 : `cset_references_fvar` x D -> `cset_references_fvar` x (cset_union C D).
  Proof. unfold cset_union in *; simpl in *. fsetdec. Qed.

  Lemma union_bvar_1 : `cset_references_bvar` k (cset_union C D) -> `cset_references_bvar` k C \/ `cset_references_bvar` k D.
  Proof. intros. unfold cset_union in *; simpl in *. fnsetdec. Qed.

  Lemma union_bvar_2 : `cset_references_bvar` k C -> `cset_references_bvar` k (cset_union C D).
  Proof. unfold cset_union in *; simpl in *. fnsetdec. Qed.

  Lemma union_bvar_3 : `cset_references_bvar` k D -> `cset_references_bvar` k (cset_union C D).
  Proof. unfold cset_union in *; simpl in *. fnsetdec. Qed.

  Lemma union_uvar_1 : `cset_references_univ` (cset_union C D) ->
    `cset_references_univ` C \/ `cset_references_univ` D.
  Proof. intros. unfold cset_union in *; simpl in *.
    rewrite orb_true_iff in H; auto*.
  Qed.

  Lemma union_uvar_2 : `cset_references_univ` C -> `cset_references_univ` (cset_union C D).
  Proof. unfold cset_union in *; simpl in *. intro.
    rewrite orb_true_iff. auto. Qed.

  Lemma union_uvar_3 : `cset_references_univ` D -> `cset_references_univ` (cset_union C D).
  Proof. unfold cset_union in *; simpl in *. intro.
    rewrite orb_true_iff. auto. Qed.

  Lemma union_lvar_1 : `cset_references_lvar` x1 (cset_union C D) -> `cset_references_lvar` x1 C \/ `cset_references_lvar` x1 D.
  Proof. intros. unfold cset_union in *; simpl in *. lsetdec. Qed.

  Lemma union_lvar_2 : `cset_references_lvar` x1 C -> `cset_references_lvar` x1 (cset_union C D).
  Proof. unfold cset_union in *; simpl in *. lsetdec. Qed.

  Lemma union_lvar_3 : `cset_references_lvar` x1 D -> `cset_references_lvar` x1 (cset_union C D).
  Proof. unfold cset_union in *; simpl in *. lsetdec. Qed.

  Lemma union_sub_1 : cset_subset_prop C D -> cset_union D C = D.
  Proof.
    unfold cset_union, cset_subset_prop.
    intros. destruct C; destruct D; simpl; f_equal.
    fsetdec. fnsetdec.
      destruct b; destruct b0; auto*.
    lsetdec.
  Qed.

  Lemma union_sub_2 : cset_subset_prop C D -> D = cset_union D C.
  Proof.
    unfold cset_union, cset_subset_prop.
    intros. destruct C; destruct D; simpl; f_equal.
    fsetdec. fnsetdec.
      destruct b; destruct b0; auto*.
    lsetdec.
  Qed.

  Lemma union_subset_distribute_1 : cset_subset_prop C1 C2 -> cset_subset_prop (cset_union C1 D) (cset_union C2 D).
  Proof.
    intros. unfold cset_subset_prop in *; inversion H as [Sub_F [Sub_B Sub_A]];
    unfold cset_union in *; destruct C1; destruct C2.
    repeat split; try fsetdec; try fnsetdec; try lsetdec.
      destruct b; destruct b0; unfold leb in *; simpl in *; destruct D; destruct b; auto*.
  Qed.

End Props.

(* TODO defined here to avoid all the implicit arguments *)
Lemma subset_univ_1 : forall R C,
  cset_subset_prop R C -> `cset_references_univ` R -> `cset_references_univ` C.
Proof. intros.
  destruct H as [_ [_ H]]. destruct R;
    destruct C; unfold leb in *; destruct b; destruct b0; auto*. Qed.

Hint Rewrite
  fvars_1 bvars_1 lvars_1
  fvars_union_1 bvars_union_1 lvars_union_1
  remove_fvar_1 remove_bvar_1
: csets.


Hint Resolve
  mem_bvar_1 mem_fvar_1 mem_uvar_1 mem_lvar_1 Is_empty
  union_fvar_1 union_fvar_2 union_fvar_3
  union_bvar_1 union_bvar_2 union_bvar_3
  union_uvar_1 union_uvar_2 union_uvar_3
  union_lvar_1 union_lvar_2 union_lvar_3
  union_sub_1 union_sub_2 union_subset_distribute_1
  subset_univ_1
: core.

Hint Immediate In_bvar_1 In_fvar_1 mem_bvar_2 mem_fvar_2 mem_lvar_2 mem_uvar_2 : core.

(* Some subset properties *)
Lemma subset_refl : forall C,
  cset_subset_prop C C.
Proof.
  intros. unfold cset_subset_prop. repeat split. fsetdec. fnsetdec.
    unfold leb; destruct C; destruct b; auto*.
  lsetdec.
Qed.

Lemma subset_union_left : forall C1 C2,
  cset_subset_prop C1 (cset_union C1 C2).
Proof.
  intros. destruct C1. destruct C2. unfold cset_subset_prop, cset_union.
  repeat split. fsetdec. fnsetdec.
    destr_bool.
  lsetdec.
Qed.

Lemma subset_union_right : forall C1 C2,
  cset_subset_prop C2 (cset_union C1 C2).
Proof.
  intros. destruct C1. destruct C2. unfold cset_subset_prop, cset_union.
  repeat split. fsetdec. fnsetdec.
    destr_bool.
  lsetdec.
Qed.

Lemma subset_trans : forall A B C,
  cset_subset_prop A B -> cset_subset_prop B C -> cset_subset_prop A C.
Proof.
  intros * AB BC.
  inversion AB as [ABF [ABN [ABU ABL]]]; subst; inversion BC as [BCF [BCN [BCU BCL]]]; subst...
  repeat (econstructor; try fsetdec; try fnsetdec; try lsetdec)...
  destruct A; destruct B; destruct C; destr_bool...
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
  | LabelSet.F.mem _ _ = true => rewrite <- LabelSetFacts.mem_iff in H
  | LabelSet.F.mem _ _ = false => rewrite <- AtomSetFacts.not_mem_iff in H
  | `cset_references_bvar_dec` _ _ = true => rewrite <- cset_bvar_mem_iff in H
  | `cset_references_fvar_dec` _ _ = true => rewrite <- cset_fvar_mem_iff in H
  | `cset_references_univ_dec` _ _ = true => rewrite <- cset_univ_mem_iff in H
  | `cset_references_lvar_dec` _ _ = true => rewrite <- cset_lvar_mem_iff in H
  | `cset_references_bvar_dec` _ _ = false => rewrite <- cset_bvar_not_mem_iff in H
  | `cset_references_fvar_dec` _ _ = false => rewrite <- cset_fvar_not_mem_iff in H
  | `cset_references_univ_dec` _ _ = false => rewrite <- cset_univ_not_mem_iff in H
  | `cset_references_lvar_dec` _ _ = false => rewrite <- cset_lvar_not_mem_iff in H
  end;
  (** argh, unused arguments need to be discharged *)
  try apply NatSet.F.empty; try apply AtomSet.F.empty; try apply LabelSet.F.empty; try apply {}.

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
  | LabelSet.F.In _ _        => rewrite -> LabelSetFacts.mem_iff in H
  | (~ LabelSet.F.In _ _ )   => rewrite -> LabelSetFacts.mem_iff in H
  | `cset_references_bvar` _ _ => rewrite -> cset_bvar_mem_iff in H
  | `cset_references_fvar` _ _ => rewrite -> cset_fvar_mem_iff in H
  | `cset_references_univ` _ _ => rewrite -> cset_univ_mem_iff in H
  | `cset_references_univ` _ _ => rewrite -> cset_lvar_mem_iff in H
  | (~ `cset_references_bvar` _ _) => rewrite -> cset_bvar_not_mem_iff in H
  | (~ `cset_references_fvar` _ _) => rewrite -> cset_fvar_not_mem_iff in H
  | (~ `cset_references_univ` _ _) => rewrite -> cset_univ_not_mem_iff in H
  | (~ `cset_references_lvar` _ _) => rewrite -> cset_lvar_not_mem_iff in H
  end;
  (** argh, unused arguments need to be discharged *)
  try apply NatSet.F.empty; try apply AtomSet.F.empty; try apply LabelSet.F.empty; try apply {}.

Ltac simpl_in_cset :=
  let go H := rewrite_set_facts_back_in H; try rewrite H in *; rewrite_set_facts_in H in
  match goal with
  | H: `cset_references_bvar_dec` ?I ?C = ?B |- _ => try rewrite H in *
  | H: ~ (`cset_references_bvar` _ _) |- _ => go H
  | H: (`cset_references_bvar` _ _)   |- _ => go H
  | H: ~ (`cset_references_fvar` _ _) |- _ => go H
  | H: (`cset_references_fvar` _ _)   |- _ => go H
  | H: ~ (`cset_references_univ` _ _) |- _ => go H
  | H: (`cset_references_univ` _ _)   |- _ => go H
  | H: ~ (`cset_references_lvar` _ _) |- _ => go H
  | H: (`cset_references_lvar` _ _)   |- _ => go H
  end.

Ltac destruct_set_mem_univ bs :=
  destruct (`cset_references_univ_dec` bs) eqn:H; rewrite_set_facts_in H; trivial.

Ltac destruct_set_mem a bs :=
  match type of bs with
  | AtomSet.F.t =>
    let H := fresh a "In" in
    destruct (AtomSet.F.mem a bs) eqn:H; rewrite_set_facts_in H
  | NatSet.F.t =>
    let H := fresh a "In" in
    destruct (NatSet.F.mem a bs) eqn:H; rewrite_set_facts_in H
  | LabelSet.F.t =>
    let H := fresh a "In" in
    destruct (LabelSet.F.mem a bs) eqn:H; rewrite_set_facts_in H
  | cap =>
    match type of a with
    | atom =>
      let H := fresh a "In" in
      destruct (`cset_references_fvar_dec` a bs) eqn:H; rewrite_set_facts_in H; trivial
    (** why argh *)
    | AtomSet.F.elt =>
      let H := fresh a "In" in
      destruct (`cset_references_fvar_dec` a bs) eqn:H; rewrite_set_facts_in H; trivial
    | nat =>
      let H := fresh a "In" in
      destruct (`cset_references_bvar_dec` a bs) eqn:H; rewrite_set_facts_in H; trivial
    | NatSet.F.elt =>
      let H := fresh a "In" in
      destruct (`cset_references_bvar_dec` a bs) eqn:H; rewrite_set_facts_in H; trivial
    | label =>
      let H := fresh a "In" in
      destruct (`cset_references_lvar_dec` a bs) eqn:H; rewrite_set_facts_in H; trivial
    | LabelSet.F.elt =>
      let H := fresh a "In" in
      destruct (`cset_references_lvar_dec` a bs) eqn:H; rewrite_set_facts_in H; trivial
    end
  end.

Ltac find_and_destroy_set_mem :=
  try match goal with
  | H : _ |- context G [`cset_references_fvar_dec` ?X ?S] => destruct_set_mem X S
  | H : _ |- context G [`cset_references_bvar_dec` ?B ?S] => destruct_set_mem B S
  | H : _ |- context G [`cset_references_univ_dec` ?S] => destruct_set_mem_univ S
  | H : _ |- context G [`cset_references_lvar_dec` ?B ?S] => destruct_set_mem B S
  | H : _ |- context G [AtomSet.F.mem ?X ?S] => destruct_set_mem X S
  | H : _ |- context G [NatSet.F.mem ?N ?S] => destruct_set_mem N S
  | H : _ |- context G [LabelSet.F.mem ?N ?S] => destruct_set_mem N S
  | H : context G [`cset_references_fvar_dec` ?X ?S] |- _ => destruct_set_mem X S
  | H : context G [`cset_references_bvar_dec` ?B ?S] |- _ => destruct_set_mem B S
  | H : context G [`cset_references_univ_dec` ?S] |- _ => destruct_set_mem_univ S
  | H : context G [`cset_references_lvar_dec` ?B ?S] |- _ => destruct_set_mem B S
  | H : context G [AtomSet.F.mem ?X ?S] |- _ => destruct_set_mem X S
  | H : context G [NatSet.F.mem ?N ?S] |- _ => destruct_set_mem N S
  | H : context G [LabelSet.F.mem ?N ?S] |- _ => destruct_set_mem N S
  end.

Lemma funion_empty_idempotent : forall xs, xs `u`N {}N = xs.
Proof. intros. fnsetdec. Qed.

Lemma empty_funion_idempotent : forall xs, {}N `u`N xs = xs.
Proof. intros. fnsetdec. Qed.

Lemma union_empty_idempotent : forall xs, xs `u`A {}A = xs.
Proof. intros. fsetdec. Qed.

Lemma empty_union_idempotent : forall xs, {}A `u`A xs = xs.
Proof. intros. fsetdec. Qed.

Lemma false_or_idempotent : forall xs, false || xs = xs.
Proof. destr_bool. Qed.

Lemma or_false_idempotent : forall xs, xs || false = xs.
Proof. destr_bool. Qed.

Lemma true_or_true : forall xs, true || xs = true.
Proof. destr_bool. Qed.

Lemma or_true_true : forall xs, xs || true = true.
Proof. destr_bool. Qed.

Lemma lunion_empty_idempotent : forall xs, xs `u`L {}L = xs.
Proof. intros. lsetdec. Qed.

Lemma empty_lunion_idempotent : forall xs, {}L `u`L xs = xs.
Proof. intros. lsetdec. Qed.

Hint Rewrite
  funion_empty_idempotent empty_funion_idempotent
  union_empty_idempotent empty_union_idempotent
  or_false_idempotent false_or_idempotent
  true_or_true or_true_true
  lunion_empty_idempotent empty_lunion_idempotent
: csets.

Lemma cunion_empty_idempotent : forall xs, xs `u` {} = xs.
Proof. intros. destruct xs. unfold cset_union. autorewrite with csets; trivial. Qed.

Lemma empty_cunion_idempotent : forall xs, {} `u` xs = xs.
Proof. intros. destruct xs. unfold cset_union. autorewrite with csets; trivial. Qed.

Hint Rewrite cunion_empty_idempotent empty_cunion_idempotent : csets.

Lemma cset_concrete_union : forall xs ns us xs' ns' us' ls ls',
  (cset_set xs ns us ls) `u` (cset_set xs' ns' us' ls') =
  (cset_set (xs `u`A xs') (ns `u`N ns') (us || us') (ls `u`L ls')).
Proof. intros. cbv [cset_union]. reflexivity. Qed.

Hint Rewrite cset_concrete_union : csets.

(* To be redefined later. *)
Ltac _csetsimpl_hook := idtac.

Ltac csetsimpl :=
  repeat (_csetsimpl_hook; subst; simpl; autorewrite with csets in *).

Ltac csetsimplIn H :=
  repeat (subst; simpl in H; autorewrite with csets in H).

Tactic Notation "csetsimpl" "in" hyp(H) := csetsimplIn H.

Ltac find_and_destroy_cap :=
  try match goal with
    | C : cap |- _ => destruct C
  end.

Ltac discharge_empty :=
  try match goal with
    | H : AtomSet.F.Empty ?S |- _ =>
      assert (S = {}A) by fsetdec; subst; clear H; subst
    | H : NatSet.F.Empty ?S |- _ =>
      assert (S = {}N) by fnsetdec; subst; clear H; subst
  end.

Ltac csetdec :=
  try (progress (csetsimpl;
                 (** destroy set membership, if any *)
                 repeat find_and_destroy_set_mem;
                 repeat find_and_destroy_cap;
                 repeat discharge_empty;
                 (* unfold, if necessary *)
                 cbv [cset_union cset_subset_prop] in *;
                 (* split, if necessary *)
                 try f_equal;
                 try notin_solve; try fsetdec; try solve [exfalso; notin_solve];
                 try nnotin_solve; try fnsetdec; try solve [exfalso; nnotin_solve];
                 try lnotin_solve; try lsetdec; try solve [exfalso; lnotin_solve];
                 try solve [destr_bool]
                 );
       intuition (csetdec)).

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


Definition capt (c : cap) : Prop := NatSet.F.Empty (`cset_bvars` c).

Lemma singleton_closed : forall f,
  capt (`cset_fvar` f).
Proof.
  unfold capt; fnsetdec.
Qed.

Lemma capt_empty_bvar : forall A N R L,
  capt (cset_set A N R L) ->
  N = {}N.
Proof.
  intros. unfold capt in *. fnsetdec.
Qed.

Lemma capt_concrete_cset : forall xs b ls,
  capt (cset_set xs {}N b ls).
Proof.
  intros. unfold capt. fnsetdec.
Qed.

Hint Unfold capt : core.
Hint Resolve capt_empty_bvar capt_concrete_cset : core.

(** Opening a capture set with a bound variable d[k -> c] *)
Definition open_cset (k : nat) (c : cap) (d : cap) : cap :=
  if `cset_references_bvar_dec` k d then
    cset_union c (`cset_remove_bvar` k d)
  else
    d.

(** Substituting a capture set with a free variable d[a -> c] *)
Definition subst_cset (a : atom) (c : cap) (d: cap) : cap :=
  if `cset_references_fvar_dec` a d then
    cset_union c (`cset_remove_fvar` a d)
  else
    d.

Lemma subst_over_subset : forall C1 C2 D x,
  cset_subset_prop C1 C2 ->
  cset_subset_prop (subst_cset x D C1) (subst_cset x D C2).
Proof.
  intros.
  unfold cset_subset_prop in *.
  destruct H as [HF [HB [HU HL]]].
  cbv [subst_cset].
  csetdec...
Qed.

Lemma subst_subset_intro : forall C1 C2 x,
  (* C1 is closed *)
  capt C1 ->
  cset_subset_prop (`cset_fvar` x) C2 ->
  cset_subset_prop C1 (subst_cset x C1 C2).
Proof.
  intros.
  cbv [subst_cset].
  unfold capt in H.
  csetdec.
Qed.

Lemma subst_cset_union : forall x D C1 C2,
  subst_cset x D (cset_union C1 C2) = (cset_union (subst_cset x D C1) (subst_cset x D C2)).
Proof with eauto.
  intros.
  cbv [subst_cset].
  csetdec...
Qed.

Lemma subst_cset_singleton : forall x C,
  subst_cset x C (`cset_fvar` x) = C.
Proof.
  intros; cbv [subst_cset].
  csetdec.
Qed.

Lemma subst_cset_fresh : forall x C1 C2,
  x `notin` (`cset_fvars` C1) ->
  C1 = subst_cset x C2 C1.
Proof with eauto.
  intros.
  cbv [subst_cset].
  csetdec.
Qed.

Lemma singleton_univ :
  `cset_references_univ` {*}.
Proof with eauto.
  trivial.
Qed.

Lemma subst_cset_fresh_id : forall x X C,
  x <> X ->
  (subst_cset X C (`cset_fvar` x)) = (`cset_fvar` x).
Proof.
  intros.
  cbv [subst_cset].
  csetdec.
Qed.

Lemma subst_cset_union_id : forall x y D C1,
  x <> y ->
  subst_cset x D (cset_union C1 (`cset_fvar` y)) = (cset_union (subst_cset x D C1) (`cset_fvar` y)).
Proof with eauto.
  intros.
  rewrite <- (subst_cset_fresh_id y x D) at 2...
  apply subst_cset_union.
Qed.

Lemma subst_cset_univ : forall x C R,
  `cset_references_univ` R ->
  `cset_references_univ` (subst_cset x C R).
Proof with eauto.
  intros. cbv [subst_cset]. csetdec.
Qed.

Lemma open_cset_capt : forall i C c,
  capt C ->
  C = open_cset i c C.
Proof with eauto*.
  intros i C c H.
  unfold open_cset in *.
  unfold capt in H.
  csetdec.
Qed.

Lemma subst_cc_intro_rec : forall X (C : cap) U k,
  X `notin` (`cset_fvars` C) ->
  open_cset k U C = subst_cset X U (open_cset k (`cset_fvar` X) C).
Proof with auto*.
  intros * NotIn.
  cbv [open_cset subst_cset].
  csetdec.
Qed.

Lemma subst_cset_capt : forall Z C1 C,
  capt C1 ->
  capt C ->
  capt (subst_cset Z C1 C).
Proof.
  intros.
  cbv [subst_cset capt] in *.
  csetdec...
Qed.

Hint Resolve singleton_closed open_cset_capt subst_cset_capt : core.
Hint Rewrite subst_cset_singleton subst_cset_union : csets.



(** Automation *)
Lemma cset_eq_injectivity : forall a1 a2 n1 n2,
    a1 = a2 ->
    n1 = n2 ->
    cset_set a1 n1 = cset_set a2 n2.
Proof.
  intros. congruence.
Qed.

Ltac fnset_mem_dec :=
  match goal with
  | |- true = _ => symmetry
  | |- false = _ => symmetry
  | |- _ => idtac
  end;
  match goal with
  | |- NatSet.F.mem _ _ = true => rewrite <- NatSetFacts.mem_iff; fnsetdec
  | |- NatSet.F.mem _ _ = false => rewrite <- NatSetFacts.not_mem_iff; fnsetdec
  end.

Ltac fset_mem_dec :=
  match goal with
  | |- true = _ => symmetry
  | |- false = _ => symmetry
  | |- _ => idtac
  end;
  match goal with
  | |- AtomSet.F.mem _ _ = true => rewrite <- AtomSetFacts.mem_iff; fsetdec
  | |- AtomSet.F.mem _ _ = false => rewrite <- AtomSetFacts.not_mem_iff; fsetdec
  end.

Ltac cset_eq_dec :=
  apply cset_eq_injectivity; [try fsetdec | try fnsetdec].

Ltac destruct_if :=
  match goal with
  | |- context[if ?t then _ else _] =>
    destruct t eqn:?
  end.

Ltac destruct_if_in_as t id :=
  match type of t with
  | context[if ?t then _ else _] =>
    destruct t eqn:id
  end.

Tactic Notation "destruct_if" :=
  destruct_if.

Tactic Notation "destruct_if" "in" constr(t) "as" simple_intropattern(id) :=
  destruct_if_in_as t id.

Tactic Notation "destruct_if" "in" constr(t) :=
  destruct_if in t as ?.

Ltac destruct_match :=
  match goal with
  | |- context[match ?t with _ => _ end] =>
    destruct t eqn:?
  end.


(* ********************************************************************** *)
(** * #<a name="csetprops"></a># Properties of capture sets *)

(* unfold subst_cb, subst_cset, `cset_references_fvar_dec`, cset_fvar, `cset_remove_fvar`, cset_union.
  destruct C1; destruct_set_mem X (singleton x)... fsetdec. *)

Lemma open_cset_rec_capt_aux : forall c j V i U,
  i <> j ->
  capt V ->
  (* TODO probably, we also want disjointness of labels here?, and that V
      and U do not both contain universal*)
  (andb (`cset_uvar` V) (`cset_uvar` U)) = false ->
  AtomSet.F.Empty (AtomSet.F.inter (`cset_fvars` V) (`cset_fvars` U)) ->
  LabelSet.F.Empty (LabelSet.F.inter (`cset_lvars` V) (`cset_lvars` U)) ->
  open_cset j V c = open_cset i U (open_cset j V c) ->
  c = open_cset i U c.
Proof with eauto.
  intros * Hfresh Hempty HdisjointUniv HdisjointV HdisjointL Eq.
  unfold capt, open_cset, cset_union in *.
  csetdec; inversion Eq; autorewrite with csets...
  * assert (t `subset` t5). {
      intros e Het.
      assert (e `in` (t `union` t2 `union` t5)) by fsetdec.
      assert (AtomSet.F.Empty (AtomSet.F.inter t2 t)). {
        rewrite H. fsetdec.
      }
      assert (e `notin` t2) by fsetdec.
      rewrite <- H1 in H0. fsetdec.
    }
    fsetdec.
  * assert (NatSet.F.In i (NatSet.F.remove j t6)) by fnsetdec.
    assert (~ NatSet.F.In i (NatSet.F.remove i (NatSet.F.remove j t6))) by fnsetdec.
    assert (NatSet.F.In i t0). {
      destruct_set_mem i t0...
      assert (~ NatSet.F.In i (t0 `u`N (t6 `\`N j) `\`N i)) by
         fnsetdec.
      rewrite <- H2 in H6. fnsetdec.
    }
    assert (NatSet.F.Subset t0 t6). {
      intros e Het6.
      destruct (e === i); subst...
      assert (NatSet.F.In e (NatSet.F.union t0 (NatSet.F.remove i (NatSet.F.remove j t6)))). fnsetdec.
      rewrite <- H2 in H7...
      assert (e <> j) by fnsetdec.
      fnsetdec.
    }
    fnsetdec.
  * assert (t1 `c`L t7). {
      intros e Het1.
      assert (e `in`L (t1 `u`L t4 `u`L t7)) by lsetdec.
      assert (e `~in`L t4) by lsetdec.
      rewrite <- H4 in H0. lsetdec.
    }
    lsetdec.
Qed.

Lemma subst_cset_open_cset_rec : forall x k C1 C2 D,
  capt C1 ->
  subst_cset x C1 (open_cset k C2 D) = open_cset k (subst_cset x C1 C2) (subst_cset x C1 D).
Proof with eauto*.
  intros x k C1 C2 D Closed.
  cbv [capt subst_cset open_cset] in *.
  csetdec.
Qed.

Lemma subst_cset_useless_repetition : forall x C1 C2 D,
  x `notin` `cset_fvars` C2 ->
  subst_cset x C1 (subst_cset x C2 D) = (subst_cset x C2 D).
Proof.
  intros.
  symmetry.
  eapply subst_cset_fresh with (C1 := subst_cset x C2 D)...
  cbv [subst_cset].
  csetdec...
Qed.


Lemma atoms_empty_union : forall xs ys,
  xs `u`A ys = {}A -> xs = {}A /\ ys = {}A.
Proof with eauto.
  intros.
  assert (AtomSet.F.Empty (xs `u`A ys)).
    rewrite H. fsetdec.
  split; fsetdec.
Qed.
Lemma atoms_empty_union_left : forall xs ys,
  xs `u`A ys = {}A -> xs = {}A.
Proof with eauto.
  intros. apply atoms_empty_union in H as [? ?]...
Qed.
Lemma atoms_empty_union_right : forall xs ys,
  xs `u`A ys = {}A -> ys = {}A.
Proof with eauto.
  intros. apply atoms_empty_union in H as [? ?]...
Qed.

Lemma nats_empty_union : forall xs ys,
  xs `u`N ys = {}N -> xs = {}N /\ ys = {}N.
Proof with eauto.
  intros.
  assert (NatSet.F.Empty (xs `u`N ys)).
    rewrite H. fnsetdec.
  split; fnsetdec.
Qed.
Lemma nats_empty_union_left : forall xs ys,
  xs `u`N ys = {}N -> xs = {}N.
Proof with eauto.
  intros. apply nats_empty_union in H as [? ?]...
Qed.
Lemma nats_empty_union_right : forall xs ys,
  xs `u`N ys = {}N -> ys = {}N.
Proof with eauto.
  intros. apply nats_empty_union in H as [? ?]...
Qed.

Lemma univ_empty_union : forall b b',
  b || b' = false -> b = false /\ b' = false.
Proof with eauto.
  intros.
  destr_bool...
Qed.
Lemma univ_empty_union_left : forall b b',
  b || b' = false -> b = false.
Proof with eauto.
  intros. apply univ_empty_union in H as [? ?]...
Qed.
Lemma univ_empty_union_right : forall b b',
  b || b' = false -> b' = false.
Proof with eauto.
  intros. apply univ_empty_union in H as [? ?]...
Qed.

Lemma labels_empty_union : forall xs ys,
  xs `u`L ys = {}L -> xs = {}L /\ ys = {}L.
Proof with eauto.
  intros.
  assert (LabelSet.F.Empty (xs `u`L ys)).
    rewrite H. lsetdec.
  split; lsetdec.
Qed.
Lemma labels_empty_union_left : forall xs ys,
  xs `u`L ys = {}L -> xs = {}L.
Proof with eauto.
  intros. apply labels_empty_union in H as [? ?]...
Qed.
Lemma labels_empty_union_right : forall xs ys,
  xs `u`L ys = {}L -> ys = {}L.
Proof with eauto.
  intros. apply labels_empty_union in H as [? ?]...
Qed.

Hint Resolve atoms_empty_union_left atoms_empty_union_right
              nats_empty_union_left nats_empty_union_right
              univ_empty_union_left univ_empty_union_right
              labels_empty_union_left labels_empty_union_right
  : core.

Lemma empty_cset_union : forall C1 C2,
  cset_union C1 C2 = {} ->
  C1 = {} /\ C2 = {}.
Proof with eauto.
  intros.
  destruct C1; destruct C2; simpl in H; try discriminate.
  inversion H; split; f_equal; try rewrite H1; try rewrite H2; try rewrite H3; try rewrite H4...
Qed.

Lemma cset_subst_self : forall C x,
  subst_cset x C (`cset_fvar` x) = C.
Proof.
  intros.
  unfold subst_cset.
  csetdec.
Qed.

Lemma not_in_fv_cset_iff : forall x C,
  x A`mem` C = false -> x `notin` (`cset_fvars` C).
Proof.
  intros.
  csetdec.
Qed.

Lemma empty_over_union : forall N1 N2,
  {}N = NatSet.F.union N1 N2 ->
  {}N = N1 /\ {}N = N2.
Proof.
  intros.
  assert (NatSet.F.Empty (NatSet.F.union N1 N2)) by (rewrite <- H; fnsetdec).
  split; fnsetdec.
Qed.

Lemma cset_references_fvar_over_union : forall C1 C2 x,
  x A`in` (cset_union C1 C2) ->
  x A`in` C1 \/ x A`in` C2.
Proof with eauto*.
  intros * H.
  destruct (cset_union C1 C2) eqn:Hunion...
  unfold cset_union in *.
  destruct C1 eqn:HC1; destruct C2 eqn:HC2; subst...
  inversion Hunion...
  assert (x `in` (t2 `union` t5)) by (rewrite H1; eauto*)...
  apply AtomSetFacts.union_iff in H0; inversion H0; subst...
Qed.


Lemma subst_cset_distributive_across_union : forall z C D1 D2,
  subst_cset z C (cset_union D1 D2) =
  cset_union (subst_cset z C D1) (subst_cset z C D2).
Proof with eauto.
  intros.
  destruct D1; destruct D2.
  unfold cset_union, subst_cset.
  csetdec.
Qed.

Lemma notin_cset_fvars_distributive_over_cset_union : forall x C D,
  x `notin` `cset_fvars` (cset_union C D) ->
  x `notin` `cset_fvars` C /\
  x `notin` `cset_fvars` D.
Proof.
  intros.
  destruct C eqn:EQ__C;
    destruct D eqn:EQ__D;
    unfold cset_union in *; split.
  all : (easy || fsetdec).
Qed.