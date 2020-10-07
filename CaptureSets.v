(** Support here for Capture Sets, a.k.a a record
    of free and bound variables tracking which variables
    are captured by a particualar type. *)

Require Import Metatheory.
Require Import Tactics.
Require Import OrderedTypeEx.
Require Import OrderedType.
Require Import FSetFacts.

(** Helpers, defining a set of natural numbers. *)
Module Type NATSET.
  Declare Module OT : UsualOrderedType with Definition t := nat.
  Parameter eq_nat_dec : forall x y : nat, {x = y} + {x <> y}.
End NATSET.

(** The implementation of the above interface is hidden for
    documentation purposes. *)

Module NatSetImpl : NATSET.
  (* begin hide *)
  Module OT := Nat_as_OT.
  Module Facts := OrderedTypeFacts OT.
  Definition eq_nat_dec : forall x y : nat, {x = y} + {x <> y} :=
    Facts.eq_dec. 
  (* end hide *)
End NatSetImpl.

(** Defining a set of Natural Numbers. *)
Module NatSet : FiniteSets.S with Module E := NatSetImpl.OT :=
  FiniteSets.Make NatSetImpl.OT.

(** The type [nats] is the type of finite sets of [nat]s. *)
Notation nats := NatSet.F.t.
Notation "{}N" :=
  NatSet.F.empty : metatheory_scope.

(** We instantiate two modules which provide useful lemmas and tactics
    work working with finite sets of atoms. *)

Module NatSetDecide := FSetDecide.Decide NatSet.F.
Module NatSetNotin  := FSetNotin.Notin   NatSet.F.
Module NatSetFacts  := FSetFacts.Facts NatSet.F.

(* *********************************************************************** *)
(** ** Tactics for working with finite sets of nats *)

(** The tactic [fnsetdec] is a general purpose decision procedure
    for solving facts about finite sets of atoms. *)

Ltac fnsetdec := try apply NatSet.eq_if_Equal; NatSetDecide.fsetdec.

(** The tactic [notin_simpl] simplifies all hypotheses of the form [(~
    In x F)], where [F] is constructed from the empty set, singleton
    sets, and unions. *)

Ltac nnotin_simpl := NatSetNotin.notin_simpl_hyps.

(** The tactic [notin_solve], solves goals of the form [(~ In x F)],
    where [F] is constructed from the empty set, singleton sets, and
    unions.  The goal must be provable from hypothesis of the form
    simplified by [notin_simpl]. *)

Ltac nnotin_solve := NatSetNotin.notin_solve.

(** A captureset -- a pair of free variables and bound variables. *)
Inductive captureset : Type :=
  | cset_universal : captureset
  | cset_set : atoms -> nats -> captureset.

Definition empty_cset := cset_set {} {}N.
Definition universal_cset := cset_universal.

(** The empty set may be written similarly to informal practice. *)
Notation "{}C" :=
  empty_cset : metatheory_scope.
Notation "{*}C" :=
  universal_cset : metatheory_scope.

(** Accessors *)
Definition cset_fvar (c : captureset) : atoms :=
  match c with
  | cset_universal => {}
  | cset_set A N => A
  end.
Definition cset_bvar (c : captureset) : nats :=
  match c with
  | cset_universal => {}N
  | cset_set A N => N
  end.

(** Singletons *)
Definition cset_singleton_fvar (a : atom) :=
  (cset_set (AtomSet.F.singleton a) (NatSet.F.empty)).
Definition cset_singleton_bvar (k : nat) :=
  (cset_set (AtomSet.F.empty) (NatSet.F.singleton k)).

(** Predicates for determining if a capture set explicity references
    a variable -- used for determining if a capture set is well formed.
    Don't use these predicates for determining if a capture set
    captures a variable, as one needs to also test cset_universal. *)
Definition cset_references_bvar (k : nat) (c : captureset) :=
  NatSet.F.In k (cset_bvar c).
Definition cset_references_fvar (a : atom) (c : captureset) :=
  AtomSet.F.In a (cset_fvar c).
Definition cset_references_bvar_dec (k : nat) (c : captureset) :=
  NatSet.F.mem k (cset_bvar c).
Definition cset_references_fvar_dec (a : atom) (c : captureset) :=
  AtomSet.F.mem a (cset_fvar c).

Lemma cset_references_bvar_eq (k : nat) (c : captureset) :
  cset_references_bvar_dec k c = true <-> cset_references_bvar k c.
Proof.
  unfold cset_references_bvar_dec. unfold cset_references_bvar.
  rewrite <-NatSetFacts.mem_iff. intuition.
Qed.

Lemma cset_references_fvar_eq (k : atom) (c : captureset) :
  cset_references_fvar_dec k c = true <-> cset_references_fvar k c.
Proof.
  unfold cset_references_fvar_dec. unfold cset_references_bvar.
  rewrite <-AtomSetFacts.mem_iff. intuition.
Qed.

Lemma cset_not_references_bvar_eq (k : nat) (c : captureset) :
  cset_references_bvar_dec k c = false <-> ~ cset_references_bvar k c.
Proof.
  unfold cset_references_bvar_dec. unfold cset_references_bvar.
  rewrite <-NatSetFacts.not_mem_iff. intuition.
Qed.

Lemma cset_not_references_fvar_eq (k : atom) (c : captureset) :
  cset_references_fvar_dec k c = false <-> ~ cset_references_fvar k c.
Proof.
  unfold cset_references_fvar_dec. unfold cset_references_bvar.
  rewrite <-AtomSetFacts.not_mem_iff. intuition.
Qed.


(** More predicates *)
Definition empty_cset_bvar_references (c : captureset) : Prop :=
  NatSet.F.Empty (cset_bvar c).
Definition empty_cset_fvar_references (c : captureset) : Prop :=
  AtomSet.F.Empty (cset_fvar c).

(** Opening a capture set with a bound variable d[k -> c] *)
Definition open_captureset_bvar (k : nat) (c : captureset) (d : captureset) : captureset :=
  if cset_references_bvar_dec k d then
    match c with
    | cset_universal => cset_universal
    | cset_set AC NC =>
      match d with 
      | cset_universal => cset_universal
      | cset_set AD ND => cset_set (AtomSet.F.union AC AD) (NatSet.F.union NC (NatSet.F.remove k ND))
      end
    end
  else
    d.

(** Substituting a capture set with a free variable d[a -> c] *)
Definition substitute_captureset_fvar (a : atom) (c : captureset) (d: captureset) : captureset :=
  if cset_references_fvar_dec a d then
    match c with
    | cset_universal => cset_universal
    | cset_set AC NC =>
      match d with 
      | cset_universal => cset_universal
      | cset_set AD ND => cset_set (AtomSet.F.union AC (AtomSet.F.remove a AD)) (NatSet.F.union NC ND)
      end
    end
  else
    d.

(** Capture set unions are what you'd expect. *)
Definition cset_union (c1 c2 : captureset) : captureset :=
  match c1 with
  | cset_universal => cset_universal
  | cset_set A1 N1 =>
    match c2 with
    | cset_universal => cset_universal
    | cset_set A2 N2 => cset_set (AtomSet.F.union A1 A2) (NatSet.F.union N1 N2)
    end
  end.

(** Empty capture sets / universal capture sets *)
Definition cset_empty (c : captureset) : Prop :=
  match c with
  | cset_universal => False
  | cset_set A N => empty_cset_bvar_references c /\ empty_cset_fvar_references c
  end.

(** Predicates around subsets, and decidability for destruction *)
Definition cset_subset_prop (c1 c2 : captureset) : Prop :=
    AtomSet.F.Subset (cset_fvar c1) (cset_fvar c2) /\ NatSet.F.Subset (cset_bvar c1) (cset_bvar c2) /\
      (c1 = cset_universal -> c2 = cset_universal).
Definition cset_subset_dec (c1 c2 : captureset) :=
    AtomSet.F.subset (cset_fvar c1) (cset_fvar c2) && NatSet.F.subset (cset_bvar c1) (cset_bvar c2) &&
      (match c1 with
        | cset_set _ _ => true
        | cset_universal => match c2 with
                              | cset_universal => true
                              | cset_set _ _ => false
                            end
      end).

(** A helper, to eliminate terms like <complex computation> && false *)
Local Lemma reduce_false (b : bool) : b && false = false.
Proof.
destr_bool.
Qed.

(** Why isn't this part of the standard library? **)
Local Lemma eliminate_false (b : bool) : (b = false) <-> (b <> true).
Proof.
destr_bool; split; destr_bool.
contradict H; trivial.
Qed.

(** Two relations relating the subset relation to the subset computation. *)
Lemma cset_subset_iff (c1 c2 : captureset) : cset_subset_prop c1 c2 <-> cset_subset_dec c1 c2 = true.
Proof with auto*.
  unfold cset_subset_prop. unfold cset_subset_dec.
  split.
  (* --> *)
  * intro.
    destruct_conjs.
    rewrite NatSetFacts.subset_iff in *.
    rewrite AtomSetFacts.subset_iff in *.
    rewrite H. rewrite H0. simpl.
    destruct c1; destruct c2...
    exfalso.
    revert H1. intuition...
  (* <-- *)
  * intro.
    case_eq (AtomSet.F.subset (cset_fvar c1) (cset_fvar c2));
      case_eq (NatSet.F.subset (cset_bvar c1) (cset_bvar c2));
      case_eq c1; case_eq c2; intros;
      rewrite NatSetFacts.subset_iff in *; rewrite AtomSetFacts.subset_iff in *; rewrite H0 in H;
      rewrite H1 in H; rewrite H2 in H; rewrite H3 in H; simpl in *; revert H; destr_bool; intuition;
      try revert H; try rewrite reduce_false; try destr_bool; try rewrite AtomSetFacts.subset_iff.
Qed.

Lemma cset_subset_not_iff (c1 c2 : captureset) : ~ cset_subset_prop c1 c2 <-> cset_subset_dec c1 c2 = false.
Proof with auto*.
  split.
  * intro H. rewrite eliminate_false. contradict H. apply cset_subset_iff...
  * intro H. rewrite eliminate_false in H. contradict H. apply cset_subset_iff...
Qed.
