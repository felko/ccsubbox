(** Support here for Capture Sets, a.k.a a record
    of free and bound variables tracking which variables
    are captured by a particualar type. *)

Require Import Metatheory.
Require Import Tactics.
Require Import OrderedTypeEx.
Require Import OrderedType.

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

(** A captureset -- a pair of free variables and bound variables. *)
Record captureset : Type := make_captureset {
  cset_fvar : atoms;
  cset_bvar : nats;
  cset_universal : bool;
}.

Definition empty_cset := (make_captureset (AtomSet.F.empty) (NatSet.F.empty) false).
Definition universal_cset := (make_captureset (AtomSet.F.empty) (NatSet.F.empty) true).

(** The empty set may be written similarly to informal practice. *)
Notation "{}C" :=
  empty_cset : metatheory_scope.
Notation "{*}C" :=
  universal_cset : metatheory_scope.

(** Singletons *)
Definition cset_singleton_fvar (a : atom) :=
  (make_captureset (AtomSet.F.singleton a) (NatSet.F.empty) false).
Definition cset_singleton_bvar (k : nat) :=
  (make_captureset (AtomSet.F.empty) (NatSet.F.singleton k) false).

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

(** More predicates *)
Definition empty_cset_bvar_references (c : captureset) :=
  NatSet.F.Empty (cset_bvar c).
Definition empty_cset_fvar_references (c : captureset) :=
  AtomSet.F.Empty (cset_fvar c).

(** Opening a capture set with a bound variable d[k -> c] *)
Definition open_captureset_bvar (k : nat) (c : captureset) (d : captureset) :=
  if cset_references_bvar_dec k c then
    make_captureset (AtomSet.F.union (cset_fvar c) (cset_fvar d)) 
                    (NatSet.F.union (cset_bvar c) (NatSet.F.remove k (cset_bvar d)))
                    (orb (cset_universal c) (cset_universal d))
  else
    d.

(** Substituting a capture set with a free variable d[a -> c] *)
Definition substitute_captureset_fvar (a : atom) (c : captureset) (d: captureset) :=
  if cset_references_fvar_dec a c then
    make_captureset (AtomSet.F.union (cset_fvar c)
                     (AtomSet.F.remove a (cset_fvar d))) 
                    (NatSet.F.union (cset_bvar c) (cset_bvar d))
                    (orb (cset_universal c) (cset_universal d))
  else
    d.

(** Capture set unions are what you'd expect. *)
Definition cset_union (c1 c2 : captureset) :=
    make_captureset (AtomSet.F.union (cset_fvar c1) (cset_fvar c2))
                    (NatSet.F.union (cset_bvar c1) (cset_bvar c2))
                    (orb (cset_universal c1) (cset_universal c2)).

(** Empty capture sets / universal capture sets *)
Definition cset_empty (c : captureset) :=
    empty_cset_bvar_references c /\ empty_cset_fvar_references c /\ (cset_universal c = false).
Definition cset_universal_prop (c : captureset) :=
    cset_universal c = true.

(** Predicates around subsets *)
Definition cset_subset_prop (c1 c2 : captureset) :=
    AtomSet.F.Subset (cset_fvar c1) (cset_fvar c2) /\ NatSet.F.Subset (cset_bvar c1) (cset_bvar c2) /\
      (cset_universal_prop c1 -> cset_universal_prop c2).