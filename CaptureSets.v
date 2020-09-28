Require Import List.
Require Import Max.
Require Import OrderedType.
Require Import OrderedTypeEx.
Open Scope nat_scope.

Require Import FiniteSets.
Require Import FSetDecide.
Require Import FSetNotin.
Require Import ListFacts.
Require Import Atom.

Require Import Tactics.


Module AtomFacts := OrderedTypeFacts Atom_as_OT.
Module NatFacts := OrderedTypeFacts Nat_as_OT.

Inductive capture_var : Set :=
  | capture_fvar : atom -> capture_var
  | capture_bvar : nat -> capture_var
  (* | cset_tvar : nat -> cset_member *)
.
 
Definition capture_var_lt (a : capture_var) (b : capture_var) : Prop :=
  match a with
    | capture_fvar a' =>
      match b with
        | capture_fvar b' => Atom_as_OT.lt a' b'
        | capture_bvar b' => False
      end
    | capture_bvar a' =>
      match b with
        | capture_bvar b' => a' < b'
        | capture_fvar b' => True
      end
  end.

Definition capture_var_cmp (a : capture_var) (b : capture_var) : comparison :=
  match a with
    | capture_fvar a' =>
      match b with
        | capture_fvar b' =>
          match Atom_as_OT.compare a' b' with
            | GT _ => Gt
            | LT _ => Lt
            | EQ _ => Eq
          end
        | capture_bvar b' => Gt
        end
    | capture_bvar a' =>
      match b with
        | capture_bvar b' =>
          match Nat_as_OT.compare a' b' with
            | GT _ => Gt
            | LT _ => Lt
            | EQ _ => Eq
          end
        | capture_fvar b' => Lt
    end
  end.

Lemma capture_var_cmp_eq (a b : capture_var):
  capture_var_cmp a b = Eq <-> a = b.
Proof.
  unfold capture_var_cmp. 
  repeat light || NatFacts.order || AtomFacts.order || destruct_match.
Qed.

Lemma capture_var_cmp_lt (a b : capture_var):
  capture_var_cmp a b = Lt <-> capture_var_lt a b.
Proof.
  unfold capture_var_cmp. 
  repeat light || NatFacts.order || AtomFacts.order || destruct_match.
Qed.

Lemma capture_var_cmp_gt (a b : capture_var):
  capture_var_cmp a b = Gt <-> capture_var_lt b a.
Proof.
  unfold capture_var_cmp. 
  repeat light || NatFacts.order || AtomFacts.order || destruct_match.
Qed.

Module capture_var_as_OT <: UsualOrderedType.
  Definition t := capture_var.

  Definition eq := @eq capture_var.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  
  Definition lt := capture_var_lt.

  Lemma lt_trans : forall x y z : capture_var, lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt. unfold capture_var_lt.
    repeat light || NatFacts.order || AtomFacts.order || destruct_match.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.   
    unfold lt. unfold capture_var_lt. unfold eq. 
    repeat light || NatFacts.order || AtomFacts.order || destruct_match.  
  Qed.

  Definition compare x y : Compare lt eq x y.
  Proof.
    case_eq (capture_var_cmp x y); intro.
    - apply EQ; apply capture_var_cmp_eq; light.
    - apply LT; apply capture_var_cmp_lt; light.
    - apply GT; apply capture_var_cmp_gt; light.
  Qed.

  Lemma eq_dec : forall x y : capture_var, {x = y} + {x <> y}.
  Proof.
    intros. 
    destruct x; 
    destruct y. 
    - destruct (Atom_as_OT.eq_dec a a0). intuition. right. intuition.
    - right. discriminate.
    - right. discriminate.
    - destruct (Nat_as_OT.eq_dec n n0). intuition. right. intuition.
  Qed.
End capture_var_as_OT.

(* ********************************************************************** *)
(** * Finite sets of capture variables *)
Module Facts := OrderedTypeFacts capture_var_as_OT.

(* ********************************************************************** *)
(** ** Definitions *)

Module CaptureSet : FiniteSets.S :=
  FiniteSets.Make capture_var_as_OT.

(** The type [atoms] is the type of finite sets of [atom]s. *)

Notation captureset := CaptureSet.F.t.

(** Basic operations on finite sets of atoms are available, in the
    remainder of this file, without qualification.  We use [Import]
    instead of [Export] in order to avoid unnecessary namespace
    pollution. *)

Import CaptureSet.F.

(** We instantiate two modules which provide useful lemmas and tactics
    work working with finite sets of atoms. *)

Module CaptureSetDecide := FSetDecide.Decide CaptureSet.F.
Module CaptureSetNotin  := FSetNotin.Notin   CaptureSet.F.


