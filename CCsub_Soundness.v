Require Import Coq.Program.Equality.
Require Import TaktikZ.

Require Import CCsub_Subcapt.
Require Import CCsub_Subtyping.
Require Import CCsub_Typing.
Require Import CCsub_Substitution.

Set Nested Proofs Allowed.


(** TODO check where this is used and maybe use "wellformed" tactic **)
Lemma wf_typ_extract_typ_arrow : forall C E T1 T2,
  wf_typ_in E (typ_capt C (typ_arrow T1 T2)) ->
  exists L, forall x, x `notin` L ->
    wf_typ ([(x, bind_typ T1)] ++ E) (dom E `union` singleton x) (dom E) (open_ct T2 (`cset_fvar` x)).
Proof with eauto.
  intros * HWf.
  inversion HWf; subst.
  inversion H5; subst...
Qed.

(** TODO check where this is used and maybe use "wellformed" tactic **)
Lemma typing_extract_typ_arrow : forall E e C T1 T2,
  typing E e (typ_capt C (typ_arrow T1 T2)) ->
  exists L, forall x, x `notin` L ->
    wf_typ ([(x, bind_typ T1)] ++ E) (dom E `union` singleton x) (dom E) (open_ct T2 (`cset_fvar` x)).
Proof with eauto.
  intros * Htyp.
  apply (wf_typ_extract_typ_arrow C)...
Qed.


(* ********************************************************************** *)
(** * #<a name="preservation"></a># Preservation *)


Definition no_type_bindings (E : env) : Prop :=
  forall X U, ~ binds X (bind_sub U) E.

Lemma inversion_toplevel_type : forall E T,
  no_type_bindings E ->
  wf_typ_in E T ->
  exists C P, T = typ_capt C P.
Proof with eauto.
  intros * NoTyp H.
  inversion H; subst.
  - inversion H; subst. specialize (NoTyp X U). contradiction.
  - exists C. exists P...
Qed.

Lemma preservation : forall E e e' T,
  no_type_bindings E ->
  typing E e T ->
  red e e' ->
  typing E e' T.
Proof with simpl_env; eauto.
  intros * NoTypBnd Typ. generalize dependent e'.
  induction Typ; intros e' Red; try solve [ inversion Red; subst; eauto ].
  - Case "typing_app".
    inversion Red; subst...
    + SCase "red_abs".
      forwards (P1 & S2 & L & P2): typing_inv_abs Typ1 T1 T2 Cf. {
        eapply sub_reflexivity...
      }
      pick fresh x.
      forwards (? & ? & ?): P2 x...
      rewrite (subst_ee_intro x)...
      rewrite (subst_ct_intro x)...
      apply typing_through_subst_ee'
        with (U := T1')
            (Ap := dom ([(x, bind_typ T1')] ++ E))
            (Am := dom E) ...
      * apply (typing_sub (open_ct S2 (`cset_fvar` x)))...
        -- rewrite_nil_concat.
           forwards (U & HtypU & HsubU): values_have_precise_captures e2; eauto.
           inversion HsubU; subst.
           eapply (typing_narrowing_typ T)...
           eauto using (sub_transitivity T1).

           (* lets (C & P & Eq): inversion_toplevel_type E T1'; subst... *)
           (* rewrite_nil_concat. *)
           (* eapply (typing_narrowing_typ T)... *)
           (* eauto using (sub_transitivity T1). *)
        -- rewrite_nil_concat.
          apply (sub_narrowing_typ) with (Q := T1)...
      * replace (singleton x `union` dom E)
          with (dom E `union` singleton x) by (clear Fr; fsetdec)...
        rewrite_nil_concat.
        apply wf_typ_narrowing_typ_base with (V := T)...
      * eapply wf_cset_set_weakening; [eapply typing_cv | fsetdec]...
      * assert (wf_cset_in E (cv T1')) as HA. {
          forwards (_ & _ & ?): typing_regular Typ2.
          apply cv_wf...
        }
        eapply wf_cset_set_weakening; [ apply HA | fsetdec ].
  - Case "typing_tapp".
    inversion Red; subst...
    SCase "red_tabs".
    forwards (Sub & P1 & L & P2): typing_inv_tabs Typ T1 T2 C. {
      eapply sub_reflexivity...
    }
    pick fresh X.
    forwards (S2 & ?): P2 X...
    rewrite (subst_te_intro X)...
    rewrite (subst_tt_intro X)...
    rewrite_env (map (subst_tb X T) empty ++ E).
    apply (typing_through_subst_te T1)...
Qed.

(* ********************************************************************** *)
(** * #<a name="progress"></a># Progress *)

(* ********************************************************************** *)
(** ** Canonical forms (14) *)

Lemma canonical_form_abs : forall e U1 U2 C,
  value e ->
  typing empty e (typ_capt C (typ_arrow U1 U2)) ->
  exists V, exists e1, e = exp_abs V e1.
Proof.
  intros e U1 U2 C Val Typ.
  remember empty.
  remember (typ_arrow U1 U2).
  revert U1 U2 Heqp Heql.
  dependent induction Typ; intros U1 U2 EQT EQE; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
  Case "typing_sub".
  inversion H; subst; eauto.
  + binds_cases H0.
  + inversion H5; subst.
    eapply IHTyp; eauto.
Qed.

Lemma canonical_form_tabs : forall e U1 U2 C,
  value e ->
  typing empty e (typ_capt C (typ_all U1 U2)) ->
  exists V, exists e1, e = exp_tabs V e1.
Proof.
  intros e U1 U2 C Val Typ.
  remember empty.
  remember (typ_all U1 U2).
  revert U1 U2 Heqp Heql.
  dependent induction Typ; intros U1 U2 EQT EQE; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
  Case "typing_sub".
  inversion H; subst; eauto.
  + binds_cases H0.
  + inversion H5; subst.
    eapply IHTyp; eauto.
Qed.

(* ********************************************************************** *)
(** ** Progress (16) *)

Lemma progress : forall e T,
  typing empty e T ->
  value e \/ exists e', red e e'.
Proof with eauto.
  intros e T Typ.
  remember empty. generalize dependent Heql.
  assert (Typ' : typing l e T)...
  induction Typ; intros EQ; subst...
  Case "typing_var".
    inversion H0.
  Case "typing_app".
    inversion H0.
    destruct IHTyp1 as [Val1 | [e1' Rede1']]...
    SCase "Val1".
      destruct IHTyp2 as [Val2 | [e2' Rede2']]...
      SSCase "Val2".
        lets (S & e3 & EQ): canonical_form_abs Val1 Typ1.
        subst.
        right.
        exists (open_ee e3 e2 (free_for_cv e2))...
  Case "typing_tapp".
    right.
    destruct IHTyp as [Val1 | [e1' Rede1']]...
    SCase "Val1".
      lets (S & e3 & EQ): canonical_form_tabs Val1 Typ.
      subst.
      exists (open_te e3 T)...
Qed.

