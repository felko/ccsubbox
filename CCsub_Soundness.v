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

Lemma ctx_typing_narrowing : forall T e S,
  |-ctx e ~: T ->
  sub empty S T ->
  |-ctx e ~: S.
Proof with eauto.
  intros * Typ Sub. generalize dependent S.
  dependent induction Typ; intros S Sub.
  - constructor...
  - inversion Sub;subst. {
      inversion select (binds _ _ _).
    }
    inversion select (sub_pre _ _ _); subst.
    econstructor.
    + apply H.
    + apply (sub_transitivity T1)...
    + apply IHTyp.
      pick fresh x.
      replace (open_ct S2 (cv T1'))
        with (subst_ct x (cv T1') (open_ct S2 (`cset_fvar` x))).
      2: {
        rewrite subst_ct_open_ct.
        3: notin_solve.
        2: eapply capt_from_wf_cset; eapply (cv_wf empty)...
        f_equal.
        2: csetdec.
        symmetry; apply subst_ct_fresh.
        notin_solve.
      }
      replace (open_ct T2 (cv T1'))
        with (subst_ct x (cv T1') (open_ct T2 (`cset_fvar` x))).
      2: {
        rewrite subst_ct_open_ct.
        3: notin_solve.
        2: eapply capt_from_wf_cset; eapply (cv_wf empty)...
        f_equal.
        2: csetdec.
        symmetry; apply subst_ct_fresh.
        notin_solve.
      }
      rewrite_env ((map (subst_cb x (cv T1')) empty) ++ empty).
      apply (sub_through_subst_ct x T1).
      2: apply sub_implies_subcapt...
      simpl_env; apply H12; notin_solve.
  - econstructor...
    1: apply (sub_transitivity T1')...
    assert (wf_pretyp_in empty (typ_arrow T1 T2)) as HA by eauto.
    inversion HA; subst.
    admit.                      (* by subst_ct_monotonicity *)
  - inversion Sub;subst. {
      inversion select (binds _ _ _).
    }
    inversion select (sub_pre _ _ _); subst.
    econstructor.
    1: apply (sub_transitivity T1)...
    apply IHTyp.
    pick fresh x.
    replace (open_tt S2 T) with (subst_tt x T (open_tt S2 x)).
    2: {
      rewrite subst_tt_open_tt...
      f_equal.
      2: unfold subst_tt; destruct (x == x); easy.
      symmetry; apply subst_tt_fresh.
      notin_solve.
    }
    replace (open_tt T2 T) with (subst_tt x T (open_tt T2 x)).
    2: {
      rewrite subst_tt_open_tt...
      f_equal.
      2: unfold subst_tt; destruct (x == x); easy.
      symmetry; apply subst_tt_fresh.
      notin_solve.
    }
    rewrite_env ((map (subst_tb x T) empty) ++ empty).
    apply sub_through_subst_tt with (Z := x) (Q := T1)...
Admitted.

Lemma preservation : forall e e',
  typing_state e ->
  step e e' ->
  typing_state e'.
Proof with simpl_env; eauto.
  intros * Typ Step.
  inversion Step; subst.
  - inversion Typ; subst.
    dependent induction H2. 2: {
      eapply IHtyping...
      eapply ctx_typing_narrowing...
    }
    econstructor...
    econstructor...
  - inversion Typ; subst.
    dependent induction H2. 2: {
      eapply IHtyping...
      eapply ctx_typing_narrowing...
    }
    econstructor...
    econstructor...
  - inversion Typ; subst.
    inversion H2; subst.
    econstructor...
    econstructor...
  - inversion Typ; subst.
    inversion H2; subst.
    dependent induction H4. 2: {
      inversion select (sub empty S _); subst. {
        inversion select (binds _ _ _).
      }
      inversion select (sub_pre empty _ _); subst.
      eapply IHtyping...
      1: eapply (sub_transitivity T1)...
      eapply (ctx_typing_narrowing (open_ct T2 (cv T0)))...
      pick fresh x.
      replace (open_ct S2 (cv T0))
        with (subst_ct x (cv T0) (open_ct S2 (`cset_fvar` x))).
      2: {
        rewrite subst_ct_open_ct.
        3: notin_solve.
        2: eapply capt_from_wf_cset; eapply (cv_wf empty)...
        f_equal.
        2: csetdec.
        symmetry; apply subst_ct_fresh.
        notin_solve.
      }
      replace (open_ct T2 (cv T0))
        with (subst_ct x (cv T0) (open_ct T2 (`cset_fvar` x))).
      2: {
        rewrite subst_ct_open_ct.
        3: notin_solve.
        2: eapply capt_from_wf_cset; eapply (cv_wf empty)...
        f_equal.
        2: csetdec.
        symmetry; apply subst_ct_fresh.
        notin_solve.
      }
      rewrite_env ((map (subst_cb x (cv T0)) empty) ++ empty).
      eapply (sub_through_subst_ct x).
      1: eauto.
      apply sub_implies_subcapt...
    }
    econstructor...
    pick fresh x.
    replace (open_ee e0 v (free_for_cv v))
         with (subst_ee x v (free_for_cv v) (open_ee e0 x (`cset_fvar` x))).
    2: {
      rewrite subst_ee_open_ee...
      2: admit.
      f_equal.
      3: csetdec.
      2: unfold subst_ee; destruct (x == x); easy.
      symmetry; apply subst_ee_fresh...
    }
    replace (open_ct T2 (cv T0))
      with (subst_ct x (cv T0) (open_ct T2 (`cset_fvar` x))).
    2: {
      rewrite subst_ct_open_ct...
      f_equal.
      2: csetdec.
      symmetry; apply subst_ct_fresh...
    }
    eapply typing_through_subst_ee'.
    (* T0 = (C T0') for some C, T0' b/c (typing empty v T0) *)
    all: admit.
  - inversion Typ; subst.
    admit.
Admitted.

(* ********************************************************************** *)
(** * #<a name="progress"></a># Progress *)

(* ********************************************************************** *)
(** ** Progress (16) *)

Lemma progress_step : forall s1,
  typing_state s1 ->
  done s1 \/ exists s2, s1 --> s2.
Proof with eauto.
  intros * Typ.
  inversion Typ; subst.
  remember empty. generalize dependent Heql.
  rename select (typing l e T) into Typ'.
  dependent induction Typ'; intros EQ; subst...
  - inversion select (binds _ _ _).
  - inversion select (binds _ _ _).
  - assert (value (exp_abs V e1)) by admit.
    inversion H; subst...
    + left...
      constructor...
    + right.
      eexists.
      rename select (typing empty e _) into TypE.
      (* forwards: canonical_form_abs TypE... *)
      admit.                    (* should KArg only contain values? *)
  - assert (value (exp_tabs V e1)) by admit.
    inversion H; subst...
    + left...
      constructor...
    + right.
      eexists.
      rename select (typing empty e _) into TypE.
      (* forwards: canonical_form_abs TypE... *)
      admit.                    (* should KArg only contain values? *)
  - apply IHTyp'...
    eapply ctx_typing_narrowing...
Admitted.
