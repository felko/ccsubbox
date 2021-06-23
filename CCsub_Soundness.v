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

Lemma typing_ctx_free_tvar : forall E k T,
  E |-ctx k ~: T ->
  no_type_bindings E.
Proof with eauto.
  intros. unfold no_type_bindings; intros.
  induction H...
  * intro. binds_cases H...
  * intro. binds_cases H0...
Qed.

Lemma preservation : forall e e',
  typing_state e ->
  step e e' ->
  typing_state e'.
Proof with simpl_env; eauto.
  intros * Typ Step.
  inversion Step; subst.
  - Case "step-app".
    inversion Typ; subst.
    dependent induction H2. 2: {
      eapply IHtyping...
      eapply typing_ctx_sub...
    }
    econstructor...
    econstructor...
  - Case "step-tapp".
    inversion Typ; subst.
    dependent induction H2. 2: {
      eapply IHtyping...
      eapply typing_ctx_sub...
    }
    econstructor...
    econstructor...
  - Case "step-fun->arg".
    inversion Typ; subst.
    dependent induction H2...
    econstructor...
    econstructor...
  - Case "step-throw".
    inversion Typ; subst.
    dependent induction H2...
    + apply IHtyping...
      eapply typing_ctx_sub...
    + econstructor...
      econstructor...
  - Case "step-handler->arg".
    inversion Typ; subst...
    dependent induction H2... 
    econstructor...
    econstructor...
  - Case "step-app".
    inversion Typ; subst...
    assert (no_type_bindings E) by (eauto using typing_ctx_free_tvar).
    dependent induction H2...
    unshelve epose proof (typing_inv_abs E T e0 (typ_capt C (typ_arrow T1 T2)) _) as InvAbs...
    unshelve epose proof (InvAbs T1 T2 C ltac:(eauto using sub_reflexivity)) as [Sub [S2 [L TypingX]]].
    pick fresh x.
    specialize (TypingX x ltac:(notin_solve)) as [TypingX [Wf SubS2]].
    {
      eapply typ_step...
      erewrite subst_ee_intro with (x := x)...
      erewrite subst_ct_intro with (X := x)...
      assert (wf_typ_in E T1') as WfTypV by eauto.
      assert (wf_typ_in E T1)  as WfTypT by eauto.
      (**
        E - environment
        x - fresh atom
        v - argument/value
        e0 - body of abstraction (\lambda T e0)
      *)
      forwards (C' & P' & ?): inversion_toplevel_type WfTypV; subst...
      forwards (C'' & P'' & ?): inversion_toplevel_type WfTypT; subst...
      eapply typing_through_subst_ee' with (Ap := dom E `union` singleton x) (Am := dom E)...
      1: {
        (* typing *)
        rewrite_nil_concat.
        eapply typing_narrowing_typ...
        eapply typing_sub...
        rewrite_nil_concat.
        eapply typing_narrowing_typ...
      }
      1: {                        (* wf_typ *)
        rewrite_env (empty ++ [(x, bind_typ (typ_capt C' P'))] ++ E).
        eapply wf_typ_narrowing_typ_base with (V := T); simpl_env...
      }
      all: eauto.                 (* garbage, evars instantiated by above goal *)
      1: {                        (* wf_cset free_for_cv *)
        rename select (typing E v _) into TypV.
        forwards WfFvV: typing_cv TypV.
        applys wf_cset_set_weakening WfFvV...
      }
      1: {                        (* wf_cset C *)
        assert (wf_cset_in E C') as WfC by eauto.
        applys wf_cset_set_weakening WfC...
      }
    }
  - Case "step-tapp".
    inversion Typ; subst...
    dependent induction H1...
    econstructor...
    unshelve epose proof (typing_inv_tabs E T1 _ (typ_capt C (typ_all T0 T3))) as InvTAbs...
    unshelve epose proof (InvTAbs H2 T0 T3 _ ltac:(eauto using sub_reflexivity)) as [Sub [S2 [L TypingX]]].
    pick fresh x.
    specialize (TypingX x ltac:(notin_solve)) as [TypingX SubS2].
    rewrite (subst_te_intro x)...
    rewrite (subst_tt_intro x)...
    rewrite_env (map (subst_tb x T2) empty ++ E).
    apply (typing_through_subst_te T0)...
  - inversion Typ; subst...
    assert (no_type_bindings E) by (eauto using typing_ctx_free_tvar).
    eapply typ_step...
    eapply typing_ctx_reset...
    dependent induction H3...
    + inv
    + admit.
  - inversion Typ; subst...
    dependent induction H2...
    econstructor...
    admit.
  - inversion Typ; subst...
    dependent induction H2...
    econstructor...
  - inversion Typ; subst...
    dependent induction H2...
    econstructor...
  - inversion Typ; subst...
    dependent induction H2...
    econstructor...
  - inversion Typ; subst...
    dependent induction H2...
    econstructor...
  - inversion Typ; subst...
    admit.
  - inversion Typ; subst...
    dependent induction H2...
    econstructor...
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
  - inversion Typ; subst.
    assert (value (exp_abs V e1))...
    inversion H; subst...
    + left...
      constructor...
    + right.
      destruct (canonical_form_abs _ _ _ _ H5 H8) as [S [ E1 EQ ] ]; subst...
  - inversion Typ; subst.
    assert (value (exp_tabs V e1))...
    inversion H; subst...
    + left...
      constructor...
    + right.
      destruct (canonical_form_abs _ _ _ _ H5 H8) as [S [ E1 EQ ] ]; subst...
  - apply IHTyp'...
    eapply ctx_typing_narrowing...
Qed.
