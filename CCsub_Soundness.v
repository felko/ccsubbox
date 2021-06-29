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
Lemma typing_extract_typ_arrow : forall E Q e C T1 T2,
  typing E Q e (typ_capt C (typ_arrow T1 T2)) ->
  exists L, forall x, x `notin` L ->
    wf_typ ([(x, bind_typ T1)] ++ E) (dom E `union` singleton x) (dom E) (open_ct T2 (`cset_fvar` x)).
Proof with eauto.
  intros * Htyp.
  apply (wf_typ_extract_typ_arrow C)...
Qed.

(* ********************************************************************** *)
(** ** Canonical forms (14) *)

Lemma canonical_form_abs : forall Q e U1 U2 C,
  value e ->
  typing empty Q e (typ_capt C (typ_arrow U1 U2)) ->
  exists V, exists e1, e = exp_abs V e1.
Proof.
  intros Q e U1 U2 C Val Typ.
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

Lemma canonical_form_tabs : forall Q e U1 U2 C,
  value e ->
  typing empty Q e (typ_capt C (typ_all U1 U2)) ->
  exists V, exists e1, e = exp_tabs V e1.
Proof.
  intros Q e U1 U2 C Val Typ.
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

Lemma typing_ctx_free_tvar : forall E Q k T,
  E @ Q |-ctx k ~: T ->
  no_type_bindings E.
Proof with eauto.
  intros. unfold no_type_bindings; intros.
  induction H...
  * intro. binds_cases H...
Qed.

Fixpoint env_fv_ct (F : env) {struct F} : atoms :=
  match F with
  | nil => {}A
  | (_, bind_typ T) :: F' => (fv_ct T) `u`A (env_fv_ct F')
  | (_, bind_sub T) :: F' => (fv_ct T) `u`A (env_fv_ct F')
  end.

Lemma binds_sig_unique : forall T1 T2 l Q,
    Signatures.binds l (bind_sig T1) Q ->
    Signatures.binds l (bind_sig T2) Q ->
    T1 = T2.
Proof.
  intros* ? ?.
  congruence.
Qed.

Lemma typing_inversion_lvar : forall E Q l T,
  E @ Q |-t (exp_lvar l) ~: T ->
  exists C P, T = typ_capt C P.
Proof.
  intros * H.
  dependent induction H; eauto.
  forwards (C & P & ?): IHtyping l; eauto; subst.
  inversion select (sub _ (typ_capt C P) _); subst.
  eauto.
Qed.

Lemma preservation : forall e e',
  typing_state e ->
  step e e' ->
  typing_state e'.
Proof with eauto using typing_ctx_sub, wf_cset_set_weakening.
  intros * Typ Step.
  inversion Step; subst.
  - Case "step-app".
    inversion Typ; subst.
    dependent induction H3...
    econstructor...
    econstructor...
  - Case "step-tapp".
    inversion Typ; subst.
    dependent induction H3...
    econstructor...
    econstructor...
  - Case "step-fun->arg".
    inversion Typ; subst.
    dependent induction H2...
    econstructor...
    econstructor...
  - Case "step-throw".
    inversion Typ; subst.
    dependent induction H3...
    econstructor...
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

    forwards (Sub & S2 & L & TypingX): typing_inv_abs H0 T1 T2 C...
    1: { eauto using sub_reflexivity. }

    pick fresh x.
    destruct (TypingX x) as (TypingX' & Wf & SubS2).
    1: { notin_solve. }

    eapply typ_step...
    rewrite (subst_ee_intro x) by notin_solve.
    rewrite (subst_ct_intro x) by notin_solve.
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

    eapply typing_through_subst_ee' with (Ap := dom E `union` singleton x) (Am := dom E); trivial.
    4,5: simpl_env; clear_frees; fsetdec.
    3: notin_solve.
    + (* typing *)
      rewrite_nil_concat.
      eapply typing_narrowing_typ...
      eapply typing_sub...
      rewrite_nil_concat.
      eapply typing_narrowing_typ...
    + rewrite_nil_concat.
      eapply wf_typ_narrowing_typ_base with (V := T); simpl_env...
    + (* wf_cset free_for_cv *)
      rename select (typing E _ v _) into TypV.
      forwards WfFvV: typing_cv TypV...
    + (* wf_cset C *)
      assert (wf_cset_in E C') as WfC by admit; simpl.
      applys wf_cset_set_weakening WfC...

  - Case "step-tapp".
    inversion Typ; subst...
    dependent induction H1...
    econstructor...

    forwards (Sub & S2 & L & TypingX): typing_inv_tabs H3 T0 T3.
    1: { eauto using sub_reflexivity. }

    pick fresh x.
    destruct (TypingX x) as [Typ' SubS2]...
    rewrite (subst_te_intro x)...
    rewrite (subst_tt_intro x)...
    rewrite_env (map (subst_tb x T2) empty ++ E).
    apply (typing_through_subst_te T0)...
  - inversion Typ; subst...
    assert (no_type_bindings E) by (eauto using typing_ctx_free_tvar).
    Notation "#H" := CCsub_Definitions.H.
    dependent induction H4...
    unfold Signatures.singleton_list.
    pick fresh x for L.
    specialize (H1 x Fr).
    assert (wf_pretyp_in E (typ_ret T)) by admit. (* come on *)
    rewrite_env (empty ++ [(x, bind_typ (typ_capt {*} (typ_ret T)))] ++ E) in H1.
    replace Q with ([(a, bind_sig (typ_capt {*} (typ_ret T)))] ++ Q) in H1 by admit. (* needs a simple lemma *)
    rename H1 into H1'.
    forwards H1: typing_narrowing_typ (`cset_lvar` a) (typ_ret T) H1'. 1: {
      constructor.
      - apply subcapt_universal...
      - eapply sub_pre_reflexivity...
    }
    apply typing_through_subst_ee with (u := (exp_lvar a)) in H1.
    2: { eauto. }
    2: {
      simpl free_for_cv.
      eapply typing_lvar...
      admit.                  (* wf_sig, needs more preconditions *)
    }
    simpl_env in H1; unfold Signatures.singleton_list in H1.
    admit.
    (* eapply typ_step. *)
  - inversion Typ; subst...
    dependent induction H2...
    clear IHtyping_ctx.
    dependent induction H0.
    + inversion H; subst.
      1: {
        rename select (typing _ _ (exp_lvar a) _) into HH.
        forwards (? & ? & ?): typing_inversion_lvar HH.
        congruence.
       }
      inversion select (sub_pre _ _ (typ_ret Targ)); subst.
      applys IHtyping a T1 C1...
    + econstructor...
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
    dependent induction H3...
    econstructor...
  - inversion Typ; subst.
    dependent induction H2...
    clear IHtyping_ctx.
    dependent induction H5...
    + inversion select (sub _ S _); subst.
      1: {
        rename select (typing _ _ (exp_lvar a) _) into HH.
        forwards (? & ? & ?): typing_inversion_lvar HH.
        congruence.
      }
      inversion select (sub_pre _ _ (typ_ret Teff)); subst.
      applys IHtyping C1 T1 a...
    + rename select (Signatures.binds a _ _) into BndA.
      forwards EQ: binds_sig_unique H1 BndA.
      inversion EQ; subst; clear EQ H1.
      econstructor...
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
  (* all is borked below *)
  remember E. generalize dependent Heql.
  rename select (typing _ _ e T) into Typ'.
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
