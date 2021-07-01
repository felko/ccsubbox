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

Lemma fv_le_vs_free_for_cv: forall v,
  fv_le v `c`L `cset_lvars` (free_for_cv v).
Proof.
  intros *.
  dependent induction v; simpl in *; trivial.
  all: lsetdec.
Qed.

Lemma subcapt_is_label_subset : forall E C D,
  ~ `* in` D ->
  E |-sc C <: D ->
  `cset_lvars` C `c`L `cset_lvars` D.
Proof with eauto.
  intros * Notin Hsc.
  dependent induction Hsc.
  - congruence.
  - lsetdec.
  - lsetdec.
  - lsetdec.
  - lsetdec.
  - lsetdec.
  - intros l lIn.
    specialize (H2 l lIn); simpl in H2.
    clear H0 H1 H3.
    dependent induction H2; try congruence.
    + assert (l `in`L {l}L) as HA by lsetdec.
      rewrite <- x1 in HA.
      exfalso; lsetdec.
    + assert (l `in`L {l}L) as HA by lsetdec.
      rewrite <- x in HA.
      assert (l0 = l) by lsetdec; subst; clear HA.
      destruct b0; congruence.
    + assert (l `in`L {l}L) as HA by lsetdec.
      rewrite <- x1 in HA.
      exfalso; lsetdec.
    + assert (l `in`L {l}L) as HA by lsetdec.
      rewrite <- x1 in HA.
      exfalso; lsetdec.
    + eapply (H3 l)...
      lsetdec.
Qed.

Lemma label_absent_from_cv_is_absent_from_fv : forall l T v E Q,
  ~ `* in` (cv T) ->
  ~ l L`in` cv T ->
  value v ->
  E @ Q |-t v ~: T ->
  l `~in`L fv_le v.
Proof with eauto.
  intros * NotUniv Notin Val Typ.
  forwards (U & TypU & SubU): values_have_precise_captures Val Typ.
  assert (fv_le v `c`L `cset_lvars` (free_for_cv v)) by (apply fv_le_vs_free_for_cv).
  assert (`cset_lvars` (free_for_cv v) `c`L `cset_lvars` (cv T)). {
    inversion SubU; subst.
    eapply subcapt_is_label_subset...
  }
  lsetdec.
Qed.

Lemma typing_strengthening_sig_absent_label : forall l S E Q v T,
  E @ [(l, bind_sig S)] ++ Q |-t v ~: T ->
  l `~in`L fv_le v ->
  E @ Q |-t v ~: T.
Proof with eauto.
  intros* Typ Notin.
  dependent induction Typ.
  - constructor...
    inversion H0...
  - econstructor...
    inversion H0...
  - pick fresh x and apply typing_abs.
    + trivial.
    + apply H0.
      notin_solve.
    + eapply H2.
      * notin_solve.
      * easy.
      * simpl in Notin.
        admit.                  (* need a lemma *)
  - simpl in Notin.
    applys typing_app H.
    + eapply IHTyp1.
      * reflexivity.
      * lsetdec.
    + eapply IHTyp2.
      * reflexivity.
      * lsetdec.
  - pick fresh X and apply typing_tabs.
    + trivial.
    + apply H0.
      notin_solve.
    + eapply H2.
      * notin_solve.
      * reflexivity.
      * simpl in Notin.
        admit.                  (* need a lemma *)
  - simpl in Notin.
    applys typing_tapp H.
    eapply IHTyp.
    + reflexivity.
    + lsetdec.
    + eauto.
  - applys typing_sub H.
    eapply IHTyp.
    + reflexivity.
    + lsetdec.
  - simpl in Notin.
    pick fresh x and apply typing_handle.
    2: { trivial. }
    eapply H0.
    + notin_solve.
    + reflexivity.
    + admit.                    (* needs a lemma *)
  - simpl in Notin.
    eapply typing_do_ret.
    + eapply IHTyp1.
      * reflexivity.
      * lsetdec.
    + eapply IHTyp2.
      * reflexivity.
      * lsetdec.
  - inversion H0; subst.
    simpl in Notin.
    eapply typing_lvar...
    assert (l <> l0) by lsetdec.
    Signatures.binds_cases H1...
Admitted.

Lemma typing_ctx_calculates_bound_capabilities : forall E Q k T,
  E @ Q |-ctx k ~: T ->
  Q = bound_capabilities k.
Proof with eauto.
  intros * TypCtx.
  dependent induction TypCtx; simpl; Signatures.simpl_env...
  - rewrite IHTypCtx.
    repeat f_equal.
Qed.

Lemma notin_fv_ld_is_notin_fv_lt_of_bind_sig : forall l1 l2 Q T,
  l1 `~in`L fv_ld Q ->
  Signatures.binds l2 (bind_sig T) Q ->
  l1 `~in`L fv_lt T.
Proof with eauto.
  intros * Notin Bnd.
  dependent induction Q.
  - inversion Bnd.
  - destruct a as (l3 & B).
    inversion Bnd.
    destruct (l2 ==== l3).
    + inversion H0; subst.
      simpl in Notin.
      lsetdec.
    + apply IHQ...
      simpl in Notin; destruct B.
      lsetdec.
Qed.

Lemma extract_nontopness : forall l C R Q E k T,
  Signatures.binds l (bind_sig (typ_capt C (typ_ret R))) Q ->
  E @ Q |-ctx k ~: T ->
  ~ `* in` (cv R).
Proof with eauto.
  intros * Bnd TypCtx.
  dependent induction TypCtx...
  - inversion Bnd.
  - destruct (l ==== l0).
    + assert (Signatures.binds l0 (bind_sig (typ_capt {*} (typ_ret T)))
                               ([(l0, bind_sig (typ_capt {*} (typ_ret T)))] ++ Q)) as Bnd' by eauto.
      subst.
      forwards EQ: binds_sig_unique Bnd Bnd'.
      inversion EQ; subst; clear EQ...
    + Signatures.binds_cases Bnd...
Qed.

Ltac hint := eauto using typing_ctx_sub, wf_cset_set_weakening.


Lemma preservation : forall e e',
  typing_state e ->
  step e e' ->
  typing_state e'.
Proof with hint.
  intros * TypState Step.
  inversion Step; subst; inversion TypState; subst.
  all: try rename select (typing _ _ _ T) into Typ.
  all: try rename select (typing _ _ _ T0) into Typ.
  all: try rename select (typing_ctx _ _ _ T) into TypCtx.
  all: try rename select (typing_ctx _ _ _ T0) into TypCtx.

  Local Ltac solve_it_ctx := dependent induction TypCtx; hint; repeat (econstructor; hint).
  Local Ltac solve_it_typ := dependent induction Typ; hint; repeat (econstructor; hint).

  - Case "step-app".
    solve_it_typ.
  - Case "step-tapp".
    solve_it_typ.
  - Case "step-fun->arg".
    solve_it_ctx.
  - Case "step-throw".
    solve_it_typ.
  - Case "step-handler->arg".
    solve_it_ctx.
  - Case "step-app".
    assert (no_type_bindings E) by (eauto using typing_ctx_free_tvar).
    dependent induction TypCtx...

    rename select (typing _ _ (exp_abs _ _) _) into TypAbs.
    forwards (Sub & S2 & L & TypingX): typing_inv_abs TypAbs T1 T2 C...
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
    + inversion WfTypV. (* wf_cset C *)
      rename select (wf_cset E _ C') into WfC.
      applys wf_cset_set_weakening WfC...
  - Case "step-tapp".
    dependent induction TypCtx...
    econstructor...

    rename select (typing _ _ (exp_tabs _ _) _) into TypTabs.
    forwards (Sub & S2 & L & TypingX): typing_inv_tabs TypTabs T0 T3.
    1: { eauto using sub_reflexivity. }

    pick fresh x.
    destruct (TypingX x) as [Typ' SubS2]...
    rewrite (subst_te_intro x)...
    rewrite (subst_tt_intro x)...
    rewrite_env (map (subst_tb x T2) empty ++ E).
    apply (typing_through_subst_te T0)...
  - assert (no_type_bindings E) by (eauto using typing_ctx_free_tvar).
    Notation "#H" := CCsub_Definitions.H.
    dependent induction Typ...
    unfold Signatures.singleton_list.
    pick fresh x.
    rename H2 into HH.
    rename HH into HH'.
    forwards HH: HH' x. 1: { notin_solve. }
    note (wf_env ((x, bind_typ (typ_capt {*} (typ_ret T))) :: E)).
    note (wf_typ_in E (typ_capt {*} (typ_ret T))) as WfTypRet.
    rename select (wf_pretyp E _ _ (typ_ret T)) into WfT.
    rewrite_env (empty ++ [(x, bind_typ (typ_capt {*} (typ_ret T)))] ++ E) in HH.
    replace Q with (nil ++ Q) in HH...
    apply (typing_weakening_sig [(l, bind_sig (typ_capt {*} (typ_ret T)))]) in HH.
    2: {
      Signatures.simpl_env.
      econstructor; simpl.
      admit.
      (* here we need to know that T is wellformed in the empty environment. *)
      admit.
      admit.
    }
    rename HH into HH''.
    forwards HH: typing_narrowing_typ (`cset_lvar` l) (typ_ret T) HH''. 1: {
      constructor.
      - apply subcapt_universal...
      - eapply sub_pre_reflexivity...
    }
    apply typing_through_subst_ee with (u := (exp_lvar l)) in HH.
    2: { eauto. }
    2: {
      simpl free_for_cv.
      eapply typing_lvar...
      admit.                  (* wf_sig, needs more preconditions *)
    }
    simpl in HH; simpl_env in HH; unfold Signatures.singleton_list in HH.
    rewrite <- subst_ee_intro in HH by notin_solve.
    rewrite <- subst_ct_fresh in HH. 2: {
      (* inversion WfTypRet. *)
      assert (x `~in`A dom E). {
        assert (wf_env ([(x, bind_typ (typ_capt {*} (typ_ret T)))] ++ E)) as HA by eauto.
        inversion HA; trivial.
      }
      enough (x `~in`A (fv_tt T `u`A fv_ct T)) by notin_solve.
      applys notin_fv_wf_pretyp WfT; trivial.
    }

    eapply typ_step...
    + eapply typing_ctx_reset...
      * destruct (`cset_uvar` (cv T)) eqn:EQ...
        enough (E |-sc {*} <: cv T) by contradiction.
        constructor.
        2: exact EQ.
        assert (wf_typ_in E T) by eauto.
        eapply cv_wf...
      * forwards EQ: typing_ctx_calculates_bound_capabilities TypCtx.
        rewrite EQ.
        lsetdec.
  - dependent induction TypCtx...
    clear IHTypCtx.
    dependent induction H0.
    + inversion H; subst.
      1: {
        rename select (typing _ _ (exp_lvar l) _) into HH.
        forwards (? & ? & ?): typing_inversion_lvar HH.
        congruence.
       }
      inversion select (sub_pre _ _ (typ_ret Targ)); subst.
      applys IHtyping l T1 C1...
    + econstructor...
  - solve_it_ctx.
  - solve_it_ctx.
  - solve_it_ctx.
  - solve_it_ctx.
  - solve_it_ctx.
  - dependent induction TypCtx...
    rename select (typing _ _ (exp_lvar l1) _) into TypLvar.
    clear IHTypCtx.
    dependent induction TypLvar.
    1: {
      inversion select (sub _ S _); subst.
      1: {
        rename select (typing _ _ (exp_lvar l1) _) into HH.
        forwards (? & ? & ?): typing_inversion_lvar HH.
        congruence.
      }
      inversion select (sub_pre _ _ (typ_ret R)); subst.
      applys IHTypLvar T l2 T1...
    }
    assert (Signatures.binds l1 (bind_sig (typ_capt C0 (typ_ret R))) Q) as BndL1. {
      rename select (Signatures.binds l1 _ _) into HA.
      Signatures.binds_cases HA...
    }
    econstructor...
    + applys typing_strengthening_sig_absent_label H4.
      applys label_absent_from_cv_is_absent_from_fv H4; trivial.
      * applys extract_nontopness BndL1...
      * assert (l2 `~in`L fv_lt (typ_capt C0 (typ_ret R))). {
          applys notin_fv_ld_is_notin_fv_lt_of_bind_sig BndL1...
        }
        simpl in *.
        destruct R; simpl in *; lsetdec.
    + eapply typing_lvar...
      inversion select (wf_sig _)...
  - dependent induction TypCtx...
    clear IHTypCtx.

    rename select (typing _ _ (exp_lvar l) _) into TypLvar.
    dependent induction TypLvar.
    + inversion select (sub _ S _); subst.
      1: {
        rename select (typing _ _ (exp_lvar l) _) into HH.
        forwards (? & ? & ?): typing_inversion_lvar HH.
        congruence.
      }
      inversion select (sub_pre _ _ (typ_ret R)); subst.
      applys IHTypLvar T l TypCtx T1...
    + rename select (Signatures.binds _ _ _) into BndA.
      assert (Signatures.binds l (bind_sig (typ_capt {*} (typ_ret T)))
                               ([(l, bind_sig (typ_capt {*} (typ_ret T)))] ++ Q)) as BndA' by eauto.
      forwards EQ: binds_sig_unique BndA BndA'.
      inversion EQ; subst; clear EQ BndA'.
      forwards: typing_strengthening_sig_absent_label H3.
      1: {
        applys label_absent_from_cv_is_absent_from_fv H3...
      }
      econstructor...
Admitted.

(* ********************************************************************** *)
(** * #<a name="progress"></a># Progress *)

(* ********************************************************************** *)
(** ** Progress (16) *)

Lemma canonical_form_lvar : forall e Q C R,
  value e ->
  empty @ Q |-t e ~: (typ_capt C (typ_ret R)) ->
  exists l, e = exp_lvar l.
Proof with eauto.
  intros * Val Typ.
  dependent induction Typ; try solve [inversion Val]...
  inversion select (sub _ S _); subst.
  1: {
    inversion select (binds _ _ empty).
  }
  inversion select (sub_pre _ _ (typ_ret R)); subst.
  eapply IHTyp...
Qed.

Lemma progress_value_step : forall v k,
  value v ->
  typing_state 〈 v | k 〉 ->
  done 〈 v | k 〉 \/ exists s2, 〈 v | k 〉 --> s2.
Proof with eauto.
  intros * Val Typ.
  inversion Typ; subst.
  replace E with empty in * by admit. (* definitions/lemma need adjusting *)
  dependent induction H1.
  - left; constructor...
  - right...
  - forwards (V & e1 & ?): canonical_form_abs H0...
    subst.
    right...
  - forwards (V & e1 & ?): canonical_form_tabs H2...
    subst.
    right...
  - admit.                      (* missing constructor *)
  - forwards (? & ?): canonical_form_lvar H2...
  - forwards (? & ?): canonical_form_lvar H0...
    subst.
    right...
  - eauto.
Admitted.

Lemma progress_step : forall s1,
  typing_state s1 ->
  done s1 \/ exists s2, s1 --> s2.
Proof with eauto.
  intros * Typ.
  inversion Typ; subst.
  2: {
    dependent induction H...
    - dependent induction H1...
      2: {
        inversion H1.
      }
      inversion select (sub _ S _); subst.
      1: {
        rename select (typing _ _ (exp_lvar l) _) into HH.
        forwards (? & ? & ?): typing_inversion_lvar HH.
        congruence.
      }
      inversion select (sub_pre _ _ (typ_ret R)); subst.
      applys IHtyping l C1 T1...
    - forwards IH: IHtyping_ctx H1 H2...
      1: { econstructor... }
      destruct IH as [IH|IH].
      1: { inversion IH. }
      destruct IH as (S2 & IH).
      right.
      eexists.
      admit.                    (* missing constructor *)
    - right.
      destruct (l0 ==== l); subst.
      + eexists.
        apply step_unwind_match_frame.
      + eexists...
  }
  (* all is borked below *)
  replace E with empty in * by admit. (* definitions need to be tweaked *)
  dependent induction H0.
  - inversion select (binds _ _ _).
  - inversion select (binds _ _ _).
  - assert (value (exp_abs V e1)). {
      assert (empty @ Q |-t (exp_abs V e1) ~: (typ_capt (free_for_cv e1) (typ_arrow V T1))). {
        econstructor...
      }
      eauto.
    }
    eapply progress_value_step...
  - right...
  - assert (value (exp_tabs V e1)). {
      assert (empty @ Q |-t (exp_tabs V e1) ~: (typ_capt (free_for_cv e1) (typ_all V T1))). {
        econstructor...
      }
      eauto.
    }
    eapply progress_value_step...
  - right...
  - apply IHtyping...
    applys typing_ctx_sub H1...
  - pick fresh label l for (Signatures.dom (bound_capabilities k)
                                           `u`L fv_ld (bound_capabilities k)
                                           `u`L `cset_lvars` (cv T1)).
    right; eexists.
    eapply step_try with (l := l).
    all: lsetdec.
  - right...
  - assert (value (exp_lvar l)) by eauto.
    eapply progress_value_step...
Admitted.
