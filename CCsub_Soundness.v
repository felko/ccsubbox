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

Lemma foo : forall l T v E Q,
  ~ l L`in` cv T ->
  value v ->
  E @ Q |-t v ~: T ->
  l `~in`L fv_le v.
Proof with eauto.
  intros * Notin Val Typ.
  forwards (U & TypU & SubU): values_have_precise_captures Val Typ.
  assert (fv_le v `c`L `cset_lvars` (free_for_cv v)) by admit.
  assert (`cset_lvars` (free_for_cv v) `c`L `cset_lvars` (cv T)) by admit.
  lsetdec.
Admitted.

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

Lemma preservation : forall e e',
  typing_state e ->
  step e e' ->
  typing_state e'.
Proof with eauto using typing_ctx_sub, wf_cset_set_weakening.
  intros * TypState Step.
  inversion Step; subst; inversion TypState; subst.
  all: try rename select (typing _ _ _ T) into Typ.
  all: try rename select (typing _ _ _ T0) into Typ.
  all: try rename select (typing_ctx _ _ _ T) into TypCtx.
  all: try rename select (typing_ctx _ _ _ T0) into TypCtx.
  - Case "step-app".
    dependent induction Typ...
    econstructor...
    econstructor...
  - Case "step-tapp".
    dependent induction Typ...
    econstructor...
    econstructor...
  - Case "step-fun->arg".
    dependent induction TypCtx...
    econstructor...
    econstructor...
  - Case "step-throw".
    dependent induction Typ...
    econstructor...
    econstructor...
  - Case "step-handler->arg".
    dependent induction TypCtx...
    econstructor...
    econstructor...
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
    + (* wf_cset C *)
      assert (wf_cset_in E C') as WfC by admit; simpl.
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
    pick fresh x for L.
    rename H2 into HH.
    specialize (HH x Fr).
    assert (wf_pretyp_in E (typ_ret T)) by admit. (* come on *)
    rewrite_env (empty ++ [(x, bind_typ (typ_capt {*} (typ_ret T)))] ++ E) in HH.
    replace Q with ([(l, bind_sig (typ_capt {*} (typ_ret T)))] ++ Q) in HH by admit. (* needs a simple lemma *)
    rename HH into HH'.
    forwards HH: typing_narrowing_typ (`cset_lvar` l) (typ_ret T) HH'. 1: {
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
    simpl_env in HH; unfold Signatures.singleton_list in HH.
    eapply typ_step.
    + eapply typing_ctx_reset...
    + admit.
    (* eapply typ_step. *)
  - dependent induction TypCtx...
    clear IHTypCtx.
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
  - dependent induction TypCtx...
    econstructor...
  - dependent induction TypCtx...
    econstructor...
  - dependent induction TypCtx...
    econstructor...
  - dependent induction TypCtx...
    econstructor...
  - dependent induction TypCtx...
    rename select (typing _ _ (exp_lvar a1) _) into TypLvar.
    clear IHTypCtx.
    dependent induction TypLvar...
    admit.
    assert (Signatures.binds a1 (bind_sig (typ_capt C1 (typ_ret R))) Q). {
      Signatures.binds_cases H1...
    }
    assert (a2 `~in`L fv_lt R). {
     admit.
    }
    econstructor...
    + admit.                    (* by a lemma *)
    + eapply typing_lvar...
      inversion H0...
  - dependent induction TypCtx...
    clear IHTypCtx.

    (* rewrite <- subst_ct_fresh in HH. 2: { *)
    (*   assert (wf_typ_in E T) as WfT by admit. (* from regularity of typing we're doing induction on *) *)
    (*   assert (x `~in`A dom E). { *)
    (*     assert (wf_env ([(x, bind_typ (typ_capt {*} (typ_ret T)))] ++ E)) as HA by eauto. *)
    (*     inversion HA; trivial. *)
    (*   } *)
    (*   enough (x `~in`A (fv_tt T `u`A fv_ct T)) by notin_solve. *)
    (*   applys notin_fv_wf_typ WfT; trivial. *)
    (* } *)

    (* assert (l `~in`L fv_lt T). { *)

    (* } *)

    rename select (typing _ _ (exp_lvar a) _) into TypLvar.
    dependent induction TypLvar...
    + inversion select (sub _ S _); subst.
      1: {
        rename select (typing _ _ (exp_lvar a) _) into HH.
        forwards (? & ? & ?): typing_inversion_lvar HH.
        congruence.
      }
      inversion select (sub_pre _ _ (typ_ret R)); subst.
      applys IHTypLvar C1 T1 a...
    + assert (Signatures.binds a (bind_sig (typ_capt C0 (typ_ret T)))
                               ([(a, bind_sig (typ_capt C0 (typ_ret T)))] ++ Q)) as BndA by eauto.
      forwards EQ: binds_sig_unique BndA H1.
      inversion EQ; subst; clear EQ H1.
      assert (a `~in`L fv_lt R) by admit. (* from H0 *)
      econstructor...
      admit.                    (* by lemma *)
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
    - forwards: IHtyping_ctx H1 H2.
      1: { econstructor... }
      destruct H3.
      1: { inversion H3. }
      destruct H3 as (S2 & H3).
      right.
      eexists.
      admit.                    (* missing constructor *)
    -
  }
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
