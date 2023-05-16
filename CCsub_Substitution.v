Require Import Coq.Program.Equality.
Require Import TaktikZ.
Require Import LibTactics.
Require Export CCsub_Hints.
Require Import CCsub_Subcapt.
Require Import CCsub_Subtyping.
Require Import CCsub_Typing.

Set Nested Proofs Allowed.

(************************************************************************ *)
(** ** Properties of values *)

Lemma capture_prediction : forall Γ v C R,
  value v ->
  Γ ⊢ v : (C # R) ->
  Γ ⊢ₛ (exp_cv v) <: C.
Proof with subst; simpl; eauto.
  intros * Value Typ.
  forwards (WfEnv & Expr & WfTyp): typing_regular Typ.
  eremember (C # R) as T.
  assert (Γ ⊢ T <: (C # R)) by (rewrite HeqT; apply sub_reflexivity; eauto* ).
  clear HeqT.
  generalize dependent R.
  generalize dependent C.
  induction Typ; intros C0 R0 Sub; cbn [exp_cv]; try solve [ inversion Value ].
  - inversion WfTyp; subst.
    inversion Sub...
  - inversion WfTyp; subst.
    inversion Sub...
  - apply subcapt_empty.
    enough (WfC0R0 : Γ ⊢ (C0 # R0) wf) by (inversion WfC0R0; auto).
    applys sub_regular Sub.
  - forwards: IHTyp...
    apply (sub_transitivity_type T)...
Qed.

Lemma values_have_precise_captures : forall Γ v C R,
  value v ->
  Γ ⊢ v : (C # R) ->
  exists U, Γ ⊢ v : (exp_cv v # U) /\
            Γ ⊢ (exp_cv v # U) <: (C # R).
Proof with simpl; eauto*.
  intros * Value Typ.
  assert (Γ ⊢ₛ (exp_cv v) wf) by eauto using typing_cv.
  assert (Γ ⊢ wf) by applys typing_regular Typ.
  induction Typ; try solve [inversion Value; subst].
  - Case "typing_abs".
    exists (∀ (C0 # R0) T1).
    split...
    eapply sub_reflexivity...
    constructor...
    + econstructor...
      intros x xIn.
      rename select (forall x : atom, x ∉ L -> _ ⊢ open_ve _ _ _ : _) into IH.
      forwards Typ: (IH x xIn).
      applys typing_regular Typ.
    + econstructor.
      1: eapply type_from_wf_typ...
      intros x xIn.
      rename select (forall x : atom, x ∉ L -> _ ⊢ open_ve _ _ _ : _) into IH.
      forwards Typ: (IH x xIn).
      eapply type_from_wf_typ...
      applys typing_regular Typ.
  - Case "typing_tabs".
    exists (∀ [V] T1).
    split...
    eapply sub_reflexivity...
    constructor...
    + econstructor...
      intros x xIn.
      rename select (forall x : atom, x ∉ L -> _ ⊢ open_te _ _ : _) into IH.
      forwards Typ: (IH x xIn).
      applys typing_regular Typ.
    + econstructor...
      intros x xIn.
      rename select (forall x : atom, x ∉ L -> _ ⊢ open_te _ _ : _) into IH.
      forwards Typ: (IH x xIn).
      eapply type_from_wf_typ...
      applys typing_regular Typ.
  - Case "typing_box".
    exists (□ (C0 # R0)).
    split...
    apply sub_reflexivity...
    apply wf_typ_capt...
    + apply wf_typ_box.
      applys typing_regular Typ.
    + apply type_box.
      eapply type_from_wf_typ.
      applys typing_regular Typ.
  - Case "typing_sub".
    forwards (U & HtypU & HsubS): IHTyp...
    exists U; eauto using (sub_transitivity_type S).
Qed.

(************************************************************************ *)
(** ** Other helpers *)

Lemma subst_cset_in_exp_cv : forall x C e,
    x ∈ `cset_fvars` (exp_cv e) ->
    subst_cset x C (exp_cv e) = C `u` (exp_cv e A`\` x).
Proof with eauto*.
  intros.
  unfold subst_cset.
  destruct_set_mem x (`cset_fvars` (exp_cv e)).
  - reflexivity.
  - destruct (exp_cv e) eqn:?.
    csetdec.
Qed.

Lemma subst_vv_notin_var_cv : forall u x v,
  x ∉ `cset_fvars` (var_cv v) ->
  var_cv v = var_cv (subst_vv x u v).
Proof with eauto*.
  intros.
  destruct v...
  simpl in *.
  destruct (a == x); subst...
  clear - H; fsetdec.
Qed.

Lemma subst_ve_notin_exp_cv : forall u x C e,
  x ∉ `cset_fvars` (exp_cv e) ->
  exp_cv e = exp_cv (subst_ve x u C e).
Proof with eauto using subst_vv_notin_var_cv.
  intros * Hin.
  induction e; simpl in *...
  - apply notin_cset_fvars_distributive_over_cset_union in Hin as (? & ?)...
    f_equal...
  - apply notin_cset_fvars_distributive_over_cset_union in Hin as (? & ?)...
    f_equal...
  - apply notin_cset_fvars_distributive_over_cset_union in Hin as (? & ?)...
    eremember (subst_cset x (`cset_fvar` u) c) as c'.
    f_equal...
    unfold subst_cset in *.
    destruct_set_mem x (`cset_fvars` c).
    + exfalso; apply (H xIn).
    + subst; reflexivity. 
Qed.

Lemma subst_te_fresh_exp_cv : forall Z R e,
  exp_cv e = exp_cv (subst_te Z R e).
Proof with eauto*.
  intros.
  induction e; simpl in *...
Qed.

Lemma subst_trivia2_var : forall x v (u : atom),
  x ∈ `cset_fvars` (var_cv v) ->
  var_cv u `u` (var_cv v A`\` x) = var_cv (subst_vv x u v).
Proof with eauto*.
  intros.
  destruct v; simpl in *.
  - destruct (a == x); csetdec.
  - csetdec.
Qed.   

(* x in (fv e) ->
  (fv u) union (fv e remove x) = fv (e[x !-> u][x !-> fv u])
*)

(*
Lemma subst_trivia2 : forall x e (u : atom),
  AtomSet.F.In x (`cset_fvars` (free_for_cv e)) ->
  (cset_union (free_for_cv u) ((free_for_cv e) A`\` x)) =
        (free_for_cv (subst_ve x u (free_for_cv u) e)).
Proof with eauto using cv_free_never_universal, subst_trivia2_var.
  intros * Hin.
  induction e; simpl in *...
  - destruct (free_for_cv_var v) eqn:?; destruct (free_for_cv_var v0) eqn:?;
      simpl in *; try fsetdec.
    + (* there are three cases... we also need to know that it is NOT in the other sets... then we might be able to prove it... *)
      rewrite (AtomSetFacts.mem_iff) in Hin.
      rewrite (AtomSetFacts.union_b) in Hin.
      destruct (AtomSet.F.mem x t) eqn:InT;
        destruct (AtomSet.F.mem x t1) eqn:InT2;
        rewrite_set_facts_in InT;
        rewrite_set_facts_in InT2;
        inversion Hin; subst...
      * apply cset_concrete_union.
         rewrite <- IHe1...
        rewrite <- IHe2...
        cbn [cset_union].
        csetdec.
      * rewrite <- IHe1...
        rewrite <- (subst_contratrivia2 u x _ e2)...
        2: rewrite Heqc0; assumption.
        cbn [cset_union].
        rewrite Heqc0.
        csetdec.
      * rewrite <- IHe2...
        rewrite <- (subst_contratrivia2 u x _ e1)...
        2: rewrite Heqc; assumption.
        rewrite Heqc.
        cbn [cset_union].
        csetdec.
  - destruct (free_for_cv e1) eqn:?; destruct (free_for_cv e2) eqn:?; destruct (free_for_cv u) eqn:?;
    simpl in *; try fsetdec.
    + (* there are three cases... we also need to know that it is NOT in the other sets... then we might be able to prove it... *)
      rewrite (AtomSetFacts.mem_iff) in Hin.
      rewrite (AtomSetFacts.union_b) in Hin.
      destruct (AtomSet.F.mem x t) eqn:InT;
        destruct (AtomSet.F.mem x t2) eqn:InT2;
        rewrite_set_facts_in InT;
        rewrite_set_facts_in InT2;
        inversion Hin; subst...
      * rewrite <- IHe1...
        rewrite <- IHe2...
        cbn [cset_union].
        csetdec.
      * rewrite <- IHe1...
        rewrite <- (subst_contratrivia2 u x _ e2)...
        2: rewrite Heqc0; assumption.
        cbn [cset_union].
        rewrite Heqc0.
        csetdec.
      * rewrite <- IHe2...
        rewrite <- (subst_contratrivia2 u x _ e1)...
        2: rewrite Heqc; assumption.
        rewrite Heqc.
        cbn [cset_union].
        csetdec.
  - fsetdec.
Qed.
*)

Lemma fvar_open_inversion : forall (x : atom) e y C,
  exp_var x = open_ve e y C ->
  e = x \/ exists (n : nat), e = n.
Proof with eauto*.
  intros. induction e;
    try solve [exfalso; cbv [open_ve open_ve_rec] in H; fold open_ve_rec in H; discriminate].
  destruct v.
  - left...
  - right. exists n...
Qed.

(* REVIEW: where is this needed? *)
(*
Lemma subst_ct_monotonicity : forall Γ x C D T,
  Γ ⊢ wf ->
  type T ->
  Γ ⊢ T wf ->
  Γ ⊢ₛ C <: D ->
  ((x ∉ dom Γ -> Γ ⊢ₛ C wf -> Γ ⊢ₛ D wf -> Γ ⊢ (subst_ct x C T) <: (subst_ct x D T)) /\
   (x ∉ dom Γ -> Γ ⊢ₛ C wf -> Γ ⊢ₛ D wf -> Γ ⊢ (subst_ct x D T) <: (subst_ct x C T))).
Proof with simpl_env; eauto; fold subst_ct.
  intros * WfEnv TypeT WfT Subcapt.
  induction TypeT; inversion WfT; subst; split; intros xNotIn WfC WfD...
  (* assert (type T) as Typ by auto. *)
  induction Typ; inversion HwfT; subst.
  - simpl. constructor...
  - destruct (subst_cpt_monotonicity E Ap Am x C D P HwfE H0 SubAp SubAm H7 Hsc).
    split; intros; constructor...
    + eapply subst_cset_across_subcapt...
    + replace (subst_cset x D C0) with C0.
      replace (subst_cset x C C0) with C0.
      apply subcapt_reflexivity with (A := Ap)...
      apply subst_cset_fresh. inversion H6...
      apply subst_cset_fresh. inversion H6...
------
  intros * HwfE Typ SubAp SubAm HwfT Hsc.
  (* assert (pretype T) as Typ by auto. *)
  induction Typ; inversion HwfT; subst.
  - simpl. constructor...
  - (* specializing the hypothesis to the argument type of arrow *)
    destruct (subst_ct_monotonicity E Am Ap x C D T1 HwfE H SubAm SubAp H6 Hsc).
    split; intros ? WfC WfD.
    + specialize (H2 H3 WfC WfD).
      pick fresh y and apply sub_arrow; fold subst_ct...
      {
        rewrite subst_ct_open_ct_var...
        specialize (H7 y ltac:(notin_solve)).
        rewrite_nil_concat.
        eapply wf_typ_ignores_typ_bindings.
        eapply wf_typ_set_weakening.
        eapply wf_typ_preserved_by_subst_wf_cset in H7.
        simpl_env.
        apply (proj1 H7).
        all : trivial...
        rewrite_nil_concat.
        eapply wf_cset_weakening; [ apply WfD | simpl_env; auto .. ].
        all: clear - SubAp SubAm; fsetdec.
      }
      {
        rewrite subst_ct_open_ct_var...
        specialize (H7 y ltac:(notin_solve)).
        rewrite_nil_concat.
        eapply wf_typ_ignores_typ_bindings.
        eapply wf_typ_set_weakening.
        eapply wf_typ_preserved_by_subst_wf_cset in H7.
        simpl_env.
        apply (proj1 H7).
        all : trivial...
        rewrite_nil_concat.
        eapply wf_cset_weakening; [ apply WfC | simpl_env; auto .. ].
        all: clear - SubAp SubAm; fsetdec.
      }
      rewrite subst_ct_open_ct_var...
      rewrite subst_ct_open_ct_var...
      (* we cannot call subst_ct_monotonicity on anything that is larger than wf_typ.... *)
      assert (y `notin` L) as NotIn by notin_solve.
      specialize (H0 y NotIn).
      unshelve epose proof (subst_ct_monotonicity
        ([(y, bind_typ (subst_ct x D T1))] ++ E)
        (Ap `union` singleton y)
        Am x C D (open_ct T2 (`cset_fvar` y)) _ H0 _ _ _).
      * econstructor...
      (* we need to help fsetdec here a little *)
      * clear Fr; simpl; fsetdec.
      * clear Fr; simpl; fsetdec.
      * rewrite_env (empty ++ [(y, bind_typ (subst_ct x D T1))] ++ E).
        eapply wf_typ_ignores_typ_bindings...
      * destruct H4.
        -- rewrite_env (empty ++ [(y, bind_typ (subst_ct x D T1))] ++ E).
           apply subcapt_weakening...
        -- apply H4...
           ++ rewrite_nil_concat.
              applys wf_cset_ignores_typ_bindings T1.
              eapply wf_cset_weakening ; [ apply WfC | simpl_env; auto .. ].
              clear; fsetdec.
           ++ rewrite_nil_concat.
              applys wf_cset_ignores_typ_bindings T1.
              eapply wf_cset_weakening ; [ apply WfD | simpl_env; auto .. ].
              clear; fsetdec.
    + specialize (H1 H3 WfC WfD).
      pick fresh y and apply sub_arrow; fold subst_ct...
      {
        rewrite subst_ct_open_ct_var...
        specialize (H7 y ltac:(notin_solve)).
        rewrite_nil_concat.
        eapply wf_typ_ignores_typ_bindings.
        eapply wf_typ_set_weakening.
        eapply wf_typ_preserved_by_subst_wf_cset in H7.
        simpl_env.
        apply (proj2 H7).
        all : trivial...
        rewrite_nil_concat.
        eapply wf_cset_weakening; [ apply WfC | simpl_env; auto .. ].
        all: clear - SubAp SubAm; fsetdec.
      }
      {
        rewrite subst_ct_open_ct_var...
        specialize (H7 y ltac:(notin_solve)).
        rewrite_nil_concat.
        eapply wf_typ_ignores_typ_bindings.
        eapply wf_typ_set_weakening.
        eapply wf_typ_preserved_by_subst_wf_cset in H7.
        simpl_env.
        apply (proj2 H7).
        all : trivial...
        rewrite_nil_concat.
        eapply wf_cset_weakening; [ apply WfD | simpl_env; auto .. ].
        all: clear - SubAp SubAm; fsetdec.
      }
      rewrite subst_ct_open_ct_var...
      rewrite subst_ct_open_ct_var...
      (* we cannot call subst_ct_monotonicity on anything that is larger than wf_typ.... *)
      assert (y `notin` L) as NotIn by notin_solve.
      specialize (H0 y NotIn).
      unshelve epose proof (subst_ct_monotonicity
        ([(y, bind_typ (subst_ct x C T1))] ++ E)
        (Ap `union` singleton y)
        Am x C D (open_ct T2 (`cset_fvar` y)) _ H0 _ _ _).
      * econstructor...
      (* we need to help fsetdec here a little *)
      * clear Fr; simpl; fsetdec.
      * clear Fr; simpl; fsetdec.
      * rewrite_env (empty ++ [(y, bind_typ (subst_ct x C T1))] ++ E).
        eapply wf_typ_ignores_typ_bindings...
      * destruct H4.
        -- rewrite_env (empty ++ [(y, bind_typ (subst_ct x C T1))] ++ E).
           apply subcapt_weakening...
        -- apply H5...
           ++ rewrite_nil_concat.
              applys wf_cset_ignores_typ_bindings T1.
              eapply wf_cset_weakening ; [ apply WfC | simpl_env; auto .. ].
              clear; fsetdec.
           ++ rewrite_nil_concat.
              applys wf_cset_ignores_typ_bindings T1.
              eapply wf_cset_weakening ; [ apply WfD | simpl_env; auto .. ].
              clear; fsetdec.
  - (* specializing the hypothesis to the argument type of arrow *)
    destruct (subst_ct_monotonicity E Am Ap x C D T1 HwfE H SubAm SubAp H6 Hsc).
    split; intros ? WfC WfD.
    + specialize (H2 H3 WfC WfD).
      pick fresh y and apply sub_all; fold subst_ct...
      { rewrite subst_ct_open_tt_var...
        specialize (H7 y ltac:(notin_solve)).
        rewrite_nil_concat.
        apply wf_typ_ignores_sub_bindings with (T1 := T1)...
        eapply wf_typ_set_weakening.
        eapply wf_typ_preserved_by_subst_wf_cset in H7.
        simpl_env.
        apply (proj1 H7).
        all : trivial...
        rewrite_nil_concat.
        eapply wf_cset_weakening; [ apply WfD | simpl_env; auto .. ].
        all: clear - SubAp SubAm; fsetdec.
      }
      { rewrite subst_ct_open_tt_var...
        specialize (H7 y ltac:(notin_solve)).
        rewrite_nil_concat.
        apply wf_typ_ignores_sub_bindings with (T1 := T1)...
        eapply wf_typ_set_weakening.
        eapply wf_typ_preserved_by_subst_wf_cset in H7.
        simpl_env.
        apply (proj1 H7).
        all : trivial...
        rewrite_nil_concat.
        eapply wf_cset_weakening; [ apply WfC | simpl_env; auto .. ].
        all: clear - SubAp SubAm; fsetdec.
      }
      rewrite subst_ct_open_tt_var...
      rewrite subst_ct_open_tt_var...
      (* we cannot call subst_ct_monotonicity on anything that is larger than wf_typ.... *)
      assert (y `notin` L) as NotIn by notin_solve.
      specialize (H0 y NotIn).
      unshelve epose proof (subst_ct_monotonicity
        ([(y, bind_sub (subst_ct x D T1))] ++ E)
        (Ap `u`A {y}A) (Am `u`A {y}A)
        x C D (open_tt T2 y) _ H0 _ _ _).
      * econstructor...
      (* we need to help fsetdec here a little *)
      * clear Fr; simpl; fsetdec.
      * clear Fr; simpl; fsetdec.
      * assert (y `notin` L0) by notin_solve.
        rewrite_env (empty ++ [(y, bind_sub (subst_ct x D T1))] ++ E).
        eapply wf_typ_ignores_sub_bindings with (T1 := T1)...
      * destruct H4.
        -- rewrite_env (empty ++ [(y, bind_sub (subst_ct x D T1))] ++ E).
           apply subcapt_weakening...
        -- apply H4...
           ++ rewrite_nil_concat.
              applys wf_cset_ignores_sub_bindings T1.
              eapply wf_cset_weakening ; [ apply WfC | simpl_env; auto .. ].
              clear; fsetdec.
           ++ rewrite_nil_concat.
              applys wf_cset_ignores_sub_bindings T1.
              eapply wf_cset_weakening ; [ apply WfD | simpl_env; auto .. ].
              clear; fsetdec.
    + specialize (H1 H3 WfC WfD).
      pick fresh y and apply sub_all; fold subst_ct...
      { rewrite subst_ct_open_tt_var...
        specialize (H7 y ltac:(notin_solve)).
        rewrite_nil_concat.
        apply wf_typ_ignores_sub_bindings with (T1 := T1)...
        eapply wf_typ_set_weakening.
        eapply wf_typ_preserved_by_subst_wf_cset in H7.
        simpl_env.
        apply (proj2 H7).
        all : trivial...
        rewrite_nil_concat.
        eapply wf_cset_weakening; [ apply WfC | simpl_env; auto .. ].
        all: clear - SubAp SubAm; fsetdec.
      }
      { rewrite subst_ct_open_tt_var...
        specialize (H7 y ltac:(notin_solve)).
        rewrite_nil_concat.
        apply wf_typ_ignores_sub_bindings with (T1 := T1)...
        eapply wf_typ_set_weakening.
        eapply wf_typ_preserved_by_subst_wf_cset in H7.
        simpl_env.
        apply (proj2 H7).
        all : trivial...
        rewrite_nil_concat.
        eapply wf_cset_weakening; [ apply WfD | simpl_env; auto .. ].
        all: clear - SubAp SubAm; fsetdec.
      }
      rewrite subst_ct_open_tt_var...
      rewrite subst_ct_open_tt_var...
      (* we cannot call subst_ct_monotonicity on anything that is larger than wf_typ.... *)
      assert (y `notin` L) as NotIn by notin_solve.
      specialize (H0 y NotIn).
      unshelve epose proof (subst_ct_monotonicity
                              ([(y, bind_sub (subst_ct x C T1))] ++ E)
                              (Ap `u`A {y}A) (Am `u`A {y}A)
                              x C D (open_tt T2 y) _ H0 _ _ _).
      * econstructor...
      (* we need to help fsetdec here a little *)
      * clear Fr; simpl; fsetdec.
      * clear Fr; simpl; fsetdec.
      * rewrite_env (empty ++ [(y, bind_sub (subst_ct x C T1))] ++ E).
        eapply wf_typ_ignores_sub_bindings with (T1 := T1)...
      * destruct H4.
        -- rewrite_env (empty ++ [(y, bind_sub (subst_ct x C T1))] ++ E).
           apply subcapt_weakening...
        -- apply H5...
           ++ rewrite_nil_concat.
              applys wf_cset_ignores_sub_bindings T1.
              eapply wf_cset_weakening ; [ apply WfC | simpl_env; auto .. ].
              clear; fsetdec.
           ++ rewrite_nil_concat.
              applys wf_cset_ignores_sub_bindings T1.
              eapply wf_cset_weakening ; [ apply WfD | simpl_env; auto .. ].
              clear; fsetdec.
Qed.

Lemma plain_subst_ct_monotonicity : forall E Ap Am x C D T,
  wf_env E ->
  type T ->
  Ap `subset` dom E ->
  Am `subset` dom E ->
  wf_typ E Ap Am T ->
  subcapt E C D ->
  x `notin` Am ->
  wf_cset E Ap C ->
  wf_cset E Ap D ->
  sub E (subst_ct x C T) (subst_ct x D T).
Proof with eauto.
  intros.
  eapply (proj1 (subst_ct_monotonicity _ Ap Am _ _ _ _ H H0 H1 H2 H3 H4))...
Qed.
*)

(* ********************************************************************** *)
(** ** Type substitution preserves subtyping (10) *)

Lemma sub_through_subst_tt : forall Q Γ Δ Z S T P,
  (Δ ++ [(Z, bind_sub Q)] ++ Γ) ⊢ S <: T ->
  Γ ⊢ P <: Q ->
  (map (subst_tb Z P) Δ ++ Γ) ⊢ (subst_tt Z P S) <: (subst_tt Z P T).
Proof with simpl_env;
           eauto 4 using wf_typ_subst_tb,
                         wf_env_subst_tb,
                         wf_typ_weaken_head,
                         subst_tt_pure_type,
                         subcapt_through_subst_tt.
  intros * SsubT PsubQ.
  assert (PureQ : pure_type Q).
  { forwards (WfEnv & _ & _): sub_regular SsubT.
    eapply wf_env_tail in WfEnv.
    inversion WfEnv...
  }
  assert (PureP : pure_type P) by (apply (proj2 (sub_pure_type _ _ _ PsubQ) PureQ)).
  dependent induction SsubT.
  - Case "sub_refl_tvar".
    simpl.
    destruct (X == Z); apply sub_reflexivity...
    replace (typ_var X) with (subst_tt Z P X).
    2: simpl; destruct (X == Z); [exfalso; apply (n e) | reflexivity ].
    eapply wf_typ_subst_tb...
  - Case "sub_trans_tvar".
    assert ((Δ ++ [(Z, bind_sub Q)] ++ Γ) ⊢ wf) as WfE by auto.
    apply binding_uniq_from_wf_env in WfE as FrZ.
    simpl.
    destruct (X == Z); subst.
    + SCase "X = Z".
      apply (sub_transitivity_type Q)...
      * rewrite_nil_concat.
        apply sub_weakening...
      * rewrite (subst_tt_fresh Z P Q).
        2: {
          assert (Γ ⊢ Q wf) as HA by auto.
          lets: notin_fv_wf_typ Z Q HA.
          fsetdec.
        }
        binds_get H.
        inversion H1; subst.
        apply (IHSsubT Q)...
    + SCase "X <> Z".
      binds_cases H.
      * assert (binds X (bind_sub U) (map (subst_tb Z P) Δ ++ Γ)) by auto.
        apply (sub_trans_tvar U)...
        rewrite (subst_tt_fresh Z P U).
        2: {
          assert (Γ ⊢ U wf) as HA. {
            eapply wf_typ_from_binds_sub...
          }
          lets: notin_fv_wf_typ Z HA.
          fsetdec.
        }
        apply (IHSsubT Q)...
      * apply (sub_trans_tvar (subst_tt Z P U)); [auto | eapply IHSsubT]...
  - Case "sub_capt".
    simpl; apply sub_capt...
  - Case "sub_top".
    simpl; apply sub_top...
  - Case "sub_arr".
    simpl; pick fresh y and apply sub_arr...
    repeat rewrite subst_tt_open_ct_var...
    rewrite <- concat_assoc.
    replace ([(y, bind_typ (C2 # subst_tt Z P R2))] ++ map (subst_tb Z P) Δ)
       with (map (subst_tb Z P) ([(y, bind_typ (C2 # R2))] ++ Δ))
         by reflexivity.
    eapply H3...
  - Case "sub_all".
    simpl; pick fresh Y and apply sub_all...
    repeat rewrite subst_tt_open_tt_var...
    rewrite <- concat_assoc.
    replace ([(Y, bind_sub (subst_tt Z P R2))] ++ map (subst_tb Z P) Δ)
       with (map (subst_tb Z P) ([(Y, bind_sub R2)] ++ Δ))
         by reflexivity.
    eapply H2...
  - Case "sub_box".
    simpl; apply sub_box...
Qed.

Lemma sub_through_subst_ct : forall x CU U C Γ Δ S T,
  (Δ ++ [(x, bind_typ (CU # U))] ++ Γ) ⊢ S <: T ->
  Γ ⊢ₛ C <: CU ->
  (map (subst_cb x C) Δ ++ Γ) ⊢ (subst_ct x C S) <: (subst_ct x C T).
Proof with eauto using wf_env_subst_cb,
                       wf_cset_over_subst,
                       subcapt_through_subst_cset,
                       subst_ct_pure_type.
  intros * Sub Subcapt.
  remember (Δ ++ [(x, bind_typ (CU # U))] ++ Γ).
  generalize dependent Δ.
  induction Sub; intros Δ EQ; subst.
  - Case "sub_refl_tvar".
    apply sub_refl_tvar...
    inversion H0; subst...
    rename select (binds X _ _) into Binds.
    binds_cases Binds...
    apply wf_typ_var with (T := subst_ct x C T).
    replace (bind_sub (subst_ct x C T))
       with (subst_cb x C (bind_sub T))
         by reflexivity.
    apply binds_head, binds_map; assumption.
  - Case "sub_trans_tvar".
    rename select (binds _ _ _) into Binds.
    binds_cases Binds.
    + apply sub_trans_tvar with (U := U0)...
      rewrite (subst_ct_fresh x C U0)...
      assert (WfEnv : (Δ ++ [(x, bind_typ (CU # U))] ++ Γ) ⊢ wf) by (applys sub_regular Sub).
      apply wf_env_tail in WfEnv.
      inversion WfEnv; subst.
      assert (WfU0 : Γ ⊢ U0 wf).
      { applys wf_typ_env_bind_sub... }
      pose proof (notin_fv_wf_typ Γ x U0 WfU0 ltac:(assumption)).
      fsetdec.
    + apply sub_trans_tvar with (U := subst_ct x C U0)...
  - Case "sub_capt".
    apply sub_capt...
  - Case "sub_top".
    apply sub_top...
    eapply wf_typ_subst_cb...
  - Case "sub_arr".
    pick fresh y and apply sub_arr...
    fold subst_ct.
    repeat rewrite subst_ct_open_ct_var...
    rewrite <- concat_assoc.
    replace ([(y, bind_typ (subst_cset x C C2 # subst_ct x C R2))] ++ map (subst_cb x C) Δ)
       with (map (subst_cb x C) ([(y, bind_typ (C2 # R2))] ++ Δ))
         by reflexivity.
    eauto.
  - Case "sub_all".
    pick fresh Y and apply sub_all...
    fold subst_ct.
    repeat rewrite subst_ct_open_tt_var...
    rewrite <- concat_assoc.
    replace ([(Y, bind_sub (subst_ct x C R2))] ++ map (subst_cb x C) Δ)
       with (map (subst_cb x C) ([(Y, bind_sub R2)] ++ Δ))
         by reflexivity.
    eauto*.
  - Case "sub_box".
    apply sub_box.
    fold subst_ct.
    apply IHSub...
Qed.

Lemma subst_cset_univ_idempotent : forall x C,
  subst_cset x C {*} = {*}.
Proof.
  intros. cbv.
  destruct_set_mem x {}A. fsetdec. trivial.
Qed.

Lemma wf_pretyp_from_wf_env_typ : forall x C P Γ,
  ([(x, bind_typ (C # P))] ++ Γ) ⊢ wf ->
  Γ ⊢ P wf.
Proof with eauto*.
  intros * WfEnv.
  inversion WfEnv; auto; subst.
  inversion select (Γ ⊢ (C # P) wf); subst...
Qed.

Hint Resolve wf_pretyp_from_wf_env_typ : core.

(*
Lemma typing_through_subst_ve : forall P E F x T Q e u,
  typing (F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E) Q e T ->
  value u ->
  typing E Q u (typ_capt (free_for_cv u) P) ->
  typing (map (subst_cb x (free_for_cv u)) F ++ E) Q
         (subst_ve x u (free_for_cv u) e)
         (subst_ct x (free_for_cv u) T).
Local Ltac hint ::=
  eauto 4 using wf_env_subst_cb, typing_cv, subst_ct_fresh, subst_cpt_fresh, wf_typ_from_binds_typ, notin_fv_wf_pretyp.
Proof with hint.
  intros *.
  intros HtypT HvalU HtypU.
  assert (wf_cset_in E (free_for_cv u)) as HwfFv...
  remember (F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E).
  generalize dependent F.
  induction HtypT; intros F EQ; subst; simpl subst_ee...

  - Case "typing_var_tvar".
    destruct (x0 == x); subst.
    + binds_get H1.
    + simpl.
      binds_cases H1...
      * apply typing_var_tvar...
        apply binds_head.
        replace (bind_typ X) with (subst_cb x (free_for_cv u) (bind_typ X))...
  - Case "typing_var".
    destruct (x0 == x); subst.
    + SCase "x0 = x".
      binds_get H1.
      inversion H3; subst.
      rewrite_nil_concat.
      apply typing_weakening; simpl_env...
      simpl.
      replace (subst_cset x (free_for_cv u) (`cset_fvar` x)) with (free_for_cv u).
      2: {
        unfold subst_cset.
        replace (AtomSet.F.mem x (singleton x)) with true by fset_mem_dec.
        replace (cset_set _ _ _ _) with {} by csetdec.
        destruct (free_for_cv u); csetdec.
      }

      replace (subst_cpt x (free_for_cv u) P) with P...
      forwards: binding_uniq_from_wf_env H.
      forwards: notin_fv_wf_pretyp E (dom E) (dom E) x P...
    + SCase "x0 <> x".
      binds_cases H1.
      * assert (x `notin` fv_cpt P). {
          assert (x `notin` dom E) as HA1. { eapply fresh_mid_tail... }
          forwards: wf_typ_from_binds_typ H1...
          assert (wf_pretyp_in E P) as HA2... (* missing hint *)
          forwards: notin_fv_wf_pretyp HA2 HA1...
        }
        replace (subst_ct x C (typ_capt (`cset_fvar` x0) P)) with (typ_capt (`cset_fvar` x0) P)...
        rewrite_nil_concat.
        apply typing_weakening; simpl_env...
        simpl.
        rewrite <- (subst_cset_fresh x)...
        replace (subst_cpt x (free_for_cv u) P0) with P0...
        { apply wf_typ_from_binds_typ in H1 as WfP0...
          wf_typ_inversion WfP0.
          apply binding_uniq_from_wf_env in H as ?.
          forwards : notin_fv_wf_pretyp x P0...
        }
      * simpl.
        rewrite <- (subst_cset_fresh x)...
        eapply typing_var with (C := subst_cset x (free_for_cv u) C)...
        replace (bind_typ
          (typ_capt (subst_cset x (free_for_cv u) C)
            (subst_cpt x (free_for_cv u) P0)))
        with (subst_cb x (free_for_cv u) (bind_typ (typ_capt C P0)))...
  - Case "typing_abs".
    assert (wf_env (F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E)) as HwfNarrE. {
      pick fresh z for L.
      pose proof (H1 z Fr)...
    }
    pose proof HwfNarrE as HxUniq.
    apply binding_uniq_from_wf_env in HxUniq.
    assert (wf_typ_in (F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E) V). {
      pick fresh z for L.
      pose proof (H1 z Fr) as HtypE1...
    }

    simpl subst_ct.
    destruct (AtomSet.F.mem x (`cset_fvars` (free_for_cv e1))) eqn:EqMem.
    + SCase "x in fv e1".
      assert (x `in` `cset_fvars` (free_for_cv e1)) by (rewrite AtomSetFacts.mem_iff; assumption).
      rewrite subst_trivia1...
      (**
        what do we have here:
            we have that (open_ee e1 y y) is well typed in an environment where x is bound to a type.
            therefore x cannot show up in a binds_lab, and hence
            x isn't wrapped in a exp_handler
      *)
      rewrite subst_trivia2 with (u := u)...
      pick fresh y and apply typing_abs...
      * eapply wf_typ_in_subst_cset...
      * assert (y <> x) by fsetdec.
        rewrite subst_ct_open_ct_var...

        simpl_env in *.
        replace ((dom F `union` dom E) `union` singleton y)
          with (((dom F `union` singleton x `union` dom E) `union` singleton y) `remove` x).
        2: { clear Fr. fsetdec. }
        replace (dom F `union` dom E)
          with ((dom F `union` singleton x `union` dom E) `remove` x).
        2: { clear Fr. fsetdec. }

        rewrite_env (map (subst_cb x (free_for_cv u)) ([(y, bind_typ V)] ++ F) ++ E).
        apply (wf_typ_subst_cb_cv (typ_capt (free_for_cv u) P)); simpl_env...
      * assert (y <> x) by fsetdec.
        rewrite subst_ee_open_ee_var...
        rewrite subst_ct_open_ct_var...
        rewrite_env (map (subst_cb x (free_for_cv u)) ([(y, bind_typ V)] ++ F) ++ E).
        apply H2...
    + SCase "x not in fv e1".
      assert (x `notin` `cset_fvars` (free_for_cv e1)) by (rewrite AtomSetFacts.not_mem_iff; assumption).
      rewrite subst_commutes_with_free_for_cv with (u := u)...
      pick fresh y and apply typing_abs...
      * eapply wf_typ_in_subst_cset...
      * assert (y <> x) by fsetdec.
        rewrite subst_ct_open_ct_var...

        simpl_env in *.
        replace ((dom F `union` dom E) `union` singleton y)
          with (((dom F `union` singleton x `union` dom E) `union` singleton y) `remove` x).
        2: { clear Fr. fsetdec. }
        replace (dom F `union` dom E)
          with ((dom F `union` singleton x `union` dom E) `remove` x).
        2: { clear Fr. fsetdec. }

        rewrite_env (map (subst_cb x (free_for_cv u)) ([(y, bind_typ V)] ++ F) ++ E).
        apply (wf_typ_subst_cb_cv (typ_capt (free_for_cv u) P)); simpl_env...
      * assert (y <> x) by fsetdec.
        rewrite subst_ee_open_ee_var...
        rewrite subst_ct_open_ct_var...
        rewrite_env (map (subst_cb x (free_for_cv u)) ([(y, bind_typ V)] ++ F) ++ E).
        apply H2...

  - Case "typing_app".
    rewrite subst_ct_open_ct...
    2: {
      assert (wf_pretyp_in (F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E) (typ_arrow T1 T2)) as HA0. {
        forwards [_ [_ WfTyp]] : typing_regular HtypT1.
        inversion WfTyp; subst...
      }

      forwards HA: bind_typ_notin_fv_tpt x HA0. 1: {
        trivial...
      }
      simpl in HA...
    }
    rewrite <- cv_subst_ct_correspondence.
    2: {
      assert (wf_typ_in (F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E) T1') as HA by auto.
      forwards: bind_typ_notin_fv_tt HA...
    }
    simpl subst_ct in IHHtypT1...
    eapply typing_app...
    eapply sub_through_subst_ct...
    eapply subcapt_reflexivity...

  - Case "typing_tabs".
    assert (wf_env (F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E)) as HwfNarrE. {
      pick fresh z for L.
      pose proof (H1 z Fr)...
    }
    pose proof HwfNarrE as HxUniq.
    apply binding_uniq_from_wf_env in HxUniq.
    assert (wf_typ_in (F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E) V). {
      pick fresh z for L.
      pose proof (H1 z Fr) as HtypE1...
    }

    simpl subst_ct.
    destruct (AtomSet.F.mem x (`cset_fvars` (free_for_cv e1))) eqn:EqMem.
    + SCase "x in fv e1".
      assert (x `in` `cset_fvars` (free_for_cv e1)) by (rewrite AtomSetFacts.mem_iff; assumption).
      rewrite subst_trivia1...
      rewrite subst_trivia2 with (u := u)...
      pick fresh y and apply typing_tabs...
      * eapply wf_typ_in_subst_cset...
      * assert (y <> x) by fsetdec.
        rewrite subst_ct_open_tt_var...

        simpl_env in *.
        replace ((dom F `union` dom E) `union` singleton y)
          with (((dom F `union` singleton x `union` dom E) `union` singleton y) `remove` x).
        2: { clear Fr. fsetdec. }
        replace (dom F `union` dom E)
          with ((dom F `union` singleton x `union` dom E) `remove` x).
        2: { clear Fr. fsetdec. }

        rewrite_env (map (subst_cb x (free_for_cv u)) ([(y, bind_sub V)] ++ F) ++ E).
        apply (wf_typ_subst_cb_cv (typ_capt (free_for_cv u) P)); simpl_env...
      * assert (y <> x) by fsetdec.
        rewrite subst_ee_open_te_var...
        rewrite subst_ct_open_tt_var...
        rewrite_env (map (subst_cb x (free_for_cv u)) ([(y, bind_sub V)] ++ F) ++ E).
        apply H2...
    + SCase "x not in fv e1".
      assert (x `notin` `cset_fvars` (free_for_cv e1)) by (rewrite AtomSetFacts.not_mem_iff; assumption).
      rewrite subst_commutes_with_free_for_cv with (u := u)...
      pick fresh y and apply typing_tabs...
      * eapply wf_typ_in_subst_cset...
      * assert (y <> x) by fsetdec.
        rewrite subst_ct_open_tt_var...

        simpl_env in *.
        replace ((dom F `union` dom E) `union` singleton y)
          with (((dom F `union` singleton x `union` dom E) `union` singleton y) `remove` x).
        2: { clear Fr. fsetdec. }
        replace (dom F `union` dom E)
          with ((dom F `union` singleton x `union` dom E) `remove` x).
        2: { clear Fr. fsetdec. }

        rewrite_env (map (subst_cb x (free_for_cv u)) ([(y, bind_sub V)] ++ F) ++ E).
        apply (wf_typ_subst_cb_cv (typ_capt (free_for_cv u) P)); simpl_env...
      * assert (y <> x) by fsetdec.
        rewrite subst_ee_open_te_var...
        rewrite subst_ct_open_tt_var...
        rewrite_env (map (subst_cb x (free_for_cv u)) ([(y, bind_sub V)] ++ F) ++ E).
        apply H2...

  - Case "typing_tapp".
    rewrite subst_ct_open_tt...
    eapply typing_tapp.
    + simpl subst_ct in IHHtypT.
      apply IHHtypT...
    + eapply sub_through_subst_ct...
      simpl.
      eapply subcapt_reflexivity...
    + forwards: cv_free_never_universal u.
      destruct T1; simpl in *; try congruence.
      unfold subst_cset.
      find_and_destroy_set_mem.
      unfold cset_union.
      destruct (`cset_uvar` (free_for_cv u)); easy.
    + assert (wf_typ_in (F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E) T) as HA by auto.
      applys bind_typ_notin_fv_tt HA...
  - Case "typing_sub".
    eapply typing_sub.
    + apply IHHtypT...
    + eapply sub_through_subst_ct...
      simpl.
      eapply subcapt_reflexivity...
  - Case "typing_handle".
    assert (wf_env (F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E)) as HwfNarrE. {
      pick fresh z for L.
      pose proof (H z Fr)...
    }
    pose proof HwfNarrE as HxUniq.
    apply binding_uniq_from_wf_env in HxUniq.
    (* assert (wf_typ_in (F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E) V). {
      pick fresh z for L.
      pose proof (H1 z Fr) as HtypE1...
    } *)

    simpl subst_ct.
    destruct (AtomSet.F.mem x (`cset_fvars` (free_for_cv e))) eqn:EqMem.
    + SCase "x in fv e1".
      assert (x `in` `cset_fvars` (free_for_cv e)) by (rewrite AtomSetFacts.mem_iff; assumption).
      pick fresh y and apply typing_handle.
      * assert (y <> x) by fsetdec.
        rewrite subst_ee_open_ee_var...
        rewrite <- (subst_cset_univ_idempotent x (free_for_cv u)).
        rewrite_env (map (subst_cb x (free_for_cv u)) ([(y, bind_typ (typ_capt {*} (typ_ret T1)))] ++ F) ++ E).
        apply H0...
      * intro ScUniv. eapply subcapt_univ_through_subst_cb in ScUniv...
        assert (wf_typ_in (F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E) T1). {
          pick fresh y for L.
          specialize (H y Fr).
          assert (wf_env ([(y, bind_typ (typ_capt {*} (typ_ret T1)))] ++ F ++
                            [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E)) as HA by eauto.
          inversion HA; subst.
          inversion select (wf_typ_in _ (typ_capt {*} (typ_ret T1))); subst.
          inversion select (wf_pretyp _ _ _ (typ_ret T1)); subst...
        }
        eapply cv_wf...
    + SCase "x not in fv e1".
      assert (x `notin` `cset_fvars` (free_for_cv e)) by (rewrite AtomSetFacts.not_mem_iff; assumption).
      pick fresh y and apply typing_handle...
      * assert (y <> x) by fsetdec.
        rewrite subst_ee_open_ee_var...
        rewrite <- (subst_cset_univ_idempotent x (free_for_cv u)).
        rewrite_env (map (subst_cb x (free_for_cv u)) ([(y, bind_typ (typ_capt {*} (typ_ret T1)))] ++ F) ++ E).
        apply H0...
      * intro ScUniv. eapply subcapt_univ_through_subst_cb in ScUniv...
        assert (wf_typ_in (F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E) T1). {
          pick fresh y for L.
          specialize (H y Fr).
          assert (wf_env ([(y, bind_typ (typ_capt {*} (typ_ret T1)))] ++ F ++
                            [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E)) as HA by eauto.
          inversion HA; subst.
          inversion select (wf_typ_in _ (typ_capt {*} (typ_ret T1))); subst.
          inversion select (wf_pretyp _ _ _ (typ_ret T1)); subst...
        }
        eapply cv_wf...
  - simpl subst_ct in IHHtypT1.
    eapply typing_do_ret...
    assert (wf_cset E (dom F `u`A {x}A `u`A dom E) (free_for_cv u)). {
      forwards WfCvU: typing_cv HtypU.
      applys wf_cset_set_weakening WfCvU.
      fsetdec.
    }
    rename select (wf_typ_in _ T2) into HH.
    forwards WfT1: wf_typ_subst_cb (free_for_cv u) HH; simpl_env...
    assert (wf_env (F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E)) as HA by auto.
    forwards: binding_uniq_from_wf_env HA.
    apply (wf_typ_adapt WfT1); simpl_env; fsetdec.
  - binds_cases H1.
    replace (subst_ct x C (typ_capt (`cset_lvar` l) P)) with (typ_capt (`cset_lvar` l) P).
    2: {
      assert (x `notin` fv_cpt P). {
        assert (x `notin` dom E) as HA1. {
          eapply fresh_mid_tail...
        }
        assert (wf_pretyp_in E P) as HA2... (* missing hint *)
        forwards: notin_fv_wf_pretyp HA2 HA1...
      }
      apply subst_ct_fresh; simpl_env...
    }
    rewrite_nil_concat.
    apply typing_weakening; simpl_env...
    simpl.
    rewrite <- (subst_cset_fresh x)...
    replace (subst_ct x (free_for_cv u) T) with T...
    assert (wf_typ_in E (typ_capt C (typ_ret T))) as WfP0. {
      assert (wf_typ_in empty (typ_capt C (typ_ret T))). {
        eapply wf_typ_from_binds_sig...
      }
      rewrite_env (empty ++ E ++ empty).
      eapply wf_typ_in_weakening; simpl_env...
    }
    wf_typ_inversion WfP0.
    apply binding_uniq_from_wf_env in H as ?.
    inversion H8; subst.
    forwards : notin_fv_wf_typ x T...
Qed.

Lemma typing_through_subst_ee' : forall U E Ap Am x T Q e u,
  typing ([(x, bind_typ U)] ++ E) Q e T ->
  wf_typ ([(x, bind_typ U)] ++ E) Ap Am T ->
  x `notin` Am ->
  Ap `subset` dom ([(x, bind_typ U)] ++ E) ->
  Am `subset` dom ([(x, bind_typ U)] ++ E) ->
  value u ->
  typing E Q u U ->
  wf_cset E Ap (free_for_cv u) ->
  wf_cset E Ap (cv U) ->
  typing E Q (subst_ee x u (free_for_cv u) e) (subst_ct x (cv U) T).
Proof with simpl_env; eauto.
  intros * HtypT HwfT Hnotin HApRsnbl HAmRsnbl HvalU HtypU WfFvU WfC.
  assert (typing E Q (subst_ee x u (free_for_cv u) e) (subst_ct x (free_for_cv u) T))
    as Hthrough. {
    apply values_have_precise_captures in HtypU...
    destruct HtypU as [P [HtypP HsubP]].
    rewrite_env (map (subst_cb x (free_for_cv u)) empty ++ E).
    eapply (typing_through_subst_ee P)...
    rewrite_nil_concat.
    eapply typing_narrowing_typ...
  }
  eapply typing_sub.
  apply Hthrough.
  enough (sub ([(x, bind_typ U)] ++ E) (subst_ct x (free_for_cv u) T) (subst_ct x (cv U) T)) as HE. {
    rewrite_env (empty ++ [(x, bind_typ U)] ++ E) in HE.
    forwards HP: sub_through_subst_ct (free_for_cv u) HE.
    1: {
      forwards (? & _ & Hsub): values_have_precise_captures u U...
      forwards Hsc: sub_implies_subcapt Hsub...
    }
    simpl_env in HP.
    lets (WfE & _): typing_regular HtypT.
    rewrite_env (empty ++ [(x, bind_typ U)] ++ E) in WfE.
    lets: binding_uniq_from_wf_env WfE.
    simpl_env in WfE.
    assert (x `notin` (fv_ee u)). {
      eapply notin_dom_is_notin_fv_ee...
      notin_solve.
    }
    assert (x `notin` (`cset_fvars` (free_for_cv u))). {
      lets HA: free_for_cv_is_free_ee u.
      inversion HA.
      subst.
      fsetdec.
    }
    assert (x `notin` (`cset_fvars` (cv U))). {
      assert (wf_cset_in _ (cv U)) as HA by eauto.
      inversion HA; subst; csetdec.
    }
    repeat (
        rewrite subst_ct_useless_repetition in HP; [|notin_solve]
      ).
    apply HP.
  }
  apply plain_subst_ct_monotonicity with (Ap := Ap) (Am := Am)...
  - eapply capture_prediction with (T := U)...
    rewrite_env (empty ++ [(x, bind_typ U)] ++ E);
      eapply typing_weakening...
  - rewrite_nil_concat.
    eapply wf_cset_weakening ; [ apply WfFvU | simpl_env; auto .. ].
  - rewrite_nil_concat.
    eapply wf_cset_weakening ; [ apply WfC | simpl_env; auto .. ].
Qed.
*)

(************************************************************************ *)
(** ** Type substitution preserves typing (11) *)

(*
Lemma subst_tt_open_ct_rec_straight : forall Z P k S T,
  type P ->
  subst_tt Z P (open_ct_rec k (typ_cv S) T) = open_ct_rec k (typ_cv (subst_tt Z P S)) (subst_tt Z P T).
Proof with eauto*.
with subst_tpt_open_cpt_rec_straight : forall Z P k S T,
  type P ->
  subst_tt Z P (open_cpt_rec k (cv S) T) = open_cpt_rec k (cv (subst_tt Z P S)) (subst_tpt Z P T).
Proof with eauto with fsetdec.
------
  intros * Typ.
  dependent induction T; cbn...
  - f_equal...
    rewrite subst_cset_open_cset_rec by (apply type_implies_capt_cv; assumption).
    rewrite cv_subst_correspondence...
  - destruct (a == Z)...
    apply open_ct_rec_type...
------
  intros * Typ.
  dependent induction T; cbn;
    f_equal; repeat (apply subst_tt_open_ct_rec_straight)...
Qed.
*)

Lemma typing_var_implies_binds_typ : forall Γ (x : atom) C R,
  Γ ⊢ x : (C # R) ->
  exists D Q, binds x (bind_typ (D # Q)) Γ
           /\ Γ ⊢ₛ `cset_fvar` x <: C
           /\ Γ ⊢ₛ D wf
           /\ Γ ⊢ Q <: R
           /\ pure_type R.
Proof with eauto using sub_reflexivity.
  intros * Typ.
  assert (WfT : Γ ⊢ (C # R) wf) by applys typing_regular Typ.
  eremember (C # R) as T.
  assert (Sub : Γ ⊢ T <: (C # R)).
  { subst.
    apply sub_reflexivity.
    - applys typing_regular Typ.
    - applys typing_regular Typ.
  }
  clear HeqT.
  generalize dependent Sub.
  generalize dependent R.
  generalize dependent C.
  dependent induction Typ; intros D Q Sub.
  - exists C, R.
    assert (WfCR : Γ ⊢ (C # R) wf).
    { destruct (wf_typ_env_bind_typ x (C # R) Γ ltac:(assumption) ltac:(assumption)) as [D' [Q' [Eq Wf]]].
      inversion Eq...
    }
    assert (WfDQ : Γ ⊢ (D # Q) wf).
    { applys sub_regular Sub. }
    inversion WfCR; inversion WfDQ; subst...
    inversion Sub...
  - assert (WfS : Γ ⊢ S wf).
    { applys sub_regular... }
    assert (SsubDQ : Γ ⊢ S <: (D # Q)).
    { apply sub_transitivity_type with (Q := T)... }
    destruct (IHTyp x ltac:(reflexivity) WfS D Q SsubDQ) as [C [R [Binds [WfD [WfC [RsubQ PureQ]]]]]].
    exists C, R.
    repeat split...
Qed.

Lemma typing_through_subst_te : forall Q Γ Δ Z e T P,
  (Δ ++ [(Z, bind_sub Q)] ++ Γ) ⊢ e : T ->
  Γ ⊢ P <: Q ->
  (map (subst_tb Z P) Δ ++ Γ) ⊢ (subst_te Z P e) : (subst_tt Z P T).
Proof with simpl_env;
           eauto 6 using wf_env_subst_tb,
                         wf_typ_subst_tb,
                         sub_through_subst_tt,
                         subcapt_from_binds,
                         wf_typ_from_binds_typ,
                         wf_typ_ignores_sub_bindings,
                         wf_typ_ignores_typ_bindings.
  intros * Typ PsubQ.
  assert (WfEnv : (Δ ++ [(Z, bind_sub Q)] ++ Γ) ⊢ wf) by applys typing_regular Typ.
  assert (PureP : pure_type P).
  { applys sub_pure_type PsubQ.
    apply wf_env_tail in WfEnv.
    inversion WfEnv...
  }
  assert (ZNotInDomΓ : Z ∉ dom Γ).
  { eapply fresh_mid_tail, ok_from_wf_env.
    applys typing_regular Typ.
  }
  remember (Δ ++ [(Z, bind_sub Q)] ++ Γ).
  generalize dependent Δ.
  induction Typ; intros Δ EQ; subst;
    simpl subst_te in *; simpl subst_tt in *.
  - Case "typing_var".
    rename select (binds _ _ _) into Binds.
    binds_cases Binds.
    + SCase "x ∈ dom Γ".
      rewrite <- subst_tt_fresh.
      * apply typing_var with (C := C)...
      * apply notin_fv_wf_typ with (Γ := Γ)...
    + SCase "x ∈ dom Δ".
      apply typing_var with (C := C)...
      replace (bind_typ (C # subst_tt Z P R))
         with (subst_tb Z P (bind_typ (C # R)))
           by reflexivity.
      apply binds_head, binds_map.
      assumption.
  - Case "typing_abs".
    replace (exp_cv e1)
       with (exp_cv (subst_te Z P e1))
         by (symmetry; apply subst_te_fresh_exp_cv).
    pick fresh x and apply typing_abs.
    + replace (C # subst_tt Z P R)
         with (subst_tt Z P (C # R))
           by reflexivity.
      eapply wf_typ_subst_tb...
    + rewrite subst_tt_open_ct_var...
      rewrite subst_te_open_ve_var...
      rewrite_env (map (subst_tb Z P) ([(x, bind_typ (C # R))] ++ Δ) ++ Γ).
      apply H1.
      1: clear - Fr; fsetdec.
      2: reflexivity.
      apply wf_env_typ...
  - Case "typing_app".
    assert (Z <> x).
    { destruct (typing_var_implies_binds_typ _ _ _ _ Typ2) as [C' [R' [Binds _]]].
      binds_cases Binds; simpl_env in *...
      assert (Z ∉ dom Δ) by (eapply fresh_mid_head; eauto* ).
      apply binds_In in H0.
      fsetdec.
    }
    replace (subst_tt Z P (open_ct T (`cset_fvar` x)))
       with (open_ct (subst_tt Z P T) (`cset_fvar` x))
         by (apply open_ct_subst_tt; eauto* )...
  - Case "typing_let".
    pick fresh y and apply typing_let...
    rewrite <- subst_te_open_ve...
    rewrite_env (map (subst_tb Z P) ([(y, bind_typ (C1 # T1))] ++ Δ) ++ Γ).
    apply H0.
    1: clear - Fr; fsetdec.
    2: reflexivity.
    assert (WfC1T1 : (Δ ++ [(Z, bind_sub Q)] ++ Γ) ⊢ (C1 # T1) wf) by applys typing_regular Typ.
    apply wf_env_typ...
  - Case "typing_tabs".
    replace (exp_cv e1)
       with (exp_cv (subst_te Z P e1))
         by (symmetry; apply subst_te_fresh_exp_cv).
    pick fresh Y and apply typing_tabs.
    + eapply wf_typ_subst_tb...
    + apply subst_tt_pure_type...
    + rewrite subst_te_open_te_var...
      rewrite subst_tt_open_tt_var...
      rewrite_env (map (subst_tb Z P) ([(Y, bind_sub V)] ++ Δ) ++ Γ).
      apply H2.
      1: clear - Fr; fsetdec.
      2: reflexivity.
      apply wf_env_sub...
  - Case "typing_tapp".
    rewrite subst_tt_open_tt...
  - Case "typing_box".
    apply typing_box...
    assert (WfCR : (Δ ++ [(Z, bind_sub Q)] ++ Γ) ⊢ (C # R) wf).
    { applys typing_regular Typ. }
    assert (WfC : (Δ ++ [(Z, bind_sub Q)] ++ Γ) ⊢ₛ C wf).
    { inversion WfCR... }
    inversion WfC; subst.
    intros y yIn.
    rename select (allbound _ fvars) into AllBound.
    destruct (AllBound y yIn) as [C' [R' Binds]].
    binds_cases Binds.
    + assert (y ∈ dom Γ) by (eapply binds_In; eauto* ).
      fsetdec.
    + assert (y ∈ dom Δ) by (eapply binds_In; eauto* ).
      fsetdec.
  - Case "typing_unbox".
    apply typing_unbox...
    eapply wf_cset_subst_tb...
  - Case "typing_sub".
    eapply typing_sub... 
Qed.
