Require Import Coq.Program.Equality.
Require Import TaktikZ.
Require Export CCsub_Hints.
Require Import CCsub_Subcapt.
Require Import CCsub_Subtyping.
Require Import CCsub_Typing.

Set Nested Proofs Allowed.

(************************************************************************ *)
(** ** Properties of values *)

Lemma capture_prediction : forall E Q t T,
  value t ->
  typing E Q t T ->
  subcapt E (free_for_cv t) (cv T).
Proof with subst; simpl; eauto.
  intros *.
  intros Hv Htyp.
  forwards (P1 & P2 & P3): typing_regular Htyp.
  induction Htyp; cbn [free_for_cv]; try solve [ inversion Hv ].
  - inversion P3; subst.
    apply subcapt_reflexivity with (A := dom E)...
  - inversion P3; subst.
    apply subcapt_reflexivity with (A := dom E)...
  - forwards: IHHtyp...
    apply (subcapt_transitivity (cv S))...
    eapply sub_implies_subcapt with (S := S) (T := T)...
  - inversion P3; subst.
    apply subcapt_reflexivity with (A := dom E)...
Qed.

Lemma values_have_precise_captures : forall E Q u T,
  value u ->
  typing E Q u T ->
  exists U, typing E Q u (typ_capt (free_for_cv u) U) /\ sub E (typ_capt (free_for_cv u) U) T.
Local Ltac hint ::=
  simpl; eauto.
Proof with hint.
  intros * Hv Htyp.
  assert (wf_cset_in E (free_for_cv u)) by eauto using typing_cv.
  assert (wf_env E) by auto.
  induction Htyp; try solve [inversion Hv; subst].
  - Case "exp_abs".
    exists (typ_arrow V T1).
    split.
    + simpl; eapply typing_abs...
    + simpl.
      eapply sub_reflexivity with (Ap := dom E) (Am := dom E)...
  - Case "exp_tabs".
    exists (typ_all V T1).
    split.
    + simpl; eapply typing_tabs...
    + simpl.
      eapply sub_reflexivity with (Ap := dom E) (Am := dom E)...
  - forwards (U & HtypU & HsubS): IHHtyp...
    exists U; eauto using (sub_transitivity S).
  - Case "exp_abs".
    exists (typ_ret T).
    split.
    + simpl; eapply typing_lvar...
    + note (wf_typ_in E (typ_capt C (typ_ret T))) by admit. (* NOTE: we need wf_sig Q E, in general *)
      eapply sub_reflexivity with (Ap := dom E) (Am := dom E)...
Admitted.


(************************************************************************ *)
(** ** Other helpers *)

Lemma subst_trivia1 : forall x C e,
    AtomSet.F.In x (`cset_fvars` (free_for_cv e)) ->
    subst_cset x C (free_for_cv e) = cset_union C ((free_for_cv e) A`\` x).
Proof.
  intros.
  unfold subst_cset.
  destruct_set_mem x (`cset_fvars` (free_for_cv e)).
  - reflexivity.
  - destruct (free_for_cv e) eqn:?.
    csetdec.
Qed.

Lemma subst_contratrivia2 : forall u x C e,
  x `notin` (`cset_fvars` (free_for_cv e)) ->
  (free_for_cv e) = (free_for_cv (subst_ee x u C e)).
Proof with eauto using cv_free_never_universal.
  intros * Hin.
  induction e; simpl in *...
  - destruct_if; fsetdec.
  - apply notin_cset_fvars_distributive_over_cset_union in Hin as (? & ?)...
    rewrite <- IHe1...
    rewrite <- IHe2...
  - apply notin_cset_fvars_distributive_over_cset_union in Hin as (? & ?)...
    rewrite <- IHe1...
    rewrite <- IHe2...
Qed.


(* x in (fv e) ->
  (fv u) union (fv e remove x) = fv (e[x !-> u][x !-> fv u])
*)

Lemma subst_trivia2 : forall x e u,
  AtomSet.F.In x (`cset_fvars` (free_for_cv e)) ->
  (cset_union (free_for_cv u) ((free_for_cv e) A`\` x)) =
        (free_for_cv (subst_ee x u (free_for_cv u) e)).
Proof with eauto using cv_free_never_universal.
  intros * Hin.
  induction e; simpl in *...
  - csetdec.
  - destruct (a == x) eqn:HX.
    + subst.
      csetdec.
      destruct (free_for_cv u)...
      csetdec.
    + exfalso. apply n. fsetdec.
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

Lemma fvar_open_inversion : forall (x : atom) e y C,
  exp_fvar x = open_ee e y C ->
  e = x \/ exists (n : nat), e = n.
Proof with eauto*.
  intros. induction e;
    try solve [exfalso; cbv [open_ee open_ee_rec] in H; fold open_ee_rec in H; discriminate].
  - right. exists n...
  - left...
Qed.

Lemma subst_ct_monotonicity : forall E Ap Am x C D T,
  wf_env E ->
  type T ->
  Ap `subset` dom E ->
  Am `subset` dom E ->
  wf_typ E Ap Am T ->
  subcapt E C D ->
  ((x `notin` Am -> wf_cset E Ap C -> wf_cset E Ap D -> sub E (subst_ct x C T) (subst_ct x D T)) /\
   (x `notin` Ap -> wf_cset E Am C -> wf_cset E Am D -> sub E (subst_ct x D T) (subst_ct x C T)))
with subst_cpt_monotonicity : forall E Ap Am x C D T,
  wf_env E ->
  pretype T ->
  Ap `subset` dom E ->
  Am `subset` dom E ->
  wf_pretyp E Ap Am T ->
  subcapt E C D ->
  ((x `notin` Am -> wf_cset E Ap C -> wf_cset E Ap D -> sub_pre E (subst_cpt x C T) (subst_cpt x D T)) /\
  (x `notin` Ap -> wf_cset E Am C -> wf_cset E Am D -> sub_pre E (subst_cpt x D T) (subst_cpt x C T))).
Proof with simpl_env; eauto; fold subst_cpt.
------
  intros * HwfE Typ SubAp SubAm HwfT Hsc.
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
              eapply wf_cset_ignores_typ_bindings.
              eapply wf_cset_weakening ; [ apply WfC | simpl_env; auto .. ].
           ++ rewrite_nil_concat.
              eapply wf_cset_ignores_typ_bindings.
              eapply wf_cset_weakening ; [ apply WfD | simpl_env; auto .. ].
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
              eapply wf_cset_ignores_typ_bindings.
              eapply wf_cset_weakening ; [ apply WfC | simpl_env; auto .. ].
           ++ rewrite_nil_concat.
              eapply wf_cset_ignores_typ_bindings.
              eapply wf_cset_weakening ; [ apply WfD | simpl_env; auto .. ].
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
              eapply wf_cset_ignores_sub_bindings.
              eapply wf_cset_weakening ; [ apply WfC | simpl_env; auto .. ].
           ++ rewrite_nil_concat.
              eapply wf_cset_ignores_sub_bindings.
              eapply wf_cset_weakening ; [ apply WfD | simpl_env; auto .. ].
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
              eapply wf_cset_ignores_sub_bindings.
              eapply wf_cset_weakening ; [ apply WfC | simpl_env; auto .. ].
           ++ rewrite_nil_concat.
              eapply wf_cset_ignores_sub_bindings.
              eapply wf_cset_weakening ; [ apply WfD | simpl_env; auto .. ].
  - simpl. split; intros.
    + constructor.
      forwards (Sub1 & Sub2) : subst_ct_monotonicity x H4 Hsc...
    + constructor.
      forwards (Sub1 & Sub2) : subst_ct_monotonicity x H4 Hsc...
Admitted.                       (* argh, some existential variables remain *)

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


(** TODO MOVE TO LEMMAS
    NOTE: Right now it can't be moved to lemmas, since it depends on regularity.
    So maybe refactor this to use wf_typ_in E T as a premise and drop the dependency on regularity.
**)
Lemma notin_dom_is_notin_fv_ee : forall x E Q e T,
  x `notin` dom E ->
  typing E Q e T ->
  x `notin` fv_ee e.
Proof with eauto.
  intros * NotIn Typ.
  assert (wf_typ_in E T) as WfTyp by auto.
  induction Typ.
  - assert (x <> x0) by (apply binds_In in H1; fsetdec).
    unfold fv_ee. notin_solve.
  - assert (x <> x0) by (apply binds_In in H1; fsetdec).
    unfold fv_ee. notin_solve.
  - simpl.
    apply notin_fv_wf_typ with (X := x) in H as ?.
    2: fsetdec.
    pick fresh y.
    forwards SpH2: H2 y; [ notin_solve
                         | simpl_env; notin_solve
                         | ..].
    + specialize (H0 y ltac:(fsetdec)).
      specialize (H1 y ltac:(fsetdec)).
      do 2 rewrite_nil_concat.
      eapply wf_typ_weakening...
    + forwards: notin_fv_ee_open_ee SpH2.
      notin_solve.
      notin_solve.
  - cbn [fv_ee].
    apply notin_union...
  - cbn [fv_ee].
    pick fresh y.
    forwards SpH2: H2 y; [ notin_solve | simpl_env; notin_solve |..|].
    + specialize (H0 y ltac:(fsetdec)).
      specialize (H1 y ltac:(fsetdec)).
      do 2 rewrite_nil_concat.
      eapply wf_typ_weakening...
    + apply notin_fv_ee_open_te in SpH2...
  - cbn [fv_ee].
    assert (wf_typ_in E T) as HA...
  - eauto.
  - simpl.
    pick fresh y.
    specialize (H0 y ltac:(fsetdec)).
    specialize (H y ltac:(fsetdec)).
    eapply notin_fv_ee_open_ee...
  - cbn [fv_ee].
    apply notin_union...
  - simpl.
    fsetdec.
Qed.


(* ********************************************************************** *)
(** ** Type substitution preserves subtyping (10) *)

Lemma sub_through_subst_tt : forall Q E F Z S T P,
  sub (F ++ [(Z, bind_sub Q)] ++ E) S T ->
  sub E P Q ->
  sub (map (subst_tb Z P) F ++ E) (subst_tt Z P S) (subst_tt Z P T)
with sub_pre_through_subst_tpt : forall Q E F Z S T P,
  sub_pre (F ++ [(Z, bind_sub Q)] ++ E) S T ->
  sub E P Q ->
  sub_pre (map (subst_tb Z P) F ++ E) (subst_tpt Z P S) (subst_tpt Z P T).
Proof with
      simpl_env;
eauto 4 using wf_typ_subst_tb, wf_env_subst_tb, wf_typ_weaken_head.
{ intros * SsubT PsubQ.
  dependent induction SsubT.
  - simpl.
    destruct (X == Z).
    + apply sub_reflexivity with (Ap := dom E) (Am := dom E)...
      rewrite_nil_concat.
      eapply wf_typ_weakening.
      solve [
          apply sub_regular, proj2, proj1 in PsubQ;
          apply PsubQ
        ].
      all : trivial...
    + apply sub_reflexivity with (Ap := dom (map (subst_tb Z P) F ++ E))
                                 (Am := dom (map (subst_tb Z P) F ++ E))...
      inversion H0; subst.
      rename select (binds X _ _) into BndX.
      binds_cases BndX...
      * forwards: binds_In H2.
        econstructor...
        fsetdec.
      * assert (binds X (subst_tb Z P (bind_sub U)) (map (subst_tb Z P) F ++ E))...
        forwards: binds_In H2.
        econstructor...
        fsetdec.
  - Case "sub_trans_tvar".
    assert (wf_env (F ++ [(Z, bind_sub Q)] ++ E)) as WfE by auto.
    apply binding_uniq_from_wf_env in WfE as FrZ.
    simpl.
    destruct (X == Z); subst.
    + SCase "X = Z".
      apply (sub_transitivity Q)...
      * rewrite_nil_concat.
        apply sub_weakening...
      * rewrite (subst_tt_fresh Z P Q).
        2: {
          assert (wf_typ_in E Q) as HA by auto.
          lets: notin_fv_wf_typ Z Q HA.
          fsetdec.
        }
        binds_get H.
        inversion H1; subst.
        apply (IHSsubT Q)...
    + SCase "X <> Z".
      binds_cases H.
      * assert (binds X (bind_sub U) (map (subst_tb Z P) F ++ E)) by auto.
        apply (sub_trans_tvar U)...
        rewrite (subst_tt_fresh Z P U).
        2: {
          assert (wf_typ_in E U) as HA. {
            eapply wf_typ_from_binds_sub...
          }
          lets: notin_fv_wf_typ Z HA.
          fsetdec.
        }
        apply (IHSsubT Q)...
      * apply (sub_trans_tvar (subst_tt Z P U)); [auto | eapply IHSsubT]...
  - simpl.
    apply sub_capt.
    + apply subcapt_through_subst_tt with (Q := Q)...
    + apply (sub_pre_through_subst_tpt Q)...
}
{ intros * SsubT PsubQ.
  dependent induction SsubT; simpl.
  - constructor...
    apply (wf_pretyp_in_subst_tb Q)...
  - pick fresh y and apply sub_arrow...
    + eapply wf_typ_in_subst_tb...
    + eapply wf_typ_in_subst_tb...
    + rewrite subst_tt_open_ct_var...
      specialize (H2 y ltac:(notin_solve)).
      simpl_env in H2.
      simpl_env.
      assert (wf_env (F ++ [(Z, bind_sub Q)] ++ E)) as HA by auto.
      apply binding_uniq_from_wf_env in HA.
      assert (y <> Z) by notin_solve.
      (* apply (wf_typ_set_strengthen Z Q) in H2... *)
      eapply wf_typ_adapt. {
        rewrite_parenthesise_binding_in H2.
        assert (wf_typ_in (empty ++ E) P) as WfP by (simpl_env;auto).
        applys wf_typ_subst_tb P H2.
        - do 2 rewrite_nil_concat.
          clear Fr.
          eapply wf_typ_weakening in WfP.
          apply WfP.
          all: simpl_env; (fsetdec || eauto).
        - do 2 rewrite_nil_concat.
          clear Fr.
          eapply wf_typ_weakening in WfP.
          apply WfP.
          all: simpl_env; (fsetdec || eauto).
        - trivial...
      }
      all : clear Fr; fsetdec.
    + rewrite subst_tt_open_ct_var...
      specialize (H3 y ltac:(notin_solve)).
      simpl_env in H3.
      simpl_env.
      assert (wf_env (F ++ [(Z, bind_sub Q)] ++ E)) as HA by auto.
      apply binding_uniq_from_wf_env in HA.
      assert (y <> Z) by notin_solve.
      (* apply (wf_typ_set_strengthen Z Q) in H3... *)
      eapply wf_typ_adapt. {
        rewrite_parenthesise_binding_in H3.
        assert (wf_typ_in (empty ++ E) P) as WfP by (simpl_env;auto).
        applys wf_typ_subst_tb P H3.
        - do 2 rewrite_nil_concat.
          clear Fr.
          eapply wf_typ_weakening in WfP.
          apply WfP.
          all: simpl_env; (fsetdec || eauto).
        - do 2 rewrite_nil_concat.
          clear Fr.
          eapply wf_typ_weakening in WfP.
          apply WfP.
          all: simpl_env; (fsetdec || eauto).
        - trivial...
      }
      all : clear Fr; fsetdec.
    + repeat rewrite subst_tt_open_ct_var...
      rewrite_env (map (subst_tb Z P) ([(y, bind_typ T1)] ++ F) ++ E).
      eapply sub_through_subst_tt...
  - pick fresh y and apply sub_all...
    + eapply wf_typ_in_subst_tb...
    + eapply wf_typ_in_subst_tb...
    + rewrite subst_tt_open_tt_var...
      specialize (H2 y ltac:(notin_solve)).
      simpl_env in H2.
      simpl_env.
      assert (wf_env (F ++ [(Z, bind_sub Q)] ++ E)) as HA by auto.
      apply binding_uniq_from_wf_env in HA.
      assert (y <> Z) by notin_solve.
      (* apply (wf_typ_set_strengthen Z Q) in H2... *)
      eapply wf_typ_adapt. {
        rewrite_parenthesise_binding_in H2.
        assert (wf_typ_in (empty ++ E) P) as WfP by (simpl_env;auto).
        applys wf_typ_subst_tb P H2.
        - do 2 rewrite_nil_concat.
          clear Fr.
          eapply wf_typ_weakening in WfP.
          apply WfP.
          all: simpl_env; (fsetdec || eauto).
        - do 2 rewrite_nil_concat.
          clear Fr.
          eapply wf_typ_weakening in WfP.
          apply WfP.
          all: simpl_env; (fsetdec || eauto).
        - trivial...
      }
      all : clear Fr; fsetdec.
    + rewrite subst_tt_open_tt_var...
      specialize (H3 y ltac:(notin_solve)).
      simpl_env in H3.
      simpl_env.
      assert (wf_env (F ++ [(Z, bind_sub Q)] ++ E)) as HA by auto.
      apply binding_uniq_from_wf_env in HA.
      assert (y <> Z) by notin_solve.
      (* apply (wf_typ_set_strengthen Z Q) in H3... *)
      eapply wf_typ_adapt. {
        rewrite_parenthesise_binding_in H3.
        assert (wf_typ_in (empty ++ E) P) as WfP by (simpl_env;auto).
        applys wf_typ_subst_tb P H3.
        - do 2 rewrite_nil_concat.
          clear Fr.
          eapply wf_typ_weakening in WfP.
          apply WfP.
          all: simpl_env; (fsetdec || eauto).
        - do 2 rewrite_nil_concat.
          clear Fr.
          eapply wf_typ_weakening in WfP.
          apply WfP.
          all: simpl_env; (fsetdec || eauto).
        - trivial...
      }
      all : clear Fr; fsetdec.
    + repeat rewrite subst_tt_open_tt_var...
      rewrite_env (map (subst_tb Z P) ([(y, bind_sub T1)] ++ F) ++ E).
      eapply sub_through_subst_tt...
  - econstructor...
}
Qed.


Lemma sub_through_subst_ct : forall x U C E F S T,
  sub (F ++ [(x, bind_typ U)] ++ E) S T ->
  subcapt E C (cv U) ->
  sub (map (subst_cb x C) F ++ E) (subst_ct x C S) (subst_ct x C T)
with sub_pre_through_subst_cpt : forall x U C E F P Q,
  sub_pre (F ++ [(x, bind_typ U)] ++ E) Q P ->
  subcapt E C (cv U) ->
  sub_pre (map (subst_cb x C) F ++ E) (subst_cpt x C Q) (subst_cpt x C P).
Proof with eauto using wf_env_subst_cb, wf_typ_in_subst_cset, subcapt_through_subst_cset.
{ intros * Hsub Hsc.
  remember (F ++ [(x, bind_typ U)] ++ E).
  generalize dependent F.
  induction Hsub; intros F ?; subst.
  - simpl.
    apply sub_refl_tvar...
    change (typ_fvar X) with (subst_ct x C X)...
  - simpl.
    destruct (x == X). {
      subst.
      binds_get H.
    }
    assert (wf_env (F ++ [(x, bind_typ U)] ++ E)). {
      specialize (IHHsub _ ltac:(reflexivity))...
    }
    SCase "x <> X".
    binds_cases H.
    + assert (x `notin` fv_ct U0). {
        apply wf_typ_from_binds_sub in H as HA; [|eauto .. ].
        assert (wf_env (F ++ [(x, bind_typ U)] ++ E)) as HA1. {
          trivial...
        }
        apply binding_uniq_from_wf_env in HA1.
        forwards: notin_fv_wf_typ x HA; notin_solve.
      }
      forwards IHHsub0: IHHsub F...
      rewrite <- (subst_ct_fresh x C U0) in IHHsub0...
    + apply sub_trans_tvar with (U := (subst_ct x C U0))...
  - apply sub_capt...
}
{ intros * Hsub Hsc.
  remember (F ++ [(x, bind_typ U)] ++ E).
  generalize dependent F.
  induction Hsub; intros F ?; subst.
  - simpl.
    apply sub_top...
    eapply wf_pretyp_in_subst_cset ...
  - simpl.
    pick fresh y and apply sub_arrow...
    + rewrite subst_ct_open_ct_var...
      specialize (H2 y ltac:(notin_solve)).
      simpl_env in H2.
      simpl_env.
      assert (wf_env (F ++ [(x, bind_typ U)] ++ E)) as HA by auto.
      apply binding_uniq_from_wf_env in HA.
      assert (y <> x) by notin_solve.
      match type of H2 with
      | wf_typ _ ?Ap ?Am _ =>
        match goal with
        | |- wf_typ _ ?Ap' ?Am' _ =>
          replace Ap' with (Ap `remove` x); [replace Am' with (Am `remove` x)|]
        end
      end.
      2,3: clear Fr; fsetdec.
      rewrite_env (map (subst_cb x C) ([(y, bind_typ T1)] ++ F) ++ E).
      specialize (H4 y ltac:(notin_solve)).
      assert (wf_cset_in E C) as WfC by auto.
      applys wf_typ_subst_cb C; simpl_env...
      * applys wf_cset_set_weakening WfC...
      * applys wf_cset_set_weakening WfC...
    + rewrite subst_ct_open_ct_var...
      specialize (H3 y ltac:(notin_solve)).
      simpl_env in H3.
      simpl_env.
      assert (wf_env (F ++ [(x, bind_typ U)] ++ E)) as HA by auto.
      apply binding_uniq_from_wf_env in HA.
      assert (y <> x) by notin_solve.
      match type of H3 with
      | wf_typ _ ?Ap ?Am _ =>
        match goal with
        | |- wf_typ _ ?Ap' ?Am' _ =>
          replace Ap' with (Ap `remove` x); [replace Am' with (Am `remove` x)|]
        end
      end.
      2,3: clear Fr; fsetdec.
      rewrite_env (map (subst_cb x C) ([(y, bind_typ S1)] ++ F) ++ E).
      specialize (H4 y ltac:(notin_solve)).
      assert (wf_cset_in E C) as WfC by auto.
      applys wf_typ_subst_cb C; simpl_env...
      * applys wf_cset_set_weakening WfC...
      * applys wf_cset_set_weakening WfC...
    + specialize (H4 y ltac:(notin_solve)).
      rewrite subst_ct_open_ct_var...
      rewrite subst_ct_open_ct_var...
      rewrite_env (map (subst_cb x C) ([(y, bind_typ T1)] ++ F) ++ E).
      eapply sub_through_subst_ct; simpl_env...
  - simpl.
    pick fresh y and apply sub_all...
    + rewrite subst_ct_open_tt_var...
      specialize (H2 y ltac:(notin_solve)).
      simpl_env in H2.
      simpl_env.
      assert (wf_env (F ++ [(x, bind_typ U)] ++ E)) as HA by auto.
      apply binding_uniq_from_wf_env in HA.
      assert (y <> x) by notin_solve.
      match type of H2 with
      | wf_typ _ ?Ap ?Am _ =>
        match goal with
        | |- wf_typ _ ?Ap' ?Am' _ =>
          replace Ap' with (Ap `remove` x); [replace Am' with (Am `remove` x)|]
        end
      end.
      2,3: clear Fr; fsetdec.
      rewrite_env (map (subst_cb x C) ([(y, bind_sub T1)] ++ F) ++ E).
      specialize (H4 y ltac:(notin_solve)).
      assert (wf_cset_in E C) as WfC by auto.
      applys wf_typ_subst_cb C; simpl_env...
      * applys wf_cset_set_weakening WfC...
      * applys wf_cset_set_weakening WfC...
    + rewrite subst_ct_open_tt_var...
      specialize (H3 y ltac:(notin_solve)).
      simpl_env in H3.
      simpl_env.
      assert (wf_env (F ++ [(x, bind_typ U)] ++ E)) as HA by auto.
      apply binding_uniq_from_wf_env in HA.
      assert (y <> x) by notin_solve.
      match type of H3 with
      | wf_typ _ ?Ap ?Am _ =>
        match goal with
        | |- wf_typ _ ?Ap' ?Am' _ =>
          replace Ap' with (Ap `remove` x); [replace Am' with (Am `remove` x)|]
        end
      end.
      2,3: clear Fr; fsetdec.
      rewrite_env (map (subst_cb x C) ([(y, bind_sub S1)] ++ F) ++ E).
      specialize (H4 y ltac:(notin_solve)).
      assert (wf_cset_in E C) as WfC by auto.
      applys wf_typ_subst_cb C; simpl_env...
      * applys wf_cset_set_weakening WfC...
      * applys wf_cset_set_weakening WfC...
    + specialize (H4 y ltac:(notin_solve)).
      rewrite subst_ct_open_tt_var...
      rewrite subst_ct_open_tt_var...
      rewrite_env (map (subst_cb x C) ([(y, bind_sub T1)] ++ F) ++ E).
      eapply sub_through_subst_ct; simpl_env...
  - econstructor...
}
Qed.


Lemma subst_cset_univ_idempotent : forall x C,
  subst_cset x C {*} = {*}.
Proof.
  intros. cbv.
  destruct_set_mem x {}A. fsetdec. trivial.
Qed.


Lemma typing_through_subst_ee : forall P E F x T Q e u,
  typing (F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E) Q e T ->
  value u ->
  typing E Q u (typ_capt (free_for_cv u) P) ->
  typing (map (subst_cb x (free_for_cv u)) F ++ E) Q
         (subst_ee x u (free_for_cv u) e)
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
      admit.                    (* missing hint *)
    + SCase "x0 <> x".
      binds_cases H1.
      * assert (x `notin` fv_cpt P). {
          assert (x `notin` dom E) as HA1. { eapply fresh_mid_tail... }
          forwards: wf_typ_from_binds_typ H1...
          assert (wf_pretyp_in E P) as HA2 by admit... (* missing hint *)
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
      note (wf_pretyp_in (F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E) (typ_arrow T1 T2)) as HA0 by admit. (* missing hint *)
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
    + admit.
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
    + SCase "x not in fv e1".
      assert (x `notin` `cset_fvars` (free_for_cv e)) by (rewrite AtomSetFacts.not_mem_iff; assumption).
      pick fresh y and apply typing_handle...
      * assert (y <> x) by fsetdec.
        rewrite subst_ee_open_ee_var...
        rewrite <- (subst_cset_univ_idempotent x (free_for_cv u)).
        rewrite_env (map (subst_cb x (free_for_cv u)) ([(y, bind_typ (typ_capt {*} (typ_ret T1)))] ++ F) ++ E).
        apply H0...
      * intro ScUniv. eapply subcapt_univ_through_subst_cb in ScUniv...
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
        assert (wf_pretyp_in E P) as HA2 by admit... (* missing hint *)
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
Admitted.

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


(************************************************************************ *)
(** ** Type substitution preserves typing (11) *)

Lemma subst_tt_open_ct_rec_straight : forall Z P k S T,
  type P ->
  subst_tt Z P (open_ct_rec k (cv S) T) = open_ct_rec k (cv (subst_tt Z P S)) (subst_tt Z P T)
with subst_tpt_open_cpt_rec_straight : forall Z P k S T,
  type P ->
  subst_tpt Z P (open_cpt_rec k (cv S) T) = open_cpt_rec k (cv (subst_tt Z P S)) (subst_tpt Z P T).
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

Lemma typing_through_subst_te : forall Q E F Z QQ e T P,
  typing (F ++ [(Z, bind_sub Q)] ++ E) QQ e T ->
  sub E P Q ->
  typing (map (subst_tb Z P) F ++ E) QQ (subst_te Z P e) (subst_tt Z P T).
Proof with simpl_env;
           eauto 6 using wf_env_subst_tb,
                         wf_typ_subst_tb,
                         sub_through_subst_tt,
                         subcapt_from_binds,
                         wf_typ_from_binds_typ,
                         wf_pretyp_weakening,
                         wf_typ_set_weakening.
  intros *.
  intros Typ PsubQ.
  remember (F ++ [(Z, bind_sub Q)] ++ E).
  generalize dependent F.
  induction Typ; intros F EQ; subst;
    simpl subst_te in *; simpl subst_tt in *...
  - Case "typing_var_tvar".
    destruct (X == Z).
    rewrite (map_subst_tb_id E Z P);
      [ | auto | eapply fresh_mid_tail; eauto ].
    + subst.
      binds_cases H1...
      * assert (type P) as TypP...
        destruct TypP.
        -- set (P' := X) in *.
           assert (wf_env (map (subst_tb Z P') F ++ E)) as HA...
           rewrite (map_subst_tb_id E Z P') in HA;
             [ | auto | eapply fresh_mid_tail; eauto ].
           eapply typing_var_tvar...
           apply binds_map with (f := (subst_tb Z P')) in H1.
           simpl in H1.
           destruct (Z == Z); try easy...
        -- assert (wf_env (map (subst_tb Z (typ_capt C P)) F ++ E)) as HA...
           rewrite (map_subst_tb_id E Z (typ_capt C P)) in HA;
             [ | auto | eapply fresh_mid_tail; eauto ].
           apply binds_map with (f := (subst_tb Z (typ_capt C P))) in H1.

           assert (binds x (bind_typ (typ_capt C P))
             (map (subst_tb Z (typ_capt C P)) F ++
              map (subst_tb Z (typ_capt C P)) E)) as HAbinds. {

             replace (bind_typ (typ_capt C P)) with (subst_tb Z (typ_capt C P) (bind_typ Z))...
             simpl.
             destruct (Z == Z); try easy.
           }
           apply (typing_sub (typ_capt (`cset_fvar` x) P))...
           apply wf_typ_from_binds_typ in HAbinds as HAwfP...
           inversion HAwfP; subst.
           simpl_env in *.
           apply sub_capt.
           ++ destruct C; eauto using wf_cset_from_binds, subcapt_from_binds.
           ++ eapply sub_pre_reflexivity...
      * rewrite <- (map_subst_tb_id E Z P);
          [ | auto | eapply fresh_mid_tail; eauto ].

        assert (binds x (subst_tb Z P (bind_typ Z)) (map (subst_tb Z P) F)) as HA...
        simpl in HA.
        destruct (Z == Z); try easy.
        assert (type P) as Typ...
        destruct Typ...
        eapply typing_sub...
        apply sub_capt...
        let d := constr:(dom (map (subst_tb Z (typ_capt C P)) F ++ E))
        in apply sub_pre_reflexivity with (Ap := d) (Am := d)...
        apply sub_regular, proj2, proj1 in PsubQ.
        inversion PsubQ; subst.
        rewrite_nil_concat.
        eapply wf_pretyp_weakening; simpl_env...
    + subst.
      apply typing_var_tvar...
      rewrite (map_subst_tb_id E Z P);
        [ | auto | eapply fresh_mid_tail; eauto ].
      binds_cases H1...
      * enough (binds x (subst_tb Z P (bind_typ X)) (map (subst_tb Z P) E)) as HA...
        simpl in HA...
        destruct (X == Z); try easy...
      * enough (binds x (subst_tb Z P (bind_typ X)) (map (subst_tb Z P) (F ++ E))) as HA...
        simpl in HA...
        rewrite_env (map (subst_tb Z P) F ++ map (subst_tb Z P) E) in HA.
        destruct (X == Z); try easy...
  - Case "typing_var".
    assert (Z <> x). {
      destruct (Z == x)...
      assert (binds Z (bind_sub Q) (F ++ [(Z, bind_sub Q)] ++ E)) by auto.
      forwards: binds_unique (bind_sub Q) (bind_typ (typ_capt C P0))...
      exfalso; congruence.
    }
    unfold subst_cset.
    find_and_destroy_set_mem; [exfalso;fsetdec|].
    apply typing_var with (C := (subst_cset Z (cv P) C))...
    rewrite (map_subst_tb_id E Z P);
      [ | auto | eapply fresh_mid_tail; eauto ].
    binds_cases H1;
      replace
        (bind_typ (typ_capt (subst_cset Z (cv P) C) (subst_tpt Z P P0)))
      with
        (subst_tb Z P (bind_typ (typ_capt C P0)))...
  - Case "typing_abs".
    assert (wf_env (F ++ [(Z, bind_sub Q)] ++ E)) as HwfNarrE. {
      pick fresh z for L.
      pose proof (H1 z Fr)...
    }
    replace (free_for_cv e1) with (free_for_cv (subst_te Z P e1)).
    2: { rewrite subst_te_idempotent_wrt_free_for_cv... }
    replace (subst_cset Z (cv P) (free_for_cv (subst_te Z P e1)))
      with (free_for_cv (subst_te Z P e1)).
    2: {
      unfold subst_cset.
      find_and_destroy_set_mem.
      pick fresh y.
      forwards HA: H2 y ([(y, bind_typ V)] ++ F); [notin_solve|..].
      1: reflexivity.
      forwards (U & Zbnd): free_for_cv_bound_typing Z HA. {
        rewrite subst_te_idempotent_wrt_free_for_cv.
        rewrite subst_te_idempotent_wrt_free_for_cv in ZIn.
        forwards (? & ? & ?): free_for_cv_open e1 0 y...
      }
      assert (ok (F ++ [(Z, bind_sub Q)] ++ E)) as Ok by auto.
      forwards: fresh_mid_tail Ok.
      forwards: fresh_mid_head Ok.
      assert (y <> Z) by notin_solve.
      clear Fr.
      binds_cases Zbnd.
      - rename select (binds Z _ E) into Err.
        forwards: binds_In Err.
        exfalso;fsetdec.
      - rename select (binds Z _ _) into Err.
        forwards: binds_In Err;simpl_env in *.
        exfalso;fsetdec.
    }
    pick fresh y and apply typing_abs.
    + eapply wf_typ_in_subst_tb...
    + specialize (H0 y ltac:(notin_solve)).
      rewrite subst_tt_open_ct_var...
      rewrite_env (map (subst_tb Z P) ([(y, bind_typ V)] ++ F) ++ E).
      apply binding_uniq_from_wf_env in HwfNarrE as ?.
      assert (y `notin` (dom F `union` singleton Z `union` dom E)) by notin_solve.
      simpl_env in H0.
      rewrite_parenthesise_binding_in H0.
      forwards HA: wf_typ_subst_tb Q H0.
      * apply sub_regular, proj2, proj1 in PsubQ.
        clear Fr.
        applys wf_typ_set_weakening PsubQ...
      * apply sub_regular, proj2, proj1 in PsubQ.
        clear Fr.
        applys wf_typ_set_weakening PsubQ...
      * pose proof (H1 y ltac:(notin_solve))...
      * apply (wf_typ_adapt HA).
        all: clear Fr; fsetdec.
    + rewrite_env (map (subst_tb Z P) ([(y, bind_typ V)] ++ F) ++ E).
      rewrite subst_te_open_ee_var...
      rewrite subst_tt_open_ct_var...
      unshelve eapply (H2 y _ ([(y, bind_typ V)] ++ F) _)...
  - Case "typing_app".
    replace (subst_tt Z P (open_ct T2 (cv T1')))
      with (open_ct (subst_tt Z P T2) (cv (subst_tt Z P T1')))...
    symmetry; apply subst_tt_open_ct_rec_straight...
  - Case "typing_tabs".
    assert (wf_env (F ++ [(Z, bind_sub Q)] ++ E)) as HwfNarrE. {
      pick fresh z for L.
      pose proof (H1 z Fr)...
    }
    replace (free_for_cv e1) with (free_for_cv (subst_te Z P e1)).
    2: { rewrite subst_te_idempotent_wrt_free_for_cv... }
    replace (subst_cset Z (cv P) (free_for_cv (subst_te Z P e1)))
      with (free_for_cv (subst_te Z P e1)).
    2: {
      unfold subst_cset.
      find_and_destroy_set_mem.
      pick fresh y.
      forwards HA: H2 y ([(y, bind_sub V)] ++ F); [notin_solve|..].
      1: reflexivity.
      forwards (U & Zbnd): free_for_cv_bound_typing Z HA. {
        rewrite subst_te_idempotent_wrt_free_for_cv.
        rewrite subst_te_idempotent_wrt_free_for_cv in ZIn.
        forwards (? & ? & ?): free_for_cv_open_type e1 0 y...
      }
      assert (ok (F ++ [(Z, bind_sub Q)] ++ E)) as Ok by auto.
      forwards: fresh_mid_tail Ok.
      forwards: fresh_mid_head Ok.
      assert (y <> Z) by notin_solve.
      clear Fr.
      binds_cases Zbnd;
        rename select (binds Z _ _) into Err;
        forwards: binds_In Err; simpl_env in *;
        exfalso;fsetdec.
    }
    pick fresh Y and apply typing_tabs.
    + eapply wf_typ_in_subst_tb...
    + specialize (H0 Y ltac:(notin_solve)).
      rewrite subst_tt_open_tt_var...
      rewrite_env (map (subst_tb Z P) ([(Y, bind_sub V)] ++ F) ++ E).
      apply binding_uniq_from_wf_env in HwfNarrE as ?.
      assert (Y `notin` (dom F `union` singleton Z `union` dom E)) by notin_solve.
      simpl_env in H0.
      rewrite_parenthesise_binding_in H0.
      forwards HA: wf_typ_subst_tb Q H0.
      * apply sub_regular, proj2, proj1 in PsubQ.
        clear Fr.
        applys wf_typ_set_weakening PsubQ...
      * apply sub_regular, proj2, proj1 in PsubQ.
        clear Fr.
        applys wf_typ_set_weakening PsubQ...
      * pose proof (H1 Y ltac:(notin_solve))...
      * apply (wf_typ_adapt HA).
        all: clear Fr; fsetdec.
    + rewrite subst_te_open_te_var...
      rewrite subst_tt_open_tt_var...
      rewrite_env (map (subst_tb Z P) ([(Y, bind_sub V)] ++ F) ++ E).
      apply H2...
  - Case "typing_tapp".
    rewrite subst_tt_open_tt...
    econstructor...
    admit.
  - Case "typing_handle".
    assert (wf_env (F ++ [(Z, bind_sub Q)] ++ E)) as HwfNarrE. {
      pick fresh z for L.
      pose proof (H z Fr)...
    }
    replace (free_for_cv e) with (free_for_cv (subst_te Z P e)).
    2: { rewrite subst_te_idempotent_wrt_free_for_cv... }
    replace (subst_cset Z (cv P) (free_for_cv (subst_te Z P e)))
      with (free_for_cv (subst_te Z P e)).
    2: {
      unfold subst_cset.
      find_and_destroy_set_mem.
      pick fresh y.
      forwards HA: H0 y ([(y, bind_typ (typ_capt {*} (typ_ret T1)))] ++ F); [notin_solve|..]...
      forwards (U & Zbnd): free_for_cv_bound_typing Z HA. {
        rewrite subst_te_idempotent_wrt_free_for_cv.
        rewrite subst_te_idempotent_wrt_free_for_cv in ZIn.
        forwards (? & ? & ?): free_for_cv_open e 0 y...
      }
      assert (ok (F ++ [(Z, bind_sub Q)] ++ E)) as Ok by auto.
      forwards: fresh_mid_tail Ok.
      forwards: fresh_mid_head Ok.
      assert (y <> Z) by notin_solve.
      clear Fr.
      binds_cases Zbnd.
      - rename select (binds Z _ E) into Err.
        forwards: binds_In Err.
        exfalso;fsetdec.
      - rename select (binds Z _ _) into Err.
        forwards: binds_In Err;simpl_env in *.
        exfalso;fsetdec.
    }
    pick fresh y and apply typing_handle.
    + rewrite subst_te_open_ee_var...
      rewrite <- (subst_cset_univ_idempotent Z (cv P)).
      rewrite_env (map (subst_tb Z P) ([(y,  bind_typ (typ_capt {*} (typ_ret T1)))] ++ F) ++ E).
      apply H0...
    + intro ScUniv.
      eapply subcapt_univ_through_subst_tb in ScUniv...
      * apply H1.
        destruct ScUniv as [ScUniv|ScUniv].
        1: { eapply subcapt_widening_univ... }
        admit. (** need substitution requirement *)
      * eapply wf_env_narrowing...
  - eapply typing_do_ret.
    + eapply IHTyp1...
    + eapply IHTyp2...
    + assert (wf_typ E (dom F `u`A {Z}A `u`A dom E) (dom F `u`A {Z}A `u`A dom E) P) as WfP. {
        forwards (? & WfP & ?): sub_regular PsubQ.
        applys wf_typ_set_weakening WfP...
      }
      rename select (wf_typ_in _ T2) into HH.
      forwards WfP': wf_typ_subst_tb Q HH; simpl_env...
  - unfold subst_cset.
    find_and_destroy_set_mem; [exfalso;fsetdec|].
    admit.                      (* T wf in empty, therefore subst doesn't affect it *)
    (* apply typing_lvar with (C := (subst_cset Z (cv P) C))... *)
    (* rewrite (map_subst_tb_id E Z P); *)
    (*   [ | auto | eapply fresh_mid_tail; eauto ]. *)
    (* binds_cases H0; *)
    (*   replace *)
    (*     (bind_lab (typ_capt (subst_cset Z (cv P) C) (typ_ret (subst_tt Z P T)))) *)
    (*   with *)
    (*     (subst_tb Z P (bind_lab (typ_capt C (typ_ret T))))... *)
Admitted.
