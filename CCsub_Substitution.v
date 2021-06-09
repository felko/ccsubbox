Require Import Coq.Program.Equality.
Require Import TaktikZ.
Require Export CCsub_Hints.
Require Import CCsub_CvFacts.
Require Export CCsub_Subtyping.

Set Nested Proofs Allowed.

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

Lemma notin_cset_fvars_distributive_over_cset_union : forall x C D,
  x `notin` `cset_fvars` (cset_union C D) ->
  x `notin` `cset_fvars` C /\
  x `notin` `cset_fvars` D.
Proof.
  intros.
  destruct C eqn:EQ__C;
    destruct D eqn:EQ__D;
    unfold cset_union in *; split.
  all : (easy || fsetdec).
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
    (* + rewrite (AtomSetFacts.union_iff t t1 x) in Hin. *)
    (*   destruct Hin. *)
    (*   * specialize (IHe1 H). *)
    (*     epose proof (cv_free_never_universal (subst_ee x u cset_universal e1)). *)
    (*     symmetry in IHe1. *)
    (*     contradiction. *)
    (*   * specialize (IHe2 H). *)
    (*     epose proof (cv_free_never_universal (subst_ee x u cset_universal e2)). *)
    (*     symmetry in IHe2. *)
    (*     contradiction. *)
    (*   (* we only want to consider the case where all u, e1 and e2 have a concrete cv...  *) *)
    + (* there are three cases... we also need to know that it is NOT in the other sets... then we might be able to prove it... *)
      rewrite (AtomSetFacts.mem_iff) in Hin.
      rewrite (AtomSetFacts.union_b) in Hin.
      destruct (AtomSet.F.mem x t) eqn:InT;
        destruct (AtomSet.F.mem x t1) eqn:InT1;
        rewrite_set_facts_in InT;
        rewrite_set_facts_in InT1;
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
Qed.

Lemma notin_dom_is_notin_fv_ee : forall x E e T,
  x `notin` dom E ->
  typing E e T ->
  x `notin` fv_ee e.
Proof with eauto.
  intros * NotIn Typ.
  assert (wf_typ_in E T) as WfTyp by auto.
  induction Typ.
  - assert (x <> x0) by (apply binds_In in H0; fsetdec).
    unfold fv_ee. notin_solve.
  - assert (x <> x0) by (apply binds_In in H0; fsetdec).
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
Qed.


(*
  opening capture sets in types preserves well-formedness. *)
Lemma open_ct_wf_typ : forall E Ap Am T C,
  wf_typ E Ap Am T -> wf_typ E Ap Am (open_ct T C).
Proof with eauto using type_from_wf_typ.
  intros *.
  intros H.
  closed_type...
Qed.

(* capture set substitution does not affect subtyping

  depends on opening in the context
    binds X (bind_sub U) E -> binds X (bind_sub (open_ct U C)) E
 *)
Lemma open_ct_sub : forall E S T C,
  wf_env E ->
  sub E S T ->
  sub E (open_ct S C) (open_ct T C).
Proof with auto using open_ct_wf_typ.
  intros E S T C Eok H.
  inversion H ; simpl ; closed_type ; subst...
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
}
Qed.