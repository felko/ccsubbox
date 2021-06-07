Require Import Coq.Program.Equality.
Require Import TaktikZ.
Require Export CCsub_Hints.
Require Import CCsub_CvFacts.

Set Nested Proofs Allowed.

Local Ltac hint := idtac.

(* Local Lemma cheat : forall A, A. *)
(* Admitted. *)

(* Local Lemma cheat_with : forall A B, A -> B. *)
(* Admitted. *)

Local Lemma subst_trivia1 : forall x C e,
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

Local Lemma subst_contratrivia2 : forall u x C e,
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
Local Lemma subst_trivia2 : forall x e u,
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

(* ********************************************************************** *)
(** * #<a name="subtyping"></a># Properties of subtyping *)

(* ********************************************************************** *)
(** ** Weakening (2) *)

Lemma sub_weakening : forall E F G S T,
  sub (G ++ E) S T ->
  wf_env (G ++ F ++ E) ->
  sub (G ++ F ++ E) S T
with sub_pre_weakening : forall E F G S T,
  sub_pre (G ++ E) S T ->
  wf_env (G ++ F ++ E) ->
  sub_pre (G ++ F ++ E) S T.
Proof with simpl_env; eauto using wf_typ_weakening, wf_pretyp_weakening, subcapt_weakening, wf_cset_weakening.
------
  intros E F G S T Sub Ok.
  remember (G ++ E).
  generalize dependent G.
  induction Sub; intros G Ok EQ; subst.
  - Case "sub_refl_tvar".
    apply sub_refl_tvar...
  - Case "sub_trans_tvar".
    apply (sub_trans_tvar U)...
  - apply sub_capt...
------
  intros E F G S T Sub Ok.
  remember (G ++ E).
  generalize dependent G.
  induction Sub; intros G Ok EQ; subst.
  - Case "sub_top".
    apply sub_top...
  - Case "sub_arrow".
    pick fresh Y and apply sub_arrow...
    + rewrite <- concat_assoc.
      eapply wf_typ_weakening...
    + rewrite <- concat_assoc.
      eapply wf_typ_weakening...
    + rewrite <- concat_assoc.
      apply sub_weakening...
  - Case "sub_all".
    pick fresh Y and apply sub_all...
    + rewrite <- concat_assoc.
      eapply wf_typ_weakening...
    + rewrite <- concat_assoc.
      eapply wf_typ_weakening...
    + rewrite <- concat_assoc.
      apply sub_weakening...
Qed.

(* ********************************************************************** *)
(** ** Reflexivity (1) *)

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

Lemma sub_reflexivity : forall E Ap Am T,
  wf_env E ->
  wf_typ E Ap Am T ->
  AtomSet.F.Subset Ap (dom E) ->
  AtomSet.F.Subset Am (dom E) ->
  sub E T T
with sub_pre_reflexivity : forall E Ap Am T,
  wf_env E ->
  wf_pretyp E Ap Am T ->
  AtomSet.F.Subset Ap (dom E) ->
  AtomSet.F.Subset Am (dom E) ->
  sub_pre E T T.
Proof with eauto using subcapt_reflexivity, wf_typ_set_weakening.
------
  intros *.
  intros Ok Wf HsubsetAp HsubsetAm.
  induction Wf.
  (* eauto and econstructor is still broken... hence we need to proof this manually *)
  - apply sub_refl_tvar.
    auto.
    eapply wf_typ_var with (U := U)...
  - apply sub_capt...
------
  intros *.
  intros Ok Wf HsubsetAp HsubsetAm.
  induction Wf.
  - apply sub_top...
  - apply sub_arrow with (L := L `union` dom E)...
    intros; eapply sub_reflexivity...
  - apply sub_all with (L := L `union` dom E)...
    intros; eapply sub_reflexivity...
Qed.

(* ********************************************************************** *)
(** ** Narrowing and transitivity (3) *)

Lemma subcapt_narrowing_typ : forall F E x P Q C1 C2,
  sub E P Q ->
  wf_env (F ++ [(x, bind_typ Q)] ++ E) ->
  subcapt (F ++ [(x, bind_typ Q)] ++ E) C1 C2 ->
  subcapt (F ++ [(x, bind_typ P)] ++ E) C1 C2.
Proof with eauto using wf_cset_narrowing_typ, wf_env_narrowing_typ, wf_typ_narrowing_typ.
  intros * PsubQ Ok Hsc.
  dependent induction Hsc...
  - apply subcapt_universal...
  - apply subcapt_in...
  - destruct (x0 == x).
    + subst.
      replace T with Q in *.
      2: {
        forwards: binds_typ_unique T Q...
      }

      eapply subcapt_var with (T := P)...
      eapply (subcapt_transitivity ((cv Q)))...
      apply sub_implies_subcapt...
      rewrite_env (empty ++ (F ++ [(x, bind_typ P)]) ++ E).
      apply sub_weakening; simpl_env...
    + assert (binds x0 (bind_typ T) (F ++ [(x, bind_typ P)] ++ E)). {
        binds_cases H...
      }
      eapply subcapt_var...
  - assert (binds x0 (bind_sub T) (F ++ [(x, bind_typ P)] ++ E)). {
      binds_cases H...
    }
    eapply subcapt_tvar...
  - econstructor...
    intros ? ?...
Qed.

Lemma subcapt_narrowing : forall F E Z P Q C1 C2,
  sub E P Q ->
  wf_env (F ++ [(Z, bind_sub P)] ++ E) ->
  subcapt (F ++ [(Z, bind_sub Q)] ++ E) C1 C2 ->
  subcapt (F ++ [(Z, bind_sub P)] ++ E) C1 C2.
Proof with eauto 6 using wf_cset_narrowing, wf_env_narrowing, wf_typ_narrowing.
  intros * SubPQ WfE SubCap.

  dependent induction SubCap...
  - assert (binds x (bind_typ T) (F ++ [(Z, bind_sub P)] ++ E)). {
      binds_cases H...
    }
    eapply subcapt_var with (T := T)...
  - destruct (x == Z).
    + subst.
      replace T with Q in *.
      2: {
        forwards: binds_sub_unique T Q...
      }
      eapply subcapt_tvar with (T := P)...
      eapply (subcapt_transitivity (cv Q))...
      apply sub_implies_subcapt...
      rewrite_env (empty ++ (F ++ [(Z, bind_sub P)]) ++ E).
      apply sub_weakening; simpl_env...
    + assert (binds x (bind_sub T) (F ++ [(Z, bind_sub P)] ++ E)). {
        binds_cases H...
      }
      eapply subcapt_tvar...
  - econstructor...
    intros ? ?...
Qed.

Definition transitivity_on Q := forall E S T,
  sub E S Q -> sub E Q T -> sub E S T.

Definition transitivity_pre_on Q := forall E S T,
  sub_pre E S Q -> sub_pre E Q T -> sub_pre E S T.

Lemma sub_narrowing_aux : forall Q F E Z P S T,
  transitivity_on Q ->
  sub (F ++ [(Z, bind_sub Q)] ++ E) S T ->
  sub E P Q ->
  sub (F ++ [(Z, bind_sub P)] ++ E) S T
with sub_narrowing_pre_aux : forall Q F E Z P S T,
  transitivity_on Q ->
  sub_pre (F ++ [(Z, bind_sub Q)] ++ E) S T ->
  sub E P Q ->
  sub_pre (F ++ [(Z, bind_sub P)] ++ E) S T.
Proof with simpl_env; eauto using wf_typ_narrowing, wf_env_narrowing,
  wf_pretyp_narrowing, wf_cset_narrowing, subcapt_narrowing.
------
  intros Q F E Z P S T TransQ SsubT PsubQ.
  remember (F ++ [(Z, bind_sub Q)] ++ E). generalize dependent F.
  induction SsubT; intros F EQ; subst.
  - Case "sub_refl_tvar".
    apply sub_refl_tvar...
  - Case "sub_trans_tvar".
    destruct (X == Z); subst.
    + SCase "X = Z".
      apply (sub_trans_tvar P).
        apply binds_tail.
        apply binds_head; apply binds_singleton.
        eapply fresh_mid_head; apply ok_from_wf_env;
          apply (proj1 (sub_regular (F ++ [(Z, bind_sub Q)] ++ E) U T SsubT)).
      apply TransQ.
      SSCase "P <: Q".
        rewrite_env (empty ++ (F ++ [(Z, bind_sub P)]) ++ E).
        apply sub_weakening...
      SSCase "Q <: T".
        binds_get H.
        inversion H1; subst...
    + SCase "X <> Z".
      apply (sub_trans_tvar U)...
  - eapply sub_capt...
------
  intros Q F E Z P S T TransQ SsubT PsubQ.
  remember (F ++ [(Z, bind_sub Q)] ++ E). generalize dependent F.
  induction SsubT; intros F EQ; subst.
  - Case "sub_top".
    apply sub_top...
  - Case "sub_arrow".
    pick fresh Y and apply sub_arrow...
    + rewrite_parenthesise_binding.
      simpl_env in H2.
      eapply wf_typ_narrowing_base...
    + rewrite_parenthesise_binding.
      simpl_env in H3.
      eapply wf_typ_narrowing_base...
    + rewrite <- concat_assoc.
      eapply sub_narrowing_aux...
  - Case "sub_all".
    pick fresh Y and apply sub_all...
    + rewrite_parenthesise_binding.
      simpl_env in H2.
      eapply wf_typ_narrowing_base...
    + rewrite_parenthesise_binding.
      simpl_env in H3.
      eapply wf_typ_narrowing_base...
    + rewrite <- concat_assoc.
      eapply sub_narrowing_aux...
Qed.

Lemma empty_cset_union : forall C1 C2,
  cset_union C1 C2 = {} ->
  C1 = {} /\ C2 = {}.
Proof with eauto.
  intros.
  destruct C1; destruct C2; simpl in H; try discriminate.
  inversion H.
  split; f_equal.
  - destruct (AtomSet.F.choose (t `union` t1)) eqn:Eq.
    + assert (AtomSet.F.Equal (t `union` t1) {}A) as HA. {
        rewrite H1.
        fsetdec.
      }
      apply AtomSet.F.choose_1 in Eq.
      rewrite HA in Eq.
      exfalso.
      fsetdec.
    + apply AtomSet.F.choose_2 in Eq.
      assert (AtomSet.F.Empty t). {
        unfold AtomSet.F.Empty in *.
        unfold not in *.
        intros.
        apply (Eq a).
        fsetdec.
      }
      fsetdec.
  - destruct (NatSet.F.choose (NatSet.F.union t0 t2)) eqn:Eq.
    + assert (NatSet.F.Equal (NatSet.F.union t0 t2) {}N) as HA. {
        rewrite H2.
        fnsetdec.
      }
      apply NatSet.F.choose_1 in Eq.
      rewrite HA in Eq.
      exfalso.
      fnsetdec.
    + apply NatSet.F.choose_2 in Eq.
      assert (NatSet.F.Empty t0). {
        unfold NatSet.F.Empty in *.
        unfold not in *.
        intros.
        apply (Eq a).
        fnsetdec.
      }
      fnsetdec.
  - csetdec.
  - destruct (AtomSet.F.choose (t `union` t1)) eqn:Eq.
    + assert (AtomSet.F.Equal (t `union` t1) {}A) as HA. {
        rewrite H1.
        fsetdec.
      }
      apply AtomSet.F.choose_1 in Eq.
      rewrite HA in Eq.
      exfalso.
      fsetdec.
    + apply AtomSet.F.choose_2 in Eq.
      assert (AtomSet.F.Empty t1). {
        unfold AtomSet.F.Empty in *.
        unfold not in *.
        intros.
        apply (Eq a).
        fsetdec.
      }
      fsetdec.
  - destruct (NatSet.F.choose (NatSet.F.union t0 t2)) eqn:Eq.
    + assert (NatSet.F.Equal (NatSet.F.union t0 t2) {}N) as HA. {
        rewrite H2.
        fnsetdec.
      }
      apply NatSet.F.choose_1 in Eq.
      rewrite HA in Eq.
      exfalso.
      fnsetdec.
    + apply NatSet.F.choose_2 in Eq.
      assert (NatSet.F.Empty t2). {
        unfold NatSet.F.Empty in *.
        unfold not in *.
        intros.
        apply (Eq a).
        fnsetdec.
      }
      fnsetdec.
  - csetdec.
Qed.

Lemma sub_narrowing_typ_aux : forall Q F E x P S T,
  transitivity_on Q ->
  sub (F ++ [(x, bind_typ Q)] ++ E) S T ->
  sub E P Q ->
  sub (F ++ [(x, bind_typ P)] ++ E) S T
with sub_narrowing_pretyp_aux : forall Q F E x P S T,
  transitivity_on Q ->
  sub_pre (F ++ [(x, bind_typ Q)] ++ E) S T ->
  sub E P Q ->
  sub_pre (F ++ [(x, bind_typ P)] ++ E) S T.
Proof with simpl_env; eauto using wf_typ_narrowing_typ, wf_pretyp_narrowing_typ,
    wf_env_narrowing_typ, subcapt_narrowing_typ, wf_cset_narrowing_typ.
------
  intros Q F E x P S T TransQ SsubT PsubQ.
  remember (F ++ [(x, bind_typ Q)] ++ E). generalize dependent F.
  induction SsubT; intros F EQ; subst.
  - apply sub_refl_tvar...
  - apply sub_trans_tvar with (U := U)...
    binds_cases H.
    + apply binds_tail. apply binds_tail... auto.
    + apply binds_head...
  - apply sub_capt...
------
  intros Q F E x P S T TransQ SsubT PsubQ.
  remember (F ++ [(x, bind_typ Q)] ++ E). generalize dependent F.
  induction SsubT; intros F EQ; subst.
  - eapply sub_top...
  - pick fresh Y and apply sub_arrow...
    + rewrite_parenthesise_binding.
      simpl_env in H2.
      eapply wf_typ_narrowing_typ_base...
    + rewrite_parenthesise_binding.
      simpl_env in H3.
      eapply wf_typ_narrowing_typ_base...
    + rewrite <- concat_assoc.
      eapply sub_narrowing_typ_aux...
  - pick fresh Y and apply sub_all...
    + rewrite_parenthesise_binding.
      simpl_env in H2.
      eapply wf_typ_narrowing_typ_base...
    + rewrite_parenthesise_binding.
      simpl_env in H3.
      eapply wf_typ_narrowing_typ_base...
    + rewrite <- concat_assoc.
      eapply sub_narrowing_typ_aux...
Qed.

(* S <: Q    ->    Q <: T    ->    S <: T*)
Lemma sub_transitivity : forall Q E S T,
  type Q ->
  sub E S Q -> sub E Q T -> sub E S T
with sub_pre_transitivity : forall Q E S T,
  pretype Q ->
  sub_pre E S Q -> sub_pre E Q T -> sub_pre E S T.
Proof with simpl_env; auto.
------
  intros * W SsubQ QsubT.

  generalize dependent T.
  generalize dependent S.
  generalize dependent E.
  remember Q as Q' in |-.
  generalize dependent Q'.

  induction W; intros Q'' EQ E' S' SsubQ.

  Ltac inductionThenInversion Rel1 Rel2 :=
      induction Rel1; try discriminate; inversion EQ; subst; intros T' Rel2; inversion Rel2; subst.

  (* type_var *)
  - inductionThenInversion SsubQ QsubT; try solve [econstructor; eauto].
  (* type_capt *)
  - inductionThenInversion SsubQ QsubT; try solve [econstructor; eauto].
    apply sub_capt...
    apply (subcapt_transitivity C)...
    apply sub_pre_transitivity with (Q := P)...
------
  intros * W SsubQ QsubT.

  generalize dependent T.
  generalize dependent S.
  generalize dependent E.
  remember Q as Q' in |-.
  generalize dependent Q'.

  induction W; intros Q'' EQ E' S' SsubQ.

  Ltac inductionThenInversion2 Rel1 Rel2 :=
    induction Rel1; try discriminate; inversion EQ; subst; intros T' Rel2; inversion Rel2; subst.

  (* type_top *)
  - inductionThenInversion2 SsubQ QsubT; try solve [econstructor; eauto].

  (*  HERE `sub E S T2` is now missing! *)
  (* type_arrow *)
  - inductionThenInversion2 SsubQ QsubT.
  + eapply sub_top...
    (* wf_typ typ_arrow *)
    pick fresh X and apply wf_typ_arrow...
  + pick fresh Y and apply sub_arrow.
    all: trivial.
    (* SCase "bounds". *)
       auto using (sub_transitivity T1).
       assert (Y `notin` L1) by notin_solve...
       assert (Y `notin` L1) by notin_solve...
    SCase "bodies".
      lapply (H0 Y); [ intros K | auto ].
      assert (Y `notin` L0) by notin_solve.
      assert (Y `notin` L1) by notin_solve.
      apply sub_transitivity with (Q := (open_ct T2 (`cset_fvar` Y)))...
      rewrite_env (empty ++ [(Y, bind_typ T0)] ++ E).
      eapply sub_narrowing_typ_aux with (Q := T1)...
      unfold transitivity_on.
      auto using (sub_transitivity T1).
  (* type_all. *)
  - inductionThenInversion2 SsubQ QsubT.
  + apply sub_top...
    pick fresh X and apply wf_typ_all...
  + pick fresh Y and apply sub_all.
    all: trivial.
    SCase "bounds".
      apply sub_transitivity with (Q := T1)...
      assert (Y `notin` L1) by notin_solve...
      assert (Y `notin` L1) by notin_solve...
    SCase "bodies".
      lapply (H0 Y); [ intros K | auto ].
      apply sub_transitivity with (Q := (open_tt T2 Y))...
      rewrite_env (empty ++ [(Y, bind_sub T0)] ++ E).
      apply (sub_narrowing_aux T1)...
      unfold transitivity_on.
      auto using (sub_transitivity T1).
Admitted.

Lemma sub_narrowing : forall Q E F Z P S T,
  sub E P Q ->
  sub (F ++ [(Z, bind_sub Q)] ++ E) S T ->
  sub (F ++ [(Z, bind_sub P)] ++ E) S T.
Proof with auto.
  intros.
  eapply sub_narrowing_aux; eauto.
  unfold transitivity_on. intros.
  eapply sub_transitivity with (Q := Q)...
Qed.

Lemma sub_narrowing_typ : forall E F x P Q S T,
  sub (F ++ [(x, bind_typ Q)] ++ E) S T ->
  sub E P Q ->
  sub (F ++ [(x, bind_typ P)] ++ E) S T.
Proof with eauto using wf_typ_narrowing_typ.
  intros.
  eapply sub_narrowing_typ_aux; eauto.
  unfold transitivity_on. intros.
  eapply sub_transitivity with (Q := Q)...
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

(* ********************************************************************** *)
(** * #<a name="typing"></a># Properties of typing *)


(* ********************************************************************** *)
(** ** Weakening (5) *)

Lemma typing_weakening : forall E F G e T,
  typing (G ++ E) e T ->
  wf_env (G ++ F ++ E) ->
  typing (G ++ F ++ E) e T.
Proof with simpl_env;
           eauto using wf_typ_weakening,
                       wf_typ_from_wf_env_typ,
                       wf_typ_from_wf_env_sub,
                       sub_weakening,
                       subcapt_weakening.
  intros * Typ.
  remember (G ++ E).
  generalize dependent G.
  induction Typ; intros G EQ Ok; subst...
  - Case "typing_abs".
    pick fresh X and apply typing_abs...
    + lapply (H0 X); [intros K | auto].
      simpl_env in *.
      rewrite <- concat_assoc.
      eapply wf_typ_weakening.
      * apply K.
      * trivial...
      * clear_frees; fsetdec.
      * clear_frees; fsetdec.
    + lapply (H1 X); [intros K | auto].
      simpl_env in *.
      rewrite <- concat_assoc.
      apply (H2 X)...
  - Case "typing_tabs".
    pick fresh X and apply typing_tabs...
    + lapply (H0 X); [intros K | auto].
      simpl_env in *.
      rewrite <- concat_assoc.
      eapply wf_typ_weakening.
      * apply K.
      * trivial...
      * clear_frees; fsetdec.
      * clear_frees; fsetdec.
    + lapply (H1 X); [intros K | auto].
      simpl_env in *.
      rewrite <- concat_assoc.
      apply (H2 X)...
Qed.

(************************************************************************ *)
(** ** Narrowing for typing (7) *)

Lemma distinct_binding_from_wf_env : forall F x b E y,
  wf_env (F ++ [(x, b)] ++ E) ->
  y `in` dom E ->
  y `notin` dom F.
Proof.
  intros * H ?.
  induction F.
  - simpl_env; fsetdec.
  - inversion H; subst;
      specialize (IHF H3); simpl_env in *; fsetdec.
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
}
Qed.

Lemma wf_typ_preserved_by_subst_wf_cset : forall x C E Ap Am T,
  wf_env E ->
  Ap `c`A dom E ->
  Am `c`A dom E ->
  wf_typ E Ap Am T ->
  (x `notin` Am -> wf_cset E Ap C -> wf_typ E Ap Am (subst_ct x C T)) /\
  (x `notin` Ap -> wf_cset E Am C -> wf_typ E Ap Am (subst_ct x C T))
with wf_pretyp_preserved_by_subst_wf_cset : forall x C E Ap Am T,
  wf_env E ->
  Ap `c`A dom E ->
  Am `c`A dom E ->
  wf_pretyp E Ap Am T ->
  (x `notin` Am -> wf_cset E Ap C -> wf_pretyp E Ap Am (subst_cpt x C T)) /\
  (x `notin` Ap -> wf_cset E Am C -> wf_pretyp E Ap Am (subst_cpt x C T)).
Proof with eauto.
{ intros * ? ? ? WfT.
  generalize dependent Ap.
  generalize dependent Am.
  induction T; intros ? ? ? ? WfT.
  - simpl.
    split; intros ? WfC.
    + constructor.
      * unfold subst_cset.
        inversion WfT.
        destruct_if; eauto using wf_cset_union, wf_cset_remove_fvar.
      * inversion WfT; subst.
        unshelve epose proof (wf_pretyp_preserved_by_subst_wf_cset x C E Ap Am p _ _ _ _) as IH...
        apply (proj1 IH)...
    + constructor.
      * unfold subst_cset.
        inversion WfT; subst.
        destruct_if...
        inversion select (wf_cset _ _ c); subst.
        rewrite_set_facts_in Heqb.
        exfalso;fsetdec.
      * inversion WfT; subst.
        unshelve epose proof (wf_pretyp_preserved_by_subst_wf_cset x C E Ap Am p _ _ _ _) as IH...
        apply (proj2 IH)...
  - inversion WfT.
  - simpl...
}
{ intros * ? ? ? WfT.
  generalize dependent Ap.
  generalize dependent Am.
  induction T; intros ? ? ? ? WfT.
  - constructor...
  - wf_typ_inversion WfT.
    split; intros ? WfC.
    + pick fresh y and apply wf_typ_arrow; fold subst_ct...
      1: {
        unshelve epose proof (wf_typ_preserved_by_subst_wf_cset x C E Am Ap t _ _ _ _) as IH...
        apply (proj2 IH)...
      }
      specialize (H8 y ltac:(notin_solve)).
      apply (wf_typ_preserved_by_subst_wf_cset x C) in H8...
      rewrite subst_ct_open_ct_var ; [| notin_solve | eapply capt_from_wf_cset]...
      rewrite_nil_concat.
      eapply wf_typ_ignores_typ_bindings; simpl...
      apply (proj1 H8)...
      rewrite_nil_concat.
      eapply wf_cset_weakening; [ apply WfC | simpl_env; auto .. ].
    + pick fresh y and apply wf_typ_arrow; fold subst_ct...
      1: {
        unshelve epose proof (wf_typ_preserved_by_subst_wf_cset x C E Am Ap t _ _ _ _) as IH...
        apply (proj1 IH)...
      }
      specialize (H8 y ltac:(notin_solve)).
      apply (wf_typ_preserved_by_subst_wf_cset x C) in H8...
      rewrite subst_ct_open_ct_var ; [| notin_solve | eapply capt_from_wf_cset]...
      rewrite_nil_concat.
      eapply wf_typ_ignores_typ_bindings; simpl...
      apply (proj2 H8)...
      rewrite_nil_concat.
      eapply wf_cset_weakening; [ apply WfC | simpl_env; auto .. ].
  - wf_typ_inversion WfT.
    split; intros ? WfC.
    + pick fresh y and apply wf_typ_all; fold subst_ct...
      1: {
        unshelve epose proof (wf_typ_preserved_by_subst_wf_cset x C E Am Ap t _ _ _ _) as IH...
        apply (proj2 IH)...
      }
      specialize (H8 y ltac:(notin_solve)).
      apply (wf_typ_preserved_by_subst_wf_cset x C) in H8...
      rewrite subst_ct_open_tt_var ; [| notin_solve | eapply capt_from_wf_cset]...
      rewrite_nil_concat.
      eapply wf_typ_ignores_sub_bindings; simpl...
      apply (proj1 H8)...
      rewrite_nil_concat.
      eapply wf_cset_weakening; [ apply WfC | simpl_env; auto .. ].
    + pick fresh y and apply wf_typ_all; fold subst_ct...
      1: {
        unshelve epose proof (wf_typ_preserved_by_subst_wf_cset x C E Am Ap t _ _ _ _) as IH...
        apply (proj1 IH)...
      }
      specialize (H8 y ltac:(notin_solve)).
      apply (wf_typ_preserved_by_subst_wf_cset x C) in H8...
      rewrite subst_ct_open_tt_var ; [| notin_solve | eapply capt_from_wf_cset]...
      rewrite_nil_concat.
      eapply wf_typ_ignores_sub_bindings; simpl...
      apply (proj2 H8)...
      rewrite_nil_concat.
      eapply wf_cset_weakening; [ apply WfC | simpl_env; auto .. ].
}
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
        Ap
        Am x C D (open_tt T2 y) _ H0 _ _ _).
      * econstructor...
      (* we need to help fsetdec here a little *)
      * clear Fr; simpl; fsetdec.
      * clear Fr; simpl; fsetdec.
      * rewrite_env (empty ++ [(y, bind_sub (subst_ct x D T1))] ++ E).
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
                              Ap
                              Am x C D (open_tt T2 y) _ H0 _ _ _).
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
Admitted.

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

Lemma wf_typ_extract_typ_arrow : forall C E T1 T2,
  wf_typ_in E (typ_capt C (typ_arrow T1 T2)) ->
  exists L, forall x, x `notin` L ->
    wf_typ ([(x, bind_typ T1)] ++ E) (dom E `union` singleton x) (dom E) (open_ct T2 (`cset_fvar` x)).
Proof with eauto.
  intros * HWf.
  inversion HWf; subst.
  inversion H5; subst...
Qed.

Lemma typing_extract_typ_arrow : forall E e C T1 T2,
  typing E e (typ_capt C (typ_arrow T1 T2)) ->
  exists L, forall x, x `notin` L ->
    wf_typ ([(x, bind_typ T1)] ++ E) (dom E `union` singleton x) (dom E) (open_ct T2 (`cset_fvar` x)).
Proof with eauto.
  intros * Htyp.
  apply (wf_typ_extract_typ_arrow C)...
Qed.

Lemma applied_subst_monotonicity : forall E C1 C2 e D S T,
  subcapt E C1 C2 ->
  typing E e (typ_capt D (typ_arrow S T)) ->
  sub E (open_ct T C1) (open_ct T C2).
Proof with eauto.
  intros * Hsc Htyp.
  forwards (L & HRT): typing_extract_typ_arrow Htyp.
  pick fresh y.
  replace (open_ct T C1) with (subst_ct y C1 (open_ct T (`cset_fvar` y))).
  replace (open_ct T C2) with (subst_ct y C2 (open_ct T (`cset_fvar` y))).
  2,3: solve [symmetry; apply subst_ct_intro; fsetdec].
  forwards (_ & _ & Reg): typing_regular Htyp.
  wf_typ_inversion Reg.
  assert (wf_typ ([(y, bind_typ S)] ++ E)
                  (dom E `union` singleton y) (dom E)
                  (open_ct T (`cset_fvar` y))) by eauto.
  enough (sub ([(y, bind_typ S)] ++ E)
              (subst_ct y C1 (open_ct T (`cset_fvar` y)))
              (subst_ct y C2 (open_ct T (`cset_fvar` y)))). {
    rewrite_env (map (subst_cb y (cv S)) empty ++ E).
    replace (subst_ct y C1 (open_ct T (`cset_fvar` y)))
      with (subst_ct y (cv S) (subst_ct y C1 (open_ct T (`cset_fvar` y)))).
    replace (subst_ct y C2 (open_ct T (`cset_fvar` y)))
      with (subst_ct y (cv S) (subst_ct y C2 (open_ct T (`cset_fvar` y)))).
    2,3: solve [apply subst_ct_useless_repetition; notin_solve].
    apply sub_through_subst_ct with (U := S); simpl_env; auto.
    eapply subcapt_reflexivity.
    + apply cv_wf...
    + fsetdec.
  }
  eapply plain_subst_ct_monotonicity with (Ap := dom E `union` singleton y) (Am := dom E); eauto.
  - rewrite_nil_concat.
    apply subcapt_weakening; simpl_env; eauto.
  - forwards (WfC1 & _): subcapt_regular Hsc.
    rewrite_nil_concat.
    eapply wf_cset_weakening ; [ apply WfC1 | simpl_env; auto .. ].
  - forwards (_ & WfC2): subcapt_regular Hsc.
    rewrite_nil_concat.
    eapply wf_cset_weakening ; [ apply WfC2 | simpl_env; auto .. ].
Qed.

Lemma typing_narrowing : forall Q E F X P e T,
  sub E P Q ->
  typing (F ++ [(X, bind_sub Q)] ++ E) e T ->
  typing (F ++ [(X, bind_sub P)] ++ E) e T.
Proof with eauto 6 using wf_env_narrowing, wf_typ_narrowing, sub_narrowing, subcapt_narrowing.
  intros Q E F X P e T PsubQ Typ.
  remember (F ++ [(X, bind_sub Q)] ++ E).
  generalize dependent F.
  induction Typ; intros F EQ; subst...
  - Case "typing_var".
    binds_cases H0...
  - Case "typing_var".
    binds_cases H0...
  - Case "typing_abs".
    assert (wf_env (F ++ [(X, bind_sub P)] ++ E)). {
      pick fresh y for L.
      forwards (P0 & _): typing_regular (H1 y Fr).
      inversion P0; subst...
    }
    pick fresh y and apply typing_abs...
    + rewrite_parenthesise_binding.
      simpl_env in H0...
      eapply wf_typ_narrowing_base; simpl_env...
    + rewrite <- concat_assoc.
      apply H2...
  - Case "typing_tabs".
    assert (wf_env (F ++ [(X, bind_sub P)] ++ E)). {
      pick fresh y for L.
      forwards (P0 & _): typing_regular (H1 y Fr).
      inversion P0; subst...
    }
    pick fresh Y and apply typing_tabs...
    + rewrite_parenthesise_binding.
      simpl_env in H0...
      eapply wf_typ_narrowing_base; simpl_env...
    + rewrite <- concat_assoc.
      apply H2...
Qed.

(************************************************************************ *)
(** ** Free_for_cv lemmas *)

Lemma subst_commutes_with_free_for_cv : forall x u C e,
  x `notin` (`cset_fvars` (free_for_cv e)) ->
  (subst_cset x C (free_for_cv e)) = (free_for_cv (subst_ee x u C e)).
Proof with eauto.
  intros *.
  intro Fr.
  induction e.
  - simpl.
    unfold subst_cset.
    find_and_destroy_set_mem.
    + notin_solve.
    + easy.
  - simpl in *.
    assert (a <> x) by fsetdec.
    destruct (a == x); try easy.
    cbv.
    destruct_if.
    + rewrite <- AtomSetFacts.mem_iff in Heqb. exfalso. fsetdec.
    + reflexivity.
  - apply IHe...
  - simpl in *.
    pose proof (cv_free_never_universal e1).
    pose proof (cv_free_never_universal e2).
    destruct (free_for_cv e1); try easy.
    destruct (free_for_cv e2); try easy.
    rewrite <- IHe1...
    rewrite <- IHe2...
    rewrite subst_cset_distributive_across_union.
    reflexivity.
  - apply IHe...
  - apply IHe...
Qed.

Lemma free_for_cv_subst_ee_cset_irrelevancy: forall x u C D t,
  free_for_cv (subst_ee x u C t) =
  free_for_cv (subst_ee x u D t).
Proof.
  induction t.
  all : simpl; eauto.
  rewrite IHt1.
  rewrite IHt2.
  trivial.
Qed.

Lemma subst_te_idempotent_wrt_free_for_cv : forall e x C,
    free_for_cv (subst_te x C e) = free_for_cv e.
Proof with eauto.
  intros.
  induction e; simpl; eauto.
  rewrite IHe1.
  rewrite IHe2.
  easy.
Qed.

(************************************************************************ *)
(** ** Properties of values *)

Lemma value_therefore_fv_subcapt_cv : forall E t T,
  value t ->
  typing E t T ->
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
Qed.

Lemma values_have_precise_captures : forall E u T,
  value u ->
  typing E u T ->
  exists U, typing E u (typ_capt (free_for_cv u) U) /\ sub E (typ_capt (free_for_cv u) U) T.
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
Qed.

(************************************************************************ *)
(** ** Substitution preserves typing (8) *)

Hint Extern 1 (wf_pretyp ?E (dom ?E) (dom ?E) ?P) =>
match goal with
| H : typing E _ (typ_capt _ P) |- _ =>
  apply typing_regular in H;
  destruct H as [_ [_ H]];
  inversion H; subst; assumption
end : core.

Hint Extern 1 (wf_pretyp_in ?E ?P) =>
match goal with
| H : typing E _ (typ_capt _ P) |- _ =>
  apply typing_regular in H;
  destruct H as [_ [_ H]];
  inversion H; subst; assumption
end : core.

Lemma bind_typ_notin_fv_tt : forall x S E Ap Am T,
  binds x (bind_typ S) E ->
  wf_typ E Ap Am T ->
  x `~in`A fv_tt T
with bind_typ_notin_fv_tpt : forall x S E Ap Am T,
  binds x (bind_typ S) E ->
  wf_pretyp E Ap Am T ->
  x `~in`A fv_tpt T.
Proof with auto.
{ intros * Hbnd WfT.
  dependent induction T;simpl...
  - inversion WfT; subst.
    eapply bind_typ_notin_fv_tpt; eauto.
  - inversion WfT; subst.
    destruct (x == a); [|fsetdec].
    subst.
    forwards: binds_unique a; eauto.
}
{ intros * Hbnd WfT.
  dependent induction T; simpl.
  - fsetdec.
  - inversion WfT; subst.
    rename H4 into Wf__t.
    rename H5 into Wf__t0.
    pick fresh y.
    specialize (Wf__t0 y ltac:(fsetdec)).
    forwards: bind_typ_notin_fv_tt Wf__t; [eauto|..].
    forwards HA: bind_typ_notin_fv_tt x Wf__t0; [eauto|..].
    forwards: notin_fv_ct_open_tt HA.
    notin_solve.
  - inversion WfT; subst.
    rename H4 into Wf__t.
    rename H5 into Wf__t0.
    pick fresh y.
    specialize (Wf__t0 y ltac:(fsetdec)).
    forwards: bind_typ_notin_fv_tt Wf__t; [eauto|..].
    forwards HA: bind_typ_notin_fv_tt x Wf__t0; [eauto|..].
    forwards: notin_fv_tt_open_tt HA.
    notin_solve.
}
Qed.

Lemma typing_through_subst_ee : forall P E F x T e u,
  typing (F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E) e T ->
  value u ->
  typing E u (typ_capt (free_for_cv u) P) ->
  typing (map (subst_cb x (free_for_cv u)) F ++ E)
         (subst_ee x u (free_for_cv u) e)
         (subst_ct x (free_for_cv u) T).
Local Ltac hint ::=
  eauto 4 using wf_env_subst_cb, typing_cv.
Proof with hint.
  intros *.
  intros HtypT HvalU HtypU.
  assert (wf_env E) as HwfE. {
    apply wf_env_strengthening
      with (F := (F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))])); simpl_env...
  }
  assert (wf_cset_in E (free_for_cv u)) as HwfFv...
  assert (capt (free_for_cv u)) as HcaptFv. {
    eapply capt_from_wf_cset...
  }
  remember (F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E).
  generalize dependent F.
  induction HtypT; intros F EQ; subst; simpl subst_ee...

  - Case "typing_var_tvar".
    destruct (x0 == x); subst.
    + binds_get H0.
    + simpl.
      binds_cases H0...
      * apply typing_var_tvar...
        apply binds_head.
        replace (bind_typ X) with (subst_cb x (free_for_cv u) (bind_typ X))...
  - Case "typing_var".
    destruct (x0 == x); subst.
    + SCase "x0 = x".
      binds_get H0.
      inversion H2; subst.
      rewrite_nil_concat.
      apply typing_weakening; simpl_env...
      simpl.
      replace (subst_cset x (free_for_cv u) (`cset_fvar` x)) with (free_for_cv u).
      2: {
        unfold subst_cset.
        replace (AtomSet.F.mem x (singleton x)) with true by fset_mem_dec.
        replace (cset_set _ _ _) with {} by csetdec.
        destruct (free_for_cv u); csetdec.
      }

      replace (subst_cpt x (free_for_cv u) P) with P.
      2: {
        forwards: binding_uniq_from_wf_env H.
        pose proof (notin_fv_wf_pretyp E (dom E) (dom E) x P ltac:(auto) ltac:(notin_solve)).
        rewrite <- subst_cpt_fresh...
      }
      forwards: values_have_precise_captures E u (typ_capt (free_for_cv u) P); eauto*.
    + SCase "x0 <> x".
      binds_cases H0.
      * assert (x `notin` fv_cpt P). {
          assert (x `notin` dom E) as HA1. { eapply fresh_mid_tail... }
          forwards: wf_typ_from_binds_typ H0...
          assert (wf_pretyp_in E P) as HA2...
          forwards: notin_fv_wf_pretyp HA2 HA1...
        }
        replace (subst_ct x C (typ_capt (`cset_fvar` x0) P)) with (typ_capt (`cset_fvar` x0) P).
        2: {
          apply subst_ct_fresh; simpl_env...
        }
        rewrite_nil_concat.
        apply typing_weakening; simpl_env...
        simpl.
        rewrite <- (subst_cset_fresh x)...
        replace (subst_cpt x (free_for_cv u) P0) with P0.
        2: {
          apply wf_typ_from_binds_typ in H0 as WfP0...
          wf_typ_inversion WfP0.
          apply binding_uniq_from_wf_env in H as ?.
          pose proof (notin_fv_wf_pretyp E (dom E) (dom E) x P0 ltac:(auto) ltac:(notin_solve)).
          rewrite <- subst_cpt_fresh...
        }
        trivial...
      * simpl.
        rewrite <- (subst_cset_fresh x)...
        eapply typing_var...
        (* heavy environment wrangling ahead... *)
        assert (binds x0
                      (bind_typ (subst_ct x (free_for_cv u) (typ_capt C P0)))
                      (map (subst_cb x (free_for_cv u)) F)). {
          replace (bind_typ (subst_ct x (free_for_cv u) (typ_capt C P0)))
            with (subst_cb x (free_for_cv u) (bind_typ (typ_capt C P0))) by auto...
        }
        rewrite <- concat_nil.
        rewrite -> concat_assoc.
        apply binds_weaken.
        -- rewrite -> concat_nil...
        -- rewrite -> concat_nil...

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

    rewrite subst_ct_open_ct.
    3: {
      assert (wf_pretyp_in (F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E)
                           (typ_arrow T1 T2)) as HA0 by auto.
      forwards HA: bind_typ_notin_fv_tpt x HA0.
      1: trivial...
      simpl in HA...
    }
    2: trivial...
    rewrite <- cv_subst_ct_correspondence.
    2: {
      assert (wf_typ_in (F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E) T1') as HA by auto.
      forwards: bind_typ_notin_fv_tt HA...
    }
    simpl subst_ct in IHHtypT1...
    eapply typing_app...
    eapply sub_through_subst_ct...
    simpl.
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
    + assert (wf_typ_in (F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E) T) as HA by auto.
      applys bind_typ_notin_fv_tt HA...
  - Case "typing_sub".
    eapply typing_sub.
    + apply IHHtypT...
    + eapply sub_through_subst_ct...
      simpl.
      eapply subcapt_reflexivity...
Qed.

Lemma sub_of_tvar : forall E P (X : atom),
  sub E P X ->
  exists (Y : atom), P = Y.
Proof.
  intros * H.
  dependent induction H...
  * exists X; trivial.
  * exists X0; trivial.
Qed.

Inductive syn_cat_agree : typ -> typ -> Prop :=
| syn_cat_agree_tvar : forall (X Y : atom),
    syn_cat_agree X Y
| syn_cat_agree_concrete : forall C P D U,
    syn_cat_agree (typ_capt C P) (typ_capt D U)
.

Lemma typing_narrowing_typ : forall Q E F X P e T,
  typing (F ++ [(X, bind_typ Q)] ++ E) e T ->
  sub E P Q ->
  syn_cat_agree P Q ->
  typing (F ++ [(X, bind_typ P)] ++ E) e T.
Proof with simpl_env; eauto using
    wf_env_narrowing_typ, wf_typ_narrowing_typ, sub_narrowing_typ,
    sub_weakening, type_from_wf_typ.
  intros *. intros HT HSub HAg.
  assert (type P) as Htype by eauto*.
  dependent induction HT...
  (* typing_var_tvar *)
  - destruct (x == X) eqn:HX; subst...
    + binds_cases H0; simpl_env in *; try notin_solve...
      inversion H1; subst...
      lets (Y & HP): sub_of_tvar HSub; subst... (* lets signifies that all arguments are applied *)
      eapply typing_sub...
      * eapply typing_var_tvar...
      * rewrite_env (empty ++ (F ++ [(X, bind_typ Y)]) ++ E).
        apply sub_weakening...
    + eapply typing_var_tvar...
  (* typing_var *)
  - destruct (x == X) eqn:HX; subst...
    + dependent induction P; inversion Htype; subst...
      * binds_get H0; inversion H2; subst...
        eapply typing_sub.
        ** eapply typing_var...
        ** rewrite_env (empty ++ (F ++ [(X, bind_typ (typ_capt c p))]) ++ E).
           apply sub_capt.
           ++ eapply subcapt_reflexivity with (A := singleton X)...
              econstructor...
              intros X' HX'; assert (X = X') by fsetdec; subst.
              exists (typ_capt c p); constructor...
           ++ apply sub_pre_weakening...
              inversion HSub...
      * binds_get H0; inversion H2; subst...
        inversion HAg.
    + eapply typing_var...
  - assert (wf_env (F ++ [(X, bind_typ P)] ++ E)). {
      pick fresh z for L.
      pose proof (H1 z Fr)...
    }
    pick fresh y and apply typing_abs...
    + simpl_env in *.
      rewrite_parenthesise_binding.
      eapply wf_typ_narrowing_typ_base...
    + rewrite_parenthesise_binding.
      eapply H2...
  - assert (wf_env (F ++ [(X, bind_typ P)] ++ E)). {
      pick fresh z for L.
      pose proof (H1 z Fr)...
    }
    pick fresh y and apply typing_tabs...
    + simpl_env in *.
      rewrite_parenthesise_binding.
      eapply wf_typ_narrowing_typ_base...
    + rewrite_parenthesise_binding.
      eapply H2...
Qed.

Lemma typing_narrowing_typ_tvars : forall (X Y : atom) E F x e T,
  typing (F ++ [(x, bind_typ X)] ++ E) e T ->
  sub E Y X ->
  typing (F ++ [(x, bind_typ Y)] ++ E) e T.
Proof with eauto.
  intros.
  eapply typing_narrowing_typ...
  constructor.
Qed.

Lemma typing_narrowing_typ' : forall Q E F X C P e T,
  typing (F ++ [(X, bind_typ Q)] ++ E) e T ->
  sub E (typ_capt C P) Q ->
  typing (F ++ [(X, bind_typ (typ_capt C P))] ++ E) e T.
Proof with eauto.
  intros* ? Hsub.
  inversion Hsub; subst.
  eapply typing_narrowing_typ...
  constructor.
Qed.

Lemma typing_through_subst_ee' : forall U E Ap Am x T e u,
  typing ([(x, bind_typ U)] ++ E) e T ->
  wf_typ ([(x, bind_typ U)] ++ E) Ap Am T ->
  x `notin` Am ->
  Ap `subset` dom ([(x, bind_typ U)] ++ E) ->
  Am `subset` dom ([(x, bind_typ U)] ++ E) ->
  value u ->
  typing E u U ->
  wf_cset E Ap (free_for_cv u) ->
  wf_cset E Ap (cv U) ->
  typing E (subst_ee x u (free_for_cv u) e) (subst_ct x (cv U) T).
Proof with simpl_env; eauto.
  intros *.
  intros HtypT HwfT Hnotin HApRsnbl HAmRsnbl HvalU HtypU WfFvU WfC.
  assert (typing E (subst_ee x u (free_for_cv u) e) (subst_ct x (free_for_cv u) T))
    as Hthrough. {
    apply values_have_precise_captures in HtypU...
    destruct HtypU as [P [HtypP HsubP]].
    rewrite_env (map (subst_cb x (free_for_cv u)) empty ++ E).
    eapply (typing_through_subst_ee P)...
    rewrite_nil_concat.
    eapply typing_narrowing_typ'...
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
  - apply value_therefore_fv_subcapt_cv with (T := U)...
    rewrite_env (empty ++ [(x, bind_typ U)] ++ E);
      eapply typing_weakening...
  - rewrite_nil_concat.
    eapply wf_cset_weakening ; [ apply WfFvU | simpl_env; auto .. ].
  - rewrite_nil_concat.
    eapply wf_cset_weakening ; [ apply WfC | simpl_env; auto .. ].
Qed.

(************************************************************************ *)
(** ** Type substitution preserves typing (11) *)

Lemma free_for_cv_bound : forall E e (x : atom) S,
  typing E e S ->
  x A`in` (free_for_cv e) ->
  exists T, binds x (bind_typ T) E.
Proof with eauto using wf_cset_over_union, cv_free_never_universal.
  intros * Htyp xIn.
  induction Htyp; simpl in *...
  - assert (x = x0) by fsetdec; subst...
  - assert (x = x0) by fsetdec; subst...
  - pick fresh y.
    forwards HA: H2 y.
    + notin_solve.
    + forwards (? & ? & ?): free_for_cv_open e1 0 y.
      unfold open_ee.
      clear Fr;fsetdec.
    + destruct HA as (T & HA)...
      inversion HA.
      assert (x <> y) by notin_solve.
      destruct (x == y)...
      easy.
  - destruct_union_mem xIn...
  - pick fresh y.
    forwards HA: H2 y.
    + notin_solve.
    + forwards (? & ? & ?): free_for_cv_open_type e1 0 y.
      clear Fr;fsetdec.
    + destruct HA as (T & HA)...
      inversion HA.
      assert (x <> y) by notin_solve.
      destruct (x == y)...
      easy.
Qed.

Lemma subst_tt_open_ct_rec_straight : forall Z P k S T,
  type P ->
  subst_tt Z P (open_ct_rec k (cv S) T) = open_ct_rec k (cv (subst_tt Z P S)) (subst_tt Z P T)
with subst_tpt_open_cpt_rec_straight : forall Z P k S T,
  type P ->
  subst_tpt Z P (open_cpt_rec k (cv S) T) = open_cpt_rec k (cv (subst_tt Z P S)) (subst_tpt Z P T).
Proof with eauto with fsetdec.
{ intros * Typ.
  dependent induction T; cbn...
  - f_equal.
    2: apply subst_tpt_open_cpt_rec_straight...
    rewrite subst_cset_open_cset_rec by (apply type_implies_capt_cv;assumption).
    rewrite cv_subst_correspondence...
  - destruct (a == Z)...
    apply open_ct_rec_type...
}
{ intros * Typ.
  dependent induction T; cbn...
  - f_equal.
    + apply subst_tt_open_ct_rec_straight...
    + apply subst_tt_open_ct_rec_straight...
  - f_equal.
    + apply subst_tt_open_ct_rec_straight...
    + apply subst_tt_open_ct_rec_straight...
}
Qed.

Lemma typing_through_subst_te : forall Q E F Z e T P,
  typing (F ++ [(Z, bind_sub Q)] ++ E) e T ->
  sub E P Q ->
  typing (map (subst_tb Z P) F ++ E) (subst_te Z P e) (subst_tt Z P T).
Proof with simpl_env;
           eauto 6 using wf_env_subst_tb,
                         wf_typ_subst_tb,
                         sub_through_subst_tt.
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
      binds_cases H0...
      * assert (type P) as TypP...
        destruct TypP.
        -- set (P' := X) in *.
           assert (wf_env (map (subst_tb Z P') F ++ E)) as HA...
           rewrite (map_subst_tb_id E Z P') in HA;
             [ | auto | eapply fresh_mid_tail; eauto ].
           eapply typing_var_tvar...
           apply binds_map with (f := (subst_tb Z P')) in H0.
           simpl in H0.
           destruct (Z == Z); try easy.
           rewrite_env (empty ++ map (subst_tb Z P') F ++ map (subst_tb Z P') E).
           apply binds_weaken...
        -- assert (wf_env (map (subst_tb Z (typ_capt C P)) F ++ E)) as HA...
           rewrite (map_subst_tb_id E Z (typ_capt C P)) in HA;
             [ | auto | eapply fresh_mid_tail; eauto ].
           apply binds_map with (f := (subst_tb Z (typ_capt C P))) in H0.
           assert (binds x (subst_tb Z (typ_capt C P) (bind_typ Z))
                         (empty ++ map (subst_tb Z (typ_capt C P)) F ++
                                map (subst_tb Z (typ_capt C P)) E)) as HAbinds. {
             apply binds_weaken...
           }
           simpl in HAbinds.
           destruct (Z == Z); try easy.
           apply (typing_sub (typ_capt (`cset_fvar` x) P))...
           apply wf_typ_from_binds_typ in HAbinds as HAwfP...
           inversion HAwfP; subst.
           match goal with H : wf_pretyp _ _ _ P |- _ =>
             simpl_env in H
           end.
           apply sub_capt.
           ++ destruct C; eauto using wf_cset_from_binds, subcapt_from_binds.
           ++ let d :=
                  constr:(
                    dom (map (subst_tb Z (typ_capt C P)) F ++ map (subst_tb Z (typ_capt C P)) E))
              in apply sub_pre_reflexivity with (Ap := d) (Am := d)...
      * rewrite <- (map_subst_tb_id E Z P);
          [ | auto | eapply fresh_mid_tail; eauto ].
        assert (binds x (subst_tb Z P (bind_typ Z)) (map (subst_tb Z P) F)) as HA...
        simpl in HA.
        destruct (Z == Z); try easy.
        assert (type P) as Typ...
        destruct Typ. {
          apply typing_var_tvar...
        }
        eapply typing_sub. {
          eapply typing_var...
        }
        apply sub_capt.
        1: {
          eapply subcapt_from_binds...
        }
        let d := constr:(dom (map (subst_tb Z (typ_capt C P)) F ++ E))
        in apply sub_pre_reflexivity with (Ap := d) (Am := d)...
        apply sub_regular, proj2, proj1 in PsubQ.
        inversion PsubQ; subst.
        rewrite_nil_concat.
        eapply wf_pretyp_weakening; simpl_env.
        1: eauto.
        all: trivial...
    + subst.
      apply typing_var_tvar...
      rewrite (map_subst_tb_id E Z P);
        [ | auto | eapply fresh_mid_tail; eauto ].
      binds_cases H0...
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
      exfalso;congruence.
    }
    unfold subst_cset.
    find_and_destroy_set_mem; [exfalso;fsetdec|].
    apply typing_var with (C := (subst_cset Z (cv P) C))...
    rewrite (map_subst_tb_id E Z P);
      [ | auto | eapply fresh_mid_tail; eauto ].
    binds_cases H0.
    + enough (binds x (subst_tb Z P (bind_typ (typ_capt C P0))) (map (subst_tb Z P) E))...
    + enough (binds x (subst_tb Z P (bind_typ (typ_capt C P0))) (map (subst_tb Z P) (F ++ E))) as HA...
      simpl in HA.
      rewrite_env (map (subst_tb Z P) F ++ map (subst_tb Z P) E) in HA...
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
      forwards (U & Zbnd): free_for_cv_bound Z HA. {
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
      with (open_ct (subst_tt Z P T2) (cv (subst_tt Z P T1'))).
    2: symmetry; apply subst_tt_open_ct_rec_straight...
    eapply typing_app.
    + apply IHTyp1...
    + apply IHTyp2...
    + eapply sub_through_subst_tt...
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
      forwards (U & Zbnd): free_for_cv_bound Z HA. {
        rewrite subst_te_idempotent_wrt_free_for_cv.
        rewrite subst_te_idempotent_wrt_free_for_cv in ZIn.
        forwards (? & ? & ?): free_for_cv_open_type e1 0 y...
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
Qed.


(* ********************************************************************** *)
(** * #<a name="preservation"></a># Preservation *)


(* ********************************************************************** *)
(** ** Inversion of typing (13) *)

Lemma typing_inv_abs : forall E S1 e1 T,
  typing E (exp_abs S1 e1) T ->
  forall U1 U2 C, sub E T (typ_capt C (typ_arrow U1 U2)) ->
     sub E U1 S1
  /\ exists S2, exists L, forall x, x `notin` L ->
    typing ([(x, bind_typ S1)] ++ E) (open_ee e1 x (`cset_fvar` x)) (open_ct S2 (`cset_fvar` x)) /\
    wf_typ ([(x, bind_typ S1)] ++ E) (dom E `union` singleton x) (dom E) (open_ct U2 (`cset_fvar` x)) /\
    sub ([(x, bind_typ U1)] ++ E) (open_ct S2 (`cset_fvar` x)) (open_ct U2 (`cset_fvar` x)).
Proof with auto.
  intros * Htyp.
  dependent induction Htyp; intros U1 U2 C Hsub.
  - Case "typing_abs".
    inversion Hsub; subst.
    inversion select (sub_pre _ _ _); subst.
    split...
    exists T1.
    exists (L `union` L0).
    intros y ?.
    repeat split.
    + apply H1...
    + rewrite_nil_concat.
      eapply wf_typ_ignores_typ_bindings.
      apply H13...
    + trivial...
  - Case "typing_sub".
    eauto using (sub_transitivity T).
Qed.

Lemma typing_inv_tabs : forall E S1 e1 T,
  typing E (exp_tabs S1 e1) T ->
  forall U1 U2 C, sub E T (typ_capt C (typ_all U1 U2)) ->
     sub E U1 S1
  /\ exists S2, exists L, forall X, X `notin` L ->
     typing ([(X, bind_sub U1)] ++ E) (open_te e1 X) (open_tt S2 X)
     /\ sub ([(X, bind_sub U1)] ++ E) (open_tt S2 X) (open_tt U2 X).
Proof with simpl_env; auto.
  intros * Htyp.
  dependent induction Htyp; intros U1 U2 C Hsub.
  - Case "typing_abs".
    inversion Hsub; subst.
    inversion select (sub_pre _ _ _); subst.
    split...
    exists T1.
    exists (L `union` L0).
    intros y ?.
    repeat split...
    rewrite_env (empty ++ [(y, bind_sub U1)] ++ E).
    eapply typing_narrowing with (Q := S1)...
  - Case "typing_sub".
    eauto using (sub_transitivity T).
Qed.


(* ********************************************************************** *)
(** ** Preservation (20) *)


(* ********************************************************************** *)
(** * #<a name="progress"></a># Progress *)

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
           eapply (typing_narrowing_typ' T)...
           eauto using (sub_transitivity T1).

           (* lets (C & P & Eq): inversion_toplevel_type E T1'; subst... *)
           (* rewrite_nil_concat. *)
           (* eapply (typing_narrowing_typ' T)... *)
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

(** Variants for abort *)

Lemma valuesA_have_precise_captures : forall E u T,
  value_abort u ->
  binds abort (bind_typ (typ_capt {} (typ_all (typ_capt {*} typ_top) 0))) E ->
  typing E u T ->
  exists U, typing E u (typ_capt (free_for_cv u) U) /\ sub E (typ_capt (free_for_cv u) U) T.
Local Ltac hint ::=
  simpl; eauto*.
Proof with hint.
  intros * Hv Ha Htyp.
  assert (wf_cset_in E (free_for_cv u)) by eauto using typing_cv.
  assert (wf_env E) by auto.
  induction Htyp; try solve [inversion Hv; subst]...
  - inversion Hv; subst. exfalso.
    inversion Ha. inversion H2.
    rewrite H4 in *. inversion H5.
  - inversion Hv; subst.
    inversion Ha. inversion H2.
    rewrite H4 in *. inversion H5; subst...
    exists (typ_all (typ_capt {*} typ_top) 0); split...
    eapply sub_reflexivity with (Ap := dom E) (Am := dom E)...
    econstructor. econstructor...
    * intros x xAbort. assert (x = abort) by fsetdec; subst.
      exists (typ_capt {} (typ_all (typ_capt {*} typ_top) 0))...
    * apply binds_In in Ha...
    * pick fresh X and apply wf_typ_all...
      cbv [open_tt open_tt_rec]. destruct (0 === 0)...
      eapply wf_typ_var.
      admit. admit.
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
Admitted.

Lemma typing_through_subst_eeA : forall P E F x T e u,
  binds abort (bind_typ (typ_capt {} (typ_all (typ_capt {*} typ_top) 0))) E ->
  typing (F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E) e T ->
  value_abort u ->
  typing E u (typ_capt (free_for_cv u) P) ->
  typing (map (subst_cb x (free_for_cv u)) F ++ E)
         (subst_ee x u (free_for_cv u) e)
         (subst_ct x (free_for_cv u) T).
Local Ltac hint ::=
  eauto 4 using wf_env_subst_cb, typing_cv.
Proof with hint.
  intros *.
  intros BindsA HtypT HvalU HtypU.
  assert (wf_env E) as HwfE. {
    apply wf_env_strengthening
      with (F := (F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))])); simpl_env...
  }
  assert (wf_cset_in E (free_for_cv u)) as HwfFv...
  assert (capt (free_for_cv u)) as HcaptFv. {
    eapply capt_from_wf_cset...
  }
  remember (F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E).
  generalize dependent F.
  induction HtypT; intros F EQ; subst; simpl subst_ee...

  - Case "typing_var_tvar".
    destruct (x0 == x); subst.
    + binds_get H0.
    + simpl.
      binds_cases H0...
      * apply typing_var_tvar...
        apply binds_head.
        replace (bind_typ X) with (subst_cb x (free_for_cv u) (bind_typ X))...
  - Case "typing_var".
    destruct (x0 == x); subst.
    + SCase "x0 = x".
      binds_get H0.
      inversion H2; subst.
      rewrite_nil_concat.
      apply typing_weakening; simpl_env...
      simpl.
      replace (subst_cset x (free_for_cv u) (`cset_fvar` x)) with (free_for_cv u).
      2: {
        unfold subst_cset.
        replace (AtomSet.F.mem x (singleton x)) with true by fset_mem_dec.
        replace (cset_set _ _ _) with {} by csetdec.
        destruct (free_for_cv u); csetdec.
      }

      replace (subst_cpt x (free_for_cv u) P) with P.
      2: {
        forwards: binding_uniq_from_wf_env H.
        pose proof (notin_fv_wf_pretyp E (dom E) (dom E) x P ltac:(auto) ltac:(notin_solve)).
        rewrite <- subst_cpt_fresh...
      }
      forwards: valuesA_have_precise_captures E u (typ_capt (free_for_cv u) P); eauto*.
    + SCase "x0 <> x".
      binds_cases H0.
      * assert (x `notin` fv_cpt P). {
          assert (x `notin` dom E) as HA1. { eapply fresh_mid_tail... }
          forwards: wf_typ_from_binds_typ H0...
          assert (wf_pretyp_in E P) as HA2...
          forwards: notin_fv_wf_pretyp HA2 HA1...
        }
        replace (subst_ct x C (typ_capt (`cset_fvar` x0) P)) with (typ_capt (`cset_fvar` x0) P).
        2: {
          apply subst_ct_fresh; simpl_env...
        }
        rewrite_nil_concat.
        apply typing_weakening; simpl_env...
        simpl.
        rewrite <- (subst_cset_fresh x)...
        replace (subst_cpt x (free_for_cv u) P0) with P0.
        2: {
          apply wf_typ_from_binds_typ in H0 as WfP0...
          wf_typ_inversion WfP0.
          apply binding_uniq_from_wf_env in H as ?.
          pose proof (notin_fv_wf_pretyp E (dom E) (dom E) x P0 ltac:(auto) ltac:(notin_solve)).
          rewrite <- subst_cpt_fresh...
        }
        trivial...
      * simpl.
        rewrite <- (subst_cset_fresh x)...
        eapply typing_var...
        (* heavy environment wrangling ahead... *)
        assert (binds x0
                      (bind_typ (subst_ct x (free_for_cv u) (typ_capt C P0)))
                      (map (subst_cb x (free_for_cv u)) F)). {
          replace (bind_typ (subst_ct x (free_for_cv u) (typ_capt C P0)))
            with (subst_cb x (free_for_cv u) (bind_typ (typ_capt C P0))) by auto...
        }
        rewrite <- concat_nil.
        rewrite -> concat_assoc.
        apply binds_weaken.
        -- rewrite -> concat_nil...
        -- rewrite -> concat_nil...

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

    rewrite subst_ct_open_ct.
    3: {
      assert (wf_pretyp_in (F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E)
                           (typ_arrow T1 T2)) as HA0 by auto.
      forwards HA: bind_typ_notin_fv_tpt x HA0.
      1: trivial...
      simpl in HA...
    }
    2: trivial...
    rewrite <- cv_subst_ct_correspondence.
    2: {
      assert (wf_typ_in (F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E) T1') as HA by auto.
      forwards: bind_typ_notin_fv_tt HA...
    }
    simpl subst_ct in IHHtypT1...
    eapply typing_app...
    eapply sub_through_subst_ct...
    simpl.
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
    + assert (wf_typ_in (F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E) T) as HA by auto.
      applys bind_typ_notin_fv_tt HA...
  - Case "typing_sub".
    eapply typing_sub.
    + apply IHHtypT...
    + eapply sub_through_subst_ct...
      simpl.
      eapply subcapt_reflexivity...
Qed.

Lemma valueA_therefore_fv_subcapt_cv : forall E t T,
  binds abort (bind_typ (typ_capt {} (typ_all (typ_capt {*} typ_top) 0))) E ->
  value_abort t ->
  typing E t T ->
  subcapt E (free_for_cv t) (cv T).
Proof with subst; simpl; eauto.
  intros *.
  intros BindsA Hv Htyp.
  forwards (P1 & P2 & P3): typing_regular Htyp.
  induction Htyp; cbn [free_for_cv]; try solve [ inversion Hv ].
  - inversion Hv; inversion BindsA; inversion H0; subst; rewrite H3 in *; inversion H4.
  - inversion Hv; inversion BindsA; inversion H0; subst; rewrite H3 in *; inversion H4; subst.
    cbv [cv]. apply subcapt_reflexivity with (A := dom E)...
    (** todo : abort is in E dammit *)
    econstructor. 
    * intros x xIsAbort.
      assert (x = abort) by fsetdec; subst. exists (typ_capt {} (typ_all (typ_capt {*} typ_top) 0))...
    * apply binds_In in H0...
  - inversion P3; subst.
    apply subcapt_reflexivity with (A := dom E)...
  - inversion P3; subst.
    apply subcapt_reflexivity with (A := dom E)...
  - forwards: IHHtyp...
    apply (subcapt_transitivity (cv S))...
    eapply sub_implies_subcapt with (S := S) (T := T)...
Qed.

Lemma typing_through_subst_eeA' : forall U E Ap Am x T e u,
  binds abort (bind_typ (typ_capt {} (typ_all (typ_capt {*} typ_top) 0))) E ->
  typing ([(x, bind_typ U)] ++ E) e T ->
  wf_typ ([(x, bind_typ U)] ++ E) Ap Am T ->
  x `notin` Am ->
  Ap `subset` dom ([(x, bind_typ U)] ++ E) ->
  Am `subset` dom ([(x, bind_typ U)] ++ E) ->
  value_abort u ->
  typing E u U ->
  wf_cset E Ap (free_for_cv u) ->
  wf_cset E Ap (cv U) ->
  typing E (subst_ee x u (free_for_cv u) e) (subst_ct x (cv U) T).
Proof with simpl_env; eauto.
  intros *.
  intros BindsA HtypT HwfT Hnotin HApRsnbl HAmRsnbl HvalU HtypU WfFvU WfC.
  assert (typing E (subst_ee x u (free_for_cv u) e) (subst_ct x (free_for_cv u) T))
    as Hthrough. {
    apply valuesA_have_precise_captures in HtypU...
    destruct HtypU as [P [HtypP HsubP]].
    rewrite_env (map (subst_cb x (free_for_cv u)) empty ++ E).
    eapply (typing_through_subst_eeA P)...
    rewrite_nil_concat.
    eapply typing_narrowing_typ'...
  }
  eapply typing_sub.
  apply Hthrough.
  enough (sub ([(x, bind_typ U)] ++ E) (subst_ct x (free_for_cv u) T) (subst_ct x (cv U) T)) as HE. {
    rewrite_env (empty ++ [(x, bind_typ U)] ++ E) in HE.
    forwards HP: sub_through_subst_ct (free_for_cv u) HE.
    1: {
      forwards (? & _ & Hsub): valuesA_have_precise_captures u U...
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
  - apply valueA_therefore_fv_subcapt_cv with (T := U)...
    rewrite_env (empty ++ [(x, bind_typ U)] ++ E);
      eapply typing_weakening...
  - rewrite_nil_concat.
    eapply wf_cset_weakening ; [ apply WfFvU | simpl_env; auto .. ].
  - rewrite_nil_concat.
    eapply wf_cset_weakening ; [ apply WfC | simpl_env; auto .. ].
Qed.

Lemma preservation_abort : forall E e (e' : exp) T,
  no_type_bindings E ->
  binds abort (bind_typ (typ_capt {} (typ_all (typ_capt {*} typ_top) 0))) E ->
  typing E e T ->
  red_abort e e' ->
  typing E e' T.
Proof with simpl_env; eauto.
  intros * NoTypBnd BndA Typ. generalize dependent e'.
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
      apply typing_through_subst_eeA'
        with (U := T1')
            (Ap := dom ([(x, bind_typ T1')] ++ E))
            (Am := dom E) ...
      * apply (typing_sub (open_ct S2 (`cset_fvar` x)))...
        -- rewrite_nil_concat.
           forwards (U & HtypU & HsubU): valuesA_have_precise_captures e2; eauto.
           inversion HsubU; subst.
           eapply (typing_narrowing_typ' T)...
           eauto using (sub_transitivity T1).

           (* lets (C & P & Eq): inversion_toplevel_type E T1'; subst... *)
           (* rewrite_nil_concat. *)
           (* eapply (typing_narrowing_typ' T)... *)
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

Lemma canonical_form_absA : forall e U1 U2 C,
  value_abort e ->
  typing [(abort, bind_typ (typ_capt {} (typ_all (typ_capt {*} typ_top) 0)))] e (typ_capt C (typ_arrow U1 U2)) ->
  exists V, exists e1, e = exp_abs V e1.
Proof with eauto*.
  intros e U1 U2 C Val Typ.
  dependent induction Typ; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
  Case "typing_sub".
  inversion H0; subst; eauto.
  + binds_cases H0.
  + inversion H; subst... 
    * cbv [binds] in H0. exfalso. cbv [get] in H0; destruct (X == abort)...
    * inversion H5; subst.
      eapply IHTyp; eauto.
Qed.

Lemma canonical_form_tabsA : forall e U1 U2 C,
  value_abort e ->
  typing [(abort, bind_typ (typ_capt {} (typ_all (typ_capt {*} typ_top) 0)))] e (typ_capt C (typ_all U1 U2)) ->
  e = abort \/ exists V, exists e1, e = exp_tabs V e1.
Proof with eauto*.
  intros e U1 U2 C Val Typ.
  dependent induction Typ; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
  Case "typing_sub".
  inversion H0; subst; eauto.
  + binds_cases H0... left... 
  + inversion H; subst...
    * cbv [binds] in H0. exfalso. cbv [get] in H0; destruct (X == abort)...
    * inversion H5; subst.
      eapply IHTyp; eauto.
Qed.

Lemma progress_abort : forall e T,
  typing [(abort, bind_typ (typ_capt {} (typ_all (typ_capt {*} typ_top) 0)))] e T ->
  value_abort e \/ red_abort e aborted \/ (exists (e' : exp), red_abort e e').
Proof with eauto*.
  intros e T Typ.
  remember [(abort, bind_typ (typ_capt {} (typ_all (typ_capt {*} typ_top) 0)))].
  generalize dependent Heql.
  assert (Typ' : typing l e T)...
  induction Typ; intros EQ; subst...
  - Case "typing_var_1".
    inversion H0...
    destruct (x == abort)...
  - Case "typing_var_2".
    inversion H0...
    destruct (x == abort)...
    subst... left... econstructor...
  - Case "typing_tabs".
    left. econstructor.
    apply typing_regular in Typ'...
  - Case "typing_app_2".
    destruct IHTyp1 as [Val1 | [Aborted1 | [e1' Rede1']]]; subst...
    * (** e1 is a value, now we reduce e2 *)
      destruct IHTyp2 as [Val2 | [Aborted2 | [e2' Rede2']]]; subst...
      + (* e2 value *)
        right. right.
        unshelve epose proof (canonical_form_absA _ _ _ _ Val1 Typ1) as
          [S [e3  EQ]]; subst...
        ++ subst.
           exists (open_ee e3 e2 (free_for_cv e2))...
           eapply redA_abs...
      + (** e2 congruence *)
        right. left...
        apply redA_app_aborted_2...
      + right. right.
        exists (exp_app e1 e2')...
        apply redA_app_2...
    * (** e1 aborted *)
      right. left.
      apply redA_app_aborted_1...
    * (** e1 congruence *)
      right. right.
      exists (exp_app e1' e2).
      apply redA_app_1...
  - Case "typing_tabs".
    left. econstructor.
    apply typing_regular in Typ'...
  - Case "typing_tapp".
    destruct IHTyp as [Val | [Aborted | [e' Rede']]]; subst...
    * (** is a value *)
      right.
      unshelve epose proof (canonical_form_tabsA _ _ _ _ Val Typ) as
        [abort | [S [e3  EQ]]]; subst...
      ++ left. apply redA_tabs_abort.
      ++ right. subst.
         exists (open_te e3 T)...
         apply redA_tabs...
    * (** aborted *)
      right. left.
      econstructor...
    * (** e1 congruence *)
      right. right.
      exists (exp_tapp e' T).
      apply redA_tapp...
Qed.

