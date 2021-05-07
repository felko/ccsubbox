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
    AtomSet.F.In x (cset_fvars (free_for_cv e)) ->
    subst_cset x C (free_for_cv e) = cset_union C (cset_remove_fvar x (free_for_cv e)).
Proof.
  intros.
  unfold subst_cset.
  destruct_if.
  - reflexivity.
  - unfold cset_references_fvar_dec in Heqb.
    destruct (free_for_cv e) eqn:?.
    + pose proof (cv_free_never_universal e).
      easy.
    + rewrite_set_facts_in Heqb.
      unfold cset_fvars in H.
      fsetdec.
Qed.

Lemma notin_cset_fvars_distributive_over_cset_union : forall x C D,
  C <> cset_universal ->
  D <> cset_universal ->
  x `notin` cset_fvars (cset_union C D) ->
  x `notin` cset_fvars C /\
  x `notin` cset_fvars D.
Proof.
  intros.
  destruct C eqn:EQ__C;
    destruct D eqn:EQ__D;
    unfold cset_fvars, cset_union in *; split.
  all : (easy || fsetdec).
Qed.

Local Lemma subst_contratrivia2 : forall u x C e,
  x `notin` (cset_fvars (free_for_cv e)) ->
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
  AtomSet.F.In x (cset_fvars (free_for_cv e)) ->
  (cset_union (free_for_cv u) (cset_remove_fvar x (free_for_cv e))) =
        (free_for_cv (subst_ee x u (free_for_cv u) e)).
Proof with eauto using cv_free_never_universal.
  intros * Hin.
  induction e; simpl in *...
  - csetdec.
  - destruct (a == x) eqn:HX.
    + subst.
      csetdec.
      destruct (free_for_cv u)...
      f_equal...
      * fsetdec.
      * fnsetdec.
    + exfalso. apply n. fsetdec.
  - destruct (free_for_cv e1) eqn:?; destruct (free_for_cv e2) eqn:?; destruct (free_for_cv u) eqn:?;
      unfold cset_fvars in *; simpl in *; try fsetdec.
    + rewrite (AtomSetFacts.union_iff t t1 x) in Hin.
      destruct Hin.
      * specialize (IHe1 H).
        epose proof (cv_free_never_universal (subst_ee x u cset_universal e1)).
        symmetry in IHe1.
        contradiction.
      * specialize (IHe2 H).
        epose proof (cv_free_never_universal (subst_ee x u cset_universal e2)).
        symmetry in IHe2.
        contradiction.
      (* we only want to consider the case where all u, e1 and e2 have a concrete cv...  *)
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
        cset_eq_dec.
      * rewrite <- IHe1...
        rewrite <- (subst_contratrivia2 u x _ e2)...
        2: rewrite Heqc0; unfold cset_fvars; assumption.
        cbn [cset_union].
        rewrite Heqc0.
        cset_eq_dec.
      * rewrite <- IHe2...
        rewrite <- (subst_contratrivia2 u x _ e1)...
        2: rewrite Heqc; unfold cset_fvars; assumption.
        rewrite Heqc.
        cbn [cset_union].
        cset_eq_dec.
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
    apply notin_union.
    + apply notin_fv_wf_typ with (X := x) in H as ?.
      all: fsetdec.
    + pick fresh y.
      forwards SpH2: H2 y; [ notin_solve | simpl_env; notin_solve |..|].
      * specialize (H0 y ltac:(fsetdec)).
        specialize (H1 y ltac:(fsetdec)).
        do 2 rewrite_nil_concat.
        eapply wf_typ_weakening...
      * apply notin_fv_ee_open_te in SpH2...
  - cbn [fv_ee].
    apply notin_union...
    assert (wf_typ_in E T) as HA...
    apply notin_fv_wf_typ with (X := x) in HA as ?...
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
Proof with simpl_env; eauto using wf_typ_weakening, wf_pretyp_weakening, cv_weakening, subcapt_weakening, wf_cset_weakening.
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

(* if we have a subcapture of a concrete capture set, it has to be
   concrete as well. *)
Lemma subcapt_exists : forall E C tf tb,
  subcapt E C (cset_set tf tb) ->
  exists tf' tb', C = cset_set tf' tb'.
Proof with eauto.
  intros * H.
  remember (cset_set tf tb).
  induction H...
  inversion Heqc.
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


Lemma cv_strengthening : forall F E T C,
  wf_env (F ++ E) ->
  wf_typ_in E T ->
  cv (F ++ E) T C ->
  cv E T C.
Proof with eauto.
  intros * WfE WfT Cv.
  induction F...
  destruct a as (Y & B).
  simpl_env in *.
  forwards: cv_unique_shrink_head Cv...
  rewrite_env (empty ++ F ++ E).
  eapply wf_typ_weakening.
  1: apply WfT.
  2,3: trivial...
  apply ok_from_wf_env in WfE...
Qed.

Lemma subcapt_narrowing_typ : forall F E x P Q C1 C2,
  sub E P Q ->
  wf_env (F ++ [(x, bind_typ Q)] ++ E) ->
  subcapt (F ++ [(x, bind_typ Q)] ++ E) C1 C2 ->
  subcapt (F ++ [(x, bind_typ P)] ++ E) C1 C2.
Proof with eauto using wf_cset_narrowing_typ, wf_env_narrowing_typ, wf_typ_narrowing_typ.
  intros * PsubQ Ok Hsc.
  dependent induction Hsc...
  - apply subcapt_in...
  - destruct (x0 == x).
    + subst.
      replace T with Q in *.
      2: {
        forwards: binds_typ_unique T Q...
      }
      forwards (C' & HcvP): cv_exists_in E P...
      assert (cv E Q C) as HcvQ__small. {
        rewrite_env ((F ++ [(x, bind_typ Q)]) ++ E) in H0.
        apply cv_strengthening in H0...
      }
      assert (wf_cset_in E C)  as WfC by auto.
      assert (wf_cset_in E C') as WfC' by auto.
      forwards: sub_implies_subcapt P Q WfC' WfC...

      eapply subcapt_var with (T := P) (C := C')...
      1: {
        rewrite_env (empty ++ (F ++ [(x, bind_typ P)]) ++ E).
        apply cv_weakening; simpl_env...
      }
      eapply subcapt_transitivity with (C2 := C)...
      rewrite_env (empty ++ (F ++ [(x, bind_typ P)]) ++ E).
      apply subcapt_weakening; simpl_env...
    + assert (binds x0 (bind_typ T) (F ++ [(x, bind_typ P)] ++ E)). {
        binds_cases H...
      }
      eapply subcapt_var...
      forwards: wf_typ_from_binds_typ Q...
      forwards: wf_typ_narrowing_typ Q P Q...
      forwards HcvQ__narr: cv_narrowing_typ Q C...
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
  - forwards (? & ? & ?): cv_regular H0...
    forwards (C' & HcvC'): cv_exists_in (F ++ [(Z, bind_sub P)] ++ E) T; simpl_env in *...
    forwards: cv_narrowing T C' C...
    assert (binds x (bind_typ T) (F ++ [(Z, bind_sub P)] ++ E)). {
      binds_cases H...
    }
    eapply subcapt_var with (T := T)...
    eapply subcapt_transitivity with (C2 := C)...
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
  unfold empty_cset.
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
    wf_env_narrowing_typ, cv_narrowing_typ, subcapt_narrowing_typ, wf_cset_narrowing_typ.
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
  intros Q E S T W SsubQ QsubT.

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
    apply subcapt_transitivity with (C2 := C)...
    apply sub_pre_transitivity with (Q := P)...
------
  intros Q E S T W SsubQ QsubT.

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
      apply sub_transitivity with (Q := (open_ct T2 Y))...
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
Qed.

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

Lemma wf_cset_atom_union : forall E A xs ys,
  wf_cset E A (cset_set xs {}N) ->
  wf_cset E A (cset_set ys {}N) ->
  (xs `union` ys) `subset` A ->
  wf_cset E A (cset_set (xs `union` ys) {}N).
Proof with eauto.
  intros * WfXs WfYs SSet.
  inversion WfXs; inversion WfYs; subst.
  constructor...
  intros ? ?.
  rewrite AtomSetFacts.union_iff in *.
  auto*.
Qed.

Lemma subcapt_expansion : forall E C D1 D2,
  wf_cset_in E D2 ->
  subcapt E C D1 ->
  subcapt E C (cset_union D1 D2).
Proof with eauto using wf_cset_union, wf_cset_atom_union with fsetdec.
  intros * HwfD2 Hsubcapt.
  induction Hsubcapt.
  - simpl.
    destruct D2...
  - inversion HwfD2; simpl; subst...
    replace (NatSet.F.union _ _) with {}N by fnsetdec.
    inversion H0; subst.
    apply subcapt_in...
  - eapply subcapt_var...
  - apply subcapt_set...
    intros ? ?...
Qed.

Ltac destruct_union_mem H :=
  rewrite AtomSetFacts.union_iff in H; destruct H.

Tactic Notation "subst_mem_singleton" hyp(H) :=
  rewrite AtomSetFacts.singleton_iff in H; subst.

Tactic Notation "subst_mem_singleton" "<-" hyp(H) :=
  rewrite AtomSetFacts.singleton_iff in H; symmetry in H; subst.

Lemma subcapt_union_distributivity : forall E C1 C2 D,
  subcapt E C1 D ->
  subcapt E C2 D ->
  subcapt E (cset_union C1 C2) D.
Proof with eauto using wf_cset_union with fsetdec.
  intros * HscC1 HscC2.
  assert (wf_cset_in E (cset_union C1 C2)) by auto using wf_cset_union.
  generalize dependent C2.
  dependent induction HscC1; intros C2 HscC2 Wf__union...
  - note (wf_cset_in E C2)...
    simpl in *; replace (NatSet.F.union _ _) with {}N by fnsetdec.
    rename fvars into cs.
    apply subcapt_set...
    intros y yIn.
    destruct_union_mem yIn. {
      subst_mem_singleton H4.
      apply subcapt_in...
    }
    inversion HscC2; subst.
    + apply subcapt_in...
    + subst_mem_singleton H4.
      eapply subcapt_var...
    + trivial...
  - note (wf_cset_in E D)...
    note (wf_cset_in E C2)...
    simpl in *; replace (NatSet.F.union _ _) with {}N in * by fnsetdec.
    rename fvars into ds.
    rename fvars0 into cs.
    apply subcapt_set...
    intros y yIn.
    destruct_union_mem yIn. {
      subst_mem_singleton H5.
      eapply subcapt_var...
    }
    inversion HscC2; subst.
    * apply subcapt_in...
    * subst_mem_singleton <- H5.
      eapply subcapt_var...
    * trivial...
  - note (wf_cset_in E D)...
    note (wf_cset_in E C2)...
    simpl in *; replace (NatSet.F.union _ _) with {}N in * by fnsetdec.
    rename fvars into ds.
    rename fvars0 into cs.
    apply subcapt_set...
    intros y yIn.
    destruct_union_mem yIn. {
      trivial...
    }

    inversion HscC2; subst.
    * apply subcapt_in...
    * subst_mem_singleton H6.
      eapply subcapt_var...
    * trivial...
Qed.

Lemma cset_union_symmetrical : forall C D,
  cset_union C D = cset_union D C.
Proof with eauto.
  intros.
  destruct C; destruct D; simpl; try easy.
  apply cset_eq_injectivity; [fsetdec|fnsetdec].
Qed.

Lemma union_under_subcapturing : forall E C1 C2 D1 D2,
  subcapt E C1 C2 ->
  subcapt E D1 D2 ->
  subcapt E (cset_union C1 D1) (cset_union C2 D2).
Proof with eauto.
  intros *.
  intros Hsc1 Hsc2.
  apply subcapt_union_distributivity.
  - apply subcapt_expansion...
  - rewrite cset_union_symmetrical.
    apply subcapt_expansion...
Qed.

Lemma cv_through_subst_tt_exists : forall Q X P T E G C,
  wf_env (G ++ [(X, bind_sub Q)] ++ E) ->
  wf_typ_in (G ++ [(X, bind_sub Q)] ++ E) T ->
  cv (G ++ [(X, bind_sub Q)] ++ E) T C ->
  sub E P Q ->
  exists D, cv (map (subst_tb X P) G ++ E) (subst_tt X P T) D /\ subcapt (map (subst_tb X P) G ++ E) D C.
Proof with eauto using wf_env_subst_tb, wf_pretyp_subst_tb, wf_cset_subst_tb.
  intros * Hwf_env Hwf_typ HcvWide Hsub.
  (* assert (type T) as Typ by (eapply type_from_wf_typ; eauto). *)
  dependent induction HcvWide.
  (* Variable Case *)
  - forwards (D & Cv' & Subcapt): IHHcvWide H0 Hsub; [eauto .. |].
    simpl; destruct (X0 == X); subst; simpl in *; simpl_env in *.
    + forwards (C & Cv): cv_exists_in E P...
      assert (cv (map (subst_tb X P) G ++ E) P C). {
        rewrite_nil_concat.
        apply cv_weakening; simpl_env...
      }
      exists C. split...
      binds_get H. inversion H3; subst.
      (* WORK IN E HERE!!! *)
      rewrite_nil_concat.
      (*  since we know that P and Q are wellformed in E we can shrink and widen! *)
      apply subcapt_weakening; simpl_env...
      assert (cv E P C). {
        apply cv_unique_shrink with (F := map (subst_tb X P) G)...
      }
      assert (cv (map (subst_tb X P) G ++ E) Q CT). {
        assert (wf_typ_in E Q) by auto.
        apply cv_weakening_head...
        apply cv_unique_shrink with (F := G ++ [(X, bind_sub Q)]); simpl_env...
      }
      assert (cv E Q CT). {
        apply cv_unique_shrink with (F := map (subst_tb X P) G)...
      }

      eapply sub_implies_subcapt with (S := P) (T := Q) (A1 := dom E) (A2 := dom E); simpl_env...
    + binds_cases H.
      * assert (wf_typ_in E T). {
          eapply wf_typ_from_binds_sub...
        }
        exists CT. split.
        -- eapply cv_typ_var...
           rewrite_nil_concat.
           apply cv_weakening; simpl_env...
           apply cv_unique_shrink with (F := (G ++ [(X, bind_sub Q)])); simpl_env...
        -- eapply subcapt_reflexivity...
      * forwards (D2 & Cv2 & Subcapt2): IHHcvWide H0 Hsub; [eauto ..|].
        simpl_env...
        exists D2. split... eapply cv_typ_var with (T := (subst_tt X P T))...

  (* Capt Case *)
  - inversion Hwf_typ; subst.
    simpl. exists C. split...
    + eapply cv_typ_capt...
      * eapply (wf_pretyp_in_subst_tb Q)...
      * eapply (wf_cset_in_subst_tb Q)...
    + eapply subcapt_reflexivity with (A := dom ((map (subst_tb X P) G ++ E)))...
      (* same problem with wf_cset_subst_tb as above *)
      eapply (wf_cset_in_subst_tb Q)...
Qed.

Lemma cv_through_subst_tt : forall Q X P T E G C D,
  wf_env (G ++ [(X, bind_sub Q)] ++ E) ->
  wf_typ_in (G ++ [(X, bind_sub Q)] ++ E) T ->
  cv (G ++ [(X, bind_sub Q)] ++ E) T C ->
  cv (map (subst_tb X P) G ++ E) (subst_tt X P T) D ->
  sub E P Q ->
  subcapt (map (subst_tb X P) G ++ E) D C.
Proof with eauto.
  intros * Hwf_env Hwf_typ HcvWide HcvNarr Hsub.
  forwards (D' & HcvD & HscD): (>> cv_through_subst_tt_exists Q X P T E G C)...
  assert (D' = D). {
    apply (cv_unique (map (subst_tb X P) G ++ E) (subst_tt X P T))...
  }
  subst.
  assumption.
Qed.

Lemma subcapt_through_subst_tt : forall E P Q G X C D,
  wf_env (G ++ [(X, bind_sub Q)] ++ E) ->
  subcapt (G ++ [(X, bind_sub Q)] ++ E) C D ->
  sub E P Q ->
  subcapt (map (subst_tb X P) G ++ E) C D.
Proof with eauto using wf_env_subst_tb, wf_cset_in_subst_tb, wf_typ_in_subst_tb.
  intros * Hwf H Hsub.
  dependent induction H...
  - constructor...
  - binds_cases H.
    + assert (T = (subst_tt X P T)) as EQ__T. {
        rewrite <- subst_tt_fresh; [trivial|].
        enough (X `notin` (fv_tt T `union` fv_et T)) by fsetdec.
        forwards: wf_typ_from_binds_typ H...
        eapply (notin_fv_wf_typ E)...
        eapply fresh_mid_tail...
      }
      forwards (C' & HcvC'): cv_exists_in (map (subst_tb X P) G ++ E) (subst_tt X P T)...
      forwards: cv_through_subst_tt H0 HcvC'...
      rewrite <- EQ__T in HcvC'.
      eapply subcapt_var with (T := T)...
      apply subcapt_transitivity with (C2 := C)...
    + assert (binds x (bind_typ (subst_tt X P T)) (map (subst_tb X P) G ++ E)) by auto.
      forwards (C' & HcvC'): cv_exists_in (map (subst_tb X P) G ++ E) (subst_tt X P T)...
      forwards: cv_through_subst_tt H0 HcvC'...
      eapply subcapt_var with (T := (subst_tt X P T))...
      apply subcapt_transitivity with (C2 := C)...
  - apply subcapt_set...
    intros y yIn.
    eapply H1.
    3: reflexivity.
    all: auto.
Qed.

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
    + apply sub_reflexivity with (Ap := dom E) (Am := dom E)...
      inversion H0; subst.
      rename select (binds X _ _) into BndX.
      binds_cases BndX...
      enough (binds X (subst_tb Z P (bind_sub U)) (map (subst_tb Z P) F ++ E))...
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
      apply (wf_typ_set_strengthen Z Q) in H2...
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
      apply (wf_typ_set_strengthen Z Q) in H3...
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
      apply (wf_typ_set_strengthen Z Q) in H2...
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
      apply (wf_typ_set_strengthen Z Q) in H3...
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
                       subcapt_weakening,
                       cv_weakening.
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
  - Case "typing_app".
    eapply typing_app.
    + apply IHTyp1...
    + apply IHTyp2...
    + apply sub_weakening...
    + apply cv_weakening...
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

Definition subst_atoms z ys xs :=
  if AtomSet.F.mem z xs then
    ys `union` (xs `remove` z)
  else
    xs.

Lemma subst_atoms_rel_subst_subst_cset : forall x ys zs,
  (cset_set (subst_atoms x ys zs) {}N) = (subst_cset x (cset_set ys {}N) (cset_set zs {}N)).
Proof.
  intros.
  unfold subst_cset, subst_atoms, cset_references_fvar_dec.
  destruct (AtomSet.F.mem x zs); cset_eq_dec.
Qed.

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

Lemma cv_implies_bvars_empty : forall E U xs ns,
  cv E U (cset_set xs ns) -> ns = {}N.
Proof.
  intros * Cv.
  apply cv_regular, proj2, proj2 in Cv.
  inversion Cv...
  easy.
Qed.

Ltac rewrite_empty_bvars_from_cv H :=
  let H' := fresh "H" in
  lets H': cv_implies_bvars_empty H;
  (* pose proof (cv_implies_bvars_empty _ _ _ _ H) as H'; *)
  rewrite H' in *; clear H'.

Lemma subst_cset_across_subcapt : forall E x C D C0 A,
  wf_env E ->
  wf_cset E A C0 ->
  A `subset` dom E ->
  subcapt E C D ->
  subcapt E (subst_cset x C C0) (subst_cset x D C0).
Proof with eauto.
  intros * WfEnv Wf Subset Sub.
  remember C0.
  inversion Wf; subst. {
    unfold subst_cset, cset_references_fvar_dec...
  }
  rename fvars into zs.

  note (wf_cset_in E C). {
    inversion Sub; subst.
    unfold subst_cset.
    destruct_if; simpl; eapply subcapt_reflexivity...
  }
  rename fvars into cs.

  note (wf_cset_in E D). {
    unfold subst_cset.
    destruct_if; simpl.
    - constructor...
      inversion Wf; subst.
      change (cset_set (cs `union` zs `remove` x) (NatSet.F.union {}N {}N))
        with (cset_union (cset_set cs {}N) (cset_set (zs `remove` x) {}N)).
      apply wf_cset_union...
      change (cset_set (zs `remove` x) {}N)
        with (cset_remove_fvar x (cset_set zs {}N)).
      apply wf_cset_remove_fvar...
    - eapply subcapt_reflexivity...
  }
  rename fvars into ds.

  inversion Sub; subst.
  - unfold subst_cset, cset_references_fvar_dec.
    destruct_set_mem x zs; simpl.
    2: {
      eapply subcapt_reflexivity...
    }
    rewrite elim_empty_nat_set.
    assert (wf_cset_in E (cset_set (ds `union` zs `remove` x) {}N)). {
      replace (cset_set (ds `union` zs `remove` x) {}N)
        with (cset_union (cset_set ds {}N) (cset_remove_fvar x (cset_set zs {}N))).
      2: {
        simpl; rewrite elim_empty_nat_set...
      }
      apply wf_cset_union...
      apply wf_cset_remove_fvar...
    }
    apply subcapt_set...
    intros y yIn.
    destruct_union_mem yIn. {
      apply subcapt_in...
      fsetdec.
    }
    apply subcapt_in...
    2: fsetdec.
    apply wf_cset_singleton_by_mem with (xs := (ds `union` zs `remove` x))...
    fsetdec.
  - unfold subst_cset, cset_references_fvar_dec.
    destruct_set_mem x zs; simpl.
    2: eapply subcapt_reflexivity...
    rewrite elim_empty_nat_set.

    assert (wf_cset_in E (cset_set (ds `union` zs `remove` x) {}N)). {
      replace (cset_set (ds `union` zs `remove` x) {}N)
        with (cset_union (cset_set ds {}N) (cset_remove_fvar x (cset_set zs {}N))).
      2: simpl; rewrite elim_empty_nat_set...

      apply wf_cset_union...
      apply wf_cset_remove_fvar...
    }

    apply subcapt_set...
    intros y yIn.
    destruct_union_mem yIn. {
      subst_mem_singleton H8.
      eapply subcapt_var...
      replace (cset_set (ds `union` zs `remove` x) {}N)
        with (cset_union (cset_set ds {}N) (cset_set (zs `remove` x) {}N)).
      2: simpl; rewrite elim_empty_nat_set...

      apply subcapt_expansion...
      change (cset_set (zs `remove` x) {}N)
        with (cset_remove_fvar x (cset_set zs {}N)).
      apply wf_cset_remove_fvar...
    }

    apply subcapt_in; trivial.
    2: fsetdec.
    apply wf_cset_singleton_by_mem with (xs := (ds `union` zs `remove` x))...
    fsetdec.
  - unfold subst_cset, cset_references_fvar_dec.
    destruct_set_mem x zs; simpl.
    2: eapply subcapt_reflexivity...
    rewrite elim_empty_nat_set.

    assert (wf_cset_in E (cset_set (ds `union` zs `remove` x) {}N)). {
      replace (cset_set (ds `union` zs `remove` x) {}N)
        with (cset_union (cset_set ds {}N) (cset_remove_fvar x (cset_set zs {}N))).
      2: simpl; rewrite elim_empty_nat_set...

      apply wf_cset_union...
      apply wf_cset_remove_fvar...
    }

    apply subcapt_set...
    intros y yIn.
    destruct_union_mem yIn. {
      replace (cset_set (ds `union` zs `remove` x) {}N)
        with (cset_union (cset_set ds {}N) (cset_remove_fvar x (cset_set zs {}N))).
      2: simpl; rewrite elim_empty_nat_set...

      apply subcapt_expansion...
      apply wf_cset_remove_fvar...
    }

    apply subcapt_in; trivial.
    2: fsetdec.
    apply wf_cset_singleton_by_mem with (xs := (ds `union` zs `remove` x))...
    fsetdec.
Qed.

Lemma sub_through_subst_ct : forall E F x U C S T,
  sub (F ++ [(x, bind_typ U)] ++ E) S T ->
  cv E U C ->
  sub (map (subst_cb x C) F ++ E) (subst_ct x C S) (subst_ct x C T)
with sub_pre_through_subst_cpt : forall E F x U C P Q,
  sub_pre (F ++ [(x, bind_typ U)] ++ E) Q P ->
  cv E U C ->
  sub_pre (map (subst_cb x C) F ++ E) (subst_cpt x C Q) (subst_cpt x C P).
Proof with eauto using wf_env_subst_cb, wf_typ_in_subst_cb_cv, subcapt_through_subst_cset.
  { intros *.
    intros Hsub HcvU.
    remember (F ++ [(x, bind_typ U)] ++ E).
    generalize dependent F.
    induction Hsub; intros F EQ; subst.
    - simpl.
      apply sub_refl_tvar...
      unsimpl (subst_ct x C X)...
    - simpl.
      destruct (x == X). {
        subst.
        binds_get H.
      }
      SCase "x <> X".
      binds_cases H.
      + assert (x `notin` fv_et U0) as FrXinU0. {
          apply wf_typ_from_binds_sub in H as HA; [|auto .. ].
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
  { intros * Hsub HcvU.
    remember (F ++ [(x, bind_typ U)] ++ E).
    generalize dependent F.
    induction Hsub; intros F EQ; subst.
    - simpl.
      apply sub_top...
      eapply wf_pretyp_in_subst_cb_cv...
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
        eapply (wf_typ_subst_cb_cv U); simpl_env...
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
        eapply (wf_typ_subst_cb_cv U); simpl_env...
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
        eapply (wf_typ_subst_cb_cv U); simpl_env...
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
        eapply (wf_typ_subst_cb_cv U); simpl_env...
      + specialize (H4 y ltac:(notin_solve)).
        rewrite subst_ct_open_tt_var...
        rewrite subst_ct_open_tt_var...
        rewrite_env (map (subst_cb x C) ([(y, bind_sub T1)] ++ F) ++ E).
        eapply sub_through_subst_ct; simpl_env...
  }
Qed.

Lemma wf_typ_preserved_by_subst_wf_cset : forall x C E Ap Am T,
  wf_env E ->
  Ap `subset` dom E ->
  Am `subset` dom E ->
  wf_typ E Ap Am T ->
  (x `notin` Am -> wf_cset E Ap C -> wf_typ E Ap Am (subst_ct x C T)) /\
  (x `notin` Ap -> wf_cset E Am C -> wf_typ E Ap Am (subst_ct x C T))
with wf_pretyp_preserved_by_subst_wf_cset : forall x C E Ap Am T,
  wf_env E ->
  Ap `subset` dom E ->
  Am `subset` dom E ->
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
        inversion H8; subst.
        {
          simpl; unfold cset_union; destruct_match; constructor...
        }
        unfold cset_references_fvar_dec in Heqb.
        rewrite_set_facts_in Heqb.
        exfalso.
        fsetdec.
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
  intros *.
  intros HwfE Typ SubAp SubAm HwfT Hsc.
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
  intros *.
  intros HwfE Typ SubAp SubAm HwfT Hsc.
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
        Am x C D (open_ct T2 y) _ H0 _ _ _).
      * econstructor...
      (* we need to help fsetdec here a little *)
      * clear Fr. simpl. fsetdec.
      * clear Fr. simpl. fsetdec.
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
        Am x C D (open_ct T2 y) _ H0 _ _ _).
      * econstructor...
      (* we need to help fsetdec here a little *)
      * clear Fr. simpl. fsetdec.
      * clear Fr. simpl. fsetdec.
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
      * clear Fr. simpl. fsetdec.
      * clear Fr. simpl. fsetdec.
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
      * clear Fr. simpl. fsetdec.
      * clear Fr. simpl. fsetdec.
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

Lemma wf_typ_extract_typ_arrow : forall C E T1 T2,
  wf_typ_in E (typ_capt C (typ_arrow T1 T2)) ->
  exists L, forall x, x `notin` L ->
     wf_typ ([(x, bind_typ T1)] ++ E) (dom E `union` singleton x) (dom E) (open_ct T2 x).
Proof with eauto.
  intros *.
  intro HWf.
  inversion HWf; subst.
  inversion H5; subst...
Qed.

Lemma typing_extract_typ_arrow : forall E e C T1 T2,
  typing E e (typ_capt C (typ_arrow T1 T2)) ->
  exists L, forall x, x `notin` L ->
     wf_typ ([(x, bind_typ T1)] ++ E) (dom E `union` singleton x) (dom E) (open_ct T2 x).
Proof with eauto.
  intros *.
  intro Htyp.
  apply (wf_typ_extract_typ_arrow C)...
Qed.

Lemma applied_subst_monotonicity : forall E C1 C2 e D S T,
  subcapt E C1 C2 ->
  typing E e (typ_capt D (typ_arrow S T)) ->
  sub E (open_ct T C1) (open_ct T C2).
Proof.
  intros *. intros Hsc Htyp.
  forwards (L & HRT): typing_extract_typ_arrow Htyp.
  pick fresh y.
  replace (open_ct T C1) with (subst_ct y C1 (open_ct T y)).
  replace (open_ct T C2) with (subst_ct y C2 (open_ct T y)).
  2,3: solve [symmetry; apply subst_ct_intro; fsetdec].
  forwards (_ & _ & Reg): typing_regular Htyp.
  wf_typ_inversion Reg.
  assert (wf_typ ([(y, bind_typ S)] ++ E)
                  (dom E `union` singleton y) (dom E)
                  (open_ct T y)) by eauto.
  enough (sub ([(y, bind_typ S)] ++ E)
              (subst_ct y C1 (open_ct T y))
              (subst_ct y C2 (open_ct T y))). {
    assert (wf_typ_in E S) as HwfS by assumption.
    forwards (C_S & ?): cv_exists_in E S; auto.
    rewrite_env (map (subst_cb y C_S) empty ++ E).
    replace (subst_ct y C1 (open_ct T y))
      with (subst_ct y C_S (subst_ct y C1 (open_ct T y))).
    replace (subst_ct y C2 (open_ct T y))
      with (subst_ct y C_S (subst_ct y C2 (open_ct T y))).
    2,3: solve [apply subst_ct_useless_repetition; notin_solve].
    apply sub_through_subst_ct with (U := S); simpl_env; auto.
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
Proof with eauto 6 using wf_env_narrowing, wf_typ_narrowing, sub_narrowing, subcapt_narrowing, cv_narrowing.
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
  - Case "typing_app".
    pose proof (cv_exists_in (F ++ [(X, bind_sub P)] ++ E) T1') as Ex.
    destruct Ex as [Cnarrow HCVnarrow]...
    apply wf_typ_narrowing with (Q := Q)...
    eapply typing_sub with (S := (open_ct T2 Cnarrow))...
    forwards Subcapt: cv_narrowing PsubQ H0 HCVnarrow.
    specialize (IHTyp1 F ltac:(auto)).

    eapply applied_subst_monotonicity.
    + assumption.
    + eauto.
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
    x `notin` (cset_fvars (free_for_cv e)) ->
    (subst_cset x C (free_for_cv e)) = (free_for_cv (subst_ee x u C e)).
Proof with eauto.
  intros *.
  intro Fr.
  induction e.
  - simpl.
    unfold subst_cset, cset_references_fvar_dec. simpl.
    destruct_if.
    + rewrite <- AtomSetFacts.mem_iff in Heqb. notin_solve.
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
    unfold cset_union, cset_fvars in Fr.
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


Lemma value_therefore_fv_subcapt_cv : forall E t T C,
  value t ->
  typing E t T ->
  cv E T C ->
  subcapt E (free_for_cv t) C.
Proof with subst; simpl; eauto.
  intros *.
  intros Hv Htyp Hcv.
  generalize dependent C.
  forwards (P1 & P2 & P3): typing_regular Htyp.
  induction Htyp; intros C0 Hcv; cbn [free_for_cv]; try solve [ inversion Hv ].
  - inversion Hcv; subst.
    apply subcapt_reflexivity with (A := dom E)...
  - inversion Hcv; subst.
    apply subcapt_reflexivity with (A := dom E)...
  - forwards (D & HcvS): cv_exists_in E S P1...
    forwards: IHHtyp Hv D HcvS...
    apply subcapt_transitivity with (C2 := D)...
    eapply sub_implies_subcapt with (S := S) (T := T)
                                    (A1 := dom E) (A2 := dom E)...
Qed.

Lemma value_typing_inv : forall E v T,
  value v ->
  typing E v T ->
  exists C, exists P, sub E (typ_capt C P) T.
Proof with eauto using typing_cv.
  intros * Val Typ.
  assert (wf_env E) by auto.
  assert (wf_cset_in E (free_for_cv v)) by eauto using typing_cv.
  induction Typ; inversion Val; subst...
  - exists (free_for_cv e1). exists (typ_arrow V T1).
    eapply sub_reflexivity with (Ap := dom E) (Am := dom E)...
  - exists (free_for_cv e1). exists (typ_all V T1).
    eapply sub_reflexivity with (Ap := dom E) (Am := dom E)...
  - destruct IHTyp as [C [P]]...
    exists C. exists P. apply sub_transitivity with (Q := S)...
  - destruct IHTyp as [C [P]]...
    exists C. exists P. apply sub_transitivity with (Q := S)...
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
end.

Hint Extern 1 (wf_pretyp_in ?E ?P) =>
match goal with
| H : typing E _ (typ_capt _ P) |- _ =>
  apply typing_regular in H;
  destruct H as [_ [_ H]];
  inversion H; subst; assumption
end.

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
      replace (subst_cset x (free_for_cv u) x) with (free_for_cv u).
      2: {
        unfold subst_cset, cset_references_fvar_dec, cset_fvar.
        replace (AtomSet.F.mem x (singleton x)) with true by fset_mem_dec.
        unfold cset_remove_fvar.
        replace (cset_set _ _) with {} by cset_eq_dec.
        destruct (free_for_cv u).
        - unfold cset_union.
          destruct_match; reflexivity.
        - unfold cset_union, empty_cset.
          cset_eq_dec.
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
      * assert (x `notin` fv_ept P). {
          assert (x `notin` dom E) as HA1. { eapply fresh_mid_tail... }
          forwards: wf_typ_from_binds_typ H0...
          assert (wf_pretyp_in E P) as HA2...
          forwards: notin_fv_wf_pretyp HA2 HA1...
        }
        replace (subst_ct x C (typ_capt x0 P)) with (typ_capt x0 P).
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
        ** rewrite -> concat_nil...
        ** rewrite -> concat_nil...

  - Case "typing_abs".
    assert (wf_env (F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E)) as HwfNarrE. {
      pick fresh z for L.
      pose proof (H1 z Fr)...
      enough (wf_env
                ([(z, bind_typ V)] ++ F ++
                                   [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E)) as HwfHugeE...
      inversion HwfHugeE...
    }
    pose proof HwfNarrE as HxUniq.
    apply binding_uniq_from_wf_env in HxUniq.
    assert (wf_typ_in (F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E) V). {
      pick fresh z for L.
      pose proof (H1 z Fr) as HtypE1...
    }

    simpl subst_ct.
    destruct (AtomSet.F.mem x (cset_fvars (free_for_cv e1))) eqn:EqMem.
    + SCase "x in fv e1".
      assert (x `in` cset_fvars (free_for_cv e1)) by (rewrite AtomSetFacts.mem_iff; assumption).
      rewrite subst_trivia1...
      rewrite subst_trivia2 with (u := u)...
      pick fresh y and apply typing_abs...
      * eapply wf_typ_in_subst_cb_cv...
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
      assert (x `notin` cset_fvars (free_for_cv e1)) by (rewrite AtomSetFacts.not_mem_iff; assumption).
      rewrite subst_commutes_with_free_for_cv with (u := u)...
      pick fresh y and apply typing_abs...
      * eapply wf_typ_in_subst_cb_cv...
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
    simpl subst_ct in IHHtypT1...
    eapply typing_app...
    + eapply sub_through_subst_ct...
    + eapply cv_through_subst_ct...

  - Case "typing_tabs".
    assert (wf_env (F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E)) as HwfNarrE. {
      pick fresh z for L.
      pose proof (H1 z Fr)...
      enough (wf_env
                ([(z, bind_sub V)] ++ F ++
                                   [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E)) as HwfHugeE...
      inversion HwfHugeE...
    }
    pose proof HwfNarrE as HxUniq.
    apply binding_uniq_from_wf_env in HxUniq.
    assert (wf_typ_in (F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E) V). {
      pick fresh z for L.
      pose proof (H1 z Fr) as HtypE1...
    }

    simpl subst_ct.
    destruct (AtomSet.F.mem x (cset_fvars (free_for_cv e1))) eqn:EqMem.
    + SCase "x in fv e1".
      assert (x `in` cset_fvars (free_for_cv e1)) by (rewrite AtomSetFacts.mem_iff; assumption).
      rewrite subst_trivia1...
      rewrite subst_trivia2 with (u := u)...
      pick fresh y and apply typing_tabs...
      * eapply wf_typ_in_subst_cb_cv...
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
      assert (x `notin` cset_fvars (free_for_cv e1)) by (rewrite AtomSetFacts.not_mem_iff; assumption).
      rewrite subst_commutes_with_free_for_cv with (u := u)...
      pick fresh y and apply typing_tabs...
      * eapply wf_typ_in_subst_cb_cv...
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
  - Case "typing_sub".
    eapply typing_sub.
    + apply IHHtypT...
    + eapply sub_through_subst_ct...
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
    wf_env_narrowing_typ, wf_typ_narrowing_typ, cv_narrowing_typ, sub_narrowing_typ,
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
              unfold allbound_typ; intros X' HX'; assert (X = X') by fsetdec; subst.
              eexists...
           ++ apply sub_pre_weakening...
              inversion HSub...
      * binds_get H0; inversion H2; subst...
        inversion HAg.
    + eapply typing_var...
  - assert (wf_env (F ++ [(X, bind_typ P)] ++ E)). {
      pick fresh z for L.
      pose proof (H1 z Fr)...
      enough (wf_env
                ([(z, bind_typ V)] ++ F ++ [(X, bind_typ Q)] ++ E)) as HwfHugeE...
      inversion HwfHugeE...
    }
    pick fresh y and apply typing_abs...
    + simpl_env in *.
      rewrite_parenthesise_binding.
      eapply wf_typ_narrowing_typ_base...
    + rewrite_parenthesise_binding.
      eapply H2...
  - eapply typing_app.
    1: eapply IHHT1...
    1: eapply IHHT2...
    all: trivial...
  - assert (wf_env (F ++ [(X, bind_typ P)] ++ E)). {
      pick fresh z for L.
      pose proof (H1 z Fr)...
      enough (wf_env
                ([(z, bind_sub V)] ++ F ++ [(X, bind_typ Q)] ++ E)) as HwfHugeE...
      inversion HwfHugeE...
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

Lemma typing_through_subst_ee' : forall U E Ap Am x T C e u,
  typing ([(x, bind_typ U)] ++ E) e T ->
  wf_typ ([(x, bind_typ U)] ++ E) Ap Am T ->
  x `notin` Am ->
  Ap `subset` dom ([(x, bind_typ U)] ++ E) ->
  Am `subset` dom ([(x, bind_typ U)] ++ E) ->
  value u ->
  typing E u U ->
  cv E U C ->
  wf_cset E Ap (free_for_cv u) ->
  wf_cset E Ap C ->
  typing E (subst_ee x u (free_for_cv u) e) (subst_ct x C T).
Proof with simpl_env; eauto.
  intros *.
  intros HtypT HwfT Hnotin HApRsnbl HAmRsnbl HvalU HtypU HcvU WfFvU WfC.
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
  enough (sub ([(x, bind_typ U)] ++ E) (subst_ct x (free_for_cv u) T) (subst_ct x C T)) as HE. {
    rewrite_env (empty ++ [(x, bind_typ U)] ++ E) in HE.
    lets HP: sub_through_subst_ct HE HcvU.
    simpl_env in HP.
    lets (WfE & _): typing_regular HtypT.
    rewrite_env (empty ++ [(x, bind_typ U)] ++ E) in WfE.
    lets: binding_uniq_from_wf_env WfE.
    simpl_env in WfE.
    assert (x `notin` (fv_ee u)). {
      eapply notin_dom_is_notin_fv_ee...
      notin_solve.
    }
    assert (x `notin` (cset_fvars (free_for_cv u))). {
      lets HA: free_for_cv_is_free_ee u.
      inversion HA.
      subst.
      unfold cset_fvars.
      fsetdec.
    }
    assert (x `notin` (cset_fvars C)). {
      lets (_ & _ & WfC'): cv_regular HcvU.
      inversion WfC'; subst.
      - unfold cset_fvars; fsetdec.
      - unfold cset_fvars. notin_solve.
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
    rewrite_env (empty ++ [(x, bind_typ U)] ++ E);
      eapply cv_weakening...
  - rewrite_nil_concat.
    eapply wf_cset_weakening ; [ apply WfFvU | simpl_env; auto .. ].
  - rewrite_nil_concat.
    eapply wf_cset_weakening ; [ apply WfC | simpl_env; auto .. ].
Qed.

(************************************************************************ *)
(** ** Type substitution preserves typing (11) *)

Lemma wf_cset_from_binds : forall b x E,
  wf_env E ->
  binds x (bind_typ b) E ->
  wf_cset_in E x.
Proof.
  intros.
  econstructor.
  - unfold allbound_typ.
    intros x0 HIn.
    rewrite AtomSetFacts.singleton_iff in HIn.
    subst.
    eauto.
  - apply binds_In in H0.
    fsetdec.
Qed.

Lemma subcapt_from_binds : forall P x C E,
  wf_env E ->
  binds x (bind_typ (typ_capt C P)) E ->
  subcapt E x C.
Proof with eauto.
  intros* ? Binds.
  eapply wf_cset_from_binds in Binds as WfC...
  destruct C...
  eapply wf_typ_from_binds_typ in Binds as WfT...
  inversion WfT;
    inversion select (wf_cset _ _ _);
    subst.
  apply subcapt_set...
  unfold AtomSet.F.For_all.
  intros x0 HIn.
  rewrite AtomSetFacts.singleton_iff in HIn.
  symmetry in HIn.
  subst.
  eapply subcapt_var...
  eapply subcapt_reflexivity...
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
           apply (typing_sub (typ_capt x P))...
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
        destruct Typ.
        -- apply typing_var_tvar...
        -- eapply typing_sub.
           ++ eapply typing_var...
           ++ apply sub_capt.
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
    apply typing_var with (C := C)...
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
      enough (wf_env ([(z, bind_typ V)] ++ F ++ [(Z, bind_sub Q)] ++ E)) as HwfHugeE...
      inversion HwfHugeE...
    }
    replace (free_for_cv e1) with (free_for_cv (subst_te Z P e1)).
    2: { rewrite subst_te_idempotent_wrt_free_for_cv... }
    pick fresh y and apply typing_abs.
    + eapply wf_typ_in_subst_tb...
    + specialize (H0 y ltac:(notin_solve)).
      rewrite subst_tt_open_ct_var...
      rewrite_env (map (subst_tb Z P) ([(y, bind_typ V)] ++ F) ++ E).
      apply binding_uniq_from_wf_env in HwfNarrE as ?.
      assert (y `notin` (dom F `union` singleton Z `union` dom E)) by notin_solve.
      eapply (wf_typ_set_strengthen Z Q) in H0.
      2: {
        apply binds_tail. apply binds_tail.
        all: trivial...
      }
      simpl_env in H0.
      apply wf_typ_subst_tb with (Q := Q).
      * apply (wf_typ_adapt H0); clear Fr; fsetdec.
      * apply sub_regular, proj2, proj1 in PsubQ.
        eapply wf_typ_set_weakening.
        -- apply PsubQ.
        -- apply ok_from_wf_env, ok_tail, ok_tail in HwfNarrE.
           assumption.
        -- clear Fr; fsetdec.
        -- clear Fr; fsetdec.
      * apply sub_regular, proj2, proj1 in PsubQ.
        eapply wf_typ_set_weakening.
        -- apply PsubQ.
        -- apply ok_from_wf_env, ok_tail, ok_tail in HwfNarrE.
           assumption.
        -- clear Fr; fsetdec.
        -- clear Fr; fsetdec.
      * pose proof (H1 y ltac:(notin_solve))...
    + rewrite_env (map (subst_tb Z P) ([(y, bind_typ V)] ++ F) ++ E).
      rewrite subst_te_open_ee_var...
      rewrite subst_tt_open_ct_var...
      unshelve eapply (H2 y _ ([(y, bind_typ V)] ++ F) _)...
  - Case "typing_app".
    forwards: IHTyp2 F...
    forwards SpIHTyp1: IHTyp1 F...
    forwards (D & HcvD): cv_exists_in (map (subst_tb Z P) F ++ E) (subst_tt Z P T1')...
    assert (wf_typ_in (map (subst_tb Z P) F ++ E)
                      (typ_capt Cf (typ_arrow (subst_tt Z P T1) (subst_tt Z P T2))))...
    forwards (? & ?): cv_exists_in (map (subst_tb Z P) F ++ E) (subst_tt Z P T1)...
    + apply (wf_typ_in_subst_tb Q)...
    + rewrite <- open_ct_subst_tt...
      apply (typing_sub (open_ct (subst_tt Z P T2) D))...

      eapply applied_subst_monotonicity.
      * apply cv_through_subst_tt with (Q := Q) (T := T1')...
      * apply SpIHTyp1.
  - Case "typing_tabs".
    assert (wf_env (F ++ [(Z, bind_sub Q)] ++ E)) as HwfNarrE. {
      pick fresh z for L.
      pose proof (H1 z Fr)...
      enough (wf_env ([(z, bind_sub V)] ++ F ++ [(Z, bind_sub Q)] ++ E)) as HwfHugeE...
      inversion HwfHugeE...
    }
    replace (free_for_cv e1) with (free_for_cv (subst_te Z P e1)).
    2: { rewrite subst_te_idempotent_wrt_free_for_cv... }
    pick fresh Y and apply typing_tabs.
    + eapply wf_typ_in_subst_tb...
    + specialize (H0 Y ltac:(notin_solve)).
      rewrite subst_tt_open_tt_var...
      rewrite_env (map (subst_tb Z P) ([(Y, bind_sub V)] ++ F) ++ E).
      apply binding_uniq_from_wf_env in HwfNarrE as ?.
      assert (Y `notin` (dom F `union` singleton Z `union` dom E)) by notin_solve.
      eapply (wf_typ_set_strengthen Z Q) in H0.
      2: {
        apply binds_tail. apply binds_tail.
        all: trivial...
      }
      simpl_env in H0.
      apply wf_typ_subst_tb with (Q := Q).
      * apply (wf_typ_adapt H0); clear Fr; fsetdec.
      * apply sub_regular, proj2, proj1 in PsubQ.
        eapply wf_typ_set_weakening.
        -- apply PsubQ.
        -- apply ok_from_wf_env, ok_tail, ok_tail in HwfNarrE.
           assumption.
        -- clear Fr; fsetdec.
        -- clear Fr; fsetdec.
      * apply sub_regular, proj2, proj1 in PsubQ.
        eapply wf_typ_set_weakening.
        -- apply PsubQ.
        -- apply ok_from_wf_env, ok_tail, ok_tail in HwfNarrE.
           assumption.
        -- clear Fr; fsetdec.
        -- clear Fr; fsetdec.
      * pose proof (H1 Y ltac:(notin_solve))...
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
     typing ([(x, bind_typ S1)] ++ E) (open_ee e1 x x) (open_ct S2 x) /\
     wf_typ ([(x, bind_typ S1)] ++ E) (dom E `union` singleton x) (dom E) (open_ct U2 x) /\
     sub ([(x, bind_typ U1)] ++ E) (open_ct S2 x) (open_ct U2 x).
Proof with auto.
  intros *.
  intro Htyp.
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
Proof with auto.
  intros *.
  intro Htyp.
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
    simpl_env...
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
      * apply (typing_sub (open_ct S2 x))...
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
      * lets (_ & _ & WfH0): cv_regular H0.
        eapply wf_cset_set_weakening; [ apply WfH0 | fsetdec ].
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