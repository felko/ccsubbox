(** Type-safety proofs for Fsub.

    Authors: Brian Aydemir and Arthur Chargu\u00e9raud, with help from
    Aaron Bohannon, Jeffrey Vaughan, and Dimitrios Vytiniotis.

    In parentheses are given the label of the corresponding lemma in
    the appendix (informal proofs) of the POPLmark Challenge.

    Table of contents:
      - #<a href="##subtyping">Properties of subtyping</a>#
      - #<a href="##typing">Properties of typing</a>#
      - #<a href="##preservation">Preservation</a>#
      - #<a href="##progress">Progress</a># *)

Require Import Coq.Program.Equality.
Require Export Fsub_Hints.
Require Import Fsub_CVfacts.

Set Nested Proofs Allowed.

Local Ltac hint := idtac.

Ltac set_facts_come_on_in H :=
  match type of H with
  | true = _ => symmetry in H
  | false = _ => symmetry in H
  | _ => idtac
  end;
  match type of H with
  | NatSet.F.mem _ _ = true => rewrite <- NatSetFacts.mem_iff in H
  | NatSet.F.mem _ _ = false => rewrite <- NatSetFacts.not_mem_iff in H
  | AtomSet.F.mem _ _ = true => rewrite <- AtomSetFacts.mem_iff in H
  | AtomSet.F.mem _ _ = false => rewrite <- AtomSetFacts.not_mem_iff in H
  end.

Ltac rewrite_parenthesise_binding_in H :=
  match type of H with
  | context[[(?x, ?b)] ++ ?F ++ ?E] =>
    rewrite_env (([(x, b)] ++ F) ++ E) in H
  end.

Local Lemma cheat : forall A, A.
Admitted.

Local Lemma cheat_with : forall A B, A -> B.
Admitted.


Local Lemma foo : forall x C e,
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
    + set_facts_come_on_in Heqb.
      exfalso.
      fsetdec.
Qed.

Local Lemma bar : forall x C e u,
  AtomSet.F.In x (cset_fvars (free_for_cv e)) ->
  (cset_union C (cset_remove_fvar x (free_for_cv e))) =
        (free_for_cv (subst_ee x u C e)).
Proof.
Admitted.

Lemma notin_dom_is_notin_fv_ee : forall x E e T,
  x `notin` dom E ->
  typing E e T ->
  x `notin` fv_ee e.
Admitted.

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
Proof with auto.
  intros E C tf tb H.
  remember (cset_set tf tb).
  induction H.
  - inversion Heqc.
  - exists xs. exists {}N...
Qed.

Lemma wf_env_weaken_head : forall E F,
  wf_env (F ++ E) ->
  wf_env E.
Proof with eauto*.
  intros E F Hwf.
  induction F...
  inversion Hwf...
Qed.

Lemma captures_transitivity : forall E xs ys x,
  (* E |- {x} <: {ys} *)
  captures E ys x ->
  (* E |- {ys} <: {xs} *)
  AtomSet.F.For_all (captures E xs) ys ->
  (* E |- {x} <: {xs} *)
  captures E xs x.
Proof with auto.
  intros E xs ys x Hc Hall.
  dependent induction Hc ; intros ; subst...
  eapply captures_var.
  apply H.
  apply H0.
  unfold AtomSet.F.For_all. intros.
  eapply H2...
Qed.

Lemma captures_transitivity_forall : forall E xs ys zs,
  AtomSet.F.For_all (captures E ys) xs ->
  AtomSet.F.For_all (captures E zs) ys ->
  AtomSet.F.For_all (captures E zs) xs.
Proof with auto.
  intros * XsYs YsZs.
  unfold AtomSet.F.For_all in *; intros.
  eapply captures_transitivity with (ys := ys).
  apply XsYs...
  unfold AtomSet.F.For_all in *; intros.
  apply YsZs...
Qed.

Lemma subcapt_transitivity : forall E C1 C2 C3,
  wf_env E ->
  subcapt E C1 C2 ->
  subcapt E C2 C3 ->
  subcapt E C1 C3.
Proof with auto.
  intros E C1 C2 C3 Ok H12 H23.
  remember C1.
  remember C2.
  pose proof (subcapt_regular _ _ _ H23) as [_ Wf].
  assert (capt C3). { auto. }
  inversion H12.
  - Case "subcapt_universal".
    destruct C3... exfalso. subst. inversion H23.
  - Case "subcapt_set".
    subst.
    remember C3.
    destruct C3. subst...
    inversion H; subst.
    inversion H3. inversion H3; subst.
    subst.
    inversion H23; subst.
    eapply subcapt_set...
    unfold AtomSet.F.For_all. intros.
    apply captures_transitivity with (ys := ys)...
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


Lemma captures_narrowing_forall : forall F Z P Q E xs ys,
  ok (F ++ [(Z, bind_sub P)] ++ E) ->
  sub E P Q ->
  AtomSet.F.For_all (captures (F ++ [(Z, bind_sub Q)] ++ E) xs) ys ->
  AtomSet.F.For_all (captures (F ++ [(Z, bind_sub P)] ++ E) xs) ys.
Proof with eauto using wf_cset_narrowing, wf_env_narrowing, cv_narrowing.
  intros * Wf Sub H.
  unfold AtomSet.F.For_all in *; intros.
  specialize (H x H0).
  generalize dependent ys.
  dependent induction H; intros ys' In...
  - destruct (cv_narrowing_exists _ _ _ _ _ _ _ Sub H0) as [C2 [CvC2 SubcaptC2]].
    inversion SubcaptC2; subst.  
    eapply captures_var with (T := T) (ys := xs0).
    * binds_cases H.
      ** apply binds_tail; trivial. apply binds_tail...
      ** apply binds_head; trivial.
    * trivial.
    * eapply captures_transitivity_forall with (ys := ys)...
      unfold AtomSet.F.For_all; intros.
      destruct (x == x0); subst...
Qed.

Lemma captures_narrowing : forall F Z P Q E xs x,
  ok (F ++ [(Z, bind_sub P)] ++ E) ->
  sub E P Q ->
  captures (F ++ [(Z, bind_sub Q)] ++ E) xs x ->
  captures (F ++ [(Z, bind_sub P)] ++ E) xs x.
Proof with eauto using wf_cset_narrowing, wf_env_narrowing, cv_narrowing.
  intros F Z P Q E xs x Ok Sub H.
  eapply captures_narrowing_forall with (Q := Q) (ys := singleton x)...
  - unfold AtomSet.F.For_all; intros.
    assert (x = x0) by fsetdec; subst.
    trivial.
  - fsetdec.
Qed.

(* I currently only use it such that captures_narrowing_typ_forall has a similar proof structure
   as captures_narrowing_forall. 
   Once we simplify captures_narrowing_typ_forall, we can drop this lemma here.
*)
Lemma cv_narrowing_typ_exists : forall T G Z Q E P C1,
  ok (G ++ [(Z, bind_typ Q)] ++ E) ->
  sub E P Q ->
  cv (G ++ [(Z, bind_typ Q)] ++ E) T C1 ->
  exists C2, cv (G ++ [(Z, bind_typ P)] ++ E) T C2 /\ subcapt (G ++ [(Z, bind_typ P)] ++ E) C2 C1.
Proof with simpl_env; eauto.
  intros * Wf Sub Cv.
  unshelve epose proof (cv_narrowing_typ _ _ _ _ _ _ _ Sub _ Cv)...
  exists C1. split...
  eapply subcapt_reflexivity...
Qed.

Lemma captures_narrowing_typ_forall : forall F Z P Q E xs ys,
  wf_env (F ++ [(Z, bind_typ P)] ++ E) ->
  sub E P Q ->
  AtomSet.F.For_all (captures (F ++ [(Z, bind_typ Q)] ++ E) xs) ys ->
  AtomSet.F.For_all (captures (F ++ [(Z, bind_typ P)] ++ E) xs) ys.
Proof with simpl_env; eauto using wf_cset_narrowing_typ, wf_env_narrowing_typ.
  intros * Wf Sub H.
  unfold AtomSet.F.For_all in *; intros.
  specialize (H x H0).
  generalize dependent ys.
  dependent induction H; intros ys' In...

  assert (ok (F ++ [(Z, bind_typ Q)] ++ E)) as Ok. {
    assert (ok (F ++ [(Z, bind_typ P)] ++ E)) by auto...
  }
  unshelve epose proof (cv_narrowing_typ _ _ _ _ _ _ _ Sub ltac:(eauto) H0) as CvNarrow...

  - destruct (cv_narrowing_typ_exists _ _ _ _ _ _ _ Ok Sub H0) as [C2 [CvC2 SubcaptC2]].
    inversion SubcaptC2; subst.  
    destruct (x == Z); subst.
    + unshelve epose proof (cv_exists_in E P _ _) as [C' CVP].
      eauto.
      eauto.
      assert (cv E Q (cset_set ys {}N)) as CVQ. {
        unshelve epose proof (binds_mid_eq_cons _ _ _ _ _ _ H ltac:(auto)) as TQ.
        inversion TQ; subst.
        apply cv_unique_shrink with (F := (F ++ [(Z, bind_typ P)]))...
      }
      unshelve epose proof (sub_implies_subcapt E (dom E) (dom E) _ _ _ _ Sub _ _ _ _ CVP CVQ); try fsetdec.
      eauto.
      eauto.
      inversion H3; subst.
      eapply captures_var with (T := P) (ys := xs1)...
      rewrite <- concat_assoc.
      eapply cv_weakening_head...
      eapply captures_transitivity_forall with (ys := ys)...
      unfold AtomSet.F.For_all in *; intros.
      specialize (H12 x H6).
      rewrite <- concat_assoc.
      rewrite_nil_concat.
      eapply captures_weakening...
      unfold AtomSet.F.For_all in *; intros.
      eapply H2...
    + (* T = Q *)
      eapply captures_var with (T := T) (ys := ys)...
      unfold AtomSet.F.For_all; intros.
      eapply H2 with (ys := ys) (Q0 := Q) (x := x0)...
Qed.


Lemma captures_narrowing_typ : forall F X P Q E xs x,
  wf_env (F ++ [(X, bind_typ Q)] ++ E) ->
  sub E P Q ->
  captures (F ++ [(X, bind_typ Q)] ++ E) xs x ->
  captures (F ++ [(X, bind_typ P)] ++ E) xs x.
Proof with eauto using wf_cset_narrowing_typ, wf_env_narrowing_typ, cv_narrowing_typ.
  intros F Z P Q E xs x Ok Sub H.
  eapply captures_narrowing_typ_forall with (Q := Q) (ys := singleton x)...
  - unfold AtomSet.F.For_all; intros.
    assert (x = x0) by fsetdec; subst.
    trivial.
  - fsetdec.
Qed.

Lemma subcapt_narrowing : forall F E Z P Q C1 C2,
  sub E P Q ->
  ok (F ++ [(Z, bind_sub P)] ++ E) ->
  subcapt (F ++ [(Z, bind_sub Q)] ++ E) C1 C2 ->
  subcapt (F ++ [(Z, bind_sub P)] ++ E) C1 C2.
Proof with eauto using wf_cset_narrowing, wf_env_narrowing.
  intros F E Z P Q C1 C2 SubPQ Ok SubCap.

  inversion SubCap; subst...
  eapply subcapt_set...
  eapply captures_narrowing_forall with (Q := Q)...
Qed.


Lemma subcapt_narrowing_typ : forall F E x P Q C1 C2,
  sub E P Q ->
  wf_env (F ++ [(x, bind_typ Q)] ++ E) ->
  subcapt (F ++ [(x, bind_typ Q)] ++ E) C1 C2 ->
  subcapt (F ++ [(x, bind_typ P)] ++ E) C1 C2.
Proof with eauto using wf_cset_narrowing_typ, captures_narrowing_typ.
  intros F E x P Q C1 C2 PsubQ Ok C1subC2.
  remember (F ++ [(x, bind_typ Q)] ++ E). generalize dependent F.
  induction C1subC2 ; intros ; subst...
  - econstructor...
    unfold AtomSet.F.For_all.
    intros.
    specialize (H1 x0 H2)...
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
  cset_union C1 C2 = {}C ->
  C1 = {}C /\ C2 = {}C.
Proof with eauto.
  intros.
  destruct C1; destruct C2; simpl in H; try discriminate.
  inversion H.
  unfold empty_cset.
  split; f_equal.
  - destruct (AtomSet.F.choose (t `union` t1)) eqn:Eq.
    + assert (AtomSet.F.Equal (t `union` t1) {}) as HA. {
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
    + assert (AtomSet.F.Equal (t `union` t1) {}) as HA. {
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

(* Alex: this was only necessary for subtyping with Top, since that previously checked the CV *)
(* Alex: so it shouldn't be useful now *)
(* Lemma cv_subst_empty : forall S G Z Q E P, *)
(*   wf_typ_in E P -> *)
(*   cv (G ++ [(Z, bind_sub Q)] ++ E) S {}C -> *)
(*   cv (map (subst_tb Z P) G ++ E) (subst_tt Z P S) {}C. *)
(* Proof with eauto using wf_env_subst_tb, wf_typ_subst_tb, wf_pretyp_subst_tb, wf_cset_subst_tb. *)
(*   intros * Wf CV. *)
(*   dependent induction CV. *)
(*   - simpl. destruct (X == Z). *)
(*     admit. *)
(*     admit. *)
(*   - simpl. *)
(*     assert (Z `notin` dom G). { eapply fresh_mid_head... } *)
(*     assert (Z `notin` dom E). { eapply fresh_mid_tail... } *)
(*     apply cv_typ_capt... *)
(*     + unfold wf_pretyp_in. *)
(*       eapply wf_pretyp_subst_tb with (Q := Q)... *)
(*       replace (dom (map (subst_tb Z P) G ++ E))  *)
(*         with ((dom G `union` dom [(Z, bind_sub Q)] `union` dom E) `remove` Z). *)
(*         eapply wf_pretyp_set_strengthen with (S := Q)... *)
(*       repeat rewrite <- dom_concat... *)
(*       repeat rewrite dom_concat. *)
(*       rewrite dom_map. simpl. *)
(*       fsetdec. *)
(*       (* probably needs new strengthening lemmas *) *)
(*       admit. *)
(*       admit. *)
(*     + eapply wf_cset_subst_tb with (Q := Q) (Am := (dom (map (subst_tb Z P) G ++ E)))... *)
(*       replace (dom (map (subst_tb Z P) G ++ E))  *)
(*         with ((dom G `union` dom [(Z, bind_sub Q)] `union` dom E) `remove` Z). *)
(*       eapply wf_cset_set_strengthen with (S := Q)... *)
(*       repeat rewrite <- dom_concat... *)
(*       repeat rewrite dom_concat. *)
(*       rewrite dom_map. simpl. *)
(*       fsetdec. *)
(*       (* probably needs new strengthening lemmas *) *)
(*       admit. *)
(* Admitted. *)

Lemma captures_expansion : forall D2 E x D1,
  captures E D1 x ->
  captures E (D1 `union` D2) x.
Proof with eauto.
  intros *.
  intro H.
  dependent induction H.
  - apply captures_in...
    fsetdec.
  - apply captures_var with (T := T) (ys := ys)...
Qed.

Lemma wf_cset_union : forall E A C D,
  wf_cset E A C ->
  wf_cset E A D ->
  wf_cset E A (cset_union C D).
Proof with eauto.
  intros *.
  intros H1 H2.
  inversion H1; inversion H2; subst; simpl...
  unfold wf_cset_in in *.
  replace (NatSet.F.union _ _) with {}N by fnsetdec.
  constructor...
  unfold allbound_typ in *...
  intros.
  rewrite AtomSetFacts.union_iff in *.
  auto*.
Qed.

Lemma subcapt_expansion : forall E C D1 D2,
  wf_cset_in E D2 ->
  subcapt E C D1 ->
  subcapt E C (cset_union D1 D2).
Proof with eauto using wf_cset_union.
  intros *.
  intros HwfD2 Hsubcapt.
  induction Hsubcapt.
  - simpl.
    destruct D2...
  - destruct D2; simpl...
    inversion HwfD2; subst.
    replace (NatSet.F.union _ _)
      with {}N by fnsetdec.
    apply subcapt_set...
    + (* wf_cset_union doesn't work here, sigh *)
      inversion H; inversion H0; subst.
      unfold wf_cset_in in *.
      constructor...
      unfold allbound_typ in *...
      intros.
      rewrite AtomSetFacts.union_iff in *.
      auto*.
    + unfold AtomSet.F.For_all in *.
      eauto using (captures_expansion t)...
Qed.

Lemma subcapt_union_distributivity : forall E C1 C2 D,
  subcapt E C1 D ->
  subcapt E C2 D ->
  subcapt E (cset_union C1 C2) D.
Proof with eauto using wf_cset_union.
  intros *.
  intros HscC1 HscC2.
  induction HscC1...
  inversion HscC2; subst; simpl.
  replace (NatSet.F.union _ _) with {}N by fnsetdec.
  apply subcapt_set...
  - replace (cset_set (xs `union` xs0) {}N)
      with (cset_union (cset_set xs {}N) (cset_set xs0 {}N)).
    2: apply cset_eq_injectivity; [fsetdec|fnsetdec].
    apply wf_cset_union...
  - unfold AtomSet.F.For_all in *.
    intros.
    rewrite AtomSetFacts.union_iff in *.
    auto*.
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

Lemma binds_unique : forall b1 b2 x (E : env),
  binds x b1 E ->
  binds x b2 E ->
  b1 = b2.
Proof.
  intros* Hb1 Hb2.
  congruence.
Qed.

Lemma binds_sub_unique : forall T1 T2 X E,
  binds X (bind_sub T1) E ->
  binds X (bind_sub T2) E ->
  T1 = T2.
Proof.
  intros* Hb1 Hb2.
  congruence.
Qed.

Lemma binds_typ_unique : forall T1 T2 X E,
  binds X (bind_typ T1) E ->
  binds X (bind_typ T2) E ->
  T1 = T2.
Proof.
  intros* Hb1 Hb2.
  congruence.
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
  - destruct (IHHcvWide _ _ _ _ H0 ltac:(eauto) ltac:(eauto) Hsub) as [D [Cv' Subcapt]].
    simpl; destruct (X0 == X); subst; simpl in *; simpl_env in *.
    + unshelve epose proof (cv_exists_in E P _ _) as [C Cv]...
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
      * unshelve epose proof (IHHcvWide _ _ _ _ H0 ltac:(eauto) ltac:(eauto) Hsub) as [D2 [Cv2 Subcapt2]].
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
  unshelve epose proof (cv_through_subst_tt_exists Q X P T E G C _ _ _ _ ) as [D' [HcvD HscD]]...
  assert (D' = D). {
    apply (cv_unique (map (subst_tb X P) G ++ E) (subst_tt X P T))...
  }
  subst.
  assumption.
Qed.

(* Type substitution preserves subcapturing *)
Lemma captures_through_subst_tt : forall Q E F Z P C x,
  captures (F ++ [(Z, bind_sub Q)] ++ E) C x ->
  wf_typ_in E P ->
  captures (map (subst_tb Z P) F ++ E) C x.
Proof with eauto using wf_env_subst_tb, wf_cset_subst_tb.
  intros *.
  intros H Tp.
  remember  (F ++ [(Z, bind_sub Q)] ++ E).
  generalize dependent F.
  induction H; intros; subst.
  - constructor...
  (* that's the same as in captures_narrowing -> TODO refactor *)
  - assert (x <> Z). {
      unfold not. intros.
      binds_cases H.
      * subst. unfold dom in Fr0. fsetdec.
      * subst. exfalso. admit.
    }
    apply captures_var with (T := T) (ys := ys)...
    admit.
  (* - assert (exists (C3 : captureset),
      cv (subst_tt X P T) (map (subst_tb X P) G ++ E) C3 /\
      subcapt (map (subst_tb X P) G ++ E) C3 C2
           ) as [C3 [C3sub C3eq]]. {
      apply cv_through_subst_tt with (Q := Q)...
      assert (binds X0 (bind_typ T) (G ++ [(X, bind_sub Q)] ++ E)); auto.
      eapply wf_typ_from_binds_typ; auto.
      apply H.
    }
    apply subcapt_var with (C2 := C3) (T := subst_tt X P T)...
    apply subcapt_transitivity with (C2 := C2)...
    apply wf_env_subst_tb with (Q := Q)... *)
Admitted.

Lemma subcapt_through_subst_tt : forall E P Q G X C D,
  wf_env (G ++ [(X, bind_sub Q)] ++ E) ->
  subcapt (G ++ [(X, bind_sub Q)] ++ E) C D ->
  sub E P Q ->
  subcapt (map (subst_tb X P) G ++ E) C D.
Proof with eauto using wf_env_subst_tb, wf_cset_subst_tb, captures_through_subst_tt.
  intros E P Q G X C D Hwf H Hsub.
  remember (G ++ [(X, bind_sub Q)] ++ E).
  induction H; auto.
  subst.
  binds_cases H...
  - constructor...
    eapply wf_cset_in_subst_tb...
  - subst.
    constructor...
    (* Same as above... *)
    + eapply wf_cset_in_subst_tb...
    + eapply wf_cset_in_subst_tb...
    + unfold AtomSet.F.For_all in *. intros.
      specialize (H1 x H2)...
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
      match goal with
      | H : binds X _ _ |- _ =>
        binds_cases H
      end...
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
          apply (notin_fv_wf_typ _ _ _ Z Q) in HA...
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
          apply (notin_fv_wf_typ _ _ _ Z) in HA...
        }
        apply (IHSsubT Q)...
      * apply (sub_trans_tvar (subst_tt Z P U)); [auto| eapply IHSsubT]...
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
      eapply wf_typ_come_on. {
        rewrite_parenthesise_binding_in H2.
        assert (wf_typ_in (empty ++ E) P) as WfP by (simpl_env;auto).
        apply (wf_typ_subst_tb _ _ _ _ _ _ P _ H2).
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
      eapply wf_typ_come_on. {
        rewrite_parenthesise_binding_in H3.
        assert (wf_typ_in (empty ++ E) P) as WfP by (simpl_env;auto).
        apply (wf_typ_subst_tb _ _ _ _ _ _ P _ H3).
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
      eapply wf_typ_come_on. {
        rewrite_parenthesise_binding_in H2.
        assert (wf_typ_in (empty ++ E) P) as WfP by (simpl_env;auto).
        apply (wf_typ_subst_tb _ _ _ _ _ _ P _ H2).
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
      eapply wf_typ_come_on. {
        rewrite_parenthesise_binding_in H3.
        assert (wf_typ_in (empty ++ E) P) as WfP by (simpl_env;auto).
        apply (wf_typ_subst_tb _ _ _ _ _ _ P _ H3).
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

(* Alex: well all right, none of these are used now... *)
(* Lemma fv_et_subset_dom_env : forall E T, *)
(*   wf_typ_in E T -> *)
(*   fv_et T `subset` dom E *)
(* with fv_ept_subset_dom_env : forall E P, *)
(*   wf_pretyp_in E P -> *)
(*   fv_ept P `subset` dom E. *)
(* Proof with eauto. *)
(* { intros. *)
(*   assert (type T) as Typ. { *)
(*     apply type_from_wf_typ in H... *)
(*   } *)
(*   induction Typ. *)
(*   - simpl. *)
(*     fsetdec. *)
(*   - simpl. *)
(*     inversion H; subst. *)
(*     match goal with H : wf_pretyp _ _ _ P |- _ => *)
(*       apply fv_ept_subset_dom_env in H *)
(*     end. *)
(*     match goal with H : wf_cset _ _ C |- _ => *)
(*       inversion H; subst; simpl; fsetdec *)
(*     end. *)
(* } *)
(* { *)
(*   intros. *)
(*   assert (pretype P) as Pretyp. { *)
(*     apply pretype_from_wf_pretyp in H... *)
(*   } *)
(*   induction Pretyp; simpl. *)
(*   - fsetdec. *)
(*   - inversion H; subst. *)
(*     pick fresh X. *)
(*     unshelve epose proof (H8 X _) as SpH8... *)
(*     assert (fv_et (open_ct T2 X) `subset` dom E `union` singleton X). *)
(*     (fv_et T2 `subset` dom E) *)

(*     wf_typ *)
(* } *)

(* Lemma self_subst_idempotent : forall F E x T D, *)
(*   wf_env (F ++ [(x, bind_typ T)] ++ E) -> *)
(*   subst_ct x D T = T. *)
(* Proof. *)
(*   (* Plan: *) *)
(*   (*   - fv(T) subset E (should be prove-able using a simple lemma like bindin_uniq_from_* ) *) *)
(*   (*   - therefore x not in fv(t) *) *)
(*   (*   - therefore subst idempotent *) *)
(*   admit. *)
(* Admitted. *)

Lemma cset_subst_self : forall C x,
  subst_cset x C (cset_fvar x) = C.
Proof.
  intros.
  unfold subst_cset.
  destruct (cset_references_fvar_dec x x) eqn:EQ.
  2: {
    unfold cset_references_fvar_dec, cset_fvar in EQ.
    rewrite <- AtomSetFacts.not_mem_iff in EQ.
    exfalso.
    fsetdec.
  }
  unfold cset_remove_fvar, cset_fvar.
  replace (cset_set _ _) with {}C.
  2: {
    apply cset_eq_injectivity; [fsetdec|fnsetdec].
  }
  destruct C; simpl.
  - easy.
  - replace (cset_set _ _) with (cset_set t t0).
    2: {
      apply cset_eq_injectivity; [fsetdec|fnsetdec].
    }
    easy.
Qed.

Lemma wf_env_strengthening : forall F E,
  wf_env (F ++ E) ->
  wf_env E.
Proof with eauto.
  induction F...
  intros.
  inversion H; subst...
Qed.


Lemma wf_cset_remove_fvar : forall A E C x,
  wf_cset E A C ->
  wf_cset E A (cset_remove_fvar x C).
Proof with eauto.
  intros.
  unfold wf_cset_in in *.
  induction H; simpl...
  constructor...
  unfold allbound_typ in *.
  intros.
  apply H.
  fsetdec.
Qed.

Lemma wf_cset_subst_cb : forall Q Ap' Ap F E x C D,
  wf_cset (F ++ [(x, bind_typ Q)] ++ E) Ap C ->
  wf_env (F ++ [(x, bind_typ Q)] ++ E) ->
  wf_cset E Ap' D ->
  Ap' `subset` Ap ->
  Ap' `subset` dom E ->
  ok (map (subst_cb x D) F ++ E) ->
  wf_cset (map (subst_cb x D) F ++ E) (Ap `remove` x) (subst_cset x D C).
Proof with simpl_env; eauto*.
  intros *. intros HwfC HwfEnv HwfD Hsset HApRsnbl Hok.
  destruct C.
  1: { unfold subst_cset; unfold cset_references_fvar_dec... }
  unfold subst_cset; unfold cset_references_fvar_dec.
  apply binding_uniq_from_wf_env in HwfEnv as ?.
  destruct (AtomSet.F.mem x t) eqn:EQ...
  - apply wf_cset_union.
    + rewrite_nil_concat.
      apply wf_cset_weakening with (A := Ap'); simpl_env...
    + unfold cset_remove_fvar; simpl.
      inversion HwfC; subst.
      constructor...
      unfold allbound_typ in *.
      intros.
      destruct (x0 == x).
      * exfalso. fsetdec.
      * assert (x0 `in` t) as HA by fsetdec.
        specialize (H4 x0 HA) as [T HbindsT].
        binds_cases HbindsT...
        exists (subst_ct x D T)...
  - inversion HwfC; subst.
    rewrite <- AtomSetFacts.not_mem_iff in EQ.
    constructor...
    unfold allbound_typ in *.
    intros.
    unshelve epose proof (H4 x0 _) as [T HbindsT]...
    assert (x0 <> x) by fsetdec.
    binds_cases HbindsT...
    exists (subst_ct x D T)...
Qed.

Lemma wf_cset_in_subst_cb : forall Q F E x C D,
  wf_cset_in (F ++ [(x, bind_typ Q)] ++ E) C ->
  wf_env (F ++ [(x, bind_typ Q)] ++ E) ->
  wf_cset_in E D ->
  ok (map (subst_cb x D) F ++ E) ->
  wf_cset_in (map (subst_cb x D) F ++ E) (subst_cset x D C).
Proof with eauto.
  intros.
  assert (x `notin` (dom F `union` dom E)). {
    apply binding_uniq_from_wf_env with (b := bind_typ Q)...
  }
  unfold wf_cset_in in *.
  replace (dom (map (subst_cb x D) F ++ E))
    with ((dom (F ++ [(x, bind_typ Q)] ++ E)) `remove` x) by (simpl_env; fsetdec).
  apply (wf_cset_subst_cb Q (dom E))...
Qed.

Lemma wf_typ_subst_cb : forall U Ap Am F x C E T,
  wf_env (F ++ [(x, bind_typ U)] ++ E) ->
  cv E U C ->
  wf_typ (F ++ [(x, bind_typ U)] ++ E) Ap Am T ->
  wf_typ (map (subst_cb x C) F ++ E) (Ap `remove` x) (Am `remove` x) (subst_ct x C T)
with wf_pretyp_subst_cb : forall U Ap Am F x C E P,
  wf_env (F ++ [(x, bind_typ U)] ++ E) ->
  cv E U C ->
  wf_pretyp (F ++ [(x, bind_typ U)] ++ E) Ap Am P ->
  wf_pretyp (map (subst_cb x C) F ++ E) (Ap `remove` x) (Am `remove` x) (subst_cpt x C P).
Proof.
Admitted.

Lemma wf_typ_in_subst_cb : forall F x U C E T,
    wf_env (F ++ [(x, bind_typ U)] ++ E) ->
    cv E U C ->
    wf_typ_in (F ++ [(x, bind_typ U)] ++ E) T ->
    wf_typ_in (map (subst_cb x C) F ++ E) (subst_ct x C T)
with wf_pretyp_in_subst_cb : forall F x U C E P,
    wf_env (F ++ [(x, bind_typ U)] ++ E) ->
    cv E U C ->
    wf_pretyp_in (F ++ [(x, bind_typ U)] ++ E) P ->
    wf_pretyp_in (map (subst_cb x C) F ++ E) (subst_cpt x C P).
Proof.
  (* Use above. *)
Admitted.

Lemma wf_env_subst_cb : forall Q C x E F,
  wf_env (F ++ [(x, bind_typ Q)] ++ E) ->
  wf_cset_in E C ->
  wf_env (map (subst_cb x C) F ++ E).
Proof.
  (* with eauto 6 using wf_typ_subst_tb *)

  admit.
  (* induction F; intros Wf_env WP; simpl_env; *)
  (*   inversion Wf_env; simpl_env in *; simpl subst_tb... *)
Admitted.

Lemma not_in_fv_cset_iff : forall x C,
  cset_references_fvar_dec x C = false -> x `notin` fv_cset C.
Proof.
  intros.
  unfold cset_references_fvar_dec in H.
  unfold fv_cset.
  destruct C.
  - fsetdec.
  - rewrite AtomSetFacts.not_mem_iff.
    assumption.
Qed.

Lemma cv_through_subst_ct : forall F x U E C T D,
    cv (F ++ [(x, bind_typ U)] ++ E) T C ->
    cv E U D ->
    cv (map (subst_cb x D) F ++ E) (subst_ct x D T) (subst_cset x D C).
Proof with eauto using wf_env_subst_cb, wf_pretyp_in_subst_cb, wf_typ_in_subst_cb, wf_cset_in_subst_cb.
  intros * HcvT HcvU.
  dependent induction HcvT.
  - simpl.
    binds_cases H.
    + apply wf_typ_from_binds_sub in H as WfT...
      rewrite_nil_concat.
      apply cv_weakening; simpl_env...
      apply cv_unique_shrink in HcvT...
      2: {
        assert (wf_env (F ++ [(x, bind_typ U)] ++ E))...
        rewrite_nil_concat.
        eapply wf_typ_weakening; simpl_env.
        - apply WfT.
        - apply ok_from_wf_env, ok_tail in H1.
          assumption.
        - clear_frees. fsetdec.
        - clear_frees. fsetdec.
      }
      apply cv_unique_shrink in HcvT...
      apply cv_regular in HcvT as Reg.
      destruct Reg as [_ [_ WfCT]].
      inversion WfCT; subst.
      * unfold subst_cset, cset_references_fvar_dec.
        eapply cv_typ_var...
      * apply binding_uniq_from_wf_env in H0 as ?.
        assert (x `notin` fvars) as HA by notin_solve.
        rewrite AtomSetFacts.not_mem_iff in HA.
        unfold subst_cset, cset_references_fvar_dec.
        rewrite HA.
        eapply cv_typ_var...
    + assert (binds X (subst_cb x D (bind_sub T)) (map (subst_cb x D) F ++ E))...
  - simpl.
    constructor...
    apply (wf_cset_in_subst_cb U)...
Qed.

(* Substituting the same capture set preserves subcapturing *)
Lemma subcapt_through_subst_cset : forall F x U E C1 C2 D,
  subcapt (F ++ [(x, bind_typ U)] ++ E) C1 C2 ->
  wf_env (F ++ [(x, bind_typ U)] ++ E) ->
  cv E U D ->
  subcapt (map (subst_cb x D) F ++ E) (subst_cset x D C1) (subst_cset x D C2).
Proof with eauto.
  intros *.
  intros Hsc WfE Hcv.
  destruct C1; destruct C2; subst; simpl subst_cset; try solve [inversion Hsc]...
  1: {
    cbv [subst_cset cset_references_fvar_dec].
    constructor.
    apply cv_regular, proj2, proj2 in Hcv.
    destruct (AtomSet.F.mem x t) eqn:EQ...
    - apply wf_cset_union.
      + rewrite_nil_concat.
        assert (ok (F ++ [(x, bind_typ U)] ++ E))...
        apply wf_cset_weakening with (A := dom E); simpl_env...
      + unfold cset_remove_fvar; simpl.
        pose proof (subcapt_regular _ _ _ Hsc) as [HA _].
        inversion HA; subst.
        constructor...
        unfold allbound_typ in *.
        intros.
        destruct (x0 == x).
        * exfalso. fsetdec.
        * specialize (H3 x0 ltac:(fsetdec)) as [T HbindsT].
          binds_cases HbindsT...
          exists (subst_ct x D T)...
    - apply subcapt_regular, proj1 in Hsc.
      inversion Hsc; subst.
      rewrite <- AtomSetFacts.not_mem_iff in EQ.
      constructor.
      + simpl_env in *. unfold allbound_typ in *.
        intros.
        pose proof (H3 x0 ltac:(assumption)) as [T Hbinds].
        binds_cases Hbinds...
        * exfalso. fsetdec.
        * exists (subst_ct x D T)...
      + simpl_env in *; fsetdec.
  }
  pose proof (subcapt_regular _ _ _ Hsc) as [Wf1 Wf2].
  inversion Wf1; inversion Wf2; subst.
  unfold subst_cset.
  assert (D = cset_universal -> x `in` t -> x `in` t1). {
    intros ? x_in_t.
    subst.
    inversion Hsc; subst.
    specialize (H6 x x_in_t).
    inversion H6; subst...
    assert (wf_typ_in E U) as HA by auto.
    binds_get H.
    injection H8.
    intro. subst.
    apply cv_unique_shrink in H0...
    2: rewrite_nil_concat; eapply wf_typ_weakening...
    2: apply ok_from_wf_env in WfE;
      apply ok_tail in WfE;
      assumption.
    apply cv_unique_shrink in H0...
    unshelve epose proof (cv_unique _ _ _ _ _ _ Hcv H0)...
    easy.
  }
  (* destruct D. *)
  (* - specialize (H ltac:(reflexivity)). *)
  (*   destruct_if. *)
  (*   + unfold cset_references_fvar_dec in Heqb. *)
  (*     set_facts_come_on_in Heqb. *)
  (*     unfold cset_references_fvar_dec. *)
  (*     specialize (H Heqb). *)
  (*     rewrite AtomSetFacts.mem_iff in H. *)
  (*     rewrite H. *)
  (*     simpl. *)
  (*     constructor... *)
  (*   + destruct_if. *)
  (*     * simpl. *)
  (*       constructor... *)
  (*       apply subcapt_regular in Hsc as [? _]. *)
  (*       apply not_in_fv_cset_iff in Heqb as ?. *)
  (*       replace (cset_set t {}N) with (subst_cset x cset_universal (cset_set t {}N)). *)
  (*       2: { *)
  (*         rewrite <- subst_cset_fresh... *)
  (*       } *)
  (*       apply (wf_cset_in_subst_cb U)... *)
  (*       apply (wf_env_subst_cb _ cset_universal) in WfE... *)
  (*     * admit. *)
  (* - clear H. *)



  destruct_if; destruct_if.
  - unfold cset_remove_fvar, cset_union.
    destruct D.
    + apply subcapt_reflexivity with (A := dom (map (subst_cb x cset_universal) F ++ E))...
      (* apply wf_env_subst_cb *)
      admit.
    + admit.                    (* union-over-subcapt + remove-from-subcapt ? *)
  - destruct D.
    simpl.
    + admit.                    (* leads to contradiction, LHS must be universal *)
    + simpl.
      admit.
  - destruct D.
    + simpl.
      constructor...
      apply subcapt_regular in Hsc as [? _].
      apply not_in_fv_cset_iff in Heqb as ?.
      replace (cset_set t {}N)
        with (subst_cset x cset_universal (cset_set t {}N)).
      2: {
        rewrite <- subst_cset_fresh...
      }
      eapply wf_cset_in_subst_cb...
      assert (ok (F ++ [(x, bind_typ U)] ++ E))...
    + simpl.
      admit.
  - inversion Hsc; subst.
    constructor...
    + admit.
    + admit.
    + unfold AtomSet.F.For_all in *.
      intros z ?.
      specialize (H7 z ltac:(trivial)).
      inversion H7; subst...
      admit.
Admitted.

Lemma subst_cset_across_subcapt : forall E x C D C0 A,
  wf_env E ->
  wf_cset E A C0 ->
  A `subset` dom E ->
  subcapt E C D ->
  subcapt E (subst_cset x C C0) (subst_cset x D C0).
Proof with eauto.
  intros *.
  intros WfEnv Wf Subset Sub.
  remember C0.
  destruct C0...
  - destruct (AtomSet.F.mem x (cset_fvars c)) eqn:InAp.
    + inversion Sub; subst.
      * unfold subst_cset. unfold cset_references_fvar_dec...
      * unfold subst_cset. unfold cset_references_fvar_dec...
    + rewrite <- AtomSetFacts.not_mem_iff in InAp.
      replace (subst_cset x C c) with c.
      replace (subst_cset x D c) with c.
      apply subcapt_reflexivity with (A := A)...
      apply subst_cset_fresh. inversion Wf; subst...
      apply subst_cset_fresh. inversion Wf; subst...
  - destruct (AtomSet.F.mem x (cset_fvars c)) eqn:InAp.
    + inversion Sub; subst.
      * simpl in InAp. unfold subst_cset. unfold cset_references_fvar_dec. rewrite InAp. constructor.
        destruct C...
        simpl. inversion Wf. inversion H. rewrite elim_empty_nat_set. subst.
        constructor...
        unfold allbound_typ in *.
        intros.
        rewrite AtomSetFacts.union_iff in H0.
        destruct H0...
        apply H4.
        fsetdec.
      * simpl in InAp. unfold subst_cset. unfold cset_references_fvar_dec. rewrite InAp.
        inversion Wf; subst.
        match goal with
        | |- subcapt _ ?C _ =>
          assert (wf_cset_in E C) as WfC
        end. {
          eauto using wf_cset_union, wf_cset_remove_fvar.
        }
        match goal with
        | |- subcapt _ _ ?D =>
          assert (wf_cset_in E D) as WfD
        end. {
          eauto using wf_cset_union, wf_cset_remove_fvar.
        }
        simpl in WfC, WfD |- *. rewrite elim_empty_nat_set in WfC, WfD |- *.
        constructor...          (* well OK, what do we do here? induction? *)
        admit.
    + rewrite <- AtomSetFacts.not_mem_iff in InAp.
      replace (subst_cset x C c) with c.
      replace (subst_cset x D c) with c.
      apply subcapt_reflexivity with (A := A)...
      apply subst_cset_fresh. unfold fv_cset; subst...
      apply subst_cset_fresh. unfold fv_cset; subst...
Admitted.

Lemma sub_through_subst_ct : forall E F x U C S T,
  sub (F ++ [(x, bind_typ U)] ++ E) S T ->
  cv E U C ->
  sub (map (subst_cb x C) F ++ E) (subst_ct x C S) (subst_ct x C T)
with sub_pre_through_subst_cpt : forall E F x U C P Q,
  sub_pre (F ++ [(x, bind_typ U)] ++ E) Q P ->
  cv E U C ->
  sub_pre (map (subst_cb x C) F ++ E) (subst_cpt x C Q) (subst_cpt x C P).
Proof with eauto.
  { intros *.
    intros Hsub HcvU.
    remember (F ++ [(x, bind_typ U)] ++ E).
    generalize dependent F.
    induction Hsub; intros F EQ; subst.
    - simpl.
      apply sub_refl_tvar...
      + eapply wf_env_subst_cb...
      + unsimpl (subst_ct x C X).
        eapply wf_typ_in_subst_cb...
    - simpl.
      destruct (x == X).
      + SCase "x == X".
        subst.
        binds_get H.
      + SCase "x <> X".
        binds_cases H.
        * assert (x `notin` fv_et U0) as FrXinU0. {
            apply wf_typ_from_binds_sub in H as HA; [|auto .. ].
            assert (wf_env (F ++ [(x, bind_typ U)] ++ E)) as HA1. {
               trivial...
            }
            apply binding_uniq_from_wf_env in HA1.
            pose proof (notin_fv_wf_typ _ _ _ x _ HA ltac:(notin_solve)).
            notin_solve.
          }
          unshelve epose proof (IHHsub F _) as IHHsub0...
          rewrite <- (subst_ct_fresh x C U0) in IHHsub0...
        * apply sub_trans_tvar with (U := (subst_ct x C U0))...
    - apply sub_capt.
      + eapply subcapt_through_subst_cset...
      + eapply sub_pre_through_subst_cpt...
  }
  { intros *.
    intros Hsub HcvU.
    remember (F ++ [(x, bind_typ U)] ++ E).
    generalize dependent F.
    induction Hsub; intros F EQ; subst.
    - simpl.
      apply sub_top.
      + eapply wf_env_subst_cb...
      + eapply wf_pretyp_in_subst_cb...
    - simpl.
      pick fresh y and apply sub_arrow...
      + eapply wf_typ_in_subst_cb...
      + eapply wf_typ_in_subst_cb...
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
        eapply (wf_typ_subst_cb U); simpl_env...
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
        eapply (wf_typ_subst_cb U); simpl_env...
      + specialize (H4 y ltac:(notin_solve)).
        rewrite subst_ct_open_ct_var...
        rewrite subst_ct_open_ct_var...
        rewrite_env (map (subst_cb x C) ([(y, bind_typ T1)] ++ F) ++ E).
        eapply sub_through_subst_ct; simpl_env...
    - simpl.
      pick fresh y and apply sub_all...
      + eapply wf_typ_in_subst_cb...
      + eapply wf_typ_in_subst_cb...
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
        eapply (wf_typ_subst_cb U); simpl_env...
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
        eapply (wf_typ_subst_cb U); simpl_env...
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
        set_facts_come_on_in Heqb.
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

Lemma meaning_of : forall E Ap Am x C D T,
  wf_env E ->
  type T ->
  Ap `subset` dom E ->
  Am `subset` dom E ->
  wf_typ E Ap Am T ->
  subcapt E C D ->
  ((x `notin` Am -> wf_cset E Ap C -> wf_cset E Ap D -> sub E (subst_ct x C T) (subst_ct x D T)) /\
   (x `notin` Ap -> wf_cset E Am C -> wf_cset E Am D -> sub E (subst_ct x D T) (subst_ct x C T)))
with pre_meaning_of : forall E Ap Am x C D T,
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
  - destruct (pre_meaning_of E Ap Am x C D P HwfE H0 SubAp SubAm H7 Hsc).
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
    destruct (meaning_of E Am Ap x C D T1 HwfE H SubAm SubAp H6 Hsc).
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
      (* we cannot call meaning_of on anything that is larger than wf_typ.... *)
      assert (y `notin` L) as NotIn by notin_solve.
      specialize (H0 y NotIn).
      unshelve epose proof (meaning_of
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
      (* we cannot call meaning_of on anything that is larger than wf_typ.... *)
      assert (y `notin` L) as NotIn by notin_solve.
      specialize (H0 y NotIn).
      unshelve epose proof (meaning_of
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
    destruct (meaning_of E Am Ap x C D T1 HwfE H SubAm SubAp H6 Hsc).
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
      (* we cannot call meaning_of on anything that is larger than wf_typ.... *)
      assert (y `notin` L) as NotIn by notin_solve.
      specialize (H0 y NotIn).
      unshelve epose proof (meaning_of
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
      (* we cannot call meaning_of on anything that is larger than wf_typ.... *)
      assert (y `notin` L) as NotIn by notin_solve.
      specialize (H0 y NotIn).
      unshelve epose proof (meaning_of
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

Lemma true_meaning_of : forall E Ap Am x C D T,
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
  eapply (proj1 (meaning_of _ Ap Am _ _ _ _ H H0 H1 H2 H3 H4))...
Qed.

Lemma wf_typ_extract_typ_arrow : forall C E T1 T2,
  wf_typ_in E (typ_capt C (typ_arrow T1 T2)) ->
  exists L, forall x, x `notin` L ->
     wf_typ ([(x, bind_typ T1)] ++ E) (dom E `union` singleton x) (dom E) (open_ct T2 x).
Proof with eauto.
  intros *.
  intro HWf.
  (* type inversion *)
  inversion HWf; subst.
  (* pretype inversion *)
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

Lemma applied_meaning_of : forall E C1 C2 e D S T,
  subcapt E C1 C2 ->
  typing E e (typ_capt D (typ_arrow S T)) ->
  sub E (open_ct T C1) (open_ct T C2).
Proof.
  intros *. intros Hsc Htyp.
  pose proof (typing_extract_typ_arrow _ _ _ _ _ Htyp) as [L HRT].
  pick fresh y.
  replace (open_ct T C1) with (subst_ct y C1 (open_ct T y)).
  replace (open_ct T C2) with (subst_ct y C2 (open_ct T y)).
  2,3: solve [symmetry; apply subst_ct_intro; fsetdec].
  pose proof (typing_regular _ _ _ Htyp) as [_ [_ Reg]].
  wf_typ_inversion Reg.
  assert (wf_typ ([(y, bind_typ S)] ++ E)
                  (dom E `union` singleton y) (dom E)
                  (open_ct T y)) by eauto.
  enough (sub ([(y, bind_typ S)] ++ E)
              (subst_ct y C1 (open_ct T y))
              (subst_ct y C2 (open_ct T y))). {
    assert (wf_typ_in E S) as HwfS by assumption.
    unshelve epose proof (cv_exists_in E S _ _) as [C_S ?]; auto.
    rewrite_env (map (subst_cb y C_S) empty ++ E).
    replace (subst_ct y C1 (open_ct T y))
      with (subst_ct y C_S (subst_ct y C1 (open_ct T y))).
    replace (subst_ct y C2 (open_ct T y))
      with (subst_ct y C_S (subst_ct y C2 (open_ct T y))).
    2,3: solve [apply subst_ct_useless_repetition; notin_solve].
    apply sub_through_subst_ct with (U := S); simpl_env; auto.
  }
  eapply true_meaning_of with (Ap := dom E `union` singleton y) (Am := dom E); eauto.
  - rewrite_nil_concat.
    apply subcapt_weakening; simpl_env; eauto.
  - apply subcapt_regular in Hsc as [WfC1 _].
    rewrite_nil_concat.
    eapply wf_cset_weakening ; [ apply WfC1 | simpl_env; auto .. ].
  - apply subcapt_regular in Hsc as [_ WfC2].
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
      pose proof (typing_regular _ _ _ (H1 y Fr)) as [P0 _].
      inversion P0; subst...
    }
    pick fresh y and apply typing_abs...
    + rewrite_parenthesise_binding.
      simpl_env in H0...
      eapply wf_typ_narrowing_base; simpl_env...
    + rewrite <- concat_assoc.
      apply H2...
  - Case "typing_app".
    (* Alex: requires making use of well-formedness *)
    pose proof (cv_exists_in (F ++ [(X, bind_sub P)] ++ E) T1') as Ex.
    destruct Ex as [Cnarrow HCVnarrow]...
    apply wf_typ_narrowing with (Q := Q)...
    eapply typing_sub with (S := (open_ct T2 Cnarrow))...
    pose proof (cv_narrowing _ _ _ _ _ _ _ _ PsubQ H0 HCVnarrow) as Subcapt.
    specialize (IHTyp1 F ltac:(auto)).

    eapply applied_meaning_of.
    + assumption.
    + eauto.
  - Case "typing_tabs".
    assert (wf_env (F ++ [(X, bind_sub P)] ++ E)). {
      pick fresh y for L.
      pose proof (typing_regular _ _ _ (H1 y Fr)) as [P0 _].
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
Proof with subst; simpl; auto.
  intros *.
  intros Hv Htyp Hcv.
  generalize dependent C.
  pose proof (typing_regular _ _ _ Htyp) as [P1 [P2 P3]].
  induction Htyp; intros C0 Hcv; try solve [ inversion Hv ].
  - inversion Hcv...
    apply subcapt_reflexivity with (A := dom E)...
  - inversion Hcv.
    apply subcapt_reflexivity with (A := dom E)...
  - unshelve epose proof (cv_exists_in E S P1 _ ) as [D HcvS]...
    unshelve epose proof (IHHtyp Hv _ _ _ D HcvS)...
    apply subcapt_transitivity with (C2 := D)...
    eapply sub_implies_subcapt with (S := S) (T := T)
                                    (A1 := dom E) (A2 := dom E)...
Qed.

Lemma value_typing_inv : forall E v T,
  value v ->
  typing E v T ->
  exists C, exists P, sub E (typ_capt C P) T.
Proof with eauto using typing_cv.
  intros*.
  intros Val Typ.
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
  intros *.
  intros Hv Htyp.
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
  - unshelve epose proof (IHHtyp _ _ _) as [U [HtypU HsubS]]...
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
        replace (cset_set _ _) with {}C by cset_eq_dec.
        destruct (free_for_cv u).
        - unfold cset_union.
          destruct_match; reflexivity.
        - unfold cset_union, empty_cset.
          cset_eq_dec.
      }

      replace (subst_cpt x (free_for_cv u) P) with P.
      2: {
        pose proof (binding_uniq_from_wf_env _ _ _ _ H).
        pose proof (notin_fv_wf_pretyp E (dom E) (dom E) x P ltac:(auto) ltac:(notin_solve)).
        rewrite <- subst_cpt_fresh...
      }
      unshelve epose proof
      (values_have_precise_captures E u (typ_capt (free_for_cv u) P) _ _)
        as [? [? ?]]...
    + SCase "x0 <> x".
      binds_cases H0.
      * assert (x `notin` fv_ept P). {
          assert (x `notin` dom E) as HA1. { eapply fresh_mid_tail... }
          unshelve epose proof (wf_typ_from_binds_typ _ _ _ _ H0)...
          assert (wf_pretyp_in E P) as HA2...
          epose proof (notin_fv_wf_pretyp _ _ _ _ _ HA2 HA1)...
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
      rewrite foo...
      rewrite bar with (u := u)...
      pick fresh y and apply typing_abs...
      * eapply wf_typ_in_subst_cb...
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
        apply (wf_typ_subst_cb (typ_capt (free_for_cv u) P)); simpl_env...
      * assert (y <> x) by fsetdec.
        rewrite subst_ee_open_ee_var...
        rewrite subst_ct_open_ct_var...
        rewrite_env (map (subst_cb x (free_for_cv u)) ([(y, bind_typ V)] ++ F) ++ E).
        apply H2...
    + SCase "x not in fv e1".
      assert (x `notin` cset_fvars (free_for_cv e1)) by (rewrite AtomSetFacts.not_mem_iff; assumption).
      rewrite subst_commutes_with_free_for_cv with (u := u)...
      pick fresh y and apply typing_abs...
      * eapply wf_typ_in_subst_cb...
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
        apply (wf_typ_subst_cb (typ_capt (free_for_cv u) P)); simpl_env...
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
      rewrite foo...
      rewrite bar with (u := u)...
      pick fresh y and apply typing_tabs...
      * eapply wf_typ_in_subst_cb...
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
        apply (wf_typ_subst_cb (typ_capt (free_for_cv u) P)); simpl_env...
      * assert (y <> x) by fsetdec.
        rewrite subst_ee_open_te_var...
        rewrite subst_ct_open_tt_var...
        rewrite_env (map (subst_cb x (free_for_cv u)) ([(y, bind_sub V)] ++ F) ++ E).
        apply H2...
    + SCase "x not in fv e1".
      assert (x `notin` cset_fvars (free_for_cv e1)) by (rewrite AtomSetFacts.not_mem_iff; assumption).
      rewrite subst_commutes_with_free_for_cv with (u := u)...
      pick fresh y and apply typing_tabs...
      * eapply wf_typ_in_subst_cb...
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
        apply (wf_typ_subst_cb (typ_capt (free_for_cv u) P)); simpl_env...
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
      pose proof (sub_of_tvar _ _ _ HSub) as [Y HP]; subst...
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
        ** rewrite_env (empty ++ (F ++  [(X, bind_typ (typ_capt c p))]) ++ E).
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
    pose proof (sub_through_subst_ct _ _ _ _ _ _ _ HE HcvU) as HP.

    simpl_env in HP.
    apply typing_regular in HtypT as [WfE _].
    rewrite_env (empty ++ [(x, bind_typ U)] ++ E) in WfE.
    apply binding_uniq_from_wf_env in WfE.
    simpl_env in WfE.
    assert (x `notin` (fv_ee u)). {
      eapply notin_dom_is_notin_fv_ee...
      notin_solve.
    }
    assert (x `notin` (cset_fvars (free_for_cv u))). {
      pose proof (free_for_cv_is_free_ee u) as HA.
      inversion HA.
      subst.
      unfold cset_fvars.
      fsetdec.
    }
    assert (x `notin` (cset_fvars C)). {
      apply cv_regular in HcvU as [_ [_ WfC']].
      inversion WfC'; subst.
      - unfold cset_fvars; fsetdec.
      - unfold cset_fvars. notin_solve.
    }
    repeat (
        rewrite subst_ct_useless_repetition in HP; [|notin_solve]
      ).
    apply HP.
  }
  apply true_meaning_of with (Ap := Ap) (Am := Am)...
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

Lemma captures_from_binds : forall P x C E,
  wf_env E ->
  binds x (bind_typ (typ_capt C P)) E ->
  subcapt E x C.
Proof with eauto.
  intros* ? Binds.
  eapply wf_cset_from_binds in Binds as WfC...
  destruct C...
  eapply wf_typ_from_binds_typ in Binds as WfT...
  inversion WfT;
    match goal with
    | H : wf_cset _ _ _ |- _ =>
      inversion H
    end;
    subst.
  apply subcapt_set...
  unfold AtomSet.F.For_all.
  intros x0 HIn.
  rewrite AtomSetFacts.singleton_iff in HIn.
  symmetry in HIn.
  subst.
  eapply captures_var...
  unfold AtomSet.F.For_all.
  intros.
  apply captures_in.
  assumption.
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
           ++ destruct C; eauto using wf_cset_from_binds, captures_from_binds.
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
                eapply captures_from_binds...
              }
              let d := constr:(dom (map (subst_tb Z (typ_capt C P)) F ++ E))
              in apply sub_pre_reflexivity with (Ap := d) (Am := d)...
              apply sub_regular, proj2, proj1 in PsubQ.
              inversion PsubQ; subst.
              rewrite_nil_concat.
              eapply wf_pretyp_weakening; simpl_env.
              1: {
                match goal with
                | H : wf_pretyp _ _ _ P |- _ =>
                  apply H
                end.
              }
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
      * apply (wf_typ_come_on H0); clear Fr; fsetdec.
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
    unshelve epose proof (IHTyp2 F _)...
    unshelve epose proof (IHTyp1 F _) as SpIHTyp1...
    unshelve epose proof (cv_exists_in (map (subst_tb Z P) F ++ E) (subst_tt Z P T1') _ _) as [D HcvD]...
    assert (wf_typ_in (map (subst_tb Z P) F ++ E)
                      (typ_capt Cf (typ_arrow (subst_tt Z P T1) (subst_tt Z P T2))))...
    unshelve epose proof (cv_exists_in (map (subst_tb Z P) F ++ E) (subst_tt Z P T1) _ _) as [? ?]...
    + apply (wf_typ_in_subst_tb Q)...
    + rewrite <- open_ct_subst_tt...
      apply (typing_sub (open_ct (subst_tt Z P T2) D))...

      eapply applied_meaning_of.
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
      * apply (wf_typ_come_on H0); clear Fr; fsetdec.
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
    match goal with H : sub_pre _ _ _ |- _ =>
      inversion H; subst
    end.
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
  Admitted.
(*
  intros E S1 e1 T Typ.
  remember (exp_tabs S1 e1).
  generalize dependent e1.
  generalize dependent S1.
  induction Typ; intros S1 e0 EQ U1 U2 Sub; inversion EQ; subst.
  Case "typing_tabs".
    inversion Sub; subst.
    split...
    exists T1.
    exists (L0 `union` L).
    intros Y Fr.
    split...
    rewrite_env (empty ++ [(Y, bind_sub U1)] ++ E).
    apply (typing_narrowing S1)...
  Case "typing_sub".
    auto using (sub_transitivity T).
Qed.
*)


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
  intros * NoTyp Typ. generalize dependent e'.
  induction Typ; intros e' Red; try solve [ inversion Red; subst; eauto ].
  - Case "typing_app".
    inversion Red; subst...
    + SCase "red_abs".
      destruct (typing_inv_abs _ _ _ _ Typ1 T1 T2 Cf) as [P1 [S2 [L P2]]].
        eapply sub_reflexivity...
      pick fresh x.
      destruct (P2 x ltac:(notin_solve)) as [? [? ?]]...
      rewrite (subst_ee_intro x)...
      rewrite (subst_ct_intro x)...
      apply typing_through_subst_ee'
        with (U := T1')
            (Ap := dom ([(x, bind_typ T1')] ++ E))
            (Am := dom E) ...
      * apply (typing_sub (open_ct S2 x))...
        -- rewrite_nil_concat.
           destruct (inversion_toplevel_type E T1') as [C [P Eq]]; subst...
           rewrite_nil_concat.
           eapply (typing_narrowing_typ' T)...
           eauto using (sub_transitivity T1).
        -- rewrite_nil_concat.
          apply (sub_narrowing_typ) with (Q := T1)...
      * replace (singleton x `union` dom E)
          with (dom E `union` singleton x) by (clear Fr; fsetdec)...
        rewrite_nil_concat.
        apply wf_typ_narrowing_typ_base with (V := T)...
      * eapply wf_cset_set_weakening; [eapply typing_cv | fsetdec]...
      * apply cv_regular in H0 as [_ [_ ?]].
        eapply wf_cset_set_weakening; [ apply H0 | fsetdec ].
  - Case "typing_tapp".
    inversion Red; subst...
    SCase "red_tabs".
    admit.
    (* destruct (typing_inv_tabs _ _ _ _ Typ T1 T2 C) as [P1 [L P2]]. { *)
    (*   eapply sub_reflexivity... *)
    (* } *)
    (* pick fresh X. *)
    (* destruct (P2 X ltac:(notin_solve)) as [S2 ?]... *)
    (* rewrite (subst_te_intro X)... *)
    (* rewrite (subst_tt_intro X)... *)
    (* rewrite_env (map (subst_tb X T) empty ++ E). *)
    (* apply (typing_through_subst_te T1)... *)
Admitted.

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
  - binds_cases H0.
  - inversion H5; subst.
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
  - binds_cases H0.
  - inversion H5; subst.
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
        destruct (canonical_form_abs _ _ _ _ Val1 Typ1) as [S [e3 EQ]].
        subst.
        right.
        exists (open_ee e3 e2 (free_for_cv e2))...
  Case "typing_tapp".
    right.
    destruct IHTyp as [Val1 | [e1' Rede1']]...
    SCase "Val1".
      destruct (canonical_form_tabs _ _ _ _ Val1 Typ) as [S [e3 EQ]].
      subst.
      exists (open_te e3 T)...
Qed.
