Require Import Coq.Program.Equality.
Require Import TaktikZ.
Require Export CCsub_Hints.
Require Import CCsub_Subcapt.

(** **************************************** **)
(** Properties of the subtyping relation     **)
(** **************************************** **)

(* ********************************************************************** *)
(** ** Reflexivity (1) *)
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
  induction Wf; solve_obvious.
  (* eauto and econstructor is still broken... hence we need to proof this manually *)
  - apply sub_capt...
------
  intros *.
  intros Ok Wf HsubsetAp HsubsetAm.
  induction Wf; solve_obvious.
  - apply sub_arrow with (L := L `union` dom E)...
    intros; eapply sub_reflexivity...
  - apply sub_all with (L := L `union` dom E)...
    intros; eapply sub_reflexivity...
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
  - Case "sub_ret".
    apply sub_ret...
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
  - apply subcapt_in_fvar...
  - apply subcapt_in_lvar...
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
    + intros ? ?...
    + intros ? ?...
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
    + intros ? ?...
    + intros ? ?...
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
  intros * TransQ SsubT PsubQ.
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
      * SSCase "P <: Q".
        forwards: IHSsubT F.
        1: { congruence. }
        simpl_env in *.
        rewrite_env (empty ++ (F ++ [(Z, bind_sub P)]) ++ E).
        apply sub_weakening...
      * SSCase "Q <: T".
        binds_get H.
        inversion H1; subst...
    + SCase "X <> Z".
      forwards: IHSsubT F.
      1: { congruence. }
      simpl_env in *.
      apply (sub_trans_tvar U)...
  - eapply sub_capt...
------
  intros * TransQ SsubT PsubQ.
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
  - Case "sub_ret".
    apply sub_ret...
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
  - eapply sub_ret...
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
  - inductionThenInversion2 SsubQ QsubT...
    apply sub_ret...
    apply sub_transitivity with (Q := T1)...
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
