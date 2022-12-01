Require Import Coq.Program.Equality.
Require Import TaktikZ.
Require Export CCsub_Hints.
Require Import CCsub_Subcapt.

(** **************************************** **)
(** Properties of the subtyping relation     **)
(** **************************************** **)

(* ********************************************************************** *)
(** ** Reflexivity (1) *)
Lemma sub_reflexivity : forall Γ T,
  Γ ⊢ wf ->
  Γ ⊢ T wf ->
  Γ ⊢ T <: T.
Proof with eauto using subcapt_reflexivity, wf_typ_weakening.
  intros *.
  intros Ok Wf.
  induction Wf...
  - apply sub_arr with (L := L `u`A dom Γ)...
  - apply sub_all with (L := L `u`A dom Γ)...
Qed.

(* ********************************************************************** *)
(** * #<a name="subtyping"></a># Properties of subtyping *)

(* ********************************************************************** *)
(** ** Weakening (2) *)

Lemma sub_weakening : forall Γ Θ Δ S T,
  (Δ ++ Γ) ⊢ S <: T ->
  (Δ ++ Θ ++ Γ) ⊢ wf ->
  (Δ ++ Θ ++ Γ) ⊢ S <: T.
Proof with simpl_env; eauto using wf_typ_weakening, subcapt_weakening, wf_cset_weakening.
  intros * Sub Ok.
  remember (Δ ++ Γ).
  generalize dependent Δ.
  induction Sub; intros Δ Ok EQ; subst...
  - Case "sub_arr".
    pick fresh y and apply sub_arr...
    rewrite <- concat_assoc.
    apply H0...
  - Case "sub_all".
    pick fresh Y and apply sub_all...
    rewrite <- concat_assoc.
    apply H0...
Qed.

(* ********************************************************************** *)
(** ** Strengthening (3) *)

Lemma subcapt_concrete_implies_subset_fvars : forall Γ C D,
  Γ ⊢ wf ->
  Γ ⊢ₛ C <: D ->
  ~ ( * ∈ D) ->
  (`cset_fvars` C) ⊆ (`cset_fvars` D).
Proof with eauto*.
  intros * WfEnv CsubD DNotUniv.
  assert (WfC : Γ ⊢ₛ C wf) by applys subcapt_regular CsubD.
  assert (WfD : Γ ⊢ₛ D wf) by applys subcapt_regular CsubD.
  inversion WfC; inversion WfD; subst.
  assert (univ0 = false) by (clear - DNotUniv; destruct univ0; eauto*); subst.
  assert (univ = false).
  { assert (implb univ false = true) by applys subcapt_universal_mem WfEnv CsubD.
    destruct univ... }
  subst.
  clear DNotUniv.
  dependent induction CsubD...
  - fsetdec.
  - enough (dom Γ ⊆ fvars0) by fsetdec.
    apply IHCsubD...
    all: admit.
  - admit.
  - admit.
Admitted.  

Lemma sub_strengthening : forall x U Γ Δ S T,
  x ∉ (fv_cctx Δ `u`A fv_ct S `u`A fv_ct T) ->
  (Δ ++ [(x, bind_typ U)] ++ Γ) ⊢ S <: T ->
  (Δ ++ Γ) ⊢ S <: T.
Proof with eauto using
  wf_cset_strengthen,
  wf_typ_strengthen,
  wf_env_strengthening_typ.
  intros * NotIn SsubT.
  assert (ok (Δ ++ [(x, bind_typ U)] ++ Γ)) by (apply ok_from_wf_env; applys sub_regular SsubT).
  eremember (Δ ++ [(x, bind_typ U)] ++ Γ) as Γ'.
  generalize dependent Δ.
  induction SsubT; intros Δ NotIn EQ; subst.
  - Case "sub_refl_tvar".
    constructor.
    + eapply wf_env_strengthening_typ...
      clear - NotIn; fsetdec.
    + eapply wf_typ_strengthen...
      enough (x ∉ (dom Γ `u`A dom Δ)) by fsetdec.
      apply notin_union.
      * applys fresh_mid_tail H.
      * applys fresh_mid_head H.
  - Case "sub_trans_tvar".
    apply sub_trans_tvar with (U := U0).
    + eapply binds_remove_mid...
      binds_cases H0.
      * simpl in Fr0; clear - Fr0; fsetdec.
      * intros Xeqx; subst.
        assert (x ∈ dom Δ) by applys binds_In H2.
        assert (x ∉ dom Δ) by applys fresh_mid_head H.
        apply (H1 H0).
    + apply IHSsubT.
      * assumption.
      * repeat apply notin_union.
        -- clear - NotIn; fsetdec.
        -- admit.
        -- clear - NotIn; fsetdec.  
      * reflexivity.  
  - Case "sub_capt".
    simpl in NotIn.
    apply sub_capt...
    + destruct (subcapt_regular _ _ _ H0).
      eapply subcapt_strengthening...
      * eapply wf_env_strengthening_typ...
        clear - NotIn; fsetdec.
      * eapply wf_cset_strengthen...
        clear - NotIn; fsetdec.
      * eapply wf_cset_strengthen...
        clear - NotIn; fsetdec.
  - Case "sub_top".
    apply sub_top.
    + eapply wf_env_strengthening_typ...
      clear - NotIn; fsetdec.
    + eapply wf_typ_strengthen...
      clear - NotIn H.
      repeat apply notin_union.
      * applys fresh_mid_head H.
      * fsetdec.
  - Case "sub_arrow".
    simpl in NotIn.
    apply sub_arr with (L := L `u`A {x}A `u`A dom Δ `u`A dom Γ `u`A fv_cctx Δ).
    + clear - IHSsubT NotIn H; eapply IHSsubT...
    + intros y yNotIn.
      rewrite_env (([(y, bind_typ S1)] ++ Δ) ++ Γ).
      apply H1 with (x0 := y).
      * clear - yNotIn; fsetdec.
      * apply ok_cons; repeat rewrite dom_concat; simpl...
      * clear - NotIn yNotIn.
        repeat apply notin_union.
        -- fsetdec.
        -- fsetdec.
        -- apply notin_open_ct_rec_fv_ct; fsetdec.
        -- apply notin_open_ct_rec_fv_ct; fsetdec.
      * auto.
  - Case "sub_all".
    simpl in NotIn.
    apply sub_all with (L := L `u`A {x}A `u`A dom Δ `u`A dom Γ `u`A fv_cctx Δ).
    + clear - IHSsubT NotIn H; eapply IHSsubT...
    + intros Y YNotIn.
      rewrite_env (([(Y, bind_sub R1)] ++ Δ) ++ Γ).
      eapply H1 with (X := Y).
      * clear - YNotIn; fsetdec.
      * apply ok_cons; repeat rewrite dom_concat; simpl...
      * clear - NotIn YNotIn.
        repeat apply notin_union. 
        -- fsetdec.
        -- fsetdec.
        -- apply notin_open_tt_rec_fv_ct; simpl; fsetdec.
        -- apply notin_open_tt_rec_fv_ct; simpl; fsetdec.
      * auto.
  - Case "sub_box".
    simpl in NotIn.
    apply sub_box... 
Admitted.

(* ********************************************************************** *)
(** ** Narrowing and transitivity (3) *)

Lemma subcapt_narrowing_typ : forall Δ Γ x P Q C1 C2,
  Γ ⊢ P <: Q ->
  (Δ ++ [(x, bind_typ Q)] ++ Γ) ⊢ wf ->
  (Δ ++ [(x, bind_typ Q)] ++ Γ) ⊢ₛ C1 <: C2 ->
  (Δ ++ [(x, bind_typ P)] ++ Γ) ⊢ₛ C1 <: C2.
Proof with eauto using wf_cset_narrowing_typ, wf_env_narrowing_typ.
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
      eapply (subcapt_transitivity ((typ_cv Q)))...
      apply sub_implies_subcapt...
      rewrite_env (∅ ++ (Δ ++ [(x, bind_typ P)]) ++ Γ).
      apply sub_weakening; simpl_env...
    + assert (binds x0 (bind_typ T) (Δ ++ [(x, bind_typ P)] ++ Γ)). {
        binds_cases H...
      }
      eapply subcapt_var...
  - assert (binds x0 (bind_sub T) (Δ ++ [(x, bind_typ P)] ++ Γ)). {
      binds_cases H...
    }
    eapply subcapt_tvar...
  - econstructor...
    intros ? ?...
Qed.

Definition transitivity_on Q := forall E S T,
  sub E S Q -> sub E Q T -> sub E S T.

Lemma subcapt_narrowing : forall Δ Γ Z P Q C1 C2,
  Γ ⊢ P <: Q ->
  transitivity_on Q ->
  (Δ ++ [(Z, bind_sub P)] ++ Γ) ⊢ wf ->
  (Δ ++ [(Z, bind_sub Q)] ++ Γ) ⊢ₛ C1 <: C2 ->
  (Δ ++ [(Z, bind_sub P)] ++ Γ) ⊢ₛ C1 <: C2.
Proof with eauto 6 using wf_cset_narrowing, wf_env_narrowing.
  intros * SubPQ TransQ WfE SubCap.
  dependent induction SubCap...
  - apply sub_refl_tvar; eauto using wf_typ_ignores_sub_bindings.
  - binds_cases H...
    eapply sub_trans_tvar with (U := P)...
    inversion H0; subst...
    apply TransQ...
    rewrite_env (∅ ++ (Δ ++ [(X, bind_sub P)]) ++ Γ).
    apply sub_weakening...
    simpl_env...
  - assert (binds x (bind_typ T) (Δ ++ [(Z, bind_sub P)] ++ Γ)). {
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
Qed. (** Only slow *)

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