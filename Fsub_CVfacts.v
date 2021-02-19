Require Import Coq.Program.Equality.
Require Export Fsub_Hints.
Require Export Fsub_Lemmas.

Local Ltac hint := idtac.


Lemma cv_unique_shrink_head : forall Y B E T C,
  wf_env ([(Y, B)] ++ E) ->
  wf_typ_in E T ->
  cv ([(Y, B)] ++ E) T C ->
  cv E T C.
Proof.
 intros*.
 intros HwfE HwfT Hcv.

 assert (type T). eapply type_from_wf_typ; eauto.

 dependent induction Hcv.
 * assert (X <> Y). {
     inversion HwfT; subst.
     assert (X `in` dom E).
     eapply binds_In. apply H6.
     inversion HwfE; subst; notin_solve.
   }
   apply cv_typ_var with (T := T).
   unfold binds in H. unfold get in H. simpl in H.
   destruct (X == Y) eqn:HXY; subst; trivial.
   easy.

   inversion HwfE; trivial.
   eapply IHHcv with (Y0 := Y) (B0 := B).
   inversion HwfT; subst.
   {
     pose proof H7.
     unfold binds in H. unfold binds in H7.
     simpl in *.
     destruct (X == Y); subst; try easy.
     rewrite H in H7; inversion H7; subst.
     simpl_env in *.
     eapply wf_typ_from_binds_sub.
     inversion H0; trivial.
     apply H3.
   }
   trivial.
   trivial.
   eapply type_from_wf_typ.
   eapply wf_typ_from_binds_sub.
   apply HwfE. apply H.
 * inversion HwfT; subst. constructor; trivial.
   inversion H; trivial.
Qed.

Lemma cv_unique_shrink : forall F E T C,
  wf_env (F ++ E) ->
  wf_typ_in E T ->
  cv (F ++ E) T C ->
  cv E T C.
Proof with eauto using cv_unique_shrink_head.
  intros* WfEnv WfTyp H.
  induction F; try destruct a; simpl_env in *...
  apply IHF. inversion WfEnv... eapply cv_unique_shrink_head...
  rewrite_nil_concat.
  eapply wf_typ_weakening...
  simpl_env.
  inversion WfEnv...
Qed.

Lemma cv_unique : forall E T C1 C2,
  wf_env E ->
  wf_typ_in E T ->
  cv E T C1 ->
  cv E T C2 ->
  C1 = C2.
Proof with eauto*.
 intros E; induction E; intros T; induction T; intros...
 - inversion H1; inversion H2; subst...
 - exfalso. inversion H0.
 - exfalso.
   inversion H0...
   inversion H7...
 - inversion H1...
   inversion H2...
 - inversion H0.
 - destruct a as [Y B].
   simpl_env in *.
   destruct (Y == a0); subst...
   + inversion H2; subst...
     inversion H1; subst...
     apply IHE with (T := T)...
     * inversion H5; trivial.
     * binds_cases H4; subst; simpl_env in *; try notin_solve...
       inversion H; trivial.
     * binds_cases H4; subst; simpl_env in *; try notin_solve...
       binds_cases H6; subst; simpl_env in *; try notin_solve...
       inversion H6; subst...
       eapply cv_unique_shrink_head...
       inversion H...
     * binds_cases H4; subst; simpl_env in *; try notin_solve...
       binds_cases H6; subst; simpl_env in *; try notin_solve...
       inversion H6; subst...
       eapply cv_unique_shrink_head...
       inversion H...
   + inversion H1; subst...
     inversion H2; subst...
     apply IHE with (T := a0)...
     * inversion H5; trivial.
     * binds_cases H4; subst; simpl_env in *; try notin_solve...
     * eapply cv_unique_shrink_head...
       binds_cases H4.
       eapply wf_typ_var...
     * eapply cv_unique_shrink_head...
       binds_cases H4.
       eapply wf_typ_var...
Qed.


Lemma cv_weakening_head : forall E F T C,
  cv E T C ->
  wf_env (F ++ E) ->
  cv (F ++ E) T C.
Proof with eauto using cv_regular.
  intros E F T C Hcv Wf.

  induction Hcv.
  - apply cv_typ_var with (T := T)...
  - apply cv_typ_capt...
    rewrite_nil_concat.
    eapply wf_pretyp_weakening...
    rewrite_nil_concat.
    eapply wf_cset_weakening...
Qed.

Lemma cv_weakening : forall E F G T C,
  cv (G ++ E) T C ->
  wf_env (G ++ F ++ E) ->
  cv (G ++ F ++ E) T C.
Proof with eauto using cv_regular, wf_pretyp_weakening, wf_cset_weakening.
  intros E F G T C Hcv Hwf.

  dependent induction Hcv.
  * apply cv_typ_var with (T := T)...
  * apply cv_typ_capt...
Qed.


Lemma cv_exists_in : forall E T,
  wf_env E ->
  wf_typ_in E T ->
  exists C, cv E T C.
Proof with eauto.
  induction E; induction T; intros; try inversion H0; try inversion H; subst...
  - inversion H5.
  - simpl_env in *.
    binds_cases H5.
    + destruct (a0 == X0).
      * subst.
        specialize (IHE T H8 H9) as [C' H'].
        exists C'.
        eapply cv_typ_var...
        apply cv_weakening_head...
      * assert (wf_typ_in E a0). { inversion H0; subst... }
        specialize (IHE a0 H8 H2) as [C' H'].
        exists C'. apply cv_weakening_head...
    + inversion H3; subst.
      specialize (IHE T H8 H9) as [C' H'].
      exists C'. eapply cv_typ_var...
      apply cv_weakening_head...
  - simpl_env in *.
    assert (wf_typ_in E a0). { inversion H0; subst... binds_cases H6... }
    specialize (IHE a0 H8 H1) as [C' H'].
    exists C'. apply cv_weakening_head...
Qed.

Lemma captures_weakening : forall E F G xs x,
  captures (G ++ E) xs x ->
  wf_env (G ++ F ++ E) ->
  captures (G ++ F ++ E) xs x.
Proof with auto.
  intros E F G xs x Hcap Hwf.
  remember (G ++ E).
  remember (G ++ F ++ E).
  induction Hcap.
  - apply captures_in...
  - apply captures_var with (T := T) (ys := ys) ; subst...
    apply cv_weakening...
    unfold AtomSet.F.For_all.
    intros.
    apply H2...
Qed.

Lemma subcapt_weakening : forall E F G C1 C2,
  subcapt (G ++ E) C1 C2 ->
  wf_env (G ++ F ++ E) ->
  subcapt (G ++ F ++ E) C1 C2.
Proof with eauto using wf_cset_weakening.
  intros E F G C1 C2 Hsc Hwf.
  remember (G ++ E).
  remember (G ++ F ++ E).
  induction Hsc ; subst...
  apply subcapt_set...
  unfold AtomSet.F.For_all.
  intros.
  apply captures_weakening...
Qed.


Lemma subcapt_reflexivity : forall E A C,
  wf_env E ->
  (* We need as a precondition that C is locally closed! *)
  wf_cset E A C ->
  AtomSet.F.Subset A (dom E) ->
  subcapt E C C.
Proof with auto.
  intros *.
  intros Ok Closed Hsubset.
  destruct C...
  - assert (t0 = {}N). { inversion Closed... }
    subst.
    apply subcapt_set...
    + apply wf_cset_set_weakening with (A := A)...
    + apply wf_cset_set_weakening with (A := A)...
    + unfold AtomSet.F.For_all. intros.
      apply captures_in...
Qed.

Lemma extract_bind_cv_from_var_cv : forall X E U C,
  binds X (bind_sub U) E ->
  cv E X C ->
  cv E U C.
Proof with eauto using cv_weakening_head.
  intros *. intros Hbinds Hcv.
  dependent induction Hcv.
  unfold binds in H, Hbinds.
  rewrite Hbinds in H.
  inversion H...
Qed.

(* Subtyping implies subcapturing *)
Lemma sub_implies_subcapt : forall E A1 A2 S T C D,
  sub E S T ->
  AtomSet.F.Subset A1 (dom E) ->
  AtomSet.F.Subset A2 (dom E) ->
  wf_cset E A1 C ->
  wf_cset E A2 D ->
  cv E S C ->
  cv E T D ->
  subcapt E C D.
Local Ltac hint ::=
  eauto using subcapt_reflexivity, cv_weakening_head, extract_bind_cv_from_var_cv.
Proof with hint.
  intros *.
  intros Hsub HssetA1 HssetA2 WfC WfD HcvC HcvD.

  induction Hsub; destruct C; destruct D; try solve [inversion HcvC; inversion HcvD; subst; hint].
  - pose proof (cv_unique _ _ _ _ H H0 HcvC HcvD) as Eq; inversion Eq...
  - pose proof (cv_unique _ _ _ _ H H0 HcvC HcvD) as Eq; inversion Eq...
  (* Alex: leaving these here in case the hint breaks... *)
  (* - pose proof (cv_unique _ _ _ _ H H0 HcvC HcvD) as Eq; inversion Eq... *)
  (* - apply IHHsub... *)
  (* - econstructor... *)
  (* - inversion HcvC; subst. *)
  (*   assert (T0 = U). { *)
  (*     rewrite_env (empty ++ [(X, bind_sub T0)] ++ E0) in H. *)
  (*     apply binds_mid_eq in H... *)
  (*     inversion H... *)
  (*   } *)
  (*   inversion HcvD; subst... *)
  (*   inversion H4; subst. *)
  (*   + assert (T0 = U). { apply binds_mid_eq in H... inversion H... } *)
  (*     subst... *)
  (*   + apply IHHsub... *)
  (* - inversion HcvC. inversion HcvD. subst... *)
  (* - inversion HcvC. inversion HcvD. subst... *)
Qed.

Lemma cv_narrowing_exists : forall T G Z Q E P C1,
  sub E P Q ->
  cv (G ++ [(Z, bind_sub Q)] ++ E) T C1 ->
  exists C2, cv (G ++ [(Z, bind_sub P)] ++ E) T C2 /\ subcapt (G ++ [(Z, bind_sub P)] ++ E) C2 C1.
Local Ltac hint ::=
  eauto using wf_env_narrowing, wf_typ_narrowing, wf_pretyp_narrowing, wf_cset_narrowing.
Proof with simpl_env; hint.
  intros* Hsub Hcv.
  dependent induction Hcv.
  - destruct (X == Z).
    + subst.
      binds_get H.
      inversion H2; subst.
      assert (wf_typ_in E Q)...
      assert (cv E Q CT). {
        apply (cv_unique_shrink (G ++ [(Z, bind_sub Q)]))...
      }
      assert (wf_typ_in E P) as HA...
      unshelve epose proof (cv_exists_in _ _ _ HA) as [D HcvD]...
      exists D. split.
      * eapply cv_typ_var...
        rewrite_env (empty ++ (G ++ [(Z, bind_sub P)]) ++ E).
        apply cv_weakening...
      * rewrite_env (empty ++ (G ++ [(Z, bind_sub P)]) ++ E).
        apply subcapt_weakening...
        apply sub_implies_subcapt with (S := P) (T := Q) (A1 := dom E) (A2 := dom E)...
    + assert (binds X (bind_sub T) (G ++ [(Z, bind_sub P)] ++ E)). {
        binds_cases H.
        - assert (wf_env (G ++ [(Z, bind_sub P)] ++ E)). {
            trivial...
          }
          apply binds_tail.
          apply binds_tail.
          + assumption.
          + simpl_env in *; trivial.
          + trivial.
        - trivial...
      }
      specialize (IHHcv G Z Q E ltac:(auto) ltac:(auto)) as [C2 [HcvC2 HscC2]].
      exists C2. split.
      * eapply cv_typ_var...
      * assumption.
  - exists C.
    split...
    + constructor...
    + apply subcapt_reflexivity with (A := dom (G ++ [(Z, bind_sub P)] ++ E)); hint.
      eapply wf_cset_narrowing...
Qed.

Lemma cv_narrowing : forall T G Z Q E P C1 C2,
  sub E P Q ->
  cv (G ++ [(Z, bind_sub Q)] ++ E) T C2 ->
  cv (G ++ [(Z, bind_sub P)] ++ E) T C1 ->
  subcapt (G ++ [(Z, bind_sub P)] ++ E) C1 C2.
Proof with eauto.
  intros.
  unshelve epose proof (cv_narrowing_exists T G Z Q E P C2 _ _) as [? [? ?]]...
  assert (x = C1). {
    apply (cv_unique (G ++ [(Z, bind_sub P)] ++ E) T)...
  }
  subst...
Qed.

Lemma cv_narrowing_typ : forall Q T G x E P C,
  sub E P Q ->
  ok (G ++ [(x, bind_typ Q)] ++ E) ->
  cv (G ++ [(x, bind_typ Q)] ++ E) T C ->
  cv (G ++ [(x, bind_typ P)] ++ E) T C.
Local Ltac hint ::=
  eauto using wf_env_narrowing_typ, wf_typ_narrowing_typ,
  wf_pretyp_narrowing_typ, wf_cset_narrowing_typ.
Proof with simpl_env; hint.
  intros * HSub Ok HCv.
  dependent induction HCv.
  - apply cv_typ_var with (T := T)...
    binds_cases H.
    + apply binds_tail. apply binds_tail... trivial.
    + apply binds_head...
  - constructor...
Qed.

(** TODO: reorganize the contents of the bottom of this file **)
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

Lemma wf_typ_subst_cb_cv : forall U Ap Am F x C E T,
  wf_env (F ++ [(x, bind_typ U)] ++ E) ->
  cv E U C ->
  wf_typ (F ++ [(x, bind_typ U)] ++ E) Ap Am T ->
  wf_typ (map (subst_cb x C) F ++ E) (Ap `remove` x) (Am `remove` x) (subst_ct x C T)
with wf_pretyp_typ_subst_cb_cv : forall U Ap Am F x C E P,
  wf_env (F ++ [(x, bind_typ U)] ++ E) ->
  cv E U C ->
  wf_pretyp (F ++ [(x, bind_typ U)] ++ E) Ap Am P ->
  wf_pretyp (map (subst_cb x C) F ++ E) (Ap `remove` x) (Am `remove` x) (subst_cpt x C P).
Proof.
Admitted.

Lemma wf_typ_in_subst_cb_cv : forall F x U C E T,
  wf_env (F ++ [(x, bind_typ U)] ++ E) ->
  cv E U C ->
  wf_typ_in (F ++ [(x, bind_typ U)] ++ E) T ->
  wf_typ_in (map (subst_cb x C) F ++ E) (subst_ct x C T)
with wf_pretyp_in_subst_cb_cv : forall F x U C E P,
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
Proof with eauto using wf_env_subst_cb, wf_pretyp_in_subst_cb_cv, wf_typ_in_subst_cb_cv, wf_cset_in_subst_cb.
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


Lemma wf_env_weaken_head : forall E F,
  wf_env (F ++ E) ->
  wf_env E.
Proof with eauto*.
  intros E F Hwf.
  induction F...
  inversion Hwf...
Qed.

Lemma captures_subenv : forall E F xs y,
  wf_env (F ++ E) ->
  captures (F ++ E) xs y ->
  y `in` dom E ->
  captures E xs y.
Proof with eauto*.
  intros * Hwf HC HyE.
  dependent induction HC...
  assert (x `notin` dom F) by admit.
  binds_cases H...
  * eapply captures_var with (T := T)...
    eapply cv_unique_shrink...
    eapply wf_typ_from_binds_typ...
    eapply wf_env_weaken_head...
    intros y HyIn.
    eapply H2...
    (** of course y is in dom E **)
    admit.
  * apply binds_In in H5. notin_solve.
Admitted.

Lemma captures_through_env_subst_set : forall F x U E ys zs C,
  wf_env (F ++ [(x, bind_typ U)] ++ E) ->
  AtomSet.F.For_all (captures (F ++ [(x, bind_typ U)] ++ E) ys) zs ->
  x `notin` zs ->
  x `notin` ys ->
  cv E U C ->
  AtomSet.F.For_all (captures (map (subst_cb x C) F ++ E) ys) zs.
Proof with eauto.
  intros * Hwf HC HfreshZ HfreshY HCv.
  intros z Hin.
  specialize (HC z Hin).
  generalize dependent zs.
  dependent induction HC; intros zs HfreshZ Hin...
  binds_cases H...

  - assert (wf_typ_in E T). {
      eapply wf_typ_from_binds_typ...
    }
    assert (cv E T (cset_set ys {}N)) as HcvT. {
      apply cv_unique_shrink in H0...
      2: {
        rewrite_nil_concat.
        eapply wf_typ_weakening...
        apply ok_from_wf_env in Hwf.
        apply ok_tail in Hwf...
      }
      apply cv_unique_shrink in H0...
    }

    eapply captures_var...
    + rewrite_nil_concat.
      apply cv_weakening; simpl_env.
      2: eauto using wf_env_subst_cb.
      apply HcvT.
    + apply cv_regular in HcvT as [_ [_ WfCvT]].
      inversion WfCvT; subst.
      apply binding_uniq_from_wf_env in Hwf as ?.
      assert (x `notin` ys) by notin_solve.
      intros y ?.
      assert (y <> x) by notin_solve.
      destruct (AtomSet.F.mem y xs) eqn:EQ; set_facts_come_on_in EQ.
      * constructor...
      * eapply H2 with (x0 := y) (zs := ys); trivial.
        eauto.
  - Case "z = x".
    exfalso; notin_solve.
    (* assert (binds x0 (bind_typ (subst_ct x C T)) (map (subst_cb x C) F ++ E)) by auto. *)
  - assert (binds z (bind_typ (subst_ct x C T)) (map (subst_cb x C) F ++ E)) by auto.
    apply cv_through_subst_ct with (D := C) in H0 as H0'...
    unfold subst_cset, cset_references_fvar_dec in H0'.
    destruct (AtomSet.F.mem x ys) eqn:EQ; set_facts_come_on_in EQ.
    + SCase "x in ys".
      destruct C; simpl in H0'.
      * specialize (H1 x EQ).
        inversion H1; subst.
        -- exfalso; notin_solve.
        -- binds_get H3.
          inversion H8; subst.
          assert (cv (empty ++ (F ++ [(x, bind_typ U)]) ++ E) U cset_universal) as HA. {
            apply cv_weakening; simpl_env...
          }
          simpl_env in HA.
          unshelve epose proof (cv_unique _ _ _ _ _ _ H5 HA)...
          easy.
      * pose proof (cv_regular _ _ _ HCv) as [_ [_ Reg]].
        inversion Reg; subst.
        rewrite elim_empty_nat_set in H0'.
        eapply captures_var...

        intros y HyIn.
        rewrite AtomSetFacts.union_iff in HyIn.
        destruct HyIn...
        -- (** y is in t, if y isn't in ys, then x was in ys,
               and we've substituted away x --> t
               
               Now, as x wasn't in xs, 
               *)
            assert (captures (F ++ [(x, bind_typ U)] ++ E) xs x).
            {
              specialize (H1 x EQ). assumption.
            }

            (**
              we have that t <: xs
            *)
            inversion H5; subst; try notin_solve.
            binds_get H6; subst...
            inversion H12; subst...
            assert (ys0 = t). {
              assert (cv (empty ++ (F ++ [(x, bind_typ U)]) ++ E) U (cset_set t {}N)) as HA. {
                apply cv_weakening; simpl_env...
              }
              simpl_env in HA.
              unshelve epose proof (cv_unique _ _ _ _ _ _ HA H7) as HA'...
              inversion HA'...
            }
            subst...

            (** and in particular, E |- t <: xs, as t is bound in E *)
            assert (AtomSet.F.For_all (captures E xs) t). {
              intros s sInT.
              pose proof (cv_regular _ _ _ H0) as [HwfFx [? Hreg]].
              rewrite_env ((F ++ [(x, bind_typ U)]) ++ E) in HwfFx.
              eapply captures_subenv.
              apply HwfFx.
              simpl_env. apply H10. assumption.
              fsetdec.
            }
            rewrite_nil_concat.
            eapply captures_weakening...
            simpl_env...
        -- eapply H2 with (x0 := y) (zs := ys `remove` x)...
           fsetdec.
    + eapply captures_var...
      intros y ?.
      assert (y <> x) by notin_solve.
      destruct (AtomSet.F.mem y xs) eqn:EQ'; set_facts_come_on_in EQ'.
      * constructor...
      * eapply H2 with (x0 := y) (zs := ys); trivial.
        eauto*.
Qed.

Lemma captures_through_env_subst_cb : forall F x U E ys z C,
  wf_env (F ++ [(x, bind_typ U)] ++ E) ->
  captures (F ++ [(x, bind_typ U)] ++ E) ys z ->
  z <> x ->
  x `notin` ys ->
  cv E U C ->
  captures (map (subst_cb x C) F ++ E) ys z.
Proof with eauto*.
  intros * Hwf HC HfreshZ HfreshYs Hcv.
  eapply captures_through_env_subst_set with (zs := singleton z)...
  + intros zz Hzzisz.
    assert (zz = z) by fsetdec; subst...
  + fsetdec.
Qed.