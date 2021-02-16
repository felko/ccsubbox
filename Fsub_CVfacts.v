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
