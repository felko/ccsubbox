Require Import Coq.Program.Equality.
Require Export Fsub_Hints.
Require Export Fsub_Lemmas.

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
