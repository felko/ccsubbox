Require Import Coq.Program.Equality.
Require Export CCsub_Hints.
Require Export CCsub_Lemmas.
Require Import TaktikZ.

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

Lemma subcapt_weakening : forall E F G C1 C2,
  subcapt (G ++ E) C1 C2 ->
  wf_env (G ++ F ++ E) ->
  subcapt (G ++ F ++ E) C1 C2.
Proof with eauto using wf_cset_weakening, cv_weakening.
  intros * Hsc Hwf.
  remember (G ++ E).
  remember (G ++ F ++ E).
  induction Hsc ; subst...
  - apply subcapt_in...
  - eapply subcapt_var...
  - apply subcapt_set...
    intros ? ?...
Qed.

Create HintDb fsetdec.

Hint Extern 1 (_ `in` _) => fsetdec: fsetdec.

Lemma wf_cset_singleton_by_mem : forall E A x xs,
  wf_cset E A (cset_set xs {}N) ->
  x `in` xs ->
  wf_cset E A (cset_set (singleton x) {}N).
Proof with eauto with fsetdec.
  intros * Wfxs xIn.
  inversion Wfxs; subst...
Qed.

Hint Resolve wf_cset_singleton_by_mem : core.

Lemma subcapt_reflexivity : forall E A C,
  wf_cset E A C ->
  A `subset` dom E ->
  subcapt E C C.
Proof with eauto.
  intros * WfC HSub.
  inversion WfC; subst. {
    constructor...
  }
  apply subcapt_set...
  intros y yIn.
  apply subcapt_in...
Qed.

Lemma subcapt_transitivity : forall E C1 C2 C3,
  wf_env E ->
  subcapt E C1 C2 ->
  subcapt E C2 C3 ->
  subcapt E C1 C3.
Proof with eauto with fsetdec.
  intros * WfE SC12 SC23.
  note (wf_cset_in E C3). {
    constructor...
  }
  rename fvars into es.
  dependent induction SC12.
  - inversion SC23.
  - dependent induction SC23.
    + apply subcapt_in...
    + rewrite AtomSetFacts.singleton_iff in H1; subst...
    + apply H3...
  - eapply subcapt_var with (T := T)...
  - eapply subcapt_set...
    intros y yIn...
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
  1,2: forwards Eq: cv_unique H H0 HcvC HcvD; inversion Eq...
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
      forwards (D & HcvD): cv_exists_in HA...
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
      forwards (C2 & HcvC2 & HscC2): IHHcv G Z Q E...
      exists C2. split.
      * eapply cv_typ_var...
      * assumption.
  - exists C.
    split...
    + constructor...
    + forwards: wf_cset_narrowing P H1...
      eapply subcapt_reflexivity...
Qed.

Lemma cv_narrowing : forall T G Z Q E P C1 C2,
  sub E P Q ->
  cv (G ++ [(Z, bind_sub Q)] ++ E) T C2 ->
  cv (G ++ [(Z, bind_sub P)] ++ E) T C1 ->
  subcapt (G ++ [(Z, bind_sub P)] ++ E) C1 C2.
Proof with eauto.
  intros.
  forwards (? & ? & ?): (>> cv_narrowing_exists T G Z Q E P)...
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

Lemma wf_cset_extra : forall S2 E C,
  wf_cset_in E C ->
  dom E `subset` S2 ->
  wf_cset E S2 C.
Proof with eauto*.
  intros * HwfC.
  induction HwfC...
Qed.

Lemma dom_x_subst_away : forall F E f x b,
  wf_env (F ++ [(x, b)] ++ E) ->
  dom (map f F ++ E) = dom (F ++ [(x, b)] ++ E) `remove` x. 
Proof with eauto*.
  intros * Hwf.
  simpl_env in *.
  assert (x `notin` (dom F `union` dom E)). {
    pose proof (binding_uniq_from_ok _ F E x _ ltac:(eauto)).
    fsetdec.
  }
  fsetdec.
Qed.


Lemma wf_env_subst_cb : forall Q C x E F,
wf_env (F ++ [(x, bind_typ Q)] ++ E) ->
wf_cset_in E C ->
wf_env (map (subst_cb x C) F ++ E).
Proof with eauto using wf_typ_subst_cb, wf_cset_extra.
  intros *.
  induction F; intros Hwf HwfC; simpl_env in *;
    inversion Hwf; simpl_env in *; simpl subst_tb...
  + constructor...
    unfold wf_typ_in.
    erewrite dom_x_subst_away...
    eapply wf_typ_subst_cb...
    all : simpl_env in *; apply wf_cset_extra...
  + constructor...
    unfold wf_typ_in.
    erewrite dom_x_subst_away...
    eapply wf_typ_subst_cb...
    all : simpl_env in *; apply wf_cset_extra...
Qed.

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
Proof with eauto using wf_env_subst_cb, wf_pretyp_subst_cb, wf_typ_subst_cb, wf_cset_in_subst_cb, wf_cset_extra.
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
    unfold wf_pretyp_in.
    erewrite dom_x_subst_away...
    eapply wf_pretyp_subst_cb...
    1, 2: simpl_env in *; apply wf_cset_extra...
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

Lemma tail_not_in_head : forall (E F : env) x,
  ok (F ++ E) ->
  x `in` dom E ->
  x `notin` dom F.
Proof. 
  intros * Hok Hx.
  induction F.
  + notin_solve.
  + assert (x `notin` dom F). {
      apply IHF; inversion Hok; assumption.
    }
    destruct a; simpl_env in *...
    assert (x <> a). {
      inversion Hok; subst.
      simpl_env in *.
      fsetdec.
    }
    fsetdec.
Qed.

Lemma wf_typ_in_subst_cb_cv : forall U F E x C T,
  wf_env (F ++ [(x, bind_typ U)] ++ E) ->
  wf_typ_in (F ++ [(x, bind_typ U)] ++ E) T ->
  cv E U C ->
  wf_typ_in (map (subst_cb x C) F ++ E) (subst_ct x C T).
Proof with eauto*.
  intros * Hwf HwfT Hcv.
  pose proof (cv_regular _ _ _ Hcv) as [_ [_ _]].
  unfold wf_typ_in.
  erewrite dom_x_subst_away...
  eapply wf_typ_subst_cb...
  1, 2: simpl_env in *; apply wf_cset_extra...
  apply ok_from_wf_env...
  eapply wf_env_subst_cb...
Qed.

Lemma wf_pretyp_in_subst_cb_cv : forall U F E x C T,
  wf_env (F ++ [(x, bind_typ U)] ++ E) ->
  wf_pretyp_in (F ++ [(x, bind_typ U)] ++ E) T ->
  cv E U C ->
  wf_pretyp_in (map (subst_cb x C) F ++ E) (subst_cpt x C T).
Proof with eauto*.
  intros * Hwf HwfT Hcv.
  pose proof (cv_regular _ _ _ Hcv) as [_ [_ _]].
  unfold wf_pretyp_in.
  erewrite dom_x_subst_away...
  eapply wf_pretyp_subst_cb...
  1, 2: simpl_env in *; apply wf_cset_extra...
  apply ok_from_wf_env...
  eapply wf_env_subst_cb...
Qed.

Lemma wf_typ_subst_cb_cv : forall U G F E x C T Ap Am,
  wf_env (G ++ F ++ [(x, bind_typ U)] ++ E) ->
  wf_typ (G ++ F ++ [(x, bind_typ U)] ++ E) Ap Am T ->
  cv E U C ->
  (dom E `union` dom F) `subset` Ap ->
  (dom E `union` dom F) `subset` Am ->
  wf_typ (map (subst_cb x C) (G ++ F) ++ E) (Ap `remove` x) (Am `remove` x) (subst_ct x C T).
Proof with eauto*.
  intros * Hwf HwfT Hcv Hp Hm.
  pose proof (cv_regular _ _ _ Hcv) as [_ [_ ?]].
  eapply wf_typ_subst_cb; simpl_env...
  1, 2: simpl_env in *; apply wf_cset_extra...
  rewrite_env (map (subst_cb x C) (G ++ F) ++ E)...
  apply ok_from_wf_env...
  eapply wf_env_subst_cb...
  simpl_env in *...
Qed.

Lemma wf_pretyp_subst_cb_cv : forall U G F E x C T Ap Am,
  wf_env (G ++ F ++ [(x, bind_typ U)] ++ E) ->
  wf_pretyp (G ++ F ++ [(x, bind_typ U)] ++ E) Ap Am T ->
  cv E U C ->
  (dom E `union` dom F) `subset` Ap ->
  (dom E `union` dom F) `subset` Am ->
  wf_pretyp (map (subst_cb x C) (G ++ F) ++ E) (Ap `remove` x) (Am `remove` x) (subst_cpt x C T).
Proof with eauto*.
  intros * Hwf HwfT Hcv Hp Hm.
  pose proof (cv_regular _ _ _ Hcv) as [_ [_ _]].
  eapply wf_pretyp_subst_cb; simpl_env...
  1, 2: simpl_env in *; apply wf_cset_extra...
  rewrite_env (map (subst_cb x C) (G ++ F) ++ E)...
  apply ok_from_wf_env...
  eapply wf_env_subst_cb...
  simpl_env in *...
Qed.

Ltac destruct_set_mem a bs :=
  match type of bs with
  | AtomSet.F.t =>
    let H := fresh a "In" in
    destruct (AtomSet.F.mem a bs) eqn:H; rewrite_set_facts_in H
  | NatSet.F.t =>
    let H := fresh a "In" in
    destruct (NatSet.F.mem a bs) eqn:H; rewrite_set_facts_in H
  end.

Lemma cv_strengthen : forall F E T C,
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

(* Substituting the same capture set preserves subcapturing *)
Lemma subcapt_through_subst_cset : forall F x U E C1 C2 D,
  subcapt (F ++ [(x, bind_typ U)] ++ E) C1 C2 ->
  wf_env (F ++ [(x, bind_typ U)] ++ E) ->
  cv E U D ->
  subcapt (map (subst_cb x D) F ++ E) (subst_cset x D C1) (subst_cset x D C2).
Proof with eauto using wf_env_subst_cb, wf_cset_subst_cb with fsetdec.
  intros * Hsc WfE CvU.
  dependent induction Hsc.
  - cbn [subst_cset cset_references_fvar_dec].
    constructor...
    apply (wf_cset_in_subst_cb U)...
  - unfold subst_cset, cset_references_fvar_dec.
    destruct_set_mem x (singleton x0).
    + destruct_set_mem x xs.
      2: exfalso; fsetdec.
      note (wf_cset_in E D).
      1: simpl cset_union; constructor...
      simpl cset_union.
      rewrite elim_empty_nat_set.
      replace (fvars `union` singleton x0 `remove` x) with fvars by fsetdec.
      apply subcapt_set...
      1: admit.
      intros y yIn.
      apply subcapt_in...
      1,2: admit.
    + destruct_set_mem x xs.
      2: {
        apply subcapt_in...
        1,2: admit.
      }
      note (wf_cset_in E D).
      1: simpl; constructor...
      1: admit.
      simpl; rewrite elim_empty_nat_set.
      apply subcapt_in...
      1,2: admit.
  - unfold subst_cset at 1, cset_references_fvar_dec.
    destruct_set_mem x (singleton x0).
    + assert (x0 = x) by fsetdec; subst.
      assert (binds x (bind_typ U) (F ++ [(x, bind_typ U)] ++ E)) as HA by auto.
      forwards EQ: binds_typ_unique H HA; subst; clear HA.
      forwards: cv_through_subst_ct x U H0...
      assert (wf_typ_in E U) by auto.
      assert (x `notin` dom E) as HA. {
        assert (ok (F ++ [(x, bind_typ U)] ++ E)) as HA by auto.
        apply ok_tail in HA.
        inversion HA...
      }
      forwards: notin_fv_wf_typ H2 HA.
      rewrite <- subst_ct_fresh in H1.
      2: fsetdec.
      apply cv_strengthen in H1...
      specialize (IHHsc F x U E ltac:(trivial) ltac:(trivial) ltac:(trivial)).
      forwards EQ: cv_unique H1 CvU...
      rewrite EQ in IHHsc.
      simpl.
      replace (singleton x `remove` x) with {}.
      2: fsetdec.
      replace (cset_union D _) with D.
      2: destruct D; [simpl;auto|cset_eq_dec].
      trivial.
    + assert (x0 <> x) by fsetdec.
      binds_cases H.
      * specialize (IHHsc F x U E ltac:(trivial) ltac:(trivial) ltac:(trivial)).
        forwards: wf_typ_from_binds_typ H...
        assert (cv E T C) as HA. {
          rewrite_env ((F ++ [(x, bind_typ U)]) ++ E) in H0.
          forwards: cv_strengthen H0; simpl_env...
        }
        assert (x `notin` dom E) as HA'. {
          assert (ok (F ++ [(x, bind_typ U)] ++ E)) as HA' by auto.
          apply ok_tail in HA'.
          inversion HA'...
        }
        note (wf_cset_in E C).
        1: {
          inversion Hsc; subst.
          unfold subst_cset, cset_references_fvar_dec.
          constructor...
          forwards: binds_In H.
          constructor.
          2: simpl_env...
          intros y yIn.
          rewrite AtomSetFacts.singleton_iff in yIn; symmetry in yIn; subst...
        }
        assert (x `notin` fvars) by fsetdec.
        eapply subcapt_var with (T := T) (C := (cset_set fvars {}N)).
        1: rewrite <- nil_concat; apply binds_weaken; simpl_env...
        1: rewrite_env (empty ++ map (subst_cb x D) F ++ E); eapply cv_weakening; simpl_env...
        unfold subst_cset at 1, cset_references_fvar_dec in IHHsc.
        destruct_set_mem x fvars; [exfalso;fsetdec|].
        trivial.
      * assert (binds x0 (bind_typ (subst_ct x D T)) (map (subst_cb x D) F ++ E)) as HBnd by auto.
        forwards Cv__post: cv_through_subst_ct H0...
  - unfold subst_cset at 1, cset_references_fvar_dec.
    destruct_set_mem x xs.
    2: {
      apply subcapt_set.
      1: admit.               (* wf_cset *)
      intros y yIn.
      replace (cset_set (singleton y) {}N)
        with (subst_cset x D (cset_set (singleton y) {}N))...
      unfold subst_cset, cset_references_fvar_dec.
      destruct_set_mem x (singleton y); (trivial||exfalso;fsetdec).
    }

    unfold AtomSet.F.For_all in H1.

    note (wf_cset_in E D). {
      simpl.
      specialize (H0 x xIn).
      simpl in H0; simpl_env in H0.
      dependent induction H0.
      - unfold subst_cset, cset_references_fvar_dec.
        constructor...
      - Local Ltac cleanup_singleton_eq x y x0 x1 :=
          let HA := fresh "HA" in
          let xEQ := fresh x "EQ" in
          rename x into xEQ;
          rename x1 into x;
          assert (x0 `in` singleton x0) as HA by fsetdec;
          rewrite xEQ in HA;
          assert (x0 = y) by fsetdec;
          subst;
          clear xEQ HA.
        cleanup_singleton_eq x x x0 x1.

        unfold subst_cset, cset_references_fvar_dec.
        destruct_set_mem x xs0; [|exfalso;fsetdec]...
      - cleanup_singleton_eq x x x0 x1.
        replace T with U in *.
        2: {
          assert (binds x (bind_typ U) (F ++ [(x, bind_typ U)] ++ E)) as HBnd by auto.
          forwards: binds_unique HBnd H2.
          congruence.
        }
        replace C with cset_universal in *.
        2: {
          rewrite_env ((F ++ [(x, bind_typ U)]) ++ E) in H0.
          apply cv_strengthen in H0...
          forwards: cv_unique H0 CvU; simpl_env...
        }
        inversion H1...
      - eapply H1...
    }
    note (wf_cset_in (F ++ [(x, bind_typ U)] ++ E) D0). {
      unfold subst_cset, cset_references_fvar_dec.
      constructor...
      admit.                    (* wf_cset *)
    }

    rename fvars into ds.
    rename fvars0 into cs'.
    unfold subst_cset, cset_references_fvar_dec.
    destruct_set_mem x cs'.
    + simpl; rewrite elim_empty_nat_set.
      apply subcapt_set.
      1: admit.               (* wf_cset *)
      intros y yIn.
      Ltac destruct_union_mem H :=
        rewrite AtomSetFacts.union_iff in H; destruct H.
      destruct_union_mem yIn. {
        apply subcapt_in...
        1,2: admit.             (* wf_cset *)
      }

      specialize (H0 y ltac:(fsetdec)); simpl in H0.

      dependent induction H0.
      * cleanup_singleton_eq x y x0 x1.
        apply subcapt_in...
        1,2: admit.             (* wf_cset *)
      * cleanup_singleton_eq x y x0 x1.
        replace (cset_set (singleton y) {}N)
          with (subst_cset x (cset_set ds {}N) (cset_set (singleton y) {}N)).
        2: {
          unfold subst_cset, cset_references_fvar_dec; simpl.
          destruct_set_mem x (singleton y); (trivial || exfalso;fsetdec).
        }
        replace (cset_set (ds `union` cs' `remove` x) {}N)
          with (subst_cset x (cset_set ds {}N) (cset_set cs' {}N)).
        2: {
          unfold subst_cset, cset_references_fvar_dec; simpl.
          destruct_set_mem x cs'; [|exfalso;fsetdec].
          simpl; rewrite elim_empty_nat_set.
          trivial.
        }
        eapply H3...
      * eapply H1...
    + simpl; rewrite elim_empty_nat_set.
      apply subcapt_set.
      1: admit.                (* wf_cset *)
      intros y yIn.
      destruct_set_mem y (xs `remove` x).
      * specialize (H0 y ltac:(fsetdec)); simpl in H0.
        dependent induction H0.
        -- cleanup_singleton_eq x y x0 x1.
           apply subcapt_in...
           1,2: admit.             (* wf_cset *)
        -- cleanup_singleton_eq x y x0 x1.
           replace (cset_set (singleton y) {}N)
             with (subst_cset x (cset_set ds {}N) (cset_set (singleton y) {}N)).
           2: {
             unfold subst_cset, cset_references_fvar_dec; simpl.
             destruct_set_mem x (singleton y); (trivial || exfalso;fsetdec).
           }
           replace (cset_set cs' {}N)
             with (subst_cset x (cset_set ds {}N) (cset_set cs' {}N)).
           2: {
             unfold subst_cset, cset_references_fvar_dec; simpl.
             destruct_set_mem x cs'; (trivial||exfalso;fsetdec).
           }
           eapply H3...
        -- eapply H1...
      * destruct_union_mem yIn.
        2: exfalso...
        specialize (H1 x xIn _ _ _ _ ltac:(reflexivity) ltac:(trivial) ltac:(trivial)).
        unfold subst_cset at 1, cset_references_fvar_dec in H1.
        destruct_set_mem x (singleton x); [|exfalso;fsetdec].

        unfold subst_cset at 1, cset_references_fvar_dec in H1.
        destruct_set_mem x cs'; [exfalso;fsetdec|].

        simpl in H1; rewrite elim_empty_nat_set in H1.

        replace (ds `union` singleton x `remove` x) with ds in H1 by fsetdec.

        enough (subcapt (map (subst_cb x (cset_set ds {}N)) F ++ E)
                         (cset_set (singleton y) {}N)
                         (cset_set ds {}N)) as HA. {
          eapply subcapt_transitivity...
        }
        eapply subcapt_in...
        admit.             (* wf_cset *)
Admitted.
