Require Import Coq.Program.Equality.
Require Import TaktikZ.

Require Import CCsub_Subcapt.
Require Import CCsub_Subtyping.
Require Import CCsub_Typing.
Require Import CCsub_Substitution.

Set Nested Proofs Allowed.


(** TODO check where this is used and maybe use "wellformed" tactic **)
Lemma wf_typ_extract_typ_arrow : forall C E T1 T2,
  wf_typ_in E (typ_capt C (typ_arrow T1 T2)) ->
  exists L, forall x, x `notin` L ->
    wf_typ ([(x, bind_typ T1)] ++ E) (dom E `union` singleton x) (dom E) (open_ct T2 (`cset_fvar` x)).
Proof with eauto.
  intros * HWf.
  inversion HWf; subst.
  inversion H5; subst...
Qed.

(** TODO check where this is used and maybe use "wellformed" tactic **)
Lemma typing_extract_typ_arrow : forall E e C T1 T2,
  typing E e (typ_capt C (typ_arrow T1 T2)) ->
  exists L, forall x, x `notin` L ->
    wf_typ ([(x, bind_typ T1)] ++ E) (dom E `union` singleton x) (dom E) (open_ct T2 (`cset_fvar` x)).
Proof with eauto.
  intros * Htyp.
  apply (wf_typ_extract_typ_arrow C)...
Qed.


(* ********************************************************************** *)
(** * #<a name="preservation"></a># Preservation *)


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
           eapply (typing_narrowing_typ T)...
           eauto using (sub_transitivity T1).

           (* lets (C & P & Eq): inversion_toplevel_type E T1'; subst... *)
           (* rewrite_nil_concat. *)
           (* eapply (typing_narrowing_typ T)... *)
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
(** * #<a name="progress"></a># Progress *)

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



(* ********************************************************************** *)
(** * #<a name="abort"></a># Proofs for Abort *)

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
      eapply wf_typ_var with (U := (typ_capt {*} typ_top))...
      + simpl_env in *. apply binds_head...
      + fsetdec.
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
    eapply typing_narrowing_typ...
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
           eapply (typing_narrowing_typ T)...
           eauto using (sub_transitivity T1).

           (* lets (C & P & Eq): inversion_toplevel_type E T1'; subst... *)
           (* rewrite_nil_concat. *)
           (* eapply (typing_narrowing_typ T)... *)
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

