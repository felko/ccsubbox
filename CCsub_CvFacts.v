Require Import Coq.Program.Equality.
Require Export CCsub_Hints.
Require Export CCsub_Lemmas.
Require Import TaktikZ.

Local Ltac hint := idtac.

Lemma subcapt_weakening : forall E F G C1 C2,
  subcapt (G ++ E) C1 C2 ->
  wf_env (G ++ F ++ E) ->
  subcapt (G ++ F ++ E) C1 C2.
Proof with eauto using wf_cset_weakening.
  intros * Hsc Hwf.
  remember (G ++ E).
  remember (G ++ F ++ E).
  induction Hsc ; subst...
  - apply subcapt_universal...
  - apply subcapt_in...
  - apply subcapt_set...
    intros ? ?...
Qed.

Create HintDb fsetdec.

Hint Extern 1 (_ `in` _) => fsetdec: fsetdec.

Lemma wf_cset_singleton_by_mem : forall xs b1 E A x b2,
  wf_cset E A (cset_set xs {}N b1) ->
  x `in` xs ->
  wf_cset E A (cset_set (singleton x) {}N b2).
Proof with eauto with fsetdec.
  intros * Wfxs xIn.
  inversion Wfxs; subst...
Qed.

(* NOTE: wf_cset precondition in wf_cset_singleton_by_mem0 can be proven by
         constructor, which leaves an uninstantiated evar. This approach avoids the
         problem. *)
Hint Extern 1 (wf_cset_in ?E (cset_set (singleton ?x) {}N _)) =>
match goal with
| H1 : x `in` ?xs , H2 : (wf_cset_in ?E (cset_set ?xs {}N ?b)) |- _ =>
  apply (wf_cset_singleton_by_mem xs b)
end : core.

Hint Extern 1 (wf_cset ?E ?A (cset_set (singleton ?x) {}N _)) =>
match goal with
| H1 : x `in` ?xs , H2 : (wf_cset ?E A (cset_set ?xs {}N ?b)) |- _ =>
  apply (wf_cset_singleton_by_mem xs b)
end : core.

Local Lemma __test_wf_cset_singleton1 : forall xs b1 E x b2,
  wf_cset_in E (cset_set xs {}N b1) ->
  x `in` xs ->
  wf_cset_in E (cset_set (singleton x) {}N b2).
Proof. eauto. Qed.

Local Lemma __test_wf_cset_singleton2 : forall xs b1 E A x b2,
  wf_cset E A (cset_set xs {}N b1) ->
  x `in` xs ->
  wf_cset E A (cset_set (singleton x) {}N b2).
Proof. eauto. Qed.

Lemma subcapt_reflexivity : forall E A C,
  wf_cset E A C ->
  A `subset` dom E ->
  subcapt E C C.
Proof with eauto.
  intros * WfC HSub.
  inversion WfC; subst.
  constructor...
  - intros y yIn.
    apply subcapt_in...
    apply (wf_cset_singleton_by_mem fvars univ)...
  - csetdec.
Qed.

Lemma subcapt_transitivity : forall E C1 C2 C3,
  wf_env E ->
  subcapt E C1 C2 ->
  subcapt E C2 C3 ->
  subcapt E C1 C3.
Proof with eauto with fsetdec.
  intros * WfE SC12 SC23.
  note (wf_cset_in E C3).

  rename fvars into es, univ into u.
  dependent induction SC12.
  - inversion SC23; subst.
    + apply subcapt_universal...
    + apply subcapt_universal...
    + assert (u = true) by csetdec; subst.
      apply subcapt_universal...
  - dependent induction SC23.
    + apply subcapt_universal...
    + rewrite AtomSetFacts.singleton_iff in H1; symmetry in H1; subst...
    + apply subcapt_universal...
    + rewrite AtomSetFacts.singleton_iff in H1; symmetry in H1; subst...
    + rewrite AtomSetFacts.singleton_iff in H1; symmetry in H1; subst...
    + eauto.
  - dependent induction SC23.
    + apply subcapt_universal...
    + apply subcapt_universal...
    + assert (u = true) by csetdec; subst.
      apply subcapt_universal...
  - eapply subcapt_var with (T := T)...
  - eapply subcapt_tvar with (T := T)...
  - eapply subcapt_set...
    + intros y yIn...
    + destr_bool.
      inversion SC23; subst...
      subst...
Qed.

(* Subtyping implies subcapturing *)
Lemma sub_implies_subcapt : forall E S T,
  sub E S T ->
  wf_cset_in E (cv S) ->
  wf_cset_in E (cv T) ->
  subcapt E (cv S) (cv T).
Local Ltac hint ::=
  eauto using subcapt_reflexivity.
Proof with hint.
  intros * Hsub WfC WfD.

  induction Hsub...
  eapply subcapt_tvar...
  apply IHHsub...
  apply cv_wf.
  forwards: wf_typ_from_binds_sub H...
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
  unfold cset_union; csetsimpl.
  constructor...
  unfold allbound in *...
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

Lemma dom_x_subst_away : forall x f b F E,
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
  subst_cset x C (`cset_fvar` x) = C.
Proof.
  intros.
  unfold subst_cset.
  csetdec.
Qed.

Lemma wf_env_strengthening : forall F E, wf_env (F ++ E) -> wf_env E.
Proof with eauto.
  induction F...
  intros.
  inversion H; subst...
Qed.

Lemma wf_cset_remove_fvar : forall A E C x, wf_cset E A C -> wf_cset E A (C A`\` x).
Proof with eauto.
  intros.
  unfold wf_cset_in in *.
  induction H; simpl...
  constructor...
  unfold allbound in *.
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
  intros * HwfC HwfEnv HwfD Hsset HApRsnbl Hok.
  destruct C.
  unfold subst_cset.
  forwards: binding_uniq_from_wf_env HwfEnv.
  destruct_set_mem x t...
  - apply wf_cset_union.
    + rewrite_nil_concat.
      apply wf_cset_weakening with (A := Ap'); simpl_env...
    + inversion HwfC; subst.
      constructor...
      unfold allbound in *.
      intros y yIn.
      destruct (y == x).
      * exfalso; fsetdec.
      * forwards (T & B): H4 y.
        1: fsetdec.
        simpl_env in B.
        destruct B as [B|B]; binds_cases B...
        1,2: exists (subst_ct x D T)...
  - inversion HwfC; subst.
    constructor...
    unfold allbound in *.
    intros y yIn.
    forwards (T & B): H4 y.
    1: fsetdec.
    simpl_env in B.
    destruct B as [B|B]; binds_cases B...
    1,2: exists (subst_ct x D T)...
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
    forwards: binding_uniq_from_wf_env (bind_typ Q)...
  }
  unfold wf_cset_in in *.
  replace (dom (map (subst_cb x D) F ++ E))
    with ((dom (F ++ [(x, bind_typ Q)] ++ E)) `remove` x) by (simpl_env; fsetdec).
  apply (wf_cset_subst_cb Q (dom E))...
Qed.

Lemma not_in_fv_cset_iff : forall x C,
  x A`mem` C = false -> x `notin` (`cset_fvars` C).
Proof.
  intros.
  csetdec.
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

Lemma wf_env_tail : forall F E,
  wf_env (F ++ E) ->
  wf_env E.
Proof with eauto.
  intros * Hwf.
  induction F; (trivial || inversion Hwf; subst)...
Qed.

Hint Resolve wf_env_tail : core.

(* Lemma wf_env_tail2 : forall F x b E, *)
(*   wf_env (F ++ [(x, b)] ++ E) -> *)
(*   wf_env E. *)
(* Proof with eauto. *)
(*   intros * Hwf. *)
(*   eauto using wf_env_tail. *)
(* Qed. *)

Hint Extern 1 (ok (map ?f ?F ++ ?E)) =>
match goal with
| H : wf_env (F ++ ?b ++ E) |- _ =>
  enough (ok (F ++ b ++ E))
end : core.

Lemma wf_cv_env_bind_typ : forall F x U E,
  wf_env (F ++ [(x, bind_typ U)] ++ E) ->
  wf_cset_in E (cv U).
Proof with eauto.
  intros * H.
  apply cv_wf.
  assert (wf_env ([(x, bind_typ U)] ++ E)) as HA by eauto.
  inversion HA...
Qed.

Lemma wf_typ_env_bind_typ : forall F x U E,
  wf_env (F ++ [(x, bind_typ U)] ++ E) ->
  wf_typ_in E U.
Proof with eauto.
  intros * H.
  assert (wf_env ([(x, bind_typ U)] ++ E)) as HA by eauto.
  inversion HA...
Qed.

Lemma wf_typ_env_bind_sub : forall F x U E,
  wf_env (F ++ [(x, bind_sub U)] ++ E) ->
  wf_typ_in E U.
Proof with eauto.
  intros * H.
  assert (wf_env ([(x, bind_sub U)] ++ E)) as HA by eauto.
  inversion HA...
Qed.

Hint Resolve wf_cv_env_bind_typ : core.
Hint Resolve wf_typ_env_bind_typ : core.
Hint Resolve wf_typ_env_bind_sub : core.

Lemma wf_typ_in_subst_cb_cv : forall U F E x T,
  wf_env (F ++ [(x, bind_typ U)] ++ E) ->
  wf_typ_in (F ++ [(x, bind_typ U)] ++ E) T ->
  wf_typ_in (map (subst_cb x (cv U)) F ++ E) (subst_ct x (cv U) T).
Proof with eauto*.
  intros * Hwf HwfT.
  unfold wf_typ_in.
  erewrite dom_x_subst_away...
  eapply wf_typ_subst_cb...
  1, 2: simpl_env in *; apply wf_cset_extra...
Qed.

Lemma wf_pretyp_in_subst_cb_cv : forall U F E x T,
  wf_env (F ++ [(x, bind_typ U)] ++ E) ->
  wf_pretyp_in (F ++ [(x, bind_typ U)] ++ E) T ->
  wf_pretyp_in (map (subst_cb x (cv U)) F ++ E) (subst_cpt x (cv U) T).
Proof with eauto*.
  intros * Hwf HwfT.
  unfold wf_pretyp_in.
  erewrite dom_x_subst_away...
  eapply wf_pretyp_subst_cb...
  1, 2: simpl_env in *; apply wf_cset_extra...
Qed.

Lemma wf_typ_subst_cb_cv : forall U G F E x T Ap Am,
  wf_env (G ++ F ++ [(x, bind_typ U)] ++ E) ->
  wf_typ (G ++ F ++ [(x, bind_typ U)] ++ E) Ap Am T ->
  (dom E `union` dom F) `subset` Ap ->
  (dom E `union` dom F) `subset` Am ->
  wf_typ (map (subst_cb x (cv U)) (G ++ F) ++ E) (Ap `remove` x) (Am `remove` x) (subst_ct x (cv U) T).
Proof with eauto*.
  intros * Hwf HwfT Hp Hm.
  eapply wf_typ_subst_cb; simpl_env...
  1, 2: simpl_env in *; apply wf_cset_extra...
  rewrite_env (map (subst_cb x (cv U)) (G ++ F) ++ E)...
  apply ok_from_wf_env...
  eapply wf_env_subst_cb...
  simpl_env in *...
Qed.

Lemma wf_pretyp_subst_cb_cv : forall U G F E x T Ap Am,
  wf_env (G ++ F ++ [(x, bind_typ U)] ++ E) ->
  wf_pretyp (G ++ F ++ [(x, bind_typ U)] ++ E) Ap Am T ->
  (dom E `union` dom F) `subset` Ap ->
  (dom E `union` dom F) `subset` Am ->
  wf_pretyp (map (subst_cb x (cv U)) (G ++ F) ++ E)
            (Ap `remove` x)
            (Am `remove` x)
            (subst_cpt x (cv U) T).
Proof with eauto*.
  intros * Hwf HwfT Hp Hm.
  eapply wf_pretyp_subst_cb; simpl_env...
  1, 2: simpl_env in *; apply wf_cset_extra...
  rewrite_env (map (subst_cb x (cv U)) (G ++ F) ++ E)...
  apply ok_from_wf_env...
  eapply wf_env_subst_cb...
  simpl_env in *...
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

Lemma wf_typ_in_weakening : forall T E F G,
  wf_typ_in (G ++ E) T ->
  ok (G ++ F ++ E) ->
  wf_typ_in (G ++ F ++ E) T.
Proof with eauto.
  intros * Hwf Hok.
  eapply wf_typ_weakening...
Qed.

Lemma wf_pretyp_in_weakening : forall T E F G,
  wf_pretyp_in (G ++ E) T ->
  ok (G ++ F ++ E) ->
  wf_pretyp_in (G ++ F ++ E) T.
Proof with eauto.
  intros * Hwf Hok.
  eapply wf_pretyp_weakening...
Qed.

Lemma wf_cset_in_weakening : forall E F G C,
  wf_cset_in (G ++ E) C ->
  ok (G ++ F ++ E) ->
  wf_cset_in (G ++ F ++ E) C.
Proof with eauto.
  intros * Hwf Hok.
  eapply wf_cset_weakening...
Qed.

(* Substituting the same capture set preserves subcapturing *)
Lemma subcapt_through_subst_cset : forall x U F E C1 C2 ,
  subcapt (F ++ [(x, bind_typ U)] ++ E) C1 C2 ->
  wf_env (F ++ [(x, bind_typ U)] ++ E) ->
  subcapt (map (subst_cb x (cv U)) F ++ E) (subst_cset x (cv U) C1) (subst_cset x (cv U) C2).
Proof with eauto using wf_env_subst_cb, wf_cset_subst_cb with fsetdec.
  intros * Hsc WfE.
  dependent induction Hsc.
  - assert (wf_cset_in (map (subst_cb x (cv U)) F ++ E) (subst_cset x (cv U) C)) as ?WF. {
      eapply wf_cset_in_subst_cb...
    }
    assert (wf_cset_in (map (subst_cb x (cv U)) F ++ E)
                       (subst_cset x (cv U) (cset_set xs {}N true))) as ?WF. {
      eapply wf_cset_in_subst_cb...
    }
    cbv [subst_cset] in *.
    destruct_set_mem x xs.
    + assert (wf_typ_in (F ++ [(x, bind_typ U)] ++ E) U) as HA. {
        note (wf_env ([(x, bind_typ U)] ++ E)) by eauto...
        rewrite_env (empty ++ (F ++ [(x, bind_typ U)]) ++ E).
        apply wf_typ_in_weakening; simpl_env...
      }
      forwards: cv_wf HA.
      inversion HA; subst; unfold cset_union; csetsimpl.
      * unfold cset_union in WF; csetsimpl.
        apply subcapt_universal...
        replace (cset_set ({X}A `u`A xs `\`A x) {}N true)
          with ((`cset_fvar` X) `u` (cset_set (xs `\`A x) {}N true)) by csetdec.
        apply wf_cset_union.
        (* -- enough (wf_cset_in (map (subst_cb x (`cset_fvar` X)) F ++ E) (cv X))... *)
        (*    apply wf_cset_in_subst_cb. *)
        (* unfold wf_cset_in in H2. *)
        (* 1: apply H2. *)
        1,2: admit.             (* wf_cset *)
      * inversion H2; subst.
        apply subcapt_universal...
        admit.                  (* wf_cset *)
    + apply subcapt_universal...
  - unfold subst_cset.
    destruct_set_mem x {x0}A.
    + destruct_set_mem x xs.
      2: exfalso; fsetdec.
      assert (wf_cset_in (F ++ [(x, bind_typ U)] ++ E) (cv U)) as HA. {
        note (wf_env ([(x, bind_typ U)] ++ E)) by eauto...
        rewrite_env (empty ++ (F ++ [(x, bind_typ U)]) ++ E).
        apply wf_cset_in_weakening; simpl_env...
      }
      inversion HA; subst.
      unfold cset_union; csetsimpl.
      replace (fvars `union` singleton x0 `remove` x) with fvars by fsetdec.
      apply subcapt_set...
      * admit.                  (* wf_cset *)
      * intros y yIn.
        apply subcapt_in...
        1,2: admit.             (* wf_cset *)
      * csetdec.
    + destruct_set_mem x xs.
      2: {
        apply subcapt_in...
        1,2: admit.             (* wf_cset *)
      }
      assert (wf_cset_in (F ++ [(x, bind_typ U)] ++ E) (cv U)) as HA. {
        note (wf_env ([(x, bind_typ U)] ++ E)) by eauto...
        rewrite_env (empty ++ (F ++ [(x, bind_typ U)]) ++ E).
        apply wf_cset_in_weakening; simpl_env...
      }
      inversion HA; subst.
      unfold cset_union; csetsimpl.
      apply subcapt_in...
      1,2: admit.               (* wf_cset *)
  - assert (wf_cset_in (map (subst_cb x (cv U)) F ++ E) (subst_cset x (cv U) D)). {
      eapply wf_cset_in_subst_cb...
    }
    inversion select (wf_cset_in _ D); repeat subst. (* so apparently subst isn't idempotent *)
    unfold subst_cset in *.
    find_and_destroy_set_mem; [exfalso;fsetdec|].
    find_and_destroy_set_mem.
    + note (wf_cset_in E (cv U)) by eauto; subst.
      rename select (_ = cv U) into EQ.
      rewrite <- EQ in H1.
      csetsimpl.
      csetsimpl in H1.
      apply subcapt_universal...
    + apply subcapt_universal...
  - unfold subst_cset at 1.
    destruct_set_mem x (singleton x0).
    + assert (x0 = x) by fsetdec; subst.
      assert (binds x (bind_typ U) (F ++ [(x, bind_typ U)] ++ E)) as HA by auto.
      forwards EQ: binds_typ_unique H HA; subst; clear HA.
      assert (wf_typ_in E U) by eauto.
      assert (x `notin` dom E) as HA. {
        assert (ok (F ++ [(x, bind_typ U)] ++ E)) as HA by auto.
        apply ok_tail in HA.
        inversion HA...
      }
      forwards: notin_fv_wf_typ H0 HA.
      replace (cv U `u` cset_set ({x}A `\`A x) {}N false)
              with (cv U) by (destruct U; csetdec).
      replace (cv U) with (subst_cset x (cv U) (cv U)) at 2.
      2: {
        symmetry.
        apply subst_cset_fresh.
        destruct U; simpl in *; try fsetdec.
      }
      eapply IHHsc...
    + assert (x0 <> x) by fsetdec.
      binds_cases H.
      * specialize (IHHsc x U F E ltac:(trivial) ltac:(trivial)).
        forwards: wf_typ_from_binds_typ H...
        eapply subcapt_var with (T := T)...
        replace (cv T) with (subst_cset x (cv U) (cv T)).
        2: {
          symmetry; apply subst_cset_fresh.
          assert (x `notin` dom E) as HA. {
            assert (ok (F ++ [(x, bind_typ U)] ++ E)) as HA by auto.
            apply ok_tail in HA.
            inversion HA...
          }
          forwards: notin_fv_wf_typ H1 HA.
          destruct T; simpl in *; fsetdec.
        }
        apply IHHsc...
      * assert (binds x0 (bind_typ (subst_ct x (cv U) T)) (map (subst_cb x (cv U)) F ++ E)) as HBnd by auto.
        eapply subcapt_var...
        replace (cv (subst_ct x (cv U) T))
          with (subst_cset x (cv U) (cv T)).
        2: {
          destruct T; simpl...
          - unfold subst_cset.
            destruct_if...
            exfalso;csetdec.
          - (* x is bound as a term var, therefore `x <> a`. Needs a lemma. *)
            admit.
        }
        apply IHHsc...
  - unfold subst_cset at 1.
    destruct_set_mem x (singleton x0).
    + assert (x0 = x) by fsetdec; subst.
      assert (binds x (bind_typ U) (F ++ [(x, bind_typ U)] ++ E)) as HA by auto.
      forwards EQ: binds_unique H HA.
      exfalso;congruence.
    + assert (x0 <> x) by fsetdec.
      binds_cases H.
      * specialize (IHHsc x U F E ltac:(trivial) ltac:(trivial)).
        forwards: wf_typ_from_binds_sub H...
        eapply subcapt_tvar with (T := T)...
        replace (cv T) with (subst_cset x (cv U) (cv T)).
        2: {
          symmetry; apply subst_cset_fresh.
          assert (x `notin` dom E) as HA. {
            assert (ok (F ++ [(x, bind_typ U)] ++ E)) as HA by auto.
            apply ok_tail in HA.
            inversion HA...
          }
          forwards: notin_fv_wf_typ H1 HA.
          destruct T; simpl in *; fsetdec.
        }
        apply IHHsc...
      * assert (binds x0 (bind_sub (subst_ct x (cv U) T)) (map (subst_cb x (cv U)) F ++ E)) as HBnd by auto.
        eapply subcapt_tvar...
        replace (cv (subst_ct x (cv U) T))
          with (subst_cset x (cv U) (cv T)).
        2: {
          destruct T; simpl...
          - unfold subst_cset.
            destruct_if...
            exfalso;csetdec.
          - (* x is bound as a term var, therefore `x <> a`. Needs a lemma. *)
            admit.
        }
        apply IHHsc...
  - unfold subst_cset at 1.
    destruct_set_mem x xs.
    2: {
      apply subcapt_set.
      1: admit.               (* wf_cset *)
      2: {
        (* Should we have a lemma that `cset_uvar` is not affected by subst? *)
        (* Looking at that chain, we probably should. *)
        destruct D; unfold subst_cset; destruct_if; destruct U; csetdec.
      }
      intros y yIn.
      replace (`cset_fvar` y) with (subst_cset x (cv U) (`cset_fvar` y))...
      unfold subst_cset.
      destruct_set_mem x (singleton y)...
      exfalso;fsetdec.
    }

    unfold AtomSet.F.For_all in H0.

    inversion H; subst.
    assert (wf_cset_in (F ++ [(x, bind_typ U)] ++ E) (cv U)) as HA. {
      note (wf_env ([(x, bind_typ U)] ++ E)) by eauto...
      rewrite_env (empty ++ (F ++ [(x, bind_typ U)]) ++ E).
      apply wf_cset_in_weakening; simpl_env...
    }
    inversion HA; subst.

    rename fvars into cs', univ into b__c', fvars0 into ds, univ0 into b__d.
    unfold subst_cset.
    destruct_set_mem x cs'.
    + unfold cset_union; csetsimpl.
      apply subcapt_set.
      1: admit.               (* wf_cset *)
      2: csetdec.
      intros y yIn.
      Ltac destruct_union_mem H :=
        rewrite AtomSetFacts.union_iff in H; destruct H.
      destruct_union_mem yIn. {
        apply subcapt_in...
        1,2: admit.             (* wf_cset *)
      }

      specialize (H0 y ltac:(fsetdec)); simpl in H0.
      Local Ltac cleanup_singleton_eq x y x0 x1 :=
        let HA := fresh "HA" in
        let xEQ := fresh x "EQ" in
        rename x into xEQ;
        rename x1 into x;
        assert (x0 `in` singleton x0) as HA by fsetdec;
        rewrite xEQ in HA;
        assert (x0 = y) by fsetdec;
        subst;
        clear xEQ HA.

      dependent induction H0.
      * csetsimpl.
        apply subcapt_universal.
        1,2: admit.             (* wf_cset *)
      * cleanup_singleton_eq x y x0 x1.
        apply subcapt_in...
        1,2: admit.             (* wf_cset *)
      * cleanup_singleton_eq x y x0 x1.
        rename select (_ = cv U) into EQ.
        replace (`cset_fvar` y) with (subst_cset x (cv U) (`cset_fvar` y)).
        2: {
          unfold subst_cset; simpl.
          destruct_set_mem x (singleton y); (trivial || exfalso;fsetdec).
        }
        replace (cset_set (ds `union` cs' `remove` x) {}N (b__d || b__c'))
          with (subst_cset x (cv U) (cset_set cs' {}N b__c')).
        2: {
          unfold subst_cset; simpl.
          destruct_set_mem x cs'; [|exfalso;fsetdec].
          rewrite <- EQ.
          unfold cset_union; csetsimpl...
        }
        rewrite EQ.
        eapply H1...
      * cleanup_singleton_eq x y x0 x1.
        rename select (_ = cv U) into EQ.
        replace (`cset_fvar` y) with (subst_cset x (cv U) (`cset_fvar` y)).
        2: {
          unfold subst_cset; simpl.
          destruct_set_mem x (singleton y); (trivial || exfalso;fsetdec).
        }
        replace (cset_set (ds `union` cs' `remove` x) {}N (b__d || b__c'))
          with (subst_cset x (cv U) (cset_set cs' {}N b__c')).
        2: {
          unfold subst_cset; simpl.
          destruct_set_mem x cs'; [|exfalso;fsetdec].
          rewrite <- EQ.
          unfold cset_union; csetsimpl...
        }
        rewrite EQ.
        eapply H1...
      * rename select (_ = cv U) into EQ.
        replace (`cset_fvar` y) with (subst_cset x (cv U) (`cset_fvar` y)).
        2: {
          unfold subst_cset; simpl.
          destruct_set_mem x (singleton y); (trivial || exfalso;fsetdec).
        }
        replace (cset_set (ds `union` cs' `remove` x) {}N (b__d || b__c'))
          with (subst_cset x (cv U) (cset_set cs' {}N b__c')).
        2: {
          unfold subst_cset; simpl.
          destruct_set_mem x cs'; [|exfalso;fsetdec].
          rewrite <- EQ.
          unfold cset_union; csetsimpl...
        }
        rewrite EQ.
        eapply H1...
    + unfold cset_union; csetsimpl.
      rename select (_ = cv U) into EQ.
      apply subcapt_set.
      1: admit.                (* wf_cset *)
      2: {
        specialize (H1 x ltac:(fsetdec) _ _ _ _ ltac:(reflexivity) ltac:(trivial)).
        rewrite <- EQ in H1.
        unfold subst_cset in H1.
        find_and_destroy_set_mem; [|exfalso;fsetdec].
        find_and_destroy_set_mem; [exfalso;fsetdec|].
        unfold cset_union in H1.
        csetsimpl in H1.
        destr_bool.
        inversion H1; subst; easy.
      }
      intros y yIn.
      destruct_set_mem y (xs `remove` x).
      * specialize (H0 y ltac:(fsetdec)); simpl in H0.
        dependent induction H0.
        -- apply subcapt_universal.
           1,2: admit.             (* wf_cset *)
        -- cleanup_singleton_eq x y x0 x1.
           apply subcapt_in...
           1,2: admit.             (* wf_cset *)
        -- cleanup_singleton_eq x y x0 x1.
           replace (`cset_fvar` y)
             with (subst_cset x (cv U) (`cset_fvar` y)).
           2: {
             unfold subst_cset; simpl.
             destruct_set_mem x (`cset_fvar` y); (trivial || exfalso;fsetdec).
           }
           replace (cset_set cs' {}N b__c')
             with (subst_cset x (cv U) (cset_set cs' {}N b__c')).
           2: {
             unfold subst_cset; simpl.
             destruct_set_mem x cs'; (trivial||exfalso;fsetdec).
           }
           rewrite EQ.
           eapply H1...
        -- cleanup_singleton_eq x y x0 x1.
           replace (`cset_fvar` y)
             with (subst_cset x (cv U) (`cset_fvar` y)).
           2: {
             unfold subst_cset; simpl.
             destruct_set_mem x (`cset_fvar` y); (trivial || exfalso;fsetdec).
           }
           replace (cset_set cs' {}N b__c')
             with (subst_cset x (cv U) (cset_set cs' {}N b__c')).
           2: {
             unfold subst_cset; simpl.
             destruct_set_mem x cs'; (trivial||exfalso;fsetdec).
           }
           rewrite EQ.
           eapply H1...
        -- replace (`cset_fvar` y) with (subst_cset x (cv U) (`cset_fvar` y)).
           2: {
             unfold subst_cset; simpl.
             destruct_set_mem x (`cset_fvar` y); (trivial || exfalso;fsetdec).
           }
           replace (cset_set cs' {}N b__c') with (subst_cset x (cv U) (cset_set cs' {}N b__c')).
           2: {
             unfold subst_cset; simpl.
             destruct_set_mem x cs'; (trivial||exfalso;fsetdec).
           }
           rewrite EQ.
           eapply H1...
      * destruct_union_mem yIn.
        2: exfalso...
        rename H1 into H1'.
        forwards H1: (>> H1' x xIn x U F E)...
        move H1 before H1'; clear H1'.
        unfold subst_cset at 1 in H1.
        destruct_set_mem x {x}A; [|exfalso;fsetdec].

        unfold subst_cset at 1 in H1.
        destruct_set_mem x cs'; [exfalso;fsetdec|].

        rewrite <- EQ in H1 at 2.
        csetsimpl.

        replace (ds `u`A {x}A `\`A x) with ds in H1 by fsetdec.

        enough (subcapt (map (subst_cb x (cv U)) F ++ E)
                         (`cset_fvar` y)
                         (cset_set ds {}N b__d)) as HAA. {
          rewrite EQ.
          eapply subcapt_transitivity...
        }
        eapply subcapt_in...
        forwards (? & ?): subcapt_regular H1.
        inversion select (wf_cset_in _ (cset_set ds _ _)); subst...
Admitted.
