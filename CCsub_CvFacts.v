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

Lemma subcapt_transitivity : forall C2 E C1 C3,
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
  subcapt E (cv S) (cv T).
Local Ltac hint ::=
  eauto using subcapt_reflexivity.
Proof with hint.
  intros * Hsub.

  assert (wf_cset_in E (cv S)); [apply cv_wf|]...
  assert (wf_cset_in E (cv T)); [apply cv_wf|]...
  induction Hsub...
  eapply subcapt_tvar...
  apply IHHsub...
  apply cv_wf.
  forwards: wf_typ_from_binds_sub H1...
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

Ltac destruct_union_mem H :=
  rewrite AtomSetFacts.union_iff in H; destruct H as [H|H].

(* Substituting the same capture set preserves subcapturing *)
Lemma subcapt_through_subst_cset : forall x U C F E C1 C2 ,
  subcapt (F ++ [(x, bind_typ U)] ++ E) C1 C2 ->
  wf_env (F ++ [(x, bind_typ U)] ++ E) ->
  subcapt E C (cv U) ->
  subcapt (map (subst_cb x C) F ++ E) (subst_cset x C C1) (subst_cset x C C2).
Proof with eauto using wf_env_subst_cb, wf_cset_subst_cb with fsetdec.
  intros * Hsc WfE HscC.
  dependent induction Hsc.
  - assert (wf_cset_in (map (subst_cb x C) F ++ E) (subst_cset x C C0)) as ?WF. {
      eapply wf_cset_in_subst_cb ...
    }
    assert (wf_cset_in (map (subst_cb x C) F ++ E)
                       (subst_cset x C (cset_set xs {}N true))) as ?WF. {
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
      note (wf_cset_in E C).
      inversion HA; subst; unfold cset_union; csetsimpl.
      * unfold cset_union in WF; csetsimpl.
        apply subcapt_universal...
      * apply subcapt_universal...
    + apply subcapt_universal...
  - assert (wf_cset_in (map (subst_cb x C) F ++ E)
                       (subst_cset x C (cset_set xs {}N b))) as ?WF. {
      eapply wf_cset_in_subst_cb...
    }
    assert (wf_cset_in (map (subst_cb x C) F ++ E)
                       (subst_cset x C (`cset_fvar` x0))) as ?WF. {
      eapply wf_cset_in_subst_cb...
    }
    unfold subst_cset in *.
    destruct_set_mem x {x0}A.
    + destruct_set_mem x xs.
      2: exfalso; fsetdec.
      assert (wf_cset_in (F ++ [(x, bind_typ U)] ++ E) C) as HA. {
        note (wf_env ([(x, bind_typ U)] ++ E)) by eauto...
        rewrite_env (empty ++ (F ++ [(x, bind_typ U)]) ++ E).
        apply wf_cset_in_weakening; simpl_env...
      }
      inversion HA; subst.
      csetsimpl.
      replace (fvars `union` singleton x0 `remove` x) with fvars by fsetdec.
      apply subcapt_set...
      * intros y yIn.
        apply subcapt_in...
        eapply wf_cset_singleton_by_mem...
      * csetdec.
    + destruct_set_mem x xs.
      2: {
        apply subcapt_in...
      }
      assert (wf_cset_in (F ++ [(x, bind_typ U)] ++ E) (cv U)) as HA. {
        note (wf_env ([(x, bind_typ U)] ++ E)) by eauto...
        rewrite_env (empty ++ (F ++ [(x, bind_typ U)]) ++ E).
        apply wf_cset_in_weakening; simpl_env...
      }
      inversion HA; subst.
      note (wf_cset_in E C).
      csetsimpl.
      apply subcapt_in...
  - assert (wf_cset_in (map (subst_cb x C) F ++ E) (subst_cset x C D)). {
      eapply wf_cset_in_subst_cb...
    }
    inversion select (wf_cset_in _ D); repeat subst. (* so apparently subst isn't idempotent *)
    unfold subst_cset in *.
    find_and_destroy_set_mem; [exfalso;fsetdec|].
    find_and_destroy_set_mem.
    + note (wf_cset_in E C) by eauto; subst.
      csetsimpl.
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
      replace (C `u` cset_set ({x}A `\`A x) {}N false)
              with C by (note (wf_cset_in E C) ; csetdec).
      apply (subcapt_transitivity (cv U))... {
        rewrite_env (empty ++ (map (subst_cb x C) F ++ E)).
        apply subcapt_weakening; simpl_env...
      }
      replace (cv U) with (subst_cset x C (cv U)).
      2: {
        symmetry.
        apply subst_cset_fresh.
        destruct U; simpl in *; csetdec.
      }
      eapply IHHsc...
    + assert (x0 <> x) by fsetdec.
      binds_cases H.
      * specialize (IHHsc x U F E ltac:(trivial) ltac:(trivial)).
        forwards: wf_typ_from_binds_typ H...
        eapply subcapt_var with (T := T)...
        replace (cv T) with (subst_cset x C (cv T)).
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
      * assert (binds x0 (bind_typ (subst_ct x C T)) (map (subst_cb x C) F ++ E)) as HBnd by auto.
        eapply subcapt_var...
        replace (cv (subst_ct x C T)) with (subst_cset x C (cv T)).
        2: {
          destruct T; simpl...
          - unfold subst_cset.
            destruct_if...
            exfalso;csetdec.
          - assert (x <> a). {
              forwards WfA: wf_typ_from_binds_typ x0 a...
              assert (binds x _ (F ++ [(x, bind_typ U)] ++ E)) by auto.
              inversion WfA; subst.
              forwards: binds_unique a...
            }
            unfold subst_cset.
            destruct_set_mem x {a}A; [exfalso;fsetdec|].
            easy.
        }
        eapply IHHsc...
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
        replace (cv T) with (subst_cset x C (cv T)).
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
      * assert (binds x0 (bind_sub (subst_ct x C T)) (map (subst_cb x C) F ++ E)) as HBnd by auto.
        eapply subcapt_tvar...
        replace (cv (subst_ct x C T)) with (subst_cset x C (cv T)).
        2: {
          destruct T; simpl...
          - unfold subst_cset.
            destruct_if...
            exfalso;csetdec.
          - assert (x <> a). {
              forwards WfA: wf_typ_from_binds_sub x0 a...
              assert (binds x _ (F ++ [(x, bind_typ U)] ++ E)) by auto.
              inversion WfA; subst.
              forwards: binds_unique a...
            }
            unfold subst_cset.
            destruct_set_mem x {a}A; [exfalso;fsetdec|].
            easy.
        }
        eapply IHHsc...
  - assert (wf_cset_in (map (subst_cb x C) F ++ E)
                       (subst_cset x C (cset_set xs {}N b))) as ?WF. {
      eapply wf_cset_in_subst_cb...
      constructor.
      - intros y yIn.
        enough (wf_cset_in (F ++ [(x, bind_typ U)] ++ E) (`cset_fvar` y)) as HA. {
          inversion HA...
        }
        specialize (H0 y yIn); simpl in H0...
      - intros y yIn.
        enough (wf_cset_in (F ++ [(x, bind_typ U)] ++ E) (`cset_fvar` y)) as HA. {
          inversion HA...
        }
        specialize (H0 y yIn); simpl in H0...
    }
    assert (wf_cset_in (map (subst_cb x C) F ++ E) (subst_cset x C D)) as ?WF. {
      eapply wf_cset_in_subst_cb...
    }

    unfold subst_cset at 1.
    unfold subst_cset in WF.
    destruct_set_mem x xs.
    2: {
      apply subcapt_set...
      2: {
        (* Should we have a lemma that `cset_uvar` is not affected by subst? *)
        (* Looking at that chain, we probably should. *)
        destruct D; unfold subst_cset; destruct_if; destruct U; csetdec.
      }
      intros y yIn.
      replace (`cset_fvar` y) with (subst_cset x C (`cset_fvar` y))...
      unfold subst_cset.
      destruct_set_mem x (singleton y)...
      exfalso;fsetdec.
    }

    unfold AtomSet.F.For_all in H0.

    inversion H; subst.
      note (wf_cset_in E C).

    rename fvars into cs', univ into b__c', fvars0 into ds, univ0 into b__d.
    unfold subst_cset in WF0 |- *.
    destruct_set_mem x cs'.
    + csetsimpl.
      apply subcapt_set...
      2: csetdec.
      intros y yIn.
      destruct_union_mem yIn. {
        apply subcapt_in...
        eapply wf_cset_singleton_by_mem...
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
        apply subcapt_universal...
        applys wf_cset_singleton_by_mem (ds `u`A xs `\`A x)...
      * cleanup_singleton_eq x y x0 x1.
        apply subcapt_in...
        applys wf_cset_singleton_by_mem (ds `u`A xs `\`A x)...
      * cleanup_singleton_eq x y x0 x1.
        replace (`cset_fvar` y) with (subst_cset x (cset_set ds {}N b__d) (`cset_fvar` y)).
        2: {
          unfold subst_cset; simpl.
          destruct_set_mem x (singleton y); (trivial || exfalso;fsetdec).
        }
        replace (cset_set (ds `union` cs' `remove` x) {}N (b__d || b__c'))
          with (subst_cset x (cset_set ds {}N b__d) (cset_set cs' {}N b__c')).
        2: {
          unfold subst_cset; simpl.
          destruct_set_mem x cs'; [|exfalso;fsetdec].
          unfold cset_union; csetsimpl...
        }
        eapply H1...
      * cleanup_singleton_eq x y x0 x1.
        replace (`cset_fvar` y) with (subst_cset x (cset_set ds {}N b__d) (`cset_fvar` y)).
        2: {
          unfold subst_cset; simpl.
          destruct_set_mem x (singleton y); (trivial || exfalso;fsetdec).
        }
        replace (cset_set (ds `union` cs' `remove` x) {}N (b__d || b__c'))
          with (subst_cset x (cset_set ds {}N b__d) (cset_set cs' {}N b__c')).
        2: {
          unfold subst_cset; simpl.
          destruct_set_mem x cs'; [|exfalso;fsetdec].
          unfold cset_union; csetsimpl...
        }
        eapply H1...
      * replace (`cset_fvar` y) with (subst_cset x (cset_set ds {}N b__d) (`cset_fvar` y)).
        2: {
          unfold subst_cset; simpl.
          destruct_set_mem x (singleton y); (trivial || exfalso;fsetdec).
        }
        replace (cset_set (ds `union` cs' `remove` x) {}N (b__d || b__c'))
          with (subst_cset x (cset_set ds {}N b__d) (cset_set cs' {}N b__c')).
        2: {
          unfold subst_cset; simpl.
          destruct_set_mem x cs'; [|exfalso;fsetdec].
          unfold cset_union; csetsimpl...
        }
        eapply H1...
    + csetsimpl.
      apply subcapt_set.
      1: trivial.
      2: {
        specialize (H1 x ltac:(fsetdec) _ _ _ _ ltac:(reflexivity) ltac:(trivial) ltac:(trivial)).
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
        -- apply subcapt_universal...
        -- cleanup_singleton_eq x y x0 x1.
           apply subcapt_in...
        -- cleanup_singleton_eq x y x0 x1.
           replace (`cset_fvar` y)
             with (subst_cset x (cset_set ds {}N b__d) (`cset_fvar` y)).
           2: {
             unfold subst_cset; simpl.
             destruct_set_mem x (`cset_fvar` y); (trivial || exfalso;fsetdec).
           }
           replace (cset_set cs' {}N b__c')
             with (subst_cset x (cset_set ds {}N b__d) (cset_set cs' {}N b__c')).
           2: {
             unfold subst_cset; simpl.
             destruct_set_mem x cs'; (trivial||exfalso;fsetdec).
           }
           eapply H1...
        -- cleanup_singleton_eq x y x0 x1.
           replace (`cset_fvar` y)
             with (subst_cset x (cset_set ds {}N b__d) (`cset_fvar` y)).
           2: {
             unfold subst_cset; simpl.
             destruct_set_mem x (`cset_fvar` y); (trivial || exfalso;fsetdec).
           }
           replace (cset_set cs' {}N b__c')
             with (subst_cset x (cset_set ds {}N b__d) (cset_set cs' {}N b__c')).
           2: {
             unfold subst_cset; simpl.
             destruct_set_mem x cs'; (trivial||exfalso;fsetdec).
           }
           eapply H1...
        -- replace (`cset_fvar` y)
             with (subst_cset x (cset_set ds {}N b__d) (`cset_fvar` y)).
           2: {
             unfold subst_cset; simpl.
             destruct_set_mem x (`cset_fvar` y); (trivial || exfalso;fsetdec).
           }
           replace (cset_set cs' {}N b__c')
             with (subst_cset x (cset_set ds {}N b__d) (cset_set cs' {}N b__c')).
           2: {
             unfold subst_cset; simpl.
             destruct_set_mem x cs'; (trivial||exfalso;fsetdec).
           }
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

        csetsimpl.

        replace (ds `u`A {x}A `\`A x) with ds in H1 by fsetdec.

        enough (subcapt (map (subst_cb x (cset_set ds {}N b__d)) F ++ E)
                         (`cset_fvar` y)
                         (cset_set ds {}N b__d)) as HAA. {
          eapply subcapt_transitivity...
        }
        eapply subcapt_in...
Qed.

Lemma wf_cset_atom_union : forall E A xs ys u1 u2,
  wf_cset E A (cset_set xs {}N u1) ->
  wf_cset E A (cset_set ys {}N u2) ->
  wf_cset E A (cset_set (xs `union` ys) {}N (u1 || u2)).
Proof with eauto.
  intros * WfXs WfYs.
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
    inversion HwfD2; subst.
    forwards: wf_cset_atom_union H HwfD2.
    unfold cset_union; csetsimpl.
    apply subcapt_universal...
  - inversion HwfD2; simpl; subst...
    unfold cset_union; csetsimpl.
    inversion H0; subst.
    apply subcapt_in...
  - assert (wf_cset_in E (D `u` D2)). {
      apply wf_cset_union...
    }
    inversion H; subst; subst.
    inversion HwfD2; subst; subst.
    csetsimpl.
    apply subcapt_in_univ...
  - eapply subcapt_var...
  - eapply subcapt_tvar...
  - apply subcapt_set...
    + intros ? ?...
    + csetdec.
Qed.

Tactic Notation "subst_mem_singleton" hyp(H) :=
  rewrite AtomSetFacts.singleton_iff in H; subst.

Tactic Notation "subst_mem_singleton" "<-" hyp(H) :=
  rewrite AtomSetFacts.singleton_iff in H; symmetry in H; subst.

Lemma subcapt_singleton_mem: forall x E C D,
  wf_env E ->
  subcapt E C D ->
  x A`in` C ->
  subcapt E (`cset_fvar` x) D.
Proof with eauto with fsetdec.
  intros * WfE Hsc xIn.
  dependent induction Hsc...
  - apply subcapt_universal...
    note (wf_cset_in E C).
    eapply wf_cset_singleton_by_mem...
  - exfalso;fsetdec.
  - subst_mem_singleton xIn.
    apply (subcapt_transitivity (cv T))...
    eapply subcapt_var...
    eapply subcapt_reflexivity...
  - subst_mem_singleton xIn.
    apply (subcapt_transitivity (cv T))...
    eapply subcapt_tvar...
    eapply subcapt_reflexivity...
Qed.

Lemma subcapt_universal_mem: forall E C D,
  wf_env E ->
  subcapt E C D ->
  implb (`cset_uvar` C) (`cset_uvar` D) = true.
Proof with eauto with fsetdec.
  intros * WfE Hsc.
  dependent induction Hsc...
  csetdec.
Qed.

Lemma subcapt_union_distributivity : forall E C1 C2 D,
  wf_env E ->
  subcapt E C1 D ->
  subcapt E C2 D ->
  subcapt E (cset_union C1 C2) D.
Proof with eauto using wf_cset_union with fsetdec.
  intros * WfE HscC1 HscC2.
  assert (wf_cset_in E (cset_union C1 C2)) by auto using wf_cset_union.
  generalize dependent C2.
  dependent induction HscC1; intros C2 HscC2 WF__union...
  - note (wf_cset_in E C2); csetsimpl.
    apply subcapt_set.
    1: trivial...
    2: forwards: subcapt_universal_mem HscC2...
    intros y yIn.
    destruct_union_mem yIn.
    + subst_mem_singleton yIn.
      apply subcapt_in...
    + eapply subcapt_transitivity.
      3: apply HscC2.
      * trivial...
      * apply subcapt_in...
  - note (wf_cset_in E D); subst.
    apply subcapt_universal...
  - apply (subcapt_transitivity (cv T `u` C2))...
    assert (wf_cset_in E (cv T `u` C2)) as WfU by auto using wf_cset_union.
    note (wf_cset_in E C2).
    note (wf_cset_in E (cv T)).
    rewrite <- H2 in WfU.
    csetsimpl.
    apply subcapt_set...
    2: csetdec.
    intros y yIn.
    destruct_union_mem yIn.
    + subst_mem_singleton yIn.
      apply (subcapt_transitivity (cv T))...
      * eapply subcapt_var...
        eapply subcapt_reflexivity...
      * rewrite <- H2.
        apply subcapt_set...
        2: csetdec.
        intros z zIn.
        apply subcapt_in...
    + apply subcapt_in...
  - apply (subcapt_transitivity (cv T `u` C2))...
    assert (wf_cset_in E (cv T `u` C2)) as WfU by auto using wf_cset_union.
    note (wf_cset_in E C2).
    note (wf_cset_in E (cv T)).
    rewrite <- H2 in WfU.
    csetsimpl.
    apply subcapt_set...
    2: csetdec.
    intros y yIn.
    destruct_union_mem yIn.
    + subst_mem_singleton yIn.
      apply (subcapt_transitivity (cv T))...
      * eapply subcapt_tvar...
        eapply subcapt_reflexivity...
      * rewrite <- H2.
        apply subcapt_set...
        2: csetdec.
        intros z zIn.
        apply subcapt_in...
    + apply subcapt_in...
  - note (wf_cset_in E C2); csetsimpl.
    apply subcapt_set...
    2: forwards: subcapt_universal_mem HscC2; csetdec...
    intros y yIn.
    destruct_union_mem yIn...
    apply (subcapt_transitivity (cset_set fvars {}N univ))...
Qed.

Lemma cset_union_symmetrical : forall C D,
  cset_union C D = cset_union D C.
Proof with eauto.
  intros.
  destruct C; destruct D; simpl; try easy.
  csetdec.
Qed.

Lemma union_under_subcapturing : forall E C1 C2 D1 D2,
  wf_env E ->
  subcapt E C1 C2 ->
  subcapt E D1 D2 ->
  subcapt E (cset_union C1 D1) (cset_union C2 D2).
Proof with eauto.
  intros * WfE Hsc1 Hsc2.
  apply subcapt_union_distributivity...
  - apply subcapt_expansion...
  - rewrite cset_union_symmetrical.
    apply subcapt_expansion...
Qed.

Lemma subcapt_through_subst_tt : forall E P Q F X C D,
  wf_env (F ++ [(X, bind_sub Q)] ++ E) ->
  subcapt (F ++ [(X, bind_sub Q)] ++ E) C D ->
  sub E P Q ->
  subcapt (map (subst_tb X P) F ++ E) (subst_cset X (cv P) C) (subst_cset X (cv P) D).
Proof with eauto using wf_env_subst_tb, wf_cset_in_subst_tb, wf_typ_in_subst_tb with fsetdec.
  intros * Hwf Hsc Hsub.
  generalize dependent P.
  dependent induction Hsc; intros P Hsub.
  - assert (wf_cset_in (map (subst_tb X P) F ++ E) (subst_cset X (cv P) C)) as ?WF...
    assert (wf_cset_in (map (subst_tb X P) F ++ E)
                       (subst_cset X (cv P) (cset_set xs {}N true))) as ?WF...
    cbv [subst_cset] in *.
    destruct_set_mem X xs.
    + assert (wf_typ_in (F ++ [(X, bind_sub Q)] ++ E) P) as HA. {
        note (wf_env ([(X, bind_sub Q)] ++ E)) by eauto...
        rewrite_env (empty ++ (F ++ [(X, bind_sub Q)]) ++ E).
        apply wf_typ_in_weakening; simpl_env...
      }
      forwards: cv_wf HA.
      inversion HA; subst; simpl.
      * simpl in *; csetsimpl.
        apply subcapt_universal...
      * simpl in *; csetsimpl.
        apply subcapt_universal...
    + apply subcapt_universal...
  - assert (wf_cset_in (map (subst_tb X P) F ++ E) (subst_cset X (cv P) (`cset_fvar` x))) as ?WF...
    assert (wf_cset_in (map (subst_tb X P) F ++ E)
                       (subst_cset X (cv P) (cset_set xs {}N b))) as ?WF...
    unfold subst_cset in *.
    destruct_set_mem X {x}A.
    + destruct_set_mem X xs.
      2: exfalso; fsetdec.
      assert (wf_cset_in (F ++ [(X, bind_sub Q)] ++ E) (cv P)) as HA. {
        note (wf_env ([(X, bind_sub Q)] ++ E)) by eauto...
        rewrite_env (empty ++ (F ++ [(X, bind_sub Q)]) ++ E).
        apply wf_cset_in_weakening; simpl_env; [apply cv_wf|]...
      }
      inversion HA; subst; csetsimpl.
      replace (fvars `union` singleton x `remove` X) with fvars by fsetdec.
      rename select (_ = cv P) into EQ.
      rewrite <- EQ in WF0; csetsimpl in WF0.
      apply subcapt_set...
      * intros y yIn.
        apply subcapt_in...
        eapply wf_cset_singleton_by_mem...
      * csetdec.
    + destruct_set_mem X xs.
      2: {
        apply subcapt_in...
      }
      assert (wf_cset_in (F ++ [(X, bind_sub Q)] ++ E) (cv P)) as HA. {
        note (wf_env ([(X, bind_sub Q)] ++ E)) by eauto...
        rewrite_env (empty ++ (F ++ [(X, bind_sub Q)]) ++ E).
        apply wf_cset_in_weakening; simpl_env; [apply cv_wf|]...
      }
      inversion HA; subst; csetsimpl.
      rename select (_ = cv P) into EQ.
      rewrite <- EQ in WF0; csetsimpl in WF0.
      apply subcapt_in...
  - assert (wf_cset_in (map (subst_tb X P) F ++ E) (subst_cset X (cv P) D))...
    inversion select (wf_cset_in _ D); repeat subst. (* so apparently subst isn't idempotent *)
    unfold subst_cset in *.
    find_and_destroy_set_mem; [exfalso;fsetdec|].
    find_and_destroy_set_mem.
    + assert (wf_cset_in E (cv P)) as HA; [|inversion HA; subst]. {
        apply cv_wf...
      }
      rename select (_ = cv P) into EQ.
      rewrite <- EQ in H1.
      csetsimpl.
      apply subcapt_universal...
    + apply subcapt_universal...
  - unfold subst_cset at 1.
    destruct_set_mem X {x}A.
    + assert (x = X) by fsetdec; subst.
      assert (binds X (bind_sub Q) (F ++ [(X, bind_sub Q)] ++ E)) as HA by auto.
      forwards: binds_unique (bind_typ T) (bind_sub Q)...
      congruence.
    + assert (x <> X) by fsetdec.
      binds_cases H.
      * specialize (IHHsc X F Q E ltac:(trivial) ltac:(trivial) ltac:(trivial)).
        forwards: wf_typ_from_binds_typ H...
        eapply subcapt_var with (T := T)...
        replace (cv T) with (subst_cset X (cv P) (cv T)).
        2: {
          symmetry; apply subst_cset_fresh.
          assert (X `notin` dom E) as HA. {
            assert (ok (F ++ [(X, bind_sub Q)] ++ E)) as HA by auto.
            apply ok_tail in HA.
            inversion HA...
          }
          forwards: notin_fv_wf_typ H1 HA.
          destruct T; simpl in *; fsetdec.
        }
        apply IHHsc...
      * assert (binds x (bind_typ (subst_tt X P T)) (map (subst_tb X P) F ++ E)) as HBnd by auto.
        eapply subcapt_var...
        replace (cv (subst_tt X P T))
          with (subst_cset X (cv P) (cv T)).
        1: eapply IHHsc...
        1: {
          destruct T; simpl...
          - unfold subst_cset.
            destruct_if...
            exfalso;csetdec.
          - unfold subst_cset.
            destruct (a == X); destruct_set_mem X {a}A; try (exfalso;fsetdec).
            2: simpl...
            note (wf_typ_in E P); simpl; unfold cset_union; csetdec.
        }
  - unfold subst_cset at 1.
    destruct_set_mem X (singleton x).
    + assert (x = X) by fsetdec; subst.
      assert (binds X (bind_sub Q) (F ++ [(X, bind_sub Q)] ++ E)) as HBnd by auto.
      forwards EQ: binds_unique H HBnd.
      inversion EQ; subst.
      assert (wf_typ_in E P) as WfP by eauto.
      assert (wf_typ_in E Q) as WfQ by eauto.
      assert (X `notin` dom E) as HA. {
        assert (ok (F ++ [(X, bind_sub Q)] ++ E)) as HA by auto.
        apply ok_tail in HA.
        inversion HA...
      }
      forwards: notin_fv_wf_typ WfP HA.
      forwards: notin_fv_wf_typ WfQ HA.
      replace (cv P `u` cset_set ({X}A `\`A X) {}N false)
        with (cv P) by (destruct P; csetdec).
      replace (cv P) with (subst_cset X (cv P) (cv P)) at 1.
      2: {
        symmetry.
        apply subst_cset_fresh.
        destruct P; simpl in *; try fsetdec.
      }
      apply (subcapt_transitivity (subst_cset X (cv P) (cv Q)))...
      eenough (subcapt E _ _) as HE. {
        rewrite_env (empty ++ (map (subst_tb X P) F ++ E)).
        apply subcapt_weakening; simpl_env...
      }
      do 2 erewrite <- cv_subst_ct_correspondence by fsetdec.
      do 2 erewrite <- subst_ct_fresh by fsetdec.
      apply sub_implies_subcapt.
      1: trivial.
      all: apply cv_wf...
    + assert (x <> X) by fsetdec.
      binds_cases H.
      * specialize (IHHsc X F Q E ltac:(trivial) ltac:(trivial) ltac:(trivial)).
        forwards: wf_typ_from_binds_sub H...
        eapply subcapt_tvar with (T := T)...
        replace (cv T) with (subst_cset X (cv P) (cv T)).
        2: {
          symmetry; apply subst_cset_fresh.
          assert (X `notin` dom E) as HA. {
            assert (ok (F ++ [(X, bind_sub Q)] ++ E)) as HA by auto.
            apply ok_tail in HA.
            inversion HA...
          }
          forwards: notin_fv_wf_typ H1 HA.
          destruct T; simpl in *; fsetdec.
        }
        apply IHHsc...
      * assert (binds x (bind_sub (subst_tt X P T)) (map (subst_tb X P) F ++ E)) as HBnd by auto.
        eapply subcapt_tvar...
        replace (cv (subst_tt X P T))
          with (subst_cset X (cv P) (cv T)).
        1: eapply IHHsc...
        1: {
          destruct T; simpl...
          - unfold subst_cset.
            destruct_if...
            exfalso;csetdec.
          - unfold subst_cset.
            destruct (a == X); destruct_set_mem X {a}A; try (exfalso;fsetdec).
            2: simpl...
            note (wf_typ_in E P); simpl; unfold cset_union; csetdec.
        }
  - assert (wf_cset_in (map (subst_tb X P) F ++ E)
                       (subst_cset X (cv P) (cset_set xs {}N b))) as ?WF. {
      eapply wf_cset_in_subst_tb...
      constructor.
      - intros y yIn.
        enough (wf_cset_in (F ++ [(X, bind_sub Q)] ++ E) (`cset_fvar` y)) as HA. {
          inversion HA...
        }
        specialize (H0 y yIn); simpl in H0...
      - intros y yIn.
        enough (wf_cset_in (F ++ [(X, bind_sub Q)] ++ E) (`cset_fvar` y)) as HA. {
          inversion HA...
        }
        specialize (H0 y yIn); simpl in H0...
    }
    assert (wf_cset_in (map (subst_tb X P) F ++ E)
                       (subst_cset X (cv P) D)) as ?WF. {
      eapply wf_cset_in_subst_tb...
    }

    unfold subst_cset at 1.
    unfold subst_cset in WF.
    destruct_set_mem X xs.
    2: {
      apply subcapt_set...
      2: {
        (* Should we have a lemma that `cset_uvar` is not affected by subst? *)
        (* Looking at that chain, we probably should. *)
        destruct D; unfold subst_cset; destruct_if; destruct P; simpl; csetdec.
      }
      intros y yIn.
      assert (X <> y) by notin_solve.
      replace (`cset_fvar` y) with (subst_cset X (cv P) (`cset_fvar` y))...
      unfold subst_cset.
      destruct_set_mem X (singleton y)...
      exfalso;fsetdec.
    }

    unfold AtomSet.F.For_all in H0.

    inversion H; subst.
    assert (wf_cset_in (F ++ [(X, bind_sub Q)] ++ E) (cv P)) as HA. {
      note (wf_env ([(X, bind_sub Q)] ++ E)) by eauto...
      rewrite_env (empty ++ (F ++ [(X, bind_sub Q)]) ++ E).
      apply wf_cset_in_weakening; simpl_env; [apply cv_wf|]...
    }
    inversion HA; subst.

    rename fvars into cs', univ into b__c', fvars0 into ds, univ0 into b__d.
    unfold subst_cset in WF0 |- *.
    destruct_set_mem X cs'.
    + rename select (_ = cv P) into EQ.
      rewrite <- EQ in WF, WF0.
      csetsimpl.
      apply subcapt_set...
      2: csetdec.
      intros y yIn.
      destruct_union_mem yIn. {
        apply subcapt_in...
        eapply wf_cset_singleton_by_mem...
      }

      specialize (H0 y ltac:(fsetdec)); simpl in H0.
      Local Ltac cleanup_singleton_eq' x y x0 :=
        let HA := fresh "HA" in
        let xEQ := fresh x "EQ" in
        rename x into xEQ;
        assert (x0 `in` singleton x0) as HA by fsetdec;
        rewrite xEQ in HA;
        assert (x0 = y) by fsetdec;
        subst;
        clear xEQ HA.

      dependent induction H0.
      * csetsimpl.
        apply subcapt_universal...
        applys wf_cset_singleton_by_mem (ds `u`A xs `\`A X)...
      * cleanup_singleton_eq' x y x0.
        apply subcapt_in...
        applys wf_cset_singleton_by_mem (ds `u`A xs `\`A X)...
      * cleanup_singleton_eq' x y x0.
        rename select (_ = cv P) into EQ.
        replace (`cset_fvar` y) with (subst_cset X (cv P) (`cset_fvar` y)).
        2: {
          unfold subst_cset; simpl.
          destruct_set_mem X (singleton y); (trivial || exfalso;fsetdec).
        }
        replace (cset_set (ds `union` cs' `remove` X) {}N (b__d || b__c'))
          with (subst_cset X (cv P) (cset_set cs' {}N b__c')).
        2: {
          unfold subst_cset; simpl.
          destruct_set_mem X cs'; [|exfalso;fsetdec].
          rewrite <- EQ.
          csetsimpl...
        }
        (* rewrite EQ. *)
        eapply H1...
      * cleanup_singleton_eq' x y x0.
        rename select (_ = cv P) into EQ.
        replace (`cset_fvar` y) with (subst_cset X (cv P) (`cset_fvar` y)).
        2: {
          unfold subst_cset; simpl.
          destruct_set_mem X (singleton y); (trivial || exfalso;fsetdec).
        }
        replace (cset_set (ds `union` cs' `remove` X) {}N (b__d || b__c'))
          with (subst_cset X (cv P) (cset_set cs' {}N b__c')).
        2: {
          unfold subst_cset; simpl.
          destruct_set_mem X cs'; [|exfalso;fsetdec].
          rewrite <- EQ.
          unfold cset_union; csetsimpl...
        }
        eapply H1...
      * rename select (_ = cv P) into EQ.
        replace (`cset_fvar` y) with (subst_cset X (cv P) (`cset_fvar` y)).
        2: {
          unfold subst_cset; simpl.
          destruct_set_mem X (singleton y); (trivial || exfalso;fsetdec).
        }
        replace (cset_set (ds `union` cs' `remove` X) {}N (b__d || b__c'))
          with (subst_cset X (cv P) (cset_set cs' {}N b__c')).
        2: {
          unfold subst_cset; simpl.
          destruct_set_mem X cs'; [|exfalso;fsetdec].
          rewrite <- EQ.
          csetsimpl...
        }
        eapply H1...
    + csetsimpl.
      rename select (_ = cv P) into EQ.
      apply subcapt_set.
      1: trivial...
      2: {
        forwards SpH1: H1 X X F Q E...
        rewrite <- EQ in SpH1.
        unfold subst_cset in SpH1.
        find_and_destroy_set_mem; [|exfalso;fsetdec].
        find_and_destroy_set_mem; [exfalso;fsetdec|].
        csetsimpl in SpH1.
        destr_bool.
        inversion SpH1; subst; easy.
      }
      intros y yIn.
      destruct_set_mem y (xs `remove` X).
      * specialize (H0 y ltac:(fsetdec)); simpl in H0.
        dependent induction H0.
        -- apply subcapt_universal...
           rewrite <- EQ in WF; csetsimpl; applys wf_cset_singleton_by_mem yIn...
        -- cleanup_singleton_eq' x y x0.
           apply subcapt_in...
        -- cleanup_singleton_eq' x y x0.
           replace (`cset_fvar` y)
             with (subst_cset X (cv P) (`cset_fvar` y)).
           2: {
             unfold subst_cset; simpl.
             destruct_set_mem X (`cset_fvar` y); (trivial || exfalso;fsetdec).
           }
           replace (cset_set cs' {}N b__c')
             with (subst_cset X (cv P) (cset_set cs' {}N b__c')).
           2: {
             unfold subst_cset; simpl.
             destruct_set_mem X cs'; (trivial||exfalso;fsetdec).
           }
           eapply H1...
        -- cleanup_singleton_eq' x y x0.
           replace (`cset_fvar` y)
             with (subst_cset X (cv P) (`cset_fvar` y)).
           2: {
             unfold subst_cset; simpl.
             destruct_set_mem X (`cset_fvar` y); (trivial || exfalso;fsetdec).
           }
           replace (cset_set cs' {}N b__c')
             with (subst_cset X (cv P) (cset_set cs' {}N b__c')).
           2: {
             unfold subst_cset; simpl.
             destruct_set_mem X cs'; (trivial||exfalso;fsetdec).
           }
           eapply H1...
        -- replace (`cset_fvar` y)
             with (subst_cset X (cv P) (`cset_fvar` y)).
           2: {
             unfold subst_cset; simpl.
             destruct_set_mem X (`cset_fvar` y); (trivial || exfalso;fsetdec).
           }
           replace (cset_set cs' {}N b__c')
             with (subst_cset X (cv P) (cset_set cs' {}N b__c')).
           2: {
             unfold subst_cset; simpl.
             destruct_set_mem X cs'; (trivial||exfalso;fsetdec).
           }
           eapply H1...
      * destruct_union_mem yIn.
        2: exfalso...
        rename H1 into H1'.
        forwards H1: (>> H1' X XIn X F Q E)...
        move H1 before H1'; clear H1'.
        unfold subst_cset at 1 in H1.
        destruct_set_mem X {X}A; [|exfalso;fsetdec].

        unfold subst_cset at 1 in H1.
        destruct_set_mem X cs'; [exfalso;fsetdec|].

        rewrite <- EQ in H1.
        csetsimpl.

        replace (ds `u`A {X}A `\`A X) with ds in H1 by fsetdec.

        enough (subcapt (map (subst_tb X P) F ++ E)
                         (`cset_fvar` y)
                         (cset_set ds {}N b__d)) as HAA. {
          eapply subcapt_transitivity...
        }
        eapply subcapt_in...
        forwards (? & ?): subcapt_regular H1.
        inversion select (wf_cset_in _ (cset_set ds _ _)); subst...
Qed.

(* ********************************************************************** *)
(** ** Narrowing and transitivity (3) *)

Lemma wf_cset_from_binds : forall b x E,
  wf_env E ->
  binds x (bind_typ b) E ->
  wf_cset_in E (`cset_fvar` x).
Proof.
  intros.
  econstructor.
  - intros x0 HIn.
    rewrite AtomSetFacts.singleton_iff in HIn.
    subst.
    eauto.
  - apply binds_In in H0.
    fsetdec.
Qed.

Lemma subcapt_from_binds : forall P x C E,
  wf_env E ->
  binds x (bind_typ (typ_capt C P)) E ->
  subcapt E (`cset_fvar` x) C.
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

Lemma subst_cset_across_subcapt : forall E x C D C0 A,
  wf_env E ->
  wf_cset E A C0 ->
  A `subset` dom E ->
  subcapt E C D ->
  subcapt E (subst_cset x C C0) (subst_cset x D C0).
Proof with eauto.
  intros * WfEnv Wf Subset Sub.
  assert (wf_cset_in E (subst_cset x C C0)). {
    unfold subst_cset.
    destruct_set_mem x (`cset_fvars` C0).
    2: eapply wf_cset_set_weakening...
    apply wf_cset_union...
    apply wf_cset_remove_fvar.
    eapply wf_cset_set_weakening...
  }
  assert (wf_cset_in E (subst_cset x D C0)). {
    unfold subst_cset.
    destruct_set_mem x (`cset_fvars` C0).
    2: eapply wf_cset_set_weakening...
    apply wf_cset_union...
    apply wf_cset_remove_fvar.
    eapply wf_cset_set_weakening...
  }

  inversion Wf; subst.
  rename fvars into zs.

  note (wf_cset_in E C).
  rename fvars into cs.

  note (wf_cset_in E D).
  rename fvars into ds.

  unfold subst_cset in H0, H |- *; destruct_set_mem x zs.
  2: {
    eapply subcapt_reflexivity...
  }

  dependent induction Sub.
  - csetsimpl.
    apply subcapt_universal...
  - csetsimpl.
    apply subcapt_set...
    2: csetdec.
    intros y yIn.
    apply subcapt_in...
    destruct_union_mem yIn; csetdec.
  - csetsimpl.
    apply subcapt_universal...
  - csetsimpl.
    apply subcapt_set...
    2: csetdec.
    intros y yIn.
    destruct_union_mem yIn.
    2: {
      apply subcapt_in...
      2: fsetdec.
      rename select (wf_cset_in E (cset_set (ds `u`A zs `\`A x) _ _)) into WF.
      applys wf_cset_singleton_by_mem WF.
      fsetdec.
    }
    rename select (y `in`A _) into yIn.
    apply AtomSetFacts.singleton_iff in yIn; symmetry in yIn; subst.
    eapply subcapt_var...
    apply (subcapt_transitivity (cset_set ds {}N univ1))...
    apply subcapt_set...
    2: csetdec.
    intros z zIn.
    apply subcapt_in...
    fsetdec.
  - csetsimpl.
    apply subcapt_set...
    2: csetdec.
    intros y yIn.
    destruct_union_mem yIn.
    2: {
      apply subcapt_in...
      2: fsetdec.
      rename select (wf_cset_in E (cset_set (ds `u`A zs `\`A x) _ _)) into WF.
      applys wf_cset_singleton_by_mem WF.
      fsetdec.
    }
    rename select (y `in`A _) into yIn.
    apply AtomSetFacts.singleton_iff in yIn; symmetry in yIn; subst.
    eapply subcapt_tvar...
    apply (subcapt_transitivity (cset_set ds {}N univ1))...
    apply subcapt_set...
    2: csetdec.
    intros z zIn.
    apply subcapt_in...
    fsetdec.
  - csetsimpl.
    apply subcapt_set...
    2: csetdec.
    intros y yIn.
    destruct_union_mem yIn.
    2: {
      apply subcapt_in...
      2: fsetdec.
      rename select (wf_cset_in E (cset_set (cs `u`A zs `\`A x) _ _)) into WF.
      applys wf_cset_singleton_by_mem WF.
      fsetdec.
    }
    apply (subcapt_transitivity (cset_set ds {}N univ1))...

    apply subcapt_set...
    2: csetdec.
    intros z zIn.
    apply subcapt_in...
    fsetdec.
Qed.

Lemma capt_from_wf_cset_in : forall E C, wf_cset_in E C -> capt C.
Proof. eauto using capt_from_wf_cset. Qed.

Hint Resolve capt_from_wf_cset_in : core.

Lemma wf_typ_in_subst_cset : forall x U C F E T,
  wf_env (F ++ [(x, bind_typ U)] ++ E) ->
  wf_typ_in (F ++ [(x, bind_typ U)] ++ E) T ->
  wf_cset_in E C ->
  wf_typ_in (map (subst_cb x C) F ++ E) (subst_ct x C T).
Proof with eauto*.
  intros * Hwf HwfT HwfC.
  unfold wf_typ_in.
  erewrite dom_x_subst_away...
  eapply wf_typ_subst_cb...
  1, 2: simpl_env in *; apply wf_cset_extra...
Qed.

Lemma wf_pretyp_in_subst_cset : forall x U C F E T,
  wf_env (F ++ [(x, bind_typ U)] ++ E) ->
  wf_pretyp_in (F ++ [(x, bind_typ U)] ++ E) T ->
  wf_cset_in E C ->
  wf_pretyp_in (map (subst_cb x C) F ++ E) (subst_cpt x C T).
Proof with eauto*.
  intros * Hwf HwfT HwfC.
  unfold wf_pretyp_in.
  erewrite dom_x_subst_away...
  eapply wf_pretyp_subst_cb...
  1, 2: simpl_env in *; apply wf_cset_extra...
Qed.
