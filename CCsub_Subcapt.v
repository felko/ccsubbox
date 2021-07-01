Require Import Coq.Program.Equality.
Require Export CCsub_Hints.
Require Export CCsub_Lemmas.

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
  - apply subcapt_in_fvar...
  - apply subcapt_in_lvar...
  - apply subcapt_set...
    all : intros ? ?...
Qed.

Create HintDb lsetdec.
Hint Extern 1 (_ `in`L _) => lsetdec: lsetdec.

Lemma wf_cset_fvarless : forall E A b ls,
  wf_cset E A (cset_set {}A {}N b ls).
Proof with eauto with lsetdec.
  intros *.
  constructor...
  intros ? ?.
  exfalso; fsetdec.
Qed.

Hint Resolve wf_cset_fvarless : core.

Lemma subcapt_reflexivity : forall E A C,
  wf_cset E A C ->
  A `subset` dom E ->
  subcapt E C C.
Proof with eauto.
  intros * WfC HSub.
  inversion WfC; subst.
  constructor...
  - intros y yIn.
    apply subcapt_in_fvar...
    apply (wf_cset_singleton_by_mem xs b ls)...
  - intros ? ?...
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

  rename xs into es, b into u.
  dependent induction SC12.
  - inversion SC23; subst.
    + apply subcapt_universal...
    + apply subcapt_universal...
    + assert (u = true) by csetdec; subst.
      apply subcapt_universal...
  - dependent induction SC23.
    + apply subcapt_universal...
    + rewrite AtomSetFacts.singleton_iff in H1; symmetry in H1; subst...
    + exfalso; fsetdec.
    + apply subcapt_universal...
    + rewrite AtomSetFacts.singleton_iff in H1; symmetry in H1; subst...
    + rewrite AtomSetFacts.singleton_iff in H1; symmetry in H1; subst...
    + eauto.
  - dependent induction SC23.
    + apply subcapt_universal...
    + exfalso; lsetdec.
    + rewrite LabelSetFacts.singleton_iff in H1; symmetry in H1; subst...
    + apply subcapt_universal...
    + exfalso; lsetdec.
    + exfalso; lsetdec.
    + eauto.
  - dependent induction SC23.
    + apply subcapt_universal...
    + apply subcapt_universal...
    + assert (u = true) by csetdec; subst.
      apply subcapt_universal...
  - eapply subcapt_var with (T := T)...
  - eapply subcapt_tvar with (T := T)...
  - eapply subcapt_set...
    + intros ? ?...
    + intros ? ?...
    + destr_bool.
      inversion SC23; subst...
      subst...
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
  2: { intros ? ?; exfalso; lsetdec... }
  unfold AtomSet.F.For_all.
  intros x0 HIn.
  rewrite AtomSetFacts.singleton_iff in HIn.
  symmetry in HIn.
  subst.
  eapply subcapt_var...
  eapply subcapt_reflexivity...
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

(* Substituting the same capture set preserves subcapturing *)
Lemma subcapt_through_subst_cset : forall x U C F E C1 C2 ,
  subcapt (F ++ [(x, bind_typ U)] ++ E) C1 C2 ->
  wf_env (F ++ [(x, bind_typ U)] ++ E) ->
  subcapt E C (cv U) ->
  subcapt (map (subst_cb x C) F ++ E) (subst_cset x C C1) (subst_cset x C C2).
Proof with eauto using wf_env_subst_cb, wf_cset_subst_cb with fsetdec lsetdec.
  intros * Hsc WfE HscC.
  dependent induction Hsc.
  - assert (wf_cset_in (map (subst_cb x C) F ++ E) (subst_cset x C C0)) as ?WF. {
      eapply wf_cset_in_subst_cb ...
    }
    assert (wf_cset_in (map (subst_cb x C) F ++ E)
                       (subst_cset x C (cset_set xs {}N true ls))) as ?WF. {
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
                       (subst_cset x C (cset_set xs {}N b ls))) as ?WF. {
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
      replace (xs `union` singleton x0 `remove` x) with xs by fsetdec.
      apply subcapt_set...
      * intros ? ?...
      * intros ? ?...
      * csetdec.
    + destruct_set_mem x xs.
      2: {
        apply subcapt_in_fvar...
      }
      assert (wf_cset_in (F ++ [(x, bind_typ U)] ++ E) (cv U)) as HA. {
        note (wf_env ([(x, bind_typ U)] ++ E)) by eauto...
        rewrite_env (empty ++ (F ++ [(x, bind_typ U)]) ++ E).
        apply wf_cset_in_weakening; simpl_env...
      }
      inversion HA; subst.
      note (wf_cset_in E C).
      csetsimpl.
      apply subcapt_in_fvar...
  - assert (wf_cset_in (map (subst_cb x C) F ++ E)
                       (subst_cset x C (cset_set xs {}N b ls))) as ?WF. {
      eapply wf_cset_in_subst_cb...
    }
    assert (wf_cset_in (map (subst_cb x C) F ++ E)
                       (subst_cset x C (`cset_lvar` l))) as ?WF. {
      eapply wf_cset_in_subst_cb...
    }
    unfold subst_cset in *.
    replace (x `mem`A {}A) with false in * by fset_mem_dec.
    destruct_set_mem x xs.
    + assert (wf_cset_in (F ++ [(x, bind_typ U)] ++ E) C) as HA. {
        note (wf_env ([(x, bind_typ U)] ++ E)) by eauto...
        rewrite_env (empty ++ (F ++ [(x, bind_typ U)]) ++ E).
        apply wf_cset_in_weakening; simpl_env...
      }
      inversion HA; subst.
      csetsimpl.
      apply subcapt_in_lvar...
    + apply subcapt_in_lvar...
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
      replace (C `u` cset_set ({x}A `\`A x) {}N false {}L)
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
                       (subst_cset x C (cset_set xs {}N b ls))) as ?WF. {
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
      - intros y yIn.
        replace (`cset_fvar` y) with (subst_cset x C (`cset_fvar` y))...
        unfold subst_cset.
        destruct_set_mem x {y}A...
        exfalso;fsetdec.
      - intros l lIn.
        replace (`cset_lvar` l) with (subst_cset x C (`cset_lvar` l))...
        unfold subst_cset.
        destruct_set_mem x {}A...
        exfalso;fsetdec.
      - (* Should we have a lemma that `cset_uvar` is not affected by subst? *)
        (* Looking at that chain, we probably should. *)
        destruct D; unfold subst_cset; destruct_if; destruct U; csetdec.
    }

    unfold AtomSet.F.For_all in H0.
    inversion H; subst.
    note (wf_cset_in E C).

    rename xs0 into cs', b0 into b__c', xs1 into ds, b1 into b__d.
    unfold subst_cset in WF0 |- *.
    destruct_set_mem x cs'.
    + csetsimpl.
      apply subcapt_set...
      3: csetdec.
      2: {
        intros l lIn.
        destruct_union_mem lIn. 1: {
          apply subcapt_in_lvar...
        }
        specialize (H2 l lIn); simpl in H2.
        dependent induction H2.
        - csetsimpl.
          apply subcapt_universal...
        - assert (l `in`L {l}L) as HA by lsetdec.
          rewrite <- x2 in HA.
          exfalso; lsetdec.
        - assert (l `in`L {l}L) as HA by lsetdec.
          rewrite <- x in HA.
          assert (l0 = l) by lsetdec.
          subst; clear HA.
          apply subcapt_in_lvar...
        - assert (l `in`L {l}L) as HA by lsetdec.
          rewrite <- x2 in HA.
          exfalso; lsetdec.
        - assert (l `in`L {l}L) as HA by lsetdec.
          rewrite <- x2 in HA.
          exfalso; lsetdec.
        - replace (cset_set (ds `u`A cs' `\`A x) {}N (b__d || b__c') (ls1 `u`L ls0))
            with (subst_cset x (cset_set ds {}N b__d ls1) (cset_set cs' {}N b__c' ls0)).
          2: {
            unfold subst_cset.
            csetsimpl.
            destruct_set_mem x cs'; easy.
          }
          replace (`cset_lvar` l) with (subst_cset x (cset_set ds {}N b__d ls1) (`cset_lvar` l)).
          2: {
            unfold subst_cset.
            replace (x `mem`A {}A) with false by fset_mem_dec.
            easy.
          }
          eapply H3...
      }

      1: {
        intros y yIn.
        destruct_union_mem yIn. {
          apply subcapt_in_fvar...
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
        - csetsimpl.
          apply subcapt_universal...
          applys wf_cset_singleton_by_mem (ds `u`A xs `\`A x)...
        - cleanup_singleton_eq x y x0 x1.
          apply subcapt_in_fvar...
          applys wf_cset_singleton_by_mem (ds `u`A xs `\`A x)...
        - assert (l `in`L {l}L) as HA by lsetdec.
          rewrite x1 in HA.
          exfalso; lsetdec.
        - cleanup_singleton_eq x y x0 x1.
          replace (`cset_fvar` y)
            with (subst_cset x (cset_set ds {}N b__d ls1) (`cset_fvar` y)).
          2: {
            unfold subst_cset; simpl.
            destruct_set_mem x (singleton y); (trivial || exfalso;fsetdec).
          }
          replace (cset_set (ds `union` cs' `remove` x) {}N (b__d || b__c') (ls1 `u`L ls0))
            with (subst_cset x (cset_set ds {}N b__d ls1) (cset_set cs' {}N b__c' ls0)).
          2: {
            unfold subst_cset; simpl.
            destruct_set_mem x cs'; [|exfalso;fsetdec].
            unfold cset_union; csetsimpl...
          }
          eapply H1...
        - cleanup_singleton_eq x y x0 x1.
          replace (`cset_fvar` y) with (subst_cset x (cset_set ds {}N b__d ls1) (`cset_fvar` y)).
          2: {
            unfold subst_cset; simpl.
            destruct_set_mem x (singleton y); (trivial || exfalso;fsetdec).
          }
          replace (cset_set (ds `union` cs' `remove` x) {}N (b__d || b__c') (ls1 `u`L ls0))
            with (subst_cset x (cset_set ds {}N b__d ls1) (cset_set cs' {}N b__c' ls0)).
          2: {
            unfold subst_cset; simpl.
            destruct_set_mem x cs'; [|exfalso;fsetdec].
            unfold cset_union; csetsimpl...
          }
          eapply H1...
        - replace (`cset_fvar` y) with (subst_cset x (cset_set ds {}N b__d ls1) (`cset_fvar` y)).
          2: {
            unfold subst_cset; simpl.
            destruct_set_mem x (singleton y); (trivial || exfalso;fsetdec).
          }
          replace (cset_set (ds `union` cs' `remove` x) {}N (b__d || b__c') (ls1 `u`L ls0))
            with (subst_cset x (cset_set ds {}N b__d ls1) (cset_set cs' {}N b__c' ls0)).
          2: {
            unfold subst_cset; simpl.
            destruct_set_mem x cs'; [|exfalso;fsetdec].
            unfold cset_union; csetsimpl...
          }
          eapply H1...
      }
    + csetsimpl.
      apply subcapt_set.
      1: trivial.
      3: {
        specialize (H1 x ltac:(fsetdec) _ _ _ _ ltac:(reflexivity) ltac:(trivial) ltac:(trivial)).
        unfold subst_cset in H1.
        find_and_destroy_set_mem; [|exfalso;fsetdec].
        find_and_destroy_set_mem; [exfalso;fsetdec|].
        unfold cset_union in H1.
        csetsimpl in H1.
        destr_bool.
        inversion H1; subst; easy.
      }
      2: {
        intros l lIn.
        destruct_union_mem lIn.
        - replace (cset_set cs' {}N b__c' ls0)
            with (subst_cset x (cset_set ds {}N b__d ls1) (cset_set cs' {}N b__c' ls0)).
          2: {
            unfold subst_cset; simpl.
            destruct_set_mem x cs'; (trivial||exfalso;fsetdec).
           }
          apply (subcapt_transitivity (subst_cset x (cset_set ds {}N b__d ls1) (`cset_fvar` x)))...
          unfold subst_cset.
          destruct_set_mem x {x}A; [|exfalso; fsetdec].
          csetsimpl.
          apply subcapt_in_lvar...
          replace (ds `u`A {x}A `\`A x) with ds by csetdec...
          rewrite_nil_concat.
          apply wf_cset_in_weakening; simpl_env...
        - specialize (H3 l lIn).
           replace (`cset_lvar` l)
             with (subst_cset x (cset_set ds {}N b__d ls1) (`cset_lvar` l)).
           2: {
             unfold subst_cset; simpl.
             replace (x `mem`A {}A) with false by fset_mem_dec.
             easy.
           }
          replace (cset_set cs' {}N b__c' ls0)
            with (subst_cset x (cset_set ds {}N b__d ls1) (cset_set cs' {}N b__c' ls0)).
          2: {
            unfold subst_cset; simpl.
            destruct_set_mem x cs'; (trivial||exfalso;fsetdec).
           }
          eapply H3...
      }
      intros y yIn.
      destruct_set_mem y (xs `remove` x).
      * specialize (H0 y ltac:(fsetdec)); simpl in H0.
        dependent induction H0.
        -- apply subcapt_universal...
        -- cleanup_singleton_eq x y x0 x1.
           apply subcapt_in_fvar...
        -- assert (l `in`L {l}L) as HA by lsetdec.
          rewrite x1 in HA.
          exfalso; lsetdec.
        -- cleanup_singleton_eq x y x0 x1.
           replace (`cset_fvar` y)
             with (subst_cset x (cset_set ds {}N b__d ls1) (`cset_fvar` y)).
           2: {
             unfold subst_cset; simpl.
             destruct_set_mem x (`cset_fvar` y); (trivial || exfalso;fsetdec).
           }
           replace (cset_set cs' {}N b__c' ls0)
             with (subst_cset x (cset_set ds {}N b__d ls1) (cset_set cs' {}N b__c' ls0)).
           2: {
             unfold subst_cset; simpl.
             destruct_set_mem x cs'; (trivial||exfalso;fsetdec).
           }
           eapply H1...
        -- cleanup_singleton_eq x y x0 x1.
           replace (`cset_fvar` y)
             with (subst_cset x (cset_set ds {}N b__d ls1) (`cset_fvar` y)).
           2: {
             unfold subst_cset; simpl.
             destruct_set_mem x (`cset_fvar` y); (trivial || exfalso;fsetdec).
           }
           replace (cset_set cs' {}N b__c' ls0)
             with (subst_cset x (cset_set ds {}N b__d ls1) (cset_set cs' {}N b__c' ls0)).
           2: {
             unfold subst_cset; simpl.
             destruct_set_mem x cs'; (trivial||exfalso;fsetdec).
           }
           eapply H1...
        -- replace (`cset_fvar` y)
             with (subst_cset x (cset_set ds {}N b__d ls1) (`cset_fvar` y)).
           2: {
             unfold subst_cset; simpl.
             destruct_set_mem x (`cset_fvar` y); (trivial || exfalso;fsetdec).
           }
           replace (cset_set cs' {}N b__c' ls0)
             with (subst_cset x (cset_set ds {}N b__d ls1) (cset_set cs' {}N b__c' ls0)).
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

        enough (subcapt (map (subst_cb x (cset_set ds {}N b__d ls1)) F ++ E)
                         (`cset_fvar` y)
                         (cset_set ds {}N b__d ls1)) as HAA. {
          eapply subcapt_transitivity...
        }
        eapply subcapt_in_fvar...
Qed.

Lemma wf_cset_atom_union : forall E A xs ys u1 u2 ls1 ls2,
  wf_cset E A (cset_set xs {}N u1 ls1) ->
  wf_cset E A (cset_set ys {}N u2 ls2) ->
  wf_cset E A (cset_set (xs `union` ys) {}N (u1 || u2) (ls1 `u`L ls2)).
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
Proof with eauto using wf_cset_union, wf_cset_atom_union with fsetdec lsetdec.
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
    apply subcapt_in_fvar...
  - inversion HwfD2; simpl; subst...
    unfold cset_union; csetsimpl.
    inversion H0; subst.
    apply subcapt_in_lvar...
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
    + intros ? ?...
    + csetdec.
Qed.

Tactic Notation "subst_mem_singleton" hyp(H) :=
  match type of H with
    | _ `in`A _ => rewrite AtomSetFacts.singleton_iff in H; subst
    | _ `in`L _ => rewrite LabelSetFacts.singleton_iff in H; subst
  end.

Tactic Notation "subst_mem_singleton" "<-" hyp(H) :=
  match type of H with
    | _ `in`A _ => rewrite AtomSetFacts.singleton_iff in H; symmetry in H; subst
    | _ `in`L _ => rewrite LabelSetFacts.singleton_iff in H; symmetry in H; subst
  end.

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
    + trivial...
    + intros y yIn.
      destruct_union_mem yIn.
      * subst_mem_singleton yIn.
        apply subcapt_in_fvar...
      * applys subcapt_transitivity HscC2...
    + intros l lIn.
      applys subcapt_transitivity HscC2...
    + forwards: subcapt_universal_mem HscC2...
  - note (wf_cset_in E C2); csetsimpl.
    apply subcapt_set.
    + trivial...
    + intros y yIn.
      applys subcapt_transitivity HscC2...
    + intros l1 l1In.
      destruct_union_mem l1In.
      * subst_mem_singleton l1In.
        apply subcapt_in_lvar...
      * applys subcapt_transitivity HscC2...
    + forwards: subcapt_universal_mem HscC2...
  - note (wf_cset_in E D); subst.
    apply subcapt_universal...
  - apply (subcapt_transitivity (cv T `u` C2))...
    assert (wf_cset_in E (cv T `u` C2)) as WfU by auto using wf_cset_union.
    note (wf_cset_in E C2).
    note (wf_cset_in E (cv T)).
    rewrite <- H2 in WfU.
    csetsimpl.
    apply subcapt_set...
    3: csetdec.
    2: {
      intros l lIn.
      apply subcapt_in_lvar...
      lsetdec.
    }
    intros y yIn.
    destruct_union_mem yIn.
    + subst_mem_singleton yIn.
      apply (subcapt_transitivity (cv T))...
      * eapply subcapt_var...
        eapply subcapt_reflexivity...
      * rewrite <- H2.
        apply subcapt_set...
        3: csetdec.
        2: {
          intros l lIn.
          apply subcapt_in_lvar...
          lsetdec.
        }
        intros z zIn.
        apply subcapt_in_fvar...
    + apply subcapt_in_fvar...
  - apply (subcapt_transitivity (cv T `u` C2))...
    assert (wf_cset_in E (cv T `u` C2)) as WfU by auto using wf_cset_union.
    note (wf_cset_in E C2).
    note (wf_cset_in E (cv T)).
    rewrite <- H2 in WfU.
    csetsimpl.
    apply subcapt_set...
    3: csetdec.
    2: {
      intros l lIn.
      apply subcapt_in_lvar...
      lsetdec.
    }
    intros y yIn.
    destruct_union_mem yIn.
    + subst_mem_singleton yIn.
      apply (subcapt_transitivity (cv T))...
      * eapply subcapt_tvar...
        eapply subcapt_reflexivity...
      * rewrite <- H2.
        apply subcapt_set...
        3: csetdec.
        2: {
          intros l lIn.
          apply subcapt_in_lvar...
          lsetdec.
        }
        intros z zIn.
        apply subcapt_in_fvar...
    + apply subcapt_in_fvar...
  - note (wf_cset_in E C2); csetsimpl.
    apply subcapt_set...
    + intros y yIn.
      destruct_union_mem yIn...
      apply (subcapt_transitivity (cset_set xs0 {}N b0 ls0))...
    + intros l lIn.
      destruct_union_mem lIn...
      apply (subcapt_transitivity (cset_set xs0 {}N b0 ls0))...
    + forwards: subcapt_universal_mem HscC2; csetdec...
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
Proof with eauto using wf_env_subst_tb, wf_cset_in_subst_tb, wf_typ_in_subst_tb with fsetdec lsetdec.
  intros * Hwf Hsc Hsub.
  generalize dependent P.
  dependent induction Hsc; intros P Hsub.
  - assert (wf_cset_in (map (subst_tb X P) F ++ E) (subst_cset X (cv P) C)) as ?WF...
    assert (wf_cset_in (map (subst_tb X P) F ++ E)
                       (subst_cset X (cv P) (cset_set xs {}N true ls))) as ?WF...
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
                       (subst_cset X (cv P) (cset_set xs {}N b ls))) as ?WF...
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
      replace (xs `union` singleton x `remove` X) with xs by fsetdec.
      rename select (_ = cv P) into EQ.
      rewrite <- EQ in WF0; csetsimpl in WF0.
      apply subcapt_set...
      * intros y yIn.
        apply subcapt_in_fvar...
        eapply wf_cset_singleton_by_mem...
      * intros l lIn.
        apply subcapt_in_lvar...
      * csetdec.
    + destruct_set_mem X xs.
      2: {
        apply subcapt_in_fvar...
      }
      assert (wf_cset_in (F ++ [(X, bind_sub Q)] ++ E) (cv P)) as HA. {
        note (wf_env ([(X, bind_sub Q)] ++ E)) by eauto...
        rewrite_env (empty ++ (F ++ [(X, bind_sub Q)]) ++ E).
        apply wf_cset_in_weakening; simpl_env; [apply cv_wf|]...
      }
      inversion HA; subst; csetsimpl.
      rename select (_ = cv P) into EQ.
      rewrite <- EQ in WF0; csetsimpl in WF0.
      apply subcapt_in_fvar...
  - assert (wf_cset_in (map (subst_tb X P) F ++ E) (subst_cset X (cv P) (`cset_lvar` l))) as ?WF...
    assert (wf_cset_in (map (subst_tb X P) F ++ E)
                       (subst_cset X (cv P) (cset_set xs {}N b ls))) as ?WF...
    unfold subst_cset in *.
    replace (X `mem`A {}A) with false in * by fset_mem_dec.
    destruct_set_mem X xs.
    2: {
      apply subcapt_in_lvar...
    }
    assert (wf_cset_in (F ++ [(X, bind_sub Q)] ++ E) (cv P)) as HA. {
      note (wf_env ([(X, bind_sub Q)] ++ E)) by eauto...
      rewrite_env (empty ++ (F ++ [(X, bind_sub Q)]) ++ E).
      apply wf_cset_in_weakening; simpl_env; [apply cv_wf|]...
    }
    inversion HA; subst.
    rename select (_ = cv P) into EQ.
    rewrite <- EQ in WF0; csetsimpl in WF0.
    csetsimpl.
    apply subcapt_in_lvar...
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
      replace (cv P `u` cset_set ({X}A `\`A X) {}N false {}L)
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
      apply sub_implies_subcapt...
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
                       (subst_cset X (cv P) (cset_set xs {}N b ls))) as ?WF. {
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
      apply subcapt_set; trivial.
      - intros y yIn.
        assert (X <> y) by notin_solve.
        replace (`cset_fvar` y) with (subst_cset X (cv P) (`cset_fvar` y))...
        unfold subst_cset.
        destruct_set_mem X (singleton y)...
        exfalso; fsetdec.
      - intros l lIn.
        replace (`cset_lvar` l) with (subst_cset X (cv P) (`cset_lvar` l))...
        unfold subst_cset.
        destruct_set_mem X {}A...
        exfalso; fsetdec.
      - (* Should we have a lemma that `cset_uvar` is not affected by subst? *)
        (* Looking at that chain, we probably should. *)
        destruct D; unfold subst_cset; destruct_if; destruct P; simpl; csetdec.
    }

    unfold AtomSet.F.For_all in H0.

    inversion H; subst.
    assert (wf_cset_in (F ++ [(X, bind_sub Q)] ++ E) (cv P)) as HA. {
      note (wf_env ([(X, bind_sub Q)] ++ E)) by eauto...
      rewrite_env (empty ++ (F ++ [(X, bind_sub Q)]) ++ E).
      apply wf_cset_in_weakening; simpl_env; [apply cv_wf|]...
    }
    inversion HA; subst.

    rename xs0 into cs', b0 into b__c', xs1 into ds, b1 into b__d.
    unfold subst_cset in WF0 |- *.
    destruct_set_mem X cs'.
    + rename select (_ = cv P) into EQ.
      rewrite <- EQ in WF, WF0.
      csetsimpl.
      apply subcapt_set; trivial.
      3: csetdec.
      2: {
        intros l lIn.
        destruct_union_mem lIn. 1: {
          apply subcapt_in_lvar...
        }
        specialize (H2 l lIn); simpl in H2.
        dependent induction H2.
        - csetsimpl.
          apply subcapt_universal...
        - assert (l `in`L {l}L) as HA' by lsetdec.
          rewrite <- x1 in HA'.
          exfalso; lsetdec.
        - assert (l `in`L {l}L) as HA' by lsetdec.
          rewrite <- x in HA'.
          assert (l0 = l) by lsetdec.
          subst; clear HA.
          apply subcapt_in_lvar...
        - assert (l `in`L {l}L) as HA' by lsetdec.
          rewrite <- x1 in HA'.
          exfalso; lsetdec.
        - assert (l `in`L {l}L) as HA' by lsetdec.
          rewrite <- x1 in HA'.
          exfalso; lsetdec.
        - replace (cset_set (ds `u`A cs' `\`A X) {}N (b__d || b__c') (ls1 `u`L ls0))
            with (subst_cset X (cset_set ds {}N b__d ls1) (cset_set cs' {}N b__c' ls0)).
          2: {
            unfold subst_cset.
            csetsimpl.
            destruct_set_mem X cs'; easy.
          }
          replace (`cset_lvar` l) with (subst_cset X (cset_set ds {}N b__d ls1) (`cset_lvar` l)).
          2: {
            unfold subst_cset.
            replace (X `mem`A {}A) with false by fset_mem_dec.
            easy.
          }
          rewrite EQ.
          eapply H3...
      }
      intros y yIn.
      destruct_union_mem yIn. {
        apply subcapt_in_fvar...
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
        apply subcapt_in_fvar...
        applys wf_cset_singleton_by_mem (ds `u`A xs `\`A X)...
      * assert (l `in`L {l}L) as HA' by lsetdec.
        rewrite x0 in HA'.
        exfalso; lsetdec.
      * cleanup_singleton_eq' x y x0.
        rename select (_ = cv P) into EQ.
        replace (`cset_fvar` y) with (subst_cset X (cv P) (`cset_fvar` y)).
        2: {
          unfold subst_cset; simpl.
          destruct_set_mem X (singleton y); (trivial || exfalso;fsetdec).
        }
        replace (cset_set (ds `union` cs' `remove` X) {}N (b__d || b__c') (ls1 `u`L ls0))
          with (subst_cset X (cv P) (cset_set cs' {}N b__c' ls0)).
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
        replace (cset_set (ds `union` cs' `remove` X) {}N (b__d || b__c') (ls1 `u`L ls0))
          with (subst_cset X (cv P) (cset_set cs' {}N b__c' ls0)).
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
        replace (cset_set (ds `union` cs' `remove` X) {}N (b__d || b__c') (ls1 `u`L ls0))
          with (subst_cset X (cv P) (cset_set cs' {}N b__c' ls0)).
        2: {
          unfold subst_cset; simpl.
          destruct_set_mem X cs'; [|exfalso;fsetdec].
          rewrite <- EQ.
          csetsimpl...
        }
        eapply H1...
    + csetsimpl.
      rename select (_ = cv P) into EQ.
      apply subcapt_set; trivial.
      3: {
        forwards SpH1: H1 X X F Q E...
        rewrite <- EQ in SpH1.
        unfold subst_cset in SpH1.
        find_and_destroy_set_mem; [|exfalso;fsetdec].
        find_and_destroy_set_mem; [exfalso;fsetdec|].
        csetsimpl in SpH1.
        destr_bool.
        inversion SpH1; subst; easy.
      }
      2: {
        intros l lIn.
        destruct_union_mem lIn.
        - replace (cset_set cs' {}N b__c' ls0)
            with (subst_cset X (cv P) (cset_set cs' {}N b__c' ls0)).
          2: {
            unfold subst_cset; simpl.
            destruct_set_mem X cs'; (trivial||exfalso;fsetdec).
          }
          apply (subcapt_transitivity (subst_cset X (cv P) (`cset_fvar` X)))...
          unfold subst_cset.
          destruct_set_mem X {X}A; [|exfalso; fsetdec].
          rewrite <- EQ.
          csetsimpl.
          apply subcapt_in_lvar...
          replace (ds `u`A {X}A `\`A X) with ds by csetdec...
          rewrite_nil_concat.
          rewrite EQ.
          apply wf_cset_in_weakening; simpl_env... (* ok takes a _terrible_ amount of time *)
          apply cv_wf...
        - specialize (H3 l lIn).
           replace (`cset_lvar` l)
             with (subst_cset X (cset_set ds {}N b__d ls1) (`cset_lvar` l)).
           2: {
             unfold subst_cset; simpl.
             replace (X `mem`A {}A) with false by fset_mem_dec.
             easy.
           }
          replace (cset_set cs' {}N b__c' ls0)
            with (subst_cset X (cv P) (cset_set cs' {}N b__c' ls0)).
          2: {
            unfold subst_cset; simpl.
            destruct_set_mem X cs'; (trivial||exfalso;fsetdec).
           }
          rewrite EQ.
          eapply H3...
      }
      intros y yIn.
      destruct_set_mem y (xs `remove` X).
      * specialize (H0 y ltac:(fsetdec)); simpl in H0.
        dependent induction H0.
        -- apply subcapt_universal...
           rewrite <- EQ in WF; csetsimpl; applys wf_cset_singleton_by_mem yIn...
        -- cleanup_singleton_eq' x y x0.
           apply subcapt_in_fvar...
        -- assert (l `in`L {l}L) as HA' by lsetdec.
           rewrite x0 in HA'.
           exfalso; lsetdec.
        -- cleanup_singleton_eq' x y x0.
           replace (`cset_fvar` y) with (subst_cset X (cv P) (`cset_fvar` y)).
           2: {
             unfold subst_cset; simpl.
             destruct_set_mem X (`cset_fvar` y); (trivial || exfalso;fsetdec).
           }
           replace (cset_set cs' {}N b__c' ls0) with (subst_cset X (cv P) (cset_set cs' {}N b__c' ls0)).
           2: {
             unfold subst_cset; simpl.
             destruct_set_mem X cs'; (trivial||exfalso;fsetdec).
           }
           eapply H1...
        -- cleanup_singleton_eq' x y x0.
           replace (`cset_fvar` y) with (subst_cset X (cv P) (`cset_fvar` y)).
           2: {
             unfold subst_cset; simpl.
             destruct_set_mem X (`cset_fvar` y); (trivial || exfalso;fsetdec).
           }
           replace (cset_set cs' {}N b__c' ls0) with (subst_cset X (cv P) (cset_set cs' {}N b__c' ls0)).
           2: {
             unfold subst_cset; simpl.
             destruct_set_mem X cs'; (trivial||exfalso;fsetdec).
           }
           eapply H1...
        -- replace (`cset_fvar` y) with (subst_cset X (cv P) (`cset_fvar` y)).
           2: {
             unfold subst_cset; simpl.
             destruct_set_mem X (`cset_fvar` y); (trivial || exfalso;fsetdec).
           }
           replace (cset_set cs' {}N b__c' ls0) with (subst_cset X (cv P) (cset_set cs' {}N b__c' ls0)).
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
                         (cset_set ds {}N b__d ls1)) as HAA. {
          eapply subcapt_transitivity...
        }
        eapply subcapt_in_fvar...
        forwards (? & ?): subcapt_regular H1.
        inversion select (wf_cset_in _ (cset_set ds _ _ ls1)); subst...
Qed.

(* (* ********************************************************************** *) *)
(* (** ** Narrowing and transitivity (3) *) *)

Lemma subst_cset_across_subcapt : forall E x C D C0 A,
  wf_env E ->
  wf_cset E A C0 ->
  A `subset` dom E ->
  subcapt E C D ->
  subcapt E (subst_cset x C C0) (subst_cset x D C0).
Proof with eauto with fsetdec lsetdec.
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
  rename xs into zs.

  note (wf_cset_in E C).
  rename xs into cs.

  note (wf_cset_in E D).
  rename xs into ds.

  unfold subst_cset in H0, H |- *; destruct_set_mem x zs.
  2: {
    eapply subcapt_reflexivity...
  }

  dependent induction Sub.
  - csetsimpl.
    apply subcapt_universal...
  - csetsimpl.
    apply subcapt_set...
    + intros y yIn.
      apply subcapt_in_fvar...
    + intros l lIn.
      apply subcapt_in_lvar...
    + csetdec.
  - csetsimpl.
    apply subcapt_set...
    + intros y yIn.
      apply subcapt_in_fvar...
    + intros l1 l1In.
      apply subcapt_in_lvar...
    + csetdec.
  - csetsimpl.
    apply subcapt_universal...
  - csetsimpl.
    apply subcapt_set...
    3: csetdec.
    2: {
      intros l lIn.
      apply subcapt_in_lvar...
    }
    intros y yIn.
    destruct_union_mem yIn.
    2: {
      apply subcapt_in_fvar...
    }
    rename select (y `in`A _) into yIn.
    apply AtomSetFacts.singleton_iff in yIn; symmetry in yIn; subst.
    eapply subcapt_var...
    apply (subcapt_transitivity (cset_set ds {}N b1 ls1))...
    apply subcapt_set...
    + intros z zIn.
      apply subcapt_in_fvar...
    + intros l lIn.
      apply subcapt_in_lvar...
    + csetdec.
  - csetsimpl.
    apply subcapt_set...
    3: csetdec.
    2: {
      intros l lIn.
      apply subcapt_in_lvar...
    }
    intros y yIn.
    destruct_union_mem yIn.
    2: {
      apply subcapt_in_fvar...
    }
    rename select (y `in`A _) into yIn.
    apply AtomSetFacts.singleton_iff in yIn; symmetry in yIn; subst.
    eapply subcapt_tvar...
    apply (subcapt_transitivity (cset_set ds {}N b1 ls1))...
    apply subcapt_set...
    + intros z zIn.
      apply subcapt_in_fvar...
    + intros l lIn.
      apply subcapt_in_lvar...
    + csetdec.
  - csetsimpl.
    apply subcapt_set...
    3: csetdec.
    2: {
      intros l lIn.
      destruct_union_mem lIn. 2: {
        apply subcapt_in_lvar...
      }
      specialize (H2 l lIn); simpl in H2.
      clear H1 H3.
      dependent induction H2.
      - csetsimpl.
        apply subcapt_universal...
      - assert (l `in`L {l}L) as HA by lsetdec.
        rewrite <- x2 in HA.
        exfalso; lsetdec.
      - assert (l `in`L {l}L) as HA by lsetdec.
        rewrite <- x in HA.
        assert (l0 = l) by lsetdec.
        subst; clear HA.
        apply subcapt_in_lvar...
      - assert (l `in`L {l}L) as HA by lsetdec.
        rewrite <- x2 in HA.
        exfalso; lsetdec.
      - assert (l `in`L {l}L) as HA by lsetdec.
        rewrite <- x2 in HA.
        exfalso; lsetdec.
      - eapply H3...
    }
    intros y yIn.
    destruct_union_mem yIn.
    2: {
      apply subcapt_in_fvar...
    }
    apply (subcapt_transitivity (cset_set ds {}N b1 ls1))...

    apply subcapt_set...
    + intros z zIn.
      apply subcapt_in_fvar...
    + intros l lIn.
      apply subcapt_in_lvar...
    + csetdec.
Qed.

Lemma subcapt_strengthening : forall G F E C1 C2,
  ok (G ++ F ++ E) ->
  wf_env (G ++ E) ->
  wf_cset_in (G ++ E) C1 ->
  wf_cset_in (G ++ E) C2 ->
  G ++ F ++ E |-sc C1 <: C2 ->
  G ++ E |-sc C1 <: C2.
Proof with eauto.
  intros * Ok WfE Wf1 Wf2 Sc.
  dependent induction Sc...
  - inversion Wf1; subst; cbv [allbound] in *...
    specialize (H4 x ltac:(fsetdec)) as [Tx Hbinds].
    destruct Hbinds...
    * assert (Tx = T). {
        eapply binds_weaken in H0...
        unshelve epose proof (binds_unique _ _ _ _ H H0)...
        inversion H1...
      }
      subst...
      eapply subcapt_var...
      eapply IHSc...
      apply cv_wf...
      eapply wf_typ_from_binds_typ...
    * exfalso.
      eapply binds_weaken in H0...
      unshelve epose proof (binds_unique _ _ _ _ H H0)...
      inversion H1...
  - inversion Wf1; subst; cbv [allbound] in *...
    specialize (H4 x ltac:(fsetdec)) as [Tx Hbinds].
    destruct Hbinds...
    * exfalso.
      eapply binds_weaken in H0...
      unshelve epose proof (binds_unique _ _ _ _ H H0)...
      inversion H1...
    * assert (Tx = T). {
        eapply binds_weaken in H0...
        unshelve epose proof (binds_unique _ _ _ _ H H0)...
        inversion H1...
      }
      subst...
      eapply subcapt_tvar...
      eapply IHSc...
      apply cv_wf...
      eapply wf_typ_from_binds_sub...
  - destruct D as [fvD bvD univD lD]; subst...
    inversion H; subst...
    apply subcapt_set...
    * intros a aInXs.
      eapply H1...
    * intros l lInLs.
      eapply H3...
Qed.

Lemma subcapt_widening_univ : forall X F E P Q C,
  ok (F ++ [(X, bind_sub Q)] ++ E) ->
  F ++ [(X, bind_sub P)] ++ E |-sc {*} <: C ->
  E |-s P <: Q ->
  F ++ [(X, bind_sub Q)] ++ E |-sc {*} <: C.
Proof with eauto using wf_cset_narrowing.
  intros * Ok Sc Sub. 
  dependent induction Sc...
Qed.

Lemma subcapt_widening_typ_univ : forall X F E P Q C,
  ok (F ++ [(X, bind_typ Q)] ++ E) ->
  F ++ [(X, bind_typ P)] ++ E |-sc {*} <: C ->
  E |-s P <: Q ->
  F ++ [(X, bind_typ Q)] ++ E |-sc {*} <: C.
Proof with eauto using wf_cset_narrowing_typ.
  intros * Ok Sc Sub. 
  dependent induction Sc...
Qed.

Lemma subcapt_univ_through_subst_cb : forall F E x u P T,
  wf_env (F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E) ->
  map (subst_cb x (free_for_cv u)) F ++ E |-sc {*} <: cv (subst_ct x (free_for_cv u) T) ->
  F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E |-sc {*} <: cv T.
Proof with eauto.
  intros * Wf ScUniv.
  dependent induction ScUniv...
  * induction T; simpl in *; simpl_env in *...
    + cbv [subst_cset] in *...
      pose proof (cv_free_never_universal u).
      destruct (free_for_cv u)...
      find_and_destroy_set_mem...
      - inversion x; subst... 
        assert (`cset_uvar` c = true) by (destr_bool; eauto*); subst...
        destruct c; subst...
        apply subcapt_in_univ...
        (* wf goal *)
        admit.
      - inversion x; subst...
        apply subcapt_in_univ...
        (* wf goal *)
        admit.
    + inversion x...
    + inversion x...
  * induction T; simpl in *; simpl_env in *...
    + cbv [subst_cset] in *...
      pose proof (cv_free_never_universal u).
      destruct (free_for_cv u)...
      find_and_destroy_set_mem...
      - inversion H0; subst... 
        assert (`cset_uvar` c = true) by (destr_bool; eauto*); subst...
        destruct c; subst...
        rewrite H3.
        apply subcapt_in_univ...
        (* wf goal *)
        admit.
      - inversion H0; subst...
        destruct c...
        apply subcapt_set...
        (* wf goal *)
        ++ admit.
        ++ intros y yIn. exfalso; fsetdec.
        ++ intros l lIn. exfalso; lsetdec.
        ++ destr_bool...
    + inversion H0...
  * pose proof (cv_free_never_universal u).
    destruct (free_for_cv u)...
    assert (b = false) by (destruct b; eauto*); subst...
    cbv [subst_cset] in *; find_and_destroy_set_mem...
    induction T; simpl in *; simpl_env in *...
    + cbv [subst_cset] in *; find_and_destroy_set_mem;
      assert (`cset_uvar` c = true) by (destruct c; eauto*);
      destruct c; subst; apply subcapt_in_univ...

      1, 2: admit. (** two identical wellformedness goals *)
    + inversion H4...
Admitted.

Lemma subcapt_univ_through_subst_tb : forall F E Z P T,
  wf_env (F ++ [(Z, bind_sub P)] ++ E) ->
  map (subst_tb Z P) F ++ E |-sc {*} <: cv (subst_tt Z P T) ->
  F ++ [(Z, bind_sub P)] ++ E |-sc {*} <: cv T \/
    (Z `in` (`cset_fvars` (cv T)) /\ E |-sc {*} <: cv P).
Proof with eauto.
  intros * WfEnv ScUniv.
  dependent induction ScUniv...
  * induction T; simpl in *; simpl_env in *...
    + cbv [subst_cset] in *...
      destruct (cv P) as [Pf Pb Pu Pl]...
      destruct c as [f b u l]...
      find_and_destroy_set_mem...
      - inversion x...
        destruct u...
        ++ left. apply subcapt_in_univ...
           admit.
        ++ right; split...
           assert (Pu = true) by (destruct Pu; eauto*); subst...
           apply subcapt_in_univ...
           admit.
      - inversion x; subst...
          left. apply subcapt_in_univ...
          admit.
    + inversion x...
    + destruct (a == Z); subst...
      - right; rewrite <- x; split.
        fsetdec.
        apply subcapt_in_univ...
        admit.
      - inversion x...
  * induction T; simpl in *; simpl_env in *...
    + cbv [subst_cset] in *...
      destruct (cv P) as [Pf Pb Pu Pl]...
      destruct c as [f b u l]...
      find_and_destroy_set_mem...
      - inversion H0...
        destruct u; rewrite H2...
        ++ left. apply subcapt_in_univ...
           admit.
        ++ right; split...
           assert (Pu = true) by (destruct Pu; eauto*); subst...
           apply subcapt_in_univ...
           admit.
      - rewrite H0.
        left. apply subcapt_in_univ...
        admit.
    + destruct (a == Z); subst...
      - right; split...
        fsetdec.
        destruct (cv P); subst...
        apply subcapt_in_univ...
        admit.
      - inversion H0...
  * induction T; simpl in *; simpl_env in *...
    + cbv [subst_cset] in *...
      destruct (cv P) as [Pf Pb Pu Pl]...
      destruct c as [f b u l]...
      find_and_destroy_set_mem...
      - inversion H4...
        destruct u; rewrite H6...
        ++ left. apply subcapt_in_univ...
          admit.
        ++ right; split...
          assert (Pu = true) by (destruct Pu; eauto*); subst...
          apply subcapt_in_univ...
          admit.
      - rewrite H4.
        left. apply subcapt_in_univ...
        admit.
    + destruct (a == Z); subst...
      - right; split...
        fsetdec.
        destruct (cv P); subst...
        apply subcapt_in_univ...
        admit.
      - inversion H4...
Admitted.
