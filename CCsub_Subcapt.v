Require Import Coq.Program.Equality.
Require Export CCsub_Hints.
Require Export CCsub_Lemmas.

Local Ltac hint := idtac.

Lemma subcapt_weakening : forall Γ Θ Δ C D,
  (Δ ++ Γ) ⊢ₛ C <: D ->
  (Δ ++ Θ ++ Γ) ⊢ wf ->
  (Δ ++ Θ ++ Γ) ⊢ₛ C <: D.
Proof with eauto using wf_cset_weakening.
  intros * Hsc Hwf.
  remember (Δ ++ Γ).
  remember (Δ ++ Θ ++ Γ).
  induction Hsc; subst...
  - apply subcapt_universal; eapply wf_cset_weakening...
  - apply subcapt_in...
  - apply subcapt_set...
    intros X XNotIn...
Qed.

Lemma wf_cset_fvarless : forall Γ univ,
  Γ ⊢ₛ (cset_set {}A {}N univ) wf.
Proof with eauto.
  intros *.
  constructor...
  intros ? ?.
  exfalso; fsetdec.
Qed.

Hint Resolve wf_cset_fvarless : core.

Lemma subcapt_reflexivity : forall Γ C,
  Γ ⊢ₛ C wf ->
  Γ ⊢ₛ C <: C.
Proof with eauto.
  intros * WfC.
  inversion WfC; subst.
  constructor...
  - intros y yIn.
    apply subcapt_in...
    + apply (wf_cset_singleton_by_mem fvars univ)...
  - destruct univ...
Qed.

Lemma subcapt_transitivity : forall D Γ C E,
  Γ ⊢ wf ->
  Γ ⊢ₛ C <: D ->
  Γ ⊢ₛ D <: E ->
  Γ ⊢ₛ C <: E.
Proof with eauto with fsetdec.
  intros * WfE SCD SDE.
  note (Γ ⊢ₛ E wf).
  dependent induction SCD...
  - Case "subcapt_universal".
    inversion SDE; subst...
    assert (univ = true) by csetdec; subst.
    apply subcapt_universal...
  - Case "subcapt_in".
    dependent induction SDE...
    assert (x = x0) by fsetdec; subst.
    eapply subcapt_var...
  - Case "subcapt_in_univ".
    dependent induction SDE; eauto using subcapt_universal.
  - Case "subcapt_var".
    apply subcapt_set...
    + intros x xIn...
    + destruct b...
      destruct univ... 
      destruct D; simpl in *; subst.
      inversion SDE...
Qed.

Lemma subcapt_from_binds : forall R x C Γ,
  Γ ⊢ wf ->
  binds x (bind_typ (C # R)) Γ ->
  Γ ⊢ₛ (`cset_fvar` x) <: C.
Proof with eauto.
  intros* ? Binds.
  eapply wf_cset_from_binds in Binds as WfC...
  destruct C...
  eapply wf_typ_from_binds_typ in Binds as WfT...
  inversion WfT;
    inversion select (wf_cset _ _);
    subst.
  eapply subcapt_var...
  eapply subcapt_reflexivity...
Qed.

(* Subtyping implies subcapturing *)
Lemma sub_implies_subcapt : forall Γ S T,
  Γ ⊢ S <: T ->
  Γ ⊢ₛ (typ_cv S) <: (typ_cv T).
Local Ltac hint ::=
  eauto using subcapt_reflexivity.
Proof with hint.
  intros * Hsub.
  assert (Γ ⊢ₛ (typ_cv S) wf); [apply cv_wf|]...
  assert (Γ ⊢ₛ (typ_cv T) wf); [apply cv_wf|]...
  induction Hsub; simpl in *...
  - Case "sub_trans_tvar".
    apply subcapt_empty...
  - Case "sub_top".
    (* REVIEW: not true, this lemma only works for non pure types *)
    admit.
Admitted.

(* Substituting the same capture set preserves subcapturing *)
Lemma subcapt_through_subst_cset : forall x U C Δ Γ C1 C2 ,
  (Δ ++ [(x, bind_typ U)] ++ Γ) ⊢ₛ C1 <: C2 ->
  (Δ ++ [(x, bind_typ U)] ++ Γ) ⊢ wf ->
  Γ ⊢ₛ C <: (typ_cv U) ->
  (map (subst_cb x C) Δ ++ Γ) ⊢ₛ (subst_cset x C C1) <: (subst_cset x C C2).
Proof with eauto using wf_env_subst_cb, wf_cset_subst_cb with fsetdec.
  intros * Hsc WfE HscC.
  dependent induction Hsc.
  - Case "subcapt_universal".
    assert ((map (subst_cb x C) Δ ++ Γ) ⊢ₛ (subst_cset x C C0) wf) as ?WF. {
      eapply wf_cset_subst_cb...
    }
    assert ((map (subst_cb x C) Δ ++ Γ) ⊢ₛ (subst_cset x C (cset_set xs {}N true)) wf) as ?WF. {
      eapply wf_cset_subst_cb...
    }
    cbv [subst_cset] in *.
    destruct_set_mem x xs.
    + assert ((Δ ++ [(x, bind_typ U)] ++ Γ) ⊢ U wf) as HA. {
        note (wf_env ([(x, bind_typ U)] ++ Γ)) by eauto...
        rewrite_env (∅ ++ (Δ ++ [(x, bind_typ U)]) ++ Γ).
        apply wf_typ_weakening; simpl_env...
      }
      forwards: cv_wf HA.
      note (Γ ⊢ₛ C wf).
      inversion HA; subst; unfold cset_union; csetsimpl; apply subcapt_universal...
    + apply subcapt_universal...
  - Case "subcapt_in".
    assert ((map (subst_cb x C) Δ ++ Γ) ⊢ₛ (subst_cset x C (cset_set xs {}N b)) wf) as ?WF. {
      eapply wf_cset_subst_cb...
    }
    assert ((map (subst_cb x C) Δ ++ Γ) ⊢ₛ
                       (subst_cset x C (`cset_fvar` x0)) wf) as ?WF. {
      eapply wf_cset_subst_cb...
    }
    unfold subst_cset in *.
    destruct_set_mem x {x0}A.
    + destruct_set_mem x xs.
      2: exfalso; fsetdec.
      assert ((Δ ++ [(x, bind_typ U)] ++ Γ) ⊢ₛ C wf) as HA. {
        note (([(x, bind_typ U)] ++ Γ) ⊢ wf) by eauto...
        rewrite_env (∅ ++ (Δ ++ [(x, bind_typ U)]) ++ Γ).
        apply wf_cset_weakening; simpl_env...
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
      assert ((Δ ++ [(x, bind_typ U)] ++ Γ) ⊢ₛ C wf) as HA. {
        note (([(x, bind_typ U)] ++ Γ) ⊢ wf) by eauto...
        rewrite_env (∅ ++ (Δ ++ [(x, bind_typ U)]) ++ Γ).
        apply wf_cset_weakening; simpl_env...
      }
      note (Γ ⊢ₛ C wf).
      inversion HA; subst.
      csetsimpl.
      apply subcapt_in...
  - Case "subcapt_in_univ".
    assert ((map (subst_cb x C) Δ ++ Γ) ⊢ₛ (subst_cset x C D) wf). {
      eapply wf_cset_subst_cb...
    }
    inversion select (_ ⊢ₛ D wf); repeat subst. (* so apparently subst isn't idempotent *)
    unfold subst_cset in *.
    find_and_destroy_set_mem; [exfalso;fsetdec|].
    find_and_destroy_set_mem.
    + note (Γ ⊢ₛ C wf) by eauto; subst.
      csetsimpl.
      apply subcapt_universal...
    + apply subcapt_universal...
  - Case "subcapt_var".
    unfold subst_cset at 1.
    destruct_set_mem x (singleton x0).
    + assert (x0 = x) by fsetdec; subst.
      assert (binds x (bind_typ U) (Δ ++ [(x, bind_typ U)] ++ Γ)) as HA by auto.
      forwards EQ: binds_typ_unique H HA; subst; clear HA.
      assert (Γ ⊢ U wf) by eauto.
      assert (x ∉ dom Γ) as HA. {
        assert (ok (Δ ++ [(x, bind_typ U)] ++ Γ)) as HA by auto.
        apply ok_tail in HA.
        inversion HA...
      }
      forwards: notin_fv_wf_typ H0 HA.
      replace (C `u` cset_set ({x}A `\`A x) {}N false)
              with C by (destruct U; csetdec).
      apply (subcapt_transitivity (typ_cv U))... {
        rewrite_env (∅ ++ (map (subst_cb x C) Δ ++ Γ)).
        apply subcapt_weakening; simpl_env...
      }
      replace (typ_cv U) with (subst_cset x C (typ_cv U)).
      2: {
        symmetry.
        apply subst_cset_fresh.
        destruct U; simpl in *; csetdec.
        destruct v.
        - simpl in H2.
          apply (H1 H2).
        - simpl in H2.
          fsetdec. 
      }
      eapply IHHsc...
    + assert (x0 <> x) by fsetdec.
      binds_cases H.
      * specialize (IHHsc x U Δ Γ ltac:(trivial) ltac:(trivial)).
        forwards: wf_typ_from_binds_typ H...
        eapply subcapt_var with (T := T)...
        replace (typ_cv T) with (subst_cset x C (typ_cv T)).
        2: {
          symmetry; apply subst_cset_fresh.
          assert (x ∉ dom Γ) as HA. {
            assert (ok (Δ ++ [(x, bind_typ U)] ++ Γ)) as HA by auto.
            apply ok_tail in HA.
            inversion HA...
          }
          forwards: notin_fv_wf_typ H1 HA.
          destruct T; simpl in *; try fsetdec.
          destruct v; simpl...
        }
        apply IHHsc...
      * assert (binds x0 (bind_typ (subst_ct x C T)) (map (subst_cb x C) Δ ++ Γ)) as HBnd by auto.
        eapply subcapt_var...
        replace (typ_cv (subst_ct x C T))
          with (subst_cset x C (typ_cv T)).
        2: {
          destruct T; simpl; unfold subst_cset...
          destruct v; simpl.
          2-6: destruct_set_mem x {}A; [ clear - xIn0; exfalso; fsetdec | reflexivity ].
          assert (x <> a). {
            forwards WfA: wf_typ_from_binds_typ x0 a...
            assert (binds x _ (Δ ++ [(x, bind_typ U)] ++ Γ)) by auto.
            inversion WfA; subst.
            forwards: binds_unique a...
          }
          unfold subst_cset.
          destruct_set_mem x {a}A; [exfalso;fsetdec|].
          easy.
        }
        eapply IHHsc...
  - Case "subcapt_tvar".
    unfold subst_cset at 1.
    destruct_set_mem x (singleton x0).
    + assert (x0 = x) by fsetdec; subst.
      assert (binds x (bind_typ U) (Δ ++ [(x, bind_typ U)] ++ Γ)) as HA by auto.
      forwards EQ: binds_unique H HA.
      exfalso;congruence.
    + assert (x0 <> x) by fsetdec.
      binds_cases H.
      * specialize (IHHsc x U Δ Γ ltac:(trivial) ltac:(trivial)).
        forwards: wf_typ_from_binds_sub H...
        eapply subcapt_tvar with (T := T)...
        replace (typ_cv T) with (subst_cset x C (typ_cv T)).
        2: {
          symmetry; apply subst_cset_fresh.
          assert (x ∉ dom Γ) as HA. {
            assert (ok (Δ ++ [(x, bind_typ U)] ++ Γ)) as HA by auto.
            apply ok_tail in HA.
            inversion HA...
          }
          forwards: notin_fv_wf_typ H1 HA.
          destruct T; simpl in *; try fsetdec.
          destruct v; simpl...
        }
        apply IHHsc...
      * assert (binds x0 (bind_sub (subst_ct x C T)) (map (subst_cb x C) Δ ++ Γ)) as HBnd by auto.
        eapply subcapt_tvar...
        replace (typ_cv (subst_ct x C T)) with (subst_cset x C (typ_cv T)).
        2: {
          destruct T; simpl; unfold subst_cset...
          destruct v; simpl.
          2-6: destruct_set_mem x {}A; [ clear - xIn0; exfalso; fsetdec | reflexivity ].
          assert (x <> a). {
            forwards WfA: wf_typ_from_binds_sub x0 a...
            assert (binds x _ (Δ ++ [(x, bind_typ U)] ++ Γ)) by auto.
            inversion WfA; subst.
            forwards: binds_unique a...
          }
          unfold subst_cset.
          destruct_set_mem x {a}A; [exfalso;fsetdec|].
          easy.
        }
        eapply IHHsc...
  - Case "subcapt_set".
    assert ((map (subst_cb x C) Δ ++ Γ) ⊢ₛ
                        (subst_cset x C (cset_set xs {}N b)) wf) as ?WF. {
      eapply wf_cset_subst_cb...
      constructor.
      - intros y yIn.
        enough ((Δ ++ [(x, bind_typ U)] ++ Γ) ⊢ₛ (`cset_fvar` y) wf) as HA. {
          inversion HA...
        }
        specialize (H0 y yIn); simpl in H0...
      - intros y yIn.
        enough ((Δ ++ [(x, bind_typ U)] ++ Γ) ⊢ₛ (`cset_fvar` y) wf) as HA. {
          inversion HA...
        }
        specialize (H0 y yIn); simpl in H0...
    }
    assert ((map (subst_cb x C) Δ ++ Γ) ⊢ₛ (subst_cset x C D) wf) as ?WF. {
      eapply wf_cset_subst_cb...
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
      - (* Should we have a lemma that `cset_uvar` is not affected by subst? *)
        (* Looking at that chain, we probably should. *)
        destruct D; unfold subst_cset; destruct_if; destruct U; csetdec.
    }

    unfold AtomSet.F.For_all in H0.
    inversion H; subst.
    note (Γ ⊢ₛ C wf).

    rename fvars into cs', univ into b__c', fvars0 into ds, univ0 into b__d.
    unfold subst_cset in WF0 |- *.
    destruct_set_mem x cs'.
    + csetsimpl.
      apply subcapt_set...
      2: csetdec.
      1: {
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
        - csetsimpl.
          apply subcapt_universal...
          applys wf_cset_singleton_by_mem (ds `u`A xs `\`A x)...
        - cleanup_singleton_eq x y x0 x1.
          apply subcapt_in...
          applys wf_cset_singleton_by_mem (ds `u`A xs `\`A x)...
        - cleanup_singleton_eq x y x0 x1.
          replace (`cset_fvar` y)
            with (subst_cset x (cset_set ds {}N b__d) (`cset_fvar` y)).
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
        - cleanup_singleton_eq x y x0 x1.
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
        - replace (`cset_fvar` y) with (subst_cset x (cset_set ds {}N b__d) (`cset_fvar` y)).
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
      }
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
           replace (`cset_fvar` y) with (subst_cset x (cset_set ds {}N b__d) (`cset_fvar` y)).
           eapply wf_cset_subst_cb...
           symmetry.
           apply subst_cset_fresh...
        -- cleanup_singleton_eq x y x0 x1.
            apply subcapt_in...
            replace (`cset_fvar` y) with (subst_cset x (cset_set ds {}N b__d) (`cset_fvar` y)).
            eapply wf_cset_subst_cb...
            symmetry.
            apply subst_cset_fresh...
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
        forwards H1: (>> H1' x xIn x U Δ Γ)...
        move H1 before H1'; clear H1'.
        unfold subst_cset at 1 in H1.
        destruct_set_mem x {x}A; [|exfalso;fsetdec].

        unfold subst_cset at 1 in H1.
        destruct_set_mem x cs'; [exfalso;fsetdec|].

        csetsimpl.

        replace (ds `u`A {x}A `\`A x) with ds in H1 by fsetdec.

        enough (subcapt (map (subst_cb x (cset_set ds {}N b__d)) Δ ++ Γ)
                          (`cset_fvar` y)
                          (cset_set ds {}N b__d)) as HAA. {
          eapply subcapt_transitivity...
        }
        eapply subcapt_in...
        eapply wf_cset_singleton_by_mem...
Qed.

Lemma wf_cset_atom_union : forall Γ xs ys u1 u2,
  Γ ⊢ₛ (cset_set xs {}N u1) wf ->
  Γ ⊢ₛ (cset_set ys {}N u2) wf ->
  Γ ⊢ₛ (cset_set (xs `union` ys) {}N (u1 || u2)) wf.
Proof with eauto.
  intros * WfXs WfYs.
  inversion WfXs; inversion WfYs; subst.
  constructor...
  intros ? ?.
  rewrite AtomSetFacts.union_iff in *.
  auto*.
  fsetdec.
Qed.

Lemma subcapt_expansion : forall Γ C D1 D2,
  Γ ⊢ₛ D2 wf ->
  Γ ⊢ₛ C <: D1 ->
  Γ ⊢ₛ C <: (D1 `u` D2).
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
  - inversion HwfD2; simpl; subst...
  - eapply subcapt_var...
  - eapply subcapt_tvar...
  - apply subcapt_set...
    + intros ? ?...
    + csetdec.
Qed.

Tactic Notation "subst_mem_singleton" hyp(H) :=
  match type of H with
    | _ `in`A _ => rewrite AtomSetFacts.singleton_iff in H; subst
  end.

Tactic Notation "subst_mem_singleton" "<-" hyp(H) :=
  match type of H with
    | _ `in`A _ => rewrite AtomSetFacts.singleton_iff in H; symmetry in H; subst
  end.

Lemma subcapt_singleton_mem: forall x Γ C D,
  Γ ⊢ wf ->
  Γ ⊢ₛ C <: D ->
  x A`in` C ->
  Γ ⊢ₛ (`cset_fvar` x) <: D.
Proof with eauto with fsetdec.
  intros * WfΓ Hsc xIn.
  dependent induction Hsc...
  - apply subcapt_universal...
    note (Γ ⊢ₛ C wf).
    eapply wf_cset_singleton_by_mem...
  - eapply subcapt_in...
    replace x with x0 by (clear - xIn; fsetdec)...
  - clear - xIn; fsetdec.
  - subst_mem_singleton xIn.
    apply (subcapt_transitivity (typ_cv T))...
    eapply subcapt_var...
    eapply subcapt_reflexivity...
  - subst_mem_singleton xIn.
    apply (subcapt_transitivity (typ_cv T))...
    eapply subcapt_tvar...
    eapply subcapt_reflexivity...
Qed.

Lemma subcapt_universal_mem: forall Γ C D,
  Γ ⊢ wf ->
  Γ ⊢ₛ C <: D ->
  implb (`cset_uvar` C) (`cset_uvar` D) = true.
Proof with eauto with fsetdec.
  intros * WfE Hsc.
  dependent induction Hsc...
  csetdec.
Qed.

Lemma subcapt_union_distributivity : forall Γ C1 C2 D,
  Γ ⊢ wf ->
  Γ ⊢ₛ C1 <: D ->
  Γ ⊢ₛ C2 <: D ->
  Γ ⊢ₛ (C1 `u` C2) <: D.
Proof with eauto using wf_cset_union with fsetdec.
  intros * WfΓ HscC1 HscC2.
  assert (Γ ⊢ₛ (C1 `u` C2) wf) by auto using wf_cset_union.
  generalize dependent C2.
  dependent induction HscC1; intros C2 HscC2 WF__union...
  - note (Γ ⊢ₛ C2 wf); csetsimpl.
    apply subcapt_set.
    + trivial...
    + intros y yIn.
      destruct_union_mem yIn.
      * subst_mem_singleton yIn.
        apply subcapt_in...
      * applys subcapt_transitivity HscC2...
        apply subcapt_in...
        apply wf_concrete_cset...
        2: fsetdec.
        intros z zIn...
    + forwards: subcapt_universal_mem HscC2...
  - note (Γ ⊢ₛ C2 wf); csetsimpl.
    apply subcapt_set.
    + trivial...
    + intros y yIn.
      applys subcapt_transitivity HscC2...
      apply subcapt_in...
      apply wf_concrete_cset...
      2: fsetdec.
      intros z zIn...
    + forwards: subcapt_universal_mem HscC2...
  - apply (subcapt_transitivity (typ_cv T `u` C2))...
    assert (Γ ⊢ₛ (typ_cv T `u` C2) wf) as WfU by auto using wf_cset_union.
    note (Γ ⊢ₛ C2 wf).
    note (Γ ⊢ₛ (typ_cv T) wf).
    rewrite <- H2 in WfU.
    csetsimpl.
    apply subcapt_set...
    2: csetdec.
    intros y yIn.
    destruct_union_mem yIn.
    + subst_mem_singleton yIn.
      apply (subcapt_transitivity (typ_cv T))...
      * eapply subcapt_var...
        eapply subcapt_reflexivity...
      * rewrite <- H2.
        apply subcapt_set...
        2: csetdec.
        intros z zIn.
        apply subcapt_in...
        apply wf_concrete_cset...
        2: fsetdec.
        intros w wIn...
    + apply subcapt_in...
      apply wf_concrete_cset...
      2: fsetdec.
      intros z zIn...
  - apply (subcapt_transitivity (typ_cv T `u` C2))...
    assert (Γ ⊢ₛ (typ_cv T `u` C2) wf) as WfU by auto using wf_cset_union.
    note (Γ ⊢ₛ C2 wf).
    note (Γ ⊢ₛ (typ_cv T) wf).
    rewrite <- H2 in WfU.
    csetsimpl.
    apply subcapt_set...
    2: csetdec.
    intros y yIn.
    destruct_union_mem yIn.
    + subst_mem_singleton yIn.
      apply (subcapt_transitivity (typ_cv T))...
      * eapply subcapt_tvar...
        eapply subcapt_reflexivity...
      * rewrite <- H2.
        apply subcapt_set...
        2: csetdec.
        intros z zIn.
        apply subcapt_in...
        apply wf_concrete_cset...
        2: fsetdec.
        intros w wIn...
    + apply subcapt_in...
      apply wf_concrete_cset...
      2: fsetdec.
      intros z zIn...
  - note (Γ ⊢ₛ C2 wf); csetsimpl.
    apply subcapt_set...
    + intros y yIn.
      destruct_union_mem yIn...
      apply (subcapt_transitivity (cset_set fvars {}N univ))...
      eapply subcapt_in...
      apply wf_concrete_cset...
      2: fsetdec.
      intros z zIn...
    + forwards: subcapt_universal_mem HscC2; csetdec...
Qed.

Lemma cset_union_symmetrical : forall C D,
  C `u` D = D `u` C.
Proof with eauto.
  intros.
  destruct C; destruct D; simpl; try easy.
  csetdec.
Qed.

Lemma union_under_subcapturing : forall Γ C1 C2 D1 D2,
  Γ ⊢ wf ->
  Γ ⊢ₛ C1 <: C2 ->
  Γ ⊢ₛ D1 <: D2 ->
  Γ ⊢ₛ (C1 `u` D1) <: (C2 `u` D2).
Proof with eauto.
  intros * WfΓ Hsc1 Hsc2.
  apply subcapt_union_distributivity...
  - apply subcapt_expansion...
  - rewrite cset_union_symmetrical.
    apply subcapt_expansion...
Qed.

Lemma subcapt_through_subst_tt : forall Γ P Q Δ X C D,
  (Δ ++ [(X, bind_sub Q)] ++ Γ) ⊢ wf ->
  (Δ ++ [(X, bind_sub Q)] ++ Γ) ⊢ₛ C <: D ->
  (* TODO:
      Q pure from wf_env
      Q pure and P <: Q => P pure
  *)
  Γ ⊢ P <: Q ->
  (map (subst_tb X P) Δ ++ Γ) ⊢ₛ (subst_cset X (typ_cv P) C) <: (subst_cset X (typ_cv P) D).
Proof with eauto using wf_env_subst_tb, wf_cset_subst_tb, wf_typ_subst_tb with fsetdec.
  intros * Hwf Hsc Hsub.
  assert ((map (subst_tb X P) Δ ++ Γ) ⊢ wf).
  { eapply wf_env_subst_tb...
    admit.
  }
  generalize dependent P.
  dependent induction Hsc; intros P Hsub Henv.
  - assert ((map (subst_tb X P) Δ ++ Γ) ⊢ₛ (subst_cset X (typ_cv P) C) wf) as ?WF...
    assert ((map (subst_tb X P) Δ ++ Γ) ⊢ₛ
                       (subst_cset X (typ_cv P) (cset_set xs {}N true)) wf) as ?WF...
    cbv [subst_cset] in *.
    destruct_set_mem X xs.
    + assert ((Δ ++ [(X, bind_sub Q)] ++ Γ) ⊢ P wf) as HA. {
        note (([(X, bind_sub Q)] ++ Γ) ⊢ wf) by eauto...
        rewrite_env (∅ ++ (Δ ++ [(X, bind_sub Q)]) ++ Γ).
        apply wf_typ_weakening; simpl_env...
      }
      forwards: cv_wf HA.
      inversion HA; subst; simpl in *; csetsimpl; apply subcapt_universal...
    + apply subcapt_universal...
  - assert ((map (subst_tb X P) Δ ++ Γ) ⊢ₛ (subst_cset X (typ_cv P) (`cset_fvar` x)) wf) as ?WF...
    assert ((map (subst_tb X P) Δ ++ Γ) ⊢ₛ
                       (subst_cset X (typ_cv P) (cset_set xs {}N b)) wf) as ?WF...
    unfold subst_cset in *.
    destruct_set_mem X {x}A.
    + destruct_set_mem X xs.
      2: exfalso; fsetdec.
      assert ((Δ ++ [(X, bind_sub Q)] ++ Γ) ⊢ₛ (typ_cv P) wf) as HA. {
        note (([(X, bind_sub Q)] ++ Γ) ⊢ wf) by eauto...
        rewrite_env (∅ ++ (Δ ++ [(X, bind_sub Q)]) ++ Γ).
        apply wf_cset_weakening; simpl_env; [apply cv_wf|]...
      }
      inversion HA; subst; csetsimpl.
      replace (xs `union` singleton x `remove` X) with xs by fsetdec.
      rename select (_ = typ_cv P) into EQ.
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
      assert ((Δ ++ [(X, bind_sub Q)] ++ Γ) ⊢ₛ (typ_cv P) wf) as HA. {
        note (([(X, bind_sub Q)] ++ Γ) ⊢ wf) by eauto...
        rewrite_env (∅ ++ (Δ ++ [(X, bind_sub Q)]) ++ Γ).
        apply wf_cset_weakening; simpl_env; [apply cv_wf|]...
      }
      inversion HA; subst; csetsimpl.
      rename select (_ = typ_cv P) into EQ.
      rewrite <- EQ in WF0; csetsimpl in WF0.
      apply subcapt_in...
  - assert ((map (subst_tb X P) Δ ++ Γ) ⊢ₛ (subst_cset X (typ_cv P) D) wf)...
    inversion select (_ ⊢ₛ D wf); repeat subst. (* so apparently subst isn't idempotent *)
    unfold subst_cset in *.
    find_and_destroy_set_mem; [exfalso;fsetdec|].
    find_and_destroy_set_mem.
    + assert (Γ ⊢ₛ (typ_cv P) wf) as HA; [|inversion HA; subst]. {
        apply cv_wf...
      }
      rename select (_ = typ_cv P) into EQ.
      rewrite <- EQ in H1.
      csetsimpl.
      apply subcapt_universal...
    + apply subcapt_universal...
  - unfold subst_cset at 1.
    destruct_set_mem X {x}A.
    + assert (x = X) by fsetdec; subst.
      assert (binds X (bind_sub Q) (Δ ++ [(X, bind_sub Q)] ++ Γ)) as HA by auto.
      forwards: binds_unique (bind_typ T) (bind_sub Q)...
      congruence.
    + assert (x <> X) by fsetdec.
      binds_cases H.
      * specialize (IHHsc X Δ Q Γ ltac:(trivial) ltac:(trivial) ltac:(trivial)).
        forwards: wf_typ_from_binds_typ H...
        eapply subcapt_var with (T := T)...
        replace (typ_cv T) with (subst_cset X (typ_cv P) (typ_cv T)).
        2: {
          symmetry; apply subst_cset_fresh.
          assert (X ∉ dom Γ) as HA. {
            assert (ok (Δ ++ [(X, bind_sub Q)] ++ Γ)) as HA by auto.
            apply ok_tail in HA.
            inversion HA...
          }
          forwards: notin_fv_wf_typ H1 HA.
          destruct T; simpl in *; try fsetdec.
          destruct v...
        }
        apply IHHsc...
      * assert (binds x (bind_typ (subst_tt X P T)) (map (subst_tb X P) Δ ++ Γ)) as HBnd by auto.
        eapply subcapt_var...
        replace (typ_cv (subst_tt X P T))
          with (subst_cset X (typ_cv P) (typ_cv T)).
        1: eapply IHHsc...
        1: {
          destruct T; unfold subst_cset; simpl...
          destruct v; simpl...
          2-6: destruct_if; [ exfalso; csetdec | reflexivity ].
          destruct (a == X); destruct_set_mem X {a}A; try (exfalso;fsetdec).
          2: simpl...
          note (Γ ⊢ P wf); simpl; unfold cset_union; csetdec.
        }
  - unfold subst_cset at 1.
    destruct_set_mem X (singleton x).
    + assert (x = X) by fsetdec; subst.
      assert (binds X (bind_sub Q) (Δ ++ [(X, bind_sub Q)] ++ Γ)) as HBnd by auto.
      forwards EQ: binds_unique H HBnd.
      inversion EQ; subst.
      assert (Γ ⊢ P wf) as WfP by eauto.
      assert (Γ ⊢ Q wf) as WfQ by eauto.
      assert (X ∉ dom Γ) as HA. {
        assert (ok (Δ ++ [(X, bind_sub Q)] ++ Γ)) as HA by auto.
        apply ok_tail in HA.
        inversion HA...
      }
      forwards: notin_fv_wf_typ WfP HA.
      forwards: notin_fv_wf_typ WfQ HA.
      replace (typ_cv P `u` cset_set ({X}A `\`A X) {}N false)
        with (typ_cv P) by (destruct (typ_cv P); csetdec).
      replace (typ_cv P) with (subst_cset X (typ_cv P) (typ_cv P)) at 1.
      2: {
        symmetry.
        apply subst_cset_fresh.
        destruct P; simpl in *; try fsetdec.
        destruct v...
      }
      apply (subcapt_transitivity (subst_cset X (typ_cv P) (typ_cv Q)))...
      eenough (Γ ⊢ₛ _ <: _) as HE. {
        rewrite_env (∅ ++ (map (subst_tb X P) Δ ++ Γ)).
        apply subcapt_weakening; simpl_env...
      }
      do 2 erewrite <- typ_cv_subst_ct_correspondence by fsetdec.
      do 2 erewrite <- subst_ct_fresh by fsetdec.
      apply sub_implies_subcapt...
    + assert (x <> X) by fsetdec.
      binds_cases H.
      * specialize (IHHsc X Δ Q Γ ltac:(trivial) ltac:(trivial) ltac:(trivial)).
        forwards: wf_typ_from_binds_sub H...
        eapply subcapt_tvar with (T := T)...
        replace (typ_cv T) with (subst_cset X (typ_cv P) (typ_cv T)).
        2: {
          symmetry; apply subst_cset_fresh.
          assert (X ∉ dom Γ) as HA. {
            assert (ok (Δ ++ [(X, bind_sub Q)] ++ Γ)) as HA by auto.
            apply ok_tail in HA.
            inversion HA...
          }
          forwards: notin_fv_wf_typ H1 HA.
          destruct T; simpl in *; try fsetdec.
          destruct v...
        }
        apply IHHsc...
      * assert (binds x (bind_sub (subst_tt X P T)) (map (subst_tb X P) Δ ++ Γ)) as HBnd by auto.
        eapply subcapt_tvar...
        replace (typ_cv (subst_tt X P T))
          with (subst_cset X (typ_cv P) (typ_cv T)).
        1: eapply IHHsc...
        1: {
          destruct T; unfold subst_cset; simpl...
          destruct v; simpl.
          2-6: destruct_if; [ exfalso; csetdec | reflexivity ].
          destruct (a == X); destruct_set_mem X {a}A; try (exfalso;fsetdec).
          2: simpl...
          note (Γ ⊢ P wf); simpl; unfold cset_union; csetdec.
        }
  - assert ((map (subst_tb X P) Δ ++ Γ) ⊢ₛ
                       (subst_cset X (typ_cv P) (cset_set xs {}N b)) wf) as ?WF. {
      eapply wf_cset_subst_tb...
      constructor.
      - intros y yIn.
        enough ((Δ ++ [(X, bind_sub Q)] ++ Γ) ⊢ₛ (`cset_fvar` y) wf) as HA. {
          inversion HA...
        }
        specialize (H0 y yIn); simpl in H0...
      - intros y yIn.
        enough ((Δ ++ [(X, bind_sub Q)] ++ Γ) ⊢ₛ (`cset_fvar` y) wf) as HA. {
          inversion HA...
        }
        specialize (H0 y yIn); simpl in H0...
    }
    assert ((map (subst_tb X P) Δ ++ Γ) ⊢ₛ
                       (subst_cset X (typ_cv P) D) wf) as ?WF. {
      eapply wf_cset_subst_tb...
    }

    unfold subst_cset at 1.
    unfold subst_cset in WF.
    destruct_set_mem X xs.
    2: {
      apply subcapt_set; trivial.
      - intros y yIn.
        assert (X <> y) by notin_solve.
        replace (`cset_fvar` y) with (subst_cset X (typ_cv P) (`cset_fvar` y))...
        unfold subst_cset.
        destruct_set_mem X (singleton y)...
        exfalso; fsetdec.
      - (* Should we have a lemma that `cset_uvar` is not affected by subst? *)
        (* Looking at that chain, we probably should. *)
        destruct D; unfold subst_cset; destruct_if; destruct P; simpl; csetdec.
        destruct v...
    }

    unfold AtomSet.F.For_all in H0.

    inversion H; subst.
    assert ((Δ ++ [(X, bind_sub Q)] ++ Γ) ⊢ₛ (typ_cv P) wf) as HA. {
      note (([(X, bind_sub Q)] ++ Γ) ⊢ wf) by eauto...
      rewrite_env (∅ ++ (Δ ++ [(X, bind_sub Q)]) ++ Γ).
      apply wf_cset_weakening; simpl_env; [apply cv_wf|]...
    }
    inversion HA; subst.

    rename fvars into cs', univ into b__c', fvars0 into ds, univ0 into b__d.
    unfold subst_cset in WF0 |- *.
    destruct_set_mem X cs'.
    + rename select (_ = typ_cv P) into EQ.
      rewrite <- EQ in WF, WF0.
      csetsimpl.
      apply subcapt_set; trivial.
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
        rename select (_ = typ_cv P) into EQ.
        replace (`cset_fvar` y) with (subst_cset X (typ_cv P) (`cset_fvar` y)).
        2: {
          unfold subst_cset; simpl.
          destruct_set_mem X (singleton y); (trivial || exfalso;fsetdec).
        }
        replace (cset_set (ds `union` cs' `remove` X) {}N (b__d || b__c'))
          with (subst_cset X (typ_cv P) (cset_set cs' {}N b__c')).
        2: {
          unfold subst_cset; simpl.
          destruct_set_mem X cs'; [|exfalso;fsetdec].
          rewrite <- EQ.
          csetsimpl...
        }
        (* rewrite EQ. *)
        eapply H1...
      * cleanup_singleton_eq' x y x0.
        rename select (_ = typ_cv P) into EQ.
        replace (`cset_fvar` y) with (subst_cset X (typ_cv P) (`cset_fvar` y)).
        2: {
          unfold subst_cset; simpl.
          destruct_set_mem X (singleton y); (trivial || exfalso;fsetdec).
        }
        replace (cset_set (ds `union` cs' `remove` X) {}N (b__d || b__c'))
          with (subst_cset X (typ_cv P) (cset_set cs' {}N b__c')).
        2: {
          unfold subst_cset; simpl.
          destruct_set_mem X cs'; [|exfalso;fsetdec].
          rewrite <- EQ.
          unfold cset_union; csetsimpl...
        }
        eapply H1...
      * rename select (_ = typ_cv P) into EQ.
        replace (`cset_fvar` y) with (subst_cset X (typ_cv P) (`cset_fvar` y)).
        2: {
          unfold subst_cset; simpl.
          destruct_set_mem X (singleton y); (trivial || exfalso;fsetdec).
        }
        replace (cset_set (ds `union` cs' `remove` X) {}N (b__d || b__c'))
          with (subst_cset X (typ_cv P) (cset_set cs' {}N b__c')).
        2: {
          unfold subst_cset; simpl.
          destruct_set_mem X cs'; [|exfalso;fsetdec].
          rewrite <- EQ.
          csetsimpl...
        }
        eapply H1...
    + csetsimpl.
      rename select (_ = typ_cv P) into EQ.
      apply subcapt_set; trivial.
      2: {
        forwards SpH1: H1 X X Δ Q Γ...
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
           replace (`cset_fvar` y) with (subst_cset X (typ_cv P) (`cset_fvar` y)).
           eapply wf_cset_subst_tb...
           symmetry.
           apply subst_cset_fresh...
        -- cleanup_singleton_eq' x y x0.
           replace (`cset_fvar` y) with (subst_cset X (typ_cv P) (`cset_fvar` y)).
           2: {
             unfold subst_cset; simpl.
             destruct_set_mem X (`cset_fvar` y); (trivial || exfalso;fsetdec).
           }
           replace (cset_set cs' {}N b__c') with (subst_cset X (typ_cv P) (cset_set cs' {}N b__c')).
           2: {
             unfold subst_cset; simpl.
             destruct_set_mem X cs'; (trivial||exfalso;fsetdec).
           }
           eapply H1...
        -- cleanup_singleton_eq' x y x0.
           replace (`cset_fvar` y) with (subst_cset X (typ_cv P) (`cset_fvar` y)).
           2: {
             unfold subst_cset; simpl.
             destruct_set_mem X (`cset_fvar` y); (trivial || exfalso;fsetdec).
           }
           replace (cset_set cs' {}N b__c') with (subst_cset X (typ_cv P) (cset_set cs' {}N b__c')).
           2: {
             unfold subst_cset; simpl.
             destruct_set_mem X cs'; (trivial||exfalso;fsetdec).
           }
           eapply H1...
        -- replace (`cset_fvar` y) with (subst_cset X (typ_cv P) (`cset_fvar` y)).
           2: {
             unfold subst_cset; simpl.
             destruct_set_mem X (`cset_fvar` y); (trivial || exfalso;fsetdec).
           }
           replace (cset_set cs' {}N b__c') with (subst_cset X (typ_cv P) (cset_set cs' {}N b__c')).
           2: {
             unfold subst_cset; simpl.
             destruct_set_mem X cs'; (trivial||exfalso;fsetdec).
           }
           eapply H1...
      * destruct_union_mem yIn.
        2: exfalso...
        rename H1 into H1'.
        forwards H1: (>> H1' X XIn X Δ Q Γ)...
        move H1 before H1'; clear H1'.
        unfold subst_cset at 1 in H1.
        destruct_set_mem X {X}A; [|exfalso;fsetdec].

        unfold subst_cset at 1 in H1.
        destruct_set_mem X cs'; [exfalso;fsetdec|].

        rewrite <- EQ in H1.
        csetsimpl.

        replace (ds `u`A {X}A `\`A X) with ds in H1 by fsetdec.

        enough ((map (subst_tb X P) Δ ++ Γ) ⊢ₛ
                         (`cset_fvar` y) <:
                         (cset_set ds {}N b__d)) as HAA. {
          eapply subcapt_transitivity...
        }
        eapply subcapt_in...
        forwards (? & ?): subcapt_regular H1.
        inversion select (_ ⊢ₛ (cset_set ds _ _) wf); subst...
        eapply wf_cset_singleton_by_mem...
        repeat rewrite dom_concat in *; repeat rewrite dom_map in *; simpl in *.
        admit.
Admitted.

(* (* ********************************************************************** *) *)
(* (** ** Narrowing and transitivity (3) *) *)

Lemma subst_cset_across_subcapt : forall Γ x C D C0,
  Γ ⊢ wf ->
  Γ ⊢ₛ C0 wf ->
  Γ ⊢ₛ C <: D ->
  Γ ⊢ₛ (subst_cset x C C0) <: (subst_cset x D C0).
Proof with eauto with fsetdec.
  intros * WfEnv Wf Sub.
  assert (Γ ⊢ₛ (subst_cset x C C0) wf). {
    unfold subst_cset.
    destruct_set_mem x (`cset_fvars` C0)...
    apply wf_cset_union...
    apply wf_cset_remove_fvar...
  }
  assert (Γ ⊢ₛ (subst_cset x D C0) wf). {
    unfold subst_cset.
    destruct_set_mem x (`cset_fvars` C0)...
    apply wf_cset_union...
    apply wf_cset_remove_fvar...
  }

  inversion Wf; subst.
  rename fvars into zs.

  note (Γ ⊢ₛ C wf).
  rename fvars into cs.

  note (Γ ⊢ₛ D wf).
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
    + intros y yIn.
      apply subcapt_in...
      destruct (AtomSet.F.union_1 yIn).
      * assert (y = x0) by fsetdec; subst...
      * apply wf_concrete_cset...
        2: fsetdec.
        intros z zIn...
    + csetdec.
  - csetsimpl.
    apply subcapt_set...
    intros y yIn.
    apply subcapt_in...
    apply wf_concrete_cset...
    2: fsetdec.
    intros z zIn...
  - csetsimpl.
    apply subcapt_set...
    2: csetdec.
    intros y yIn.
    destruct_union_mem yIn.
    2: {
      apply subcapt_in...
      apply wf_concrete_cset...
      2: fsetdec.
      intros z zIn...
    }
    rename select (y `in`A _) into yIn.
    apply AtomSetFacts.singleton_iff in yIn; symmetry in yIn; subst.
    eapply subcapt_var...
    apply (subcapt_transitivity (cset_set ds {}N univ1))...
    apply subcapt_set...
    + intros z zIn.
      apply subcapt_in...
      apply wf_concrete_cset...
      2: fsetdec.
      intros w wIn...
    + csetdec.
  - csetsimpl.
    apply subcapt_set...
    2: csetdec.
    intros y yIn.
    destruct_union_mem yIn.
    2: {
      apply subcapt_in...
      apply wf_concrete_cset...
      2: fsetdec.
      intros z zIn...
    }
    rename select (y `in`A _) into yIn.
    apply AtomSetFacts.singleton_iff in yIn; symmetry in yIn; subst.
    eapply subcapt_tvar...
    apply (subcapt_transitivity (cset_set ds {}N univ1))...
    apply subcapt_set...
    + intros z zIn.
      apply subcapt_in...
      apply wf_concrete_cset...
      2: fsetdec.
      intros w wIn...
    + csetdec.
  - csetsimpl.
    apply subcapt_set...
    2: csetdec.
    intros y yIn.
    destruct_union_mem yIn.
    2: {
      apply subcapt_in...
      apply wf_concrete_cset...
      2: fsetdec.
      intros z zIn...
    }
    apply (subcapt_transitivity (cset_set ds {}N univ1))...

    apply subcapt_set...
    + intros z zIn.
      apply subcapt_in...
      apply wf_concrete_cset...
      2: fsetdec.
      intros w wIn...
    + csetdec.
Qed.

Lemma subcapt_strengthening : forall Δ Θ Γ C1 C2,
  ok (Δ ++ Θ ++ Γ) ->
  (Δ ++ Γ) ⊢ wf ->
  (Δ ++ Γ) ⊢ₛ C1 wf ->
  (Δ ++ Γ) ⊢ₛ C2 wf ->
  (Δ ++ Θ ++ Γ) ⊢ₛ C1 <:  C2 ->
  (Δ ++ Γ) ⊢ₛ C1 <: C2.
Proof with eauto.
  intros * Ok WfE Wf1 Wf2 Sc.
  dependent induction Sc...
  - inversion Wf1; subst; cbv [allbound] in *...
    specialize (H3 x ltac:(fsetdec)) as [Tx Hbinds].
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
    specialize (H3 x ltac:(fsetdec)) as [Tx Hbinds].
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
  - destruct D as [fvD bvD univD]; subst...
    inversion H; subst...
    apply subcapt_set...
    * intros a aInXs.
      eapply H1...
      inversion Wf1; subst.
      eapply wf_concrete_cset...
      -- intros z zIn; assert (z = a) by (clear - zIn; fsetdec); subst...
      -- rewrite dom_concat in H9 |- *.
         fsetdec.
Qed.

Lemma subcapt_widening_univ : forall X Δ Γ P Q C,
  ok (Δ ++ [(X, bind_sub Q)] ++ Γ) ->
  (Δ ++ [(X, bind_sub P)] ++ Γ) ⊢ₛ {*} <: C ->
  Γ ⊢ P <: Q ->
  (Δ ++ [(X, bind_sub Q)] ++ Γ) ⊢ₛ {*} <: C.
Proof with eauto using wf_cset_narrowing.
  intros * Ok Sc Sub.
  dependent induction Sc...
Qed.

Lemma subcapt_widening_typ_univ : forall X Δ Γ P Q C,
  ok (Δ ++ [(X, bind_typ Q)] ++ Γ) ->
  (Δ ++ [(X, bind_typ P)] ++ Γ) ⊢ₛ {*} <: C ->
  Γ ⊢ P <: Q ->
  (Δ ++ [(X, bind_typ Q)] ++ Γ) ⊢ₛ {*} <: C.
Proof with eauto using wf_cset_narrowing_typ.
  intros * Ok Sc Sub.
  dependent induction Sc...
Qed.

Lemma univ_supercapt_inversion : forall Γ C,
  Γ ⊢ₛ {*} <: C ->
  * ∈ C.
Proof with eauto.
  intros * Hsc.
  dependent induction Hsc...
Qed.

(* TODO: move to CCsub_Lemmas.v
typ_cv_free_never_universal *)

Lemma subcapt_univ_through_subst_cb : forall Δ Γ x u P T,
  (Δ ++ [(x, bind_typ (exp_cv u # P))] ++ Γ) ⊢ₛ (typ_cv T) wf ->
  (map (subst_cb x (exp_cv u)) Δ ++ Γ) ⊢ₛ {*} <: (typ_cv (subst_ct x (exp_cv u) T)) ->
  (Δ ++ [(x, bind_typ (typ_capt (exp_cv u) P))] ++ Γ) ⊢ₛ {*} <: (typ_cv T).
Proof with eauto.
  intros * Wf ScUniv.
  forwards UIn: univ_supercapt_inversion ScUniv.
  destruct T; simpl in *; try congruence; unfold subst_cset in UIn.
  1: destruct v...
  unfold subst_cset in UIn.
  (* forwards: cv_free_never_universal u. *)
  find_and_destroy_set_mem.
  + destruct (exp_cv u).
    destruct b; try congruence...
    inversion Wf; subst.
    csetsimpl.
    apply subcapt_in_univ; trivial.
    (* REVIEW: unsolvable? previously used cv_never_universal which is not true anymore *)
    admit.
  + apply subcapt_in_univ; trivial.
Admitted.

Lemma subcapt_univ_through_subst_tb : forall Δ Γ Z P T,
  (Δ ++ [(Z, bind_sub P)] ++ Γ) ⊢ T wf ->
  Γ ⊢ P wf ->
  (map (subst_tb Z P) Δ ++ Γ) ⊢ₛ {*} <: typ_cv (subst_tt Z P T) ->
  (Δ ++ [(Z, bind_sub P)] ++ Γ) ⊢ₛ {*} <: typ_cv T
    \/ (Z ∈ (`cset_fvars` (typ_cv T))
          /\ Γ ⊢ₛ {*} <: typ_cv P).
Proof with eauto.
  intros * WfT WfP ScUniv.
  forwards: univ_supercapt_inversion ScUniv.
  inversion WfT; subst; simpl in *; simpl_env in *; try congruence.
  - destruct (X == Z); subst.
    + right; split.
      * fsetdec.
      * apply subcapt_in_univ; trivial.
        eapply cv_wf...
    + simpl in *; congruence.
  - inversion H0; subst.
    destruct univ.
    1: {
      left.
      apply subcapt_in_univ; trivial.
    }
    unfold subst_cset in H.
    find_and_destroy_set_mem; try congruence.
    assert (Γ ⊢ₛ (typ_cv P) wf) as WfCvP by (eapply cv_wf; eauto).
    inversion WfCvP; subst.
    rename select (_ = typ_cv P) into EQ; rewrite <- EQ in *.
    unfold cset_union in H.
    destruct univ; simpl in *; try congruence.
    right; split...
Qed.
