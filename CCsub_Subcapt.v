Require Import Coq.Program.Equality.
Require Import LibTactics.
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

(* Substituting the same capture set preserves subcapturing *)
Lemma subcapt_through_subst_cset : forall x D Q C Δ Γ C1 C2 ,
  (Δ ++ [(x, bind_typ (D # Q))] ++ Γ) ⊢ₛ C1 <: C2 ->
  (Δ ++ [(x, bind_typ (D # Q))] ++ Γ) ⊢ wf ->
  Γ ⊢ₛ C <: D ->
  (map (subst_cb x C) Δ ++ Γ) ⊢ₛ (subst_cset x C C1) <: (subst_cset x C C2).
Proof with eauto using wf_env_subst_cb, wf_cset_subst_cb with fsetdec.
  intros * Hsc WfE HscC.
  assert ((Δ ++ [(x, bind_typ (D # Q))] ++ Γ) ⊢ (D # Q) wf) as WfDQ. {
    note (([(x, bind_typ (D # Q))] ++ Γ) ⊢ wf) by eauto...
    rewrite_env (∅ ++ (Δ ++ [(x, bind_typ (D # Q))]) ++ Γ).
    apply wf_typ_weakening; simpl_env...
  }
  assert ((Δ ++ [(x, bind_typ (D # Q))] ++ Γ) ⊢ₛ C wf) as WfC. {
    note (([(x, bind_typ (D # Q))] ++ Γ) ⊢ wf) by eauto...
    rewrite_env (∅ ++ (Δ ++ [(x, bind_typ (D # Q))]) ++ Γ).
    apply wf_cset_weakening; simpl_env...
  }
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
    + note (Γ ⊢ₛ C wf).
      inversion WfDQ; subst; unfold cset_union; csetsimpl; apply subcapt_universal...
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
      inversion WfC; subst.
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
      note (Γ ⊢ₛ C wf).
      inversion WfDQ; subst.
      csetsimpl.
      apply subcapt_in...
  - Case "subcapt_in_univ".
    assert (WfD : (Δ ++ [(x, bind_typ (D # Q))] ++ Γ) ⊢ₛ D wf) by (inversion WfDQ; assumption).
    assert ((map (subst_cb x C) Δ ++ Γ) ⊢ₛ (subst_cset x C D) wf). {
      eapply wf_cset_subst_cb...
    }
    inversion WfD; repeat subst. (* so apparently subst isn't idempotent *)
    unfold subst_cset in *.
    destruct_set_mem x {}A; [exfalso;fsetdec|]; clear xIn.
    destruct_set_mem x (`cset_fvars` D0).
    + note (Γ ⊢ₛ C wf) by eauto; subst.
      apply subcapt_in_univ...
      csetsimpl.
      inversion select (_ ⊢ₛ D0 wf); subst.
      apply wf_concrete_cset.
      intros y yIn.
      rename select (allbound _ fvars0) into AllBoundC1.
      rename select (allbound _ fvars1) into AllBoundC2.
      destruct (AtomSet.F.union_1 yIn).
      * destruct (AllBoundC1 y ltac:(fsetdec)) as [C' [R' Binds]].
        exists C', R'.
        apply binds_tail...
        rewrite dom_map.
        assert (y ∈ dom Γ) by (eapply binds_In, Binds).
        eapply tail_not_in_head...
        simpl.
        fsetdec.
      * destruct (AllBoundC2 y ltac:(fsetdec)) as [C' [R' Binds]].
        binds_cases Binds...
        1: exfalso; fsetdec.
        exists (subst_cset x (cset_set fvars0 {}N univ0) C'), (subst_ct x (cset_set fvars0 {}N univ0) R').
        replace (bind_typ (subst_cset x (cset_set fvars0 {}N univ0) C' # subst_ct x (cset_set fvars0 {}N univ0) R'))
           with (subst_cb x (cset_set fvars0 {}N univ0) (bind_typ (C' # R')))
             by reflexivity.
        apply binds_head, binds_map; assumption.
    + apply subcapt_in_univ...
      inversion select (_ ⊢ₛ D0 wf); subst.
      apply wf_concrete_cset.
      intros y yIn.
      rename select (allbound _ fvars0) into AllBoundC1.
      destruct (AllBoundC1 y ltac:(fsetdec)) as [C' [R' Binds]].
      binds_cases Binds...
      1: exfalso; fsetdec.
      exists (subst_cset x C C'), (subst_ct x C R').
      replace (bind_typ (subst_cset x C C' # subst_ct x C R'))
         with (subst_cb x C (bind_typ (C' # R')))
           by reflexivity.
      apply binds_head, binds_map; assumption.
- Case "subcapt_var".
    unfold subst_cset at 1.
    destruct_set_mem x (singleton x0).
    + assert (x0 = x) by fsetdec; subst.
      assert (binds x (bind_typ (D # Q)) (Δ ++ [(x, bind_typ (D # Q))] ++ Γ)) as HA by auto.
      forwards EQ: binds_typ_unique H HA; subst; clear HA.
      inversion EQ; subst; clear EQ.
      assert (Γ ⊢ (D # Q) wf).
      { apply wf_env_tail in WfE.
        inversion WfE; subst...
      }
      assert (x ∉ dom Γ) as HA. {
        assert (ok (Δ ++ [(x, bind_typ (D # Q))] ++ Γ)) as HA by auto.
        apply ok_tail in HA.
        inversion HA...
      }
      forwards NotIn: notin_fv_wf_typ H0 HA.
      replace (C `u` cset_set ({x}A `\`A x) {}N false)
              with C by csetdec.
      apply (subcapt_transitivity D)... {
        rewrite_env (∅ ++ (map (subst_cb x C) Δ ++ Γ)).
        apply subcapt_weakening; simpl_env...
      }
      simpl in NotIn.
      replace D with (subst_cset x C D)
        by (symmetry; apply subst_cset_fresh; fsetdec).
      eapply IHHsc...
    + assert (x0 <> x) by fsetdec.
      binds_cases H.
      * specialize (IHHsc x D Q Δ Γ ltac:(trivial) ltac:(trivial)).
        forwards: wf_typ_from_binds_typ H...
        eapply subcapt_var...
        assert (x ∉ dom Γ) as HA. {
            assert (ok (Δ ++ [(x, bind_typ (D # Q))] ++ Γ)) as HA by auto.
            apply ok_tail in HA.
            inversion HA...
          }
        forwards NotIn: notin_fv_wf_typ H1 HA.
        simpl in NotIn.
        replace C1 with (subst_cset x C C1)
          by (symmetry; apply subst_cset_fresh; fsetdec).
        apply IHHsc...
      * assert (Hbnd : binds x0 (bind_typ (subst_ct x C (C1 # R))) (map (subst_cb x C) Δ ++ Γ)).
        { replace (bind_typ (subst_ct x C (C1 # R)))
             with (subst_cb x C (bind_typ (C1 # R)))
             by reflexivity.
          auto.
        }
        eapply subcapt_var...
  - Case "subcapt_set".
    assert ((map (subst_cb x C) Δ ++ Γ) ⊢ₛ
                        (subst_cset x C (cset_set xs {}N b)) wf) as ?WF. {
      eapply wf_cset_subst_cb...
      constructor.
      intros y yIn.
      enough ((Δ ++ [(x, bind_typ (D # Q))] ++ Γ) ⊢ₛ (`cset_fvar` y) wf) as HA. {
        inversion HA...
      }
      specialize (H0 y yIn); simpl in H0...
    }
    assert ((map (subst_cb x C) Δ ++ Γ) ⊢ₛ (subst_cset x C D) wf) as ?WF. {
      eapply wf_cset_subst_cb...
      inversion WfDQ...
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
        destruct D; unfold subst_cset; destruct_if; destruct Q; csetdec.
    }

    unfold AtomSet.F.For_all in H0.
    inversion H; subst.
    note (Γ ⊢ₛ C wf).

    rename fvars into cs', univ into b__c', fvars0 into ds, univ0 into b__d.
    unfold subst_cset in WF0 |- *.
    destruct_set_mem x cs'.
    + csetsimpl.
      assert (WfCset : (map (subst_cb x (cset_set ds {}N b__d)) Δ ++ Γ) ⊢ₛ cset_set (ds `u`A cs' `\`A x) {}N (b__d || b__c') wf).
      { apply wf_concrete_cset.
        intros y yIn.
        rename select (allbound _ cs') into AllBoundCS'.
        rename select (allbound _ ds) into AllBoundDS.
        destruct (AtomSet.F.union_1 yIn).
        - destruct (AllBoundDS y ltac:(assumption)) as [C' [R' Binds]].
          exists C', R'.
          apply binds_tail...
          rewrite dom_map.
          assert (y ∈ dom Γ) by (eapply binds_In, Binds).
          eapply tail_not_in_head...
          simpl.
          fsetdec.
        - destruct (AllBoundCS' y ltac:(fsetdec)) as [C' [R' Binds]].
          binds_cases Binds...
          1: exfalso; fsetdec.
          exists (subst_cset x (cset_set ds {}N b__d) C'), (subst_ct x (cset_set ds {}N b__d) R').
          replace (bind_typ (subst_cset x (cset_set ds {}N b__d) C' # subst_ct x (cset_set ds {}N b__d) R'))
             with (subst_cb x (cset_set ds {}N b__d) (bind_typ (C' # R')))
               by reflexivity.
          apply binds_head, binds_map; assumption.
      }
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
      assert (WfCset : (map (subst_cb x (cset_set ds {}N b__d)) Δ ++ Γ) ⊢ₛ cset_set cs' {}N b__c' wf).
      { apply wf_concrete_cset.
        intros y yIn.
        rename select (allbound _ cs') into AllBoundCS'.
        rename select (allbound _ ds) into AllBoundDS.
        destruct (AllBoundCS' y ltac:(fsetdec)) as [C' [R' Binds]].
        binds_cases Binds...
        1: exfalso; fsetdec.
        exists (subst_cset x (cset_set ds {}N b__d) C'), (subst_ct x (cset_set ds {}N b__d) R').
        replace (bind_typ (subst_cset x (cset_set ds {}N b__d) C' # subst_ct x (cset_set ds {}N b__d) R'))
           with (subst_cb x (cset_set ds {}N b__d) (bind_typ (C' # R')))
             by reflexivity.
        apply binds_head, binds_map; assumption.
      }
      apply subcapt_set...
      2: {
        specialize (H1 x ltac:(fsetdec) _ _ _ _ _ ltac:(reflexivity) ltac:(trivial) ltac:(trivial) ltac:(trivial) ltac:(trivial)).
        unfold subst_cset in H1.
        destruct_set_mem x {x}A; [|exfalso;fsetdec].
        destruct_set_mem x cs'; [exfalso;fsetdec|].
        unfold cset_union in H1.
        csetsimpl in H1.
        destr_bool.
        inversion H1; subst; easy.
      }
      intros y yIn.
      destruct_set_mem y (xs `\`A x).
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
        forwards H1: (>> H1' x xIn x D Q Δ Γ)...
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
        eapply wf_cset_singleton_by_mem.
        2: apply yIn.
        apply wf_cset_weaken_head.
        applys subcapt_regular HscC.
        apply ok_from_wf_env...
Qed.

Tactic Notation "subst_mem_singleton" hyp(H) :=
  match type of H with
    | _ `in`A _ => rewrite AtomSetFacts.singleton_iff in H; subst
  end.

Tactic Notation "subst_mem_singleton" "<-" hyp(H) :=
  match type of H with
    | _ `in`A _ => rewrite AtomSetFacts.singleton_iff in H; symmetry in H; subst
  end.

(* REVIEW: does not make sense anymore? *)
Lemma subcapt_through_subst_tt : forall Γ P Q Δ X C D,
  (Δ ++ [(X, bind_sub Q)] ++ Γ) ⊢ wf ->
  (Δ ++ [(X, bind_sub Q)] ++ Γ) ⊢ₛ C <: D ->
  Γ ⊢ P <: Q ->
  (map (subst_tb X P) Δ ++ Γ) ⊢ₛ C <: D.
Proof with eauto using wf_env_subst_tb, wf_cset_subst_tb, wf_typ_subst_tb with fsetdec.
  intros * WfEnv Subcapt Sub.
  assert (PureQ : pure_type Q).
  { eapply wf_env_tail in WfEnv.
    inversion WfEnv...
  }
  assert (PureP : pure_type P) by (apply (proj2 (sub_pure_type _ _ _ Sub) PureQ)).
  assert ((map (subst_tb X P) Δ ++ Γ) ⊢ wf).
  { eapply wf_env_subst_tb... }
  generalize dependent P.
  dependent induction Subcapt; intros P Sub PureP WfEnvSubst.
  - Case "subcapt_univeral".
    apply subcapt_universal.
    + apply wf_concrete_cset.
      inversion select (_ ⊢ₛ cset_set xs _ _ wf); subst.
      intros x xIn.
      rename select (allbound _ _) into AllBound.
      destruct (AllBound x xIn) as [C' [R' Binds]].
      binds_cases Binds.
      * exists C', R'.
        apply binds_tail...
      * exists C', (subst_tt X P R').
        replace (bind_typ (C' # subst_tt X P R'))
          with (subst_tb X P (bind_typ (C' # R')))
            by reflexivity.
        apply binds_head...
    + eapply wf_cset_subst_tb...
  - Case "subcapt_in".
    apply subcapt_set...
    intros y yIn; assert (y = x) by fsetdec; subst; clear yIn.
    eapply subcapt_in...
  - Case "subcapt_in_univ".
    apply subcapt_in_univ...
  - Case "subcapt_var".
    rename select (binds x _ _) into Binds.
    binds_cases Binds...
    eapply subcapt_var with (R := subst_tt X P R)...
    replace (bind_typ (C1 # subst_tt X P R))
       with (subst_tb X P (bind_typ (C1 # R)))
         by reflexivity.
    apply binds_head, binds_map...
  - Case "subcapt_set".
    apply subcapt_set...
    intros y yIn.
    eapply H1...
Qed.

(* (* ********************************************************************** *) *)
(* (** ** Narrowing and transitivity (3) *) *)

(* TODO: move to CCsub_Lemmas.v
typ_cv_free_never_universal *)

(* TODO: remove? if typing_through_subst_ve is indeed not useful
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
*)
