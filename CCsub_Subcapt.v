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

(* TODO: move to lemmas.v *)
Lemma pure_type_empty_cv : forall T,
  pure_type T ->
  typ_cv T = {}.
Proof.
  intros * Hpure.
  inversion Hpure; simpl; reflexivity.
Qed.

(* Subtyping implies subcapturing *)
Lemma sub_implies_subcapt : forall Γ S T,
  Γ ⊢ S <: T ->
  Γ ⊢ₛ (typ_cv S) <: (typ_cv T).
Proof with eauto using subcapt_reflexivity.
  intros * Hsub.
  assert (Γ ⊢ₛ (typ_cv S) wf); [apply cv_wf|]...
  assert (Γ ⊢ₛ (typ_cv T) wf); [apply cv_wf|]...
  induction Hsub; simpl in *...
  - rename select (binds X _ _) into Binds.
    assert (WfEnv : Γ ⊢ wf) by (applys sub_regular Hsub).
    assert (PureU : pure_type U) by (applys wf_typ_env_bind_sub WfEnv Binds).
    replace (typ_cv T) with {}...
    symmetry.
    apply pure_type_empty_cv.
    applys sub_pure_type Hsub.
    apply PureU.
  - rename select (pure_type T) into PureT.
    rewrite (pure_type_empty_cv _ PureT)...
Qed.

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
        rewrite_env (∅ ++ (Δ ++ [(x, bind_typ (C1 # R))]) ++ Γ).
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
        rewrite_env (∅ ++ (Δ ++ [(x, bind_typ (C0 # R))]) ++ Γ).
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
        rewrite_env (∅ ++ (Δ ++ [(x, bind_typ (C0 # R))]) ++ Γ).
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
      assert (Γ ⊢ (C1 # R) wf).
      { apply wf_env_tail in WfE.
        inversion WfE...
      }
      assert (x ∉ dom Γ) as HA. {
        assert (ok (Δ ++ [(x, bind_typ (C1 # R))] ++ Γ)) as HA by auto.
        apply ok_tail in HA.
        inversion HA...
      }
      forwards NotIn: notin_fv_wf_typ H0 HA.
      replace (C `u` cset_set ({x}A `\`A x) {}N false)
              with C by csetdec.
      apply (subcapt_transitivity C1)... {
        rewrite_env (∅ ++ (map (subst_cb x C) Δ ++ Γ)).
        apply subcapt_weakening; simpl_env...
      }
      simpl in NotIn.
      replace C1 with (subst_cset x C C1)
        by (symmetry; apply subst_cset_fresh; fsetdec).
      eapply IHHsc...
    + assert (x0 <> x) by fsetdec.
      binds_cases H.
      * specialize (IHHsc x U Δ Γ ltac:(trivial) ltac:(trivial)).
        forwards: wf_typ_from_binds_typ H...
        eapply subcapt_var...
        assert (x ∉ dom Γ) as HA. {
            assert (ok (Δ ++ [(x, bind_typ U)] ++ Γ)) as HA by auto.
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
    apply (subcapt_transitivity C1)...
    eapply subcapt_var...
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
  dependent induction HscC1; intros C3 HscC3 WF__union...
  - note (Γ ⊢ₛ C3 wf); csetsimpl.
    apply subcapt_set.
    + trivial...
    + intros y yIn.
      destruct_union_mem yIn.
      * subst_mem_singleton yIn.
        apply subcapt_in...
      * applys subcapt_transitivity HscC3...
        apply subcapt_in...
        apply wf_concrete_cset...
        intros z zIn...
    + forwards: subcapt_universal_mem HscC3...
  - note (Γ ⊢ₛ C3 wf); csetsimpl.
    apply subcapt_set.
    + trivial...
    + intros y yIn.
      applys subcapt_transitivity HscC3...
      apply subcapt_in...
      apply wf_concrete_cset...
      intros z zIn...
    + forwards: subcapt_universal_mem HscC3...
  - apply (subcapt_transitivity (C1 `u` C3))...
    assert (Γ ⊢ₛ (C1 `u` C3) wf) as WfU by auto using wf_cset_union.
    note (Γ ⊢ₛ C3 wf).
    note (Γ ⊢ₛ C1 wf).
    csetsimpl.
    apply subcapt_set...
    2: csetdec.
    intros y yIn.
    destruct_union_mem yIn.
    + subst_mem_singleton yIn.
      apply (subcapt_transitivity (cset_set fvars0 {}N univ0))...
      * eapply subcapt_var...
        eapply subcapt_reflexivity...
      * apply subcapt_set...
        2: csetdec.
        intros z zIn.
        apply subcapt_in...
        apply wf_concrete_cset...
        intros w wIn...
    + apply subcapt_in...
      apply wf_concrete_cset...
      intros z zIn...
  - note (Γ ⊢ₛ C3 wf); csetsimpl.
    apply subcapt_set...
    + intros y yIn.
      destruct_union_mem yIn...
      apply (subcapt_transitivity (cset_set fvars {}N univ))...
      eapply subcapt_in...
      apply wf_concrete_cset...
      intros z zIn...
    + forwards: subcapt_universal_mem HscC3; csetdec...
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
      destruct (AllBound x xIn) as [T Binds].
      binds_cases Binds.
      * exists T.
        apply binds_tail...
      * exists (subst_tt X P T).
        replace (bind_typ (subst_tt X P T))
          with (subst_tb X P (bind_typ T))
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
        intros z zIn...
    + csetdec.
  - csetsimpl.
    apply subcapt_set...
    intros y yIn.
    apply subcapt_in...
    apply wf_concrete_cset...
    intros z zIn...
  - csetsimpl.
    apply subcapt_set...
    2: csetdec.
    intros y yIn.
    destruct_union_mem yIn.
    2: {
      apply subcapt_in...
      apply wf_concrete_cset...
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
      intros z zIn...
    }
    apply (subcapt_transitivity (cset_set ds {}N univ1))...

    apply subcapt_set...
    + intros z zIn.
      apply subcapt_in...
      apply wf_concrete_cset...
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
    rename select (forall x0, _ ∈ {x}A -> _) into Hb.
    specialize (Hb x ltac:(fsetdec)) as [Tx Hbinds].
    assert (Tx = C1 # R). {
      eapply binds_weaken in Hbinds...
      unshelve epose proof (binds_unique _ _ _ _ H Hbinds)...
      inversion H0...
    }
    subst...
    eapply subcapt_var...
    eapply IHSc...
    enough (Hwf: (Δ ++ Γ) ⊢ (C1 # R) wf) by (inversion Hwf; auto).
    eapply wf_typ_from_binds_typ...
  - destruct D as [fvD bvD univD]; subst...
    inversion H; subst...
    apply subcapt_set...
    intros a aInXs.
    eapply H1...
    inversion Wf1; subst.
    eapply wf_concrete_cset...
    intros z zIn; assert (z = a) by (clear - zIn; fsetdec); subst...
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
