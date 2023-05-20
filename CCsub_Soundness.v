Require Import Coq.Program.Equality.
Require Import TaktikZ.
Require Import Lia.

Require Import CCsub_Subcapt.
Require Import CCsub_Subtyping.
Require Import CCsub_Typing.
Require Import CCsub_Substitution.

Set Nested Proofs Allowed.

Hint Constructors store_typing eval_typing state_typing : core.

(* ********************************************************************** *)
(** * #<a name="preservation"></a># Preservation *)

Definition no_type_bindings (Γ : env) : Prop :=
  forall X U, ~ binds X (bind_sub U) Γ.

Lemma store_typing_no_type_bindings : forall S Γ,
  S ∷ Γ ->
  no_type_bindings Γ.
Proof with eauto*.
  intros * StoreTyp.
  induction StoreTyp.
  - easy.
  - intros X U Binds.
    binds_cases Binds.
    rename select (binds _ (bind_sub _) _) into Binds.
    applys IHStoreTyp Binds.
Qed.

Ltac impossible_typing Typ :=
  clear - Typ;
  repeat match type of Typ with
  | typing ?E ?e ?T =>
    let S := fresh "S" in
    eremember T as S eqn:HeqS;
    assert (Sub : sub E S T) by (subst; eapply sub_reflexivity; eauto* );
    clear HeqS;
    dependent induction Typ;
      [ inversion Sub
      | (* cannot name IH in the dependent induction tactic, so we need to match *)
        match goal with 
        | H : sub ?E S ?T, IH : forall _ _, e = _ -> _ |- _ =>
            eapply IH; [ eauto | eapply sub_transitivity_type with (Q := T); eauto* ]; trivial
        end ]
  end.

(*
Lemma typing_var_strengthen : forall E (x y : atom) U T,
  typing ([(y, bind_typ U)] ++ E) x T ->
  x <> y ->
  exists S, typing E x S /\ sub ([(y, bind_typ U)] ++ E) S T /\ y `~in`A fv_ct S.
Proof with eauto*.
  intros * Typ Neq.
  dependent induction Typ.
  - Case "typing_var_tvar".
    exists X.
    inversion H0.
    destruct (x == y); try (contradict e; apply Neq).
    repeat split...
    apply sub_refl_tvar...
    apply wf_env_bound_implies_wf_typ with (x := x)...
  - Case "typing_var".
    exists (typ_capt (`cset_fvar` x) P).
    inversion H0.
    destruct (x == y); try (contradict e; apply Neq).
    assert (WfCP : wf_typ_in E (typ_capt C P)) by (apply wf_env_bound_implies_wf_typ with (x := x); eauto* ).
    inversion WfCP; subst.
    assert (WfxP : wf_typ_in E (typ_capt (`cset_fvar` x) P)).
    { apply wf_typ_capt...
      apply wf_cset_from_binds with (b := typ_capt C P)...
    }
    repeat split.
    + apply typing_var with (C := C)...
    + apply sub_reflexivity with (Ap := dom ([(y, bind_typ U)] ++ E)) (Am := dom ([(y, bind_typ U)] ++ E))...
      rewrite_env (empty ++ [(y, bind_typ U)] ++ E).
      apply wf_typ_in_weakening...
    + simpl.
      apply notin_union.
      * apply notin_singleton...
      * inversion H; subst.
        apply wf_pretyp_in_notin_fv_cpt with (E := E)...
  - Case "typing_sub".
    destruct (IHTyp E x y U eq_refl eq_refl Neq) as [R [Typ' [Sub' NotIn]]].
    exists R.
    repeat split.
    + apply Typ'.
    + rewrite_env (empty ++ E).
      apply sub_transitivity with (Q := S)...
    + apply NotIn.
Qed.  
*)

Lemma stores_implies_value : forall S Γ x v,
  S ∷ Γ ->
  stores S x v ->
  value v.
Proof with eauto*.
  intros * StoreTyp Stores.
  induction StoreTyp; inversion Stores; subst.
  destruct (x == x0); subst...
Qed.

Lemma stores_preserves_typing : forall S Γ x v C P,
  S ∷ Γ ->
  stores S x v ->
  Γ ⊢ x : (C # P) ->
  exists D Q, Γ ⊢ v : (exp_cv v # Q)
         /\ binds x (bind_typ (D # Q)) Γ
         /\ Γ ⊢ₛ (exp_cv v) <: D
         /\ Γ ⊢ Q <: P.
Proof with eauto*.
  intros * StoreTyp xStores.
  revert C P.
  induction StoreTyp as [|y D Q w S Γ StoreTyp IH w_value Typ NotIn]; intros C P Typ'; inversion xStores.
  assert (WfEnv' : ([(y, bind_typ (D # Q))] ++ Γ) ⊢ wf) by applys typing_regular Typ'.
  assert (WfEnv : Γ ⊢ wf) by (inversion WfEnv'; auto).
  assert (WfQ : Γ ⊢ Q wf) by (inversion WfEnv'; eauto* ).
  assert (WfQ' : ([(y, bind_typ (D # Q))] ++ Γ) ⊢ Q wf) by (rewrite_nil_concat; apply wf_typ_weakening; eauto* ).
  destruct (x == y); subst.
  - Case "x = y".
    inversion select (Some _ = Some _); subst.
    destruct (values_have_precise_captures _ _ _ _ w_value Typ) as [U [TypCVU CVUSubDQ]].
    exists D, Q. 
    inversion CVUSubDQ; subst.
    repeat split...
    + rewrite_nil_concat.
      apply typing_weakening...
      apply typing_sub with (S := exp_cv v # U)...
      apply sub_capt...
      apply subcapt_reflexivity...
    + rewrite_nil_concat.
      apply subcapt_weakening...
    + eremember (C # P) as T.
      assert (Sub : ([(y, bind_typ (D # Q))] ++ Γ) ⊢ T <: (C # P)).
      { rewrite HeqT in Typ' |- *; apply sub_reflexivity.
        - apply WfEnv'.
        - applys typing_regular Typ'.
      }
      clear HeqT.
      dependent induction Typ'.
      * rename select (binds _ _ _) into Binds.
        binds_cases Binds.
        -- simpl in Fr; exfalso; fsetdec.
        -- inversion select (bind_typ _ = bind_typ _); subst.
           inversion select (_ ⊢ (_ # Q) <: (_ # P)); subst...
      * eapply IHTyp'...
        apply sub_transitivity_type with (Q := T)...
  - Case "x <> y".
    destruct (typing_var_implies_binds_typ _ _ _ _ Typ') as [C' [R' [Binds [WfC [WfC' [WfR' PureR']]]]]].
    assert (Binds' : binds x (bind_typ (C' # R')) Γ) by (binds_cases Binds; eauto* ).
    assert (WfC'R' : Γ ⊢ (C' # R') wf).
    { destruct (wf_typ_env_bind_typ x (C' # R') Γ ltac:(inversion WfEnv'; auto) Binds') as [C'' [R'' [Eq'' WfC''R'']]].
      symmetry in Eq''; inversion Eq''; subst; clear Eq''...
    }
    destruct (IH ltac:(assumption) C' R') as [D'' [Q'' [Typ'' [Binds'' [CVsubD'' Q''subR']]]]].
    + apply typing_sub with (S := `cset_fvar` x # R').
      * eapply typing_var...
      * apply sub_capt...
        -- eapply subcapt_var...
           apply subcapt_reflexivity.
           inversion WfC'R'...
        -- apply sub_reflexivity...
        -- applys sub_pure_type...
        -- applys sub_pure_type...
    + assert (Eq : bind_typ (C' # R') = bind_typ (D'' # Q'')).
      { eapply binds_unique... }
      symmetry in Eq; inversion Eq; subst.
      exists C', R'.
      repeat split...
      * rewrite_nil_concat.
        apply typing_weakening...
      * rewrite_nil_concat.
        apply subcapt_weakening...
Qed.

Lemma eval_typing_sub : forall Γ K S1 S2 T1 T2,
  Γ ⊢ S2 <: S1 ->
  Γ ⊢ K : S1 ⇒ T1 ->
  Γ ⊢ T1 <: T2 ->
  Γ ⊢ K : S2 ⇒ T2.
Proof with eauto*.
  intros * S2SubS1 EvalTyp T1SubT2.
  revert S2 T2 S2SubS1 T1SubT2.
  induction EvalTyp; intros S2 T2 S2subC1R1 C2R2subT2.
  - Case "typing_eval_nil".
    rename select (Γ ⊢ (C1 # R1) <: (C2 # R2)) into C1R1subC2R2.
    destruct (proj1 (sub_capt_type _ _ _ C2R2subT2) ltac:(eauto)) as [D2 [Q2 Eq]]; subst.
    destruct (proj2 (sub_capt_type _ _ _ S2subC1R1) ltac:(eauto)) as [D1 [Q1 Eq]]; subst.
    apply typing_eval_nil...
    apply sub_transitivity_type with (Q := C1 # R1)...
    apply sub_transitivity_type with (Q := C2 # R2)...
  - Case "typing_eval_cons".  
    destruct (proj1 (sub_capt_type _ _ _ C2R2subT2) ltac:(eauto)) as [D2 [Q2 Eq]]; subst.
    destruct (proj2 (sub_capt_type _ _ _ S2subC1R1) ltac:(eauto)) as [D1 [Q1 Eq]]; subst.
    apply typing_eval_cons with (L := L) (C2 := C2) (R2 := R2)...
    + intros x xNotIn.
      rewrite_nil_concat.
      eapply typing_narrowing_typ...
    + apply IHEvalTyp...
      apply sub_reflexivity...
      applys eval_typing_regular EvalTyp.
Qed.

Lemma eval_typing_weakening : forall Γ Δ Θ E T U,
  (Δ ++ Γ) ⊢ E : T ⇒ U ->
  (Δ ++ Θ ++ Γ) ⊢ wf ->
  (Δ ++ Θ ++ Γ) ⊢ E : T ⇒ U.
Proof with eauto*.
  intros * EvalTyp WfEnv.
  induction EvalTyp.
  - Case "typing_eval_nil".
    apply typing_eval_nil...
    apply sub_weakening...
  - Case "typing_eval_cons".
    apply typing_eval_cons with (L := L `u`A dom (Δ ++ Θ ++ Γ)) (C2 := C2) (R2 := R2)...
    intros x xNotIn.
    rename select (forall x, x ∉ L -> _ ⊢ _ : _) into Typ.
    specialize (Typ x ltac:(fsetdec)).
    rewrite <- concat_assoc in Typ.
    apply typing_weakening with (Θ := Θ) in Typ.
    + apply Typ.
    + simpl_env.
      apply wf_env_typ...
      assert (WfEnv' : (([(x, bind_typ (C1 # R1))] ++ Δ) ++ Γ) ⊢ wf) by applys typing_regular Typ.
      inversion WfEnv'; subst.
      apply wf_typ_weakening...
Qed.

(*
Lemma typing_abs_typ_arrow_implies_sub_param : forall E U e C T1 T2,
  typing E (exp_abs U e) (typ_capt C (typ_arrow T1 T2)) ->
  sub E T1 U.
Proof with eauto*.
  intros * Typ.
  destruct (typing_regular _ _ _ Typ) as [WfE [_ WfT]].
  inversion WfT; subst.
  eremember (exp_abs U e) as abs.
  eremember (typ_capt C (typ_arrow T1 T2)) as S.
  rename WfT into WfS.
  assert (Sub : sub E S (typ_capt C (typ_arrow T1 T2))).
  { subst.
    eapply sub_reflexivity with (Ap := dom E) (Am := dom E)...
  }
  clear HeqS.
  induction Typ; inversion Heqabs; subst.
  - inversion Sub; subst...
    inversion H11...
  - eapply IHTyp...
    apply sub_transitivity with (Q := T)...
Qed.
*)

Lemma store_typing_preserves_dom : forall S Γ,
  S ∷ Γ ->
  dom S = dom Γ.
Proof with eauto*.
  intros * StoreTyp.
  induction StoreTyp...
  repeat rewrite dom_concat; simpl.
  rewrite IHStoreTyp...
Qed.

Lemma subst_cset_cv_var_commutes_with_subst_vv : forall x u v,
  subst_cset x (`cset_fvar` u) (var_cv v)
  = var_cv (subst_vv x u v).
Proof with eauto*.
  unfold subst_cset.
  destruct v; simpl;
    [ destruct (a == x); subst; destruct_set_mem x {x}A
    | destruct_set_mem x {}A
    ]; csetdec.
Qed.

Lemma subst_cset_cv_commutes_with_susbt_ve : forall x u e,
    subst_cset x (`cset_fvar` u) (exp_cv e)
  = exp_cv (subst_ve x u (`cset_fvar` u) e).
Proof with auto using subst_cset_cv_var_commutes_with_subst_vv.
  induction e; simpl...
  - rewrite subst_cset_union.
    f_equal...
  - rewrite subst_cset_union.
    f_equal...
  - unfold subst_cset.
    destruct_set_mem x {}A...
    exfalso; fsetdec.
  - rewrite subst_cset_union.
    f_equal...
    unfold subst_cset.
    destruct_set_mem x (`cset_fvars` c)...
    csetdec.
Qed.

Lemma subst_cset_empty : forall x c,
  subst_cset x c {} = {}.
Proof with eauto*.
  intros.
  unfold subst_cset.
  destruct_set_mem x {}A; [exfalso; fsetdec|].
  reflexivity.
Qed.

Lemma typing_through_subst_ve : forall Γ Δ x T C R e (u : atom),
  (Δ ++ [(x, bind_typ (C # R))] ++ Γ) ⊢ e : T ->
  Γ ⊢ u : (C # R) ->
  (map (subst_cb x (`cset_fvar` u)) Δ ++ Γ) ⊢ (subst_ve x u (`cset_fvar` u) e) : (subst_ct x (`cset_fvar` u) T).
Proof with eauto*.
  intros * Typ uTyp.
  forwards (WfEnv & _ & WfT): typing_regular Typ.
  assert (WfEnv' : Γ ⊢ wf) by (repeat apply wf_env_tail in WfEnv; assumption).
  destruct (typing_var_implies_binds_typ _ _ _ _ uTyp) as [D [Q [Binds [usubC [WfD [QsubR PureR]]]]]].
  assert (PureQ : pure_type Q) by (applys sub_pure_type QsubR; eauto).
  assert (WfU : Γ ⊢ₛ (`cset_fvar` u) wf)
    by (eapply wf_cset_from_binds; eauto).
  assert (WfEnvSubst : (map (subst_cb x (`cset_fvar` u)) Δ ++ Γ) ⊢ wf) by (eapply wf_env_subst_cb; eauto).
  assert (uNotInΔ : u ∉ dom Δ).
  { eapply tail_not_in_head...
    apply binds_In in Binds.
    simpl; fsetdec.
  }
  assert (xNotInΓ : x ∉ dom Γ) by (eapply fresh_mid_tail; eauto).
  assert (xNotInΔ : x ∉ dom Δ) by (eapply fresh_mid_head; eauto).
  assert (xNotInQ : x ∉ fv_ct Q) by (eapply wf_typ_notin_fv_ct; eauto).
  assert (xNotInR : x ∉ fv_ct R) by (eapply wf_typ_notin_fv_ct; eauto).
  dependent induction Typ; simpl.
  - Case "typing_var".
    unfold subst_cset.
    destruct (x0 == x); destruct_set_mem x {x0}A; subst; try (exfalso; fsetdec).
    + SCase "x0 = x".
      rename select (binds x _ _) into Binds'.
      clear xIn.
      binds_cases Binds'.
      * exfalso; simpl in *; fsetdec.
      * inversion select (bind_typ _ = bind_typ _); subst.
        unfold subst_cset.
        csetsimpl.
        replace ({u}A `u`A {x}A `\`A x)
           with {u}A by fsetdec.
        rewrite_nil_concat.
        eapply typing_weakening.
        2: assumption.
        apply typing_sub with (S := `cset_fvar` u # Q)...
        apply sub_capt...
        -- apply subcapt_reflexivity...
        -- rewrite <- subst_ct_fresh...
        -- rewrite <- subst_ct_fresh...
      * rename select (binds x _ _) into Binds'.
        apply binds_In in Binds'.
        contradiction.
    + SCase "x0 <> x".
      rename select (binds x0 _ _) into Binds'.
      clear xIn.
      binds_cases Binds'.
      * eapply typing_var with (C := C0)...
        apply binds_tail...
        rewrite <- subst_ct_fresh...
        eapply wf_typ_notin_fv_ct with (Γ := Γ)...
        rename select (binds x0 _ _) into Binds'.
        destruct (wf_typ_env_bind_typ _ _ _ WfEnv' Binds') as [D0 [Q0 [Eq WfD0Q0]]]; inversion Eq; subst; clear Eq.
        inversion WfD0Q0; subst...
      * eapply typing_var with (C := subst_cset x (`cset_fvar` u) C0)...
        rename select (binds x0 _ _) into Binds'.
        replace (bind_typ (subst_cset x (`cset_fvar` u) C0 # subst_ct x (`cset_fvar` u) R0))
           with (subst_cb x (`cset_fvar` u) (bind_typ (C0 # R0)))
             by reflexivity.
        apply binds_head, binds_map, Binds'.
  - Case "typing_abs".
    rewrite subst_cset_cv_commutes_with_susbt_ve.
    pick fresh y and apply typing_abs.
    + replace (subst_cset x (`cset_fvar` u) C0 # subst_ct x (`cset_fvar` u) R0)
         with (subst_ct x (`cset_fvar` u) (C0 # R0))
           by reflexivity.
      eapply wf_typ_subst_cb...
    + rename select (forall x0 : atom, x0 ∉ L -> _ ⊢ open_ve _ _ _ : open_ct _ _) into e1Typ.
      specialize (e1Typ y ltac:(clear - Fr; fsetdec)).
      assert (Neq : x <> y) by (clear - Fr; fsetdec).
      rewrite_env (map (subst_cb x (`cset_fvar` u)) ([(y, bind_typ (C0 # R0))] ++ Δ) ++ Γ).
      rewrite subst_ct_open_ct_var.
      2-3: auto.
      rewrite subst_ve_open_ve_var.
      2-3: auto.
      rename select (forall x0 : atom, x0 ∉ L -> forall (Γ0 Δ0 : env), _) into IH.
      eapply IH with (C1 := C) (R1 := R)...
      * apply wf_env_typ...
      * applys typing_regular e1Typ.
      * eapply wf_env_subst_cb...
        apply wf_env_typ...
      * eapply capt_from_wf_cset... 
  - Case "typing_app".
    assert (Iff : (if f == x then var_f u else var_f f) = var_f (if f == x then u else f))
      by (destruct_if; reflexivity).
    rewrite Iff.
    destruct (x0 == x); subst.
    + SCase "x0 = x".
      rewrite <- subst_ct_open_ct_not_fresh.
      eapply typing_app.
      * rewrite <- Iff.
        eapply IHTyp1...
        applys typing_regular Typ1.
      * fold subst_ct.
        replace (subst_cset x (`cset_fvar` u) D # subst_ct x (`cset_fvar` u) Q)
           with (subst_ct x (`cset_fvar` u) (D # Q))
             by reflexivity.
        replace (exp_var u) with (subst_ve x u (`cset_fvar` u) x).
        2: simpl; destruct_if...
        eapply IHTyp2...
        applys typing_regular Typ2.
    + SCase "x0 <> x".
      rewrite <- subst_ct_open_ct_var...
      apply typing_app with (D := subst_cset x (`cset_fvar` u) D) (Q := subst_ct x (`cset_fvar` u) Q) (C := subst_cset x (`cset_fvar` u) C0) (T := subst_ct x (`cset_fvar` u) T)...
      * replace (subst_cset x (`cset_fvar` u) C0 # ∀ ((subst_cset x (`cset_fvar` u) D # subst_ct x (`cset_fvar` u) Q)) subst_ct x (`cset_fvar` u) T)
           with (subst_ct x (`cset_fvar` u) (C0 # ∀ (D # Q) T))
             by reflexivity.
        rewrite <- Iff.
        eapply IHTyp1...
        applys typing_regular Typ1.
      * replace (subst_cset x (`cset_fvar` u) D # subst_ct x (`cset_fvar` u) Q)
           with (subst_ct x (`cset_fvar` u) (D # Q))
             by reflexivity.
        erewrite subst_ve_fresh with (x := x) (u := u) (c := `cset_fvar` u) (e := x0).
        2: simpl; fsetdec.
        eapply IHTyp2...
        applys typing_regular Typ2.
  - Case "typing_let".
    pick fresh y and apply typing_let.
    + eapply IHTyp...
      applys typing_regular Typ.
    + rewrite subst_ve_open_ve_var...
      fold subst_ct.
      replace ([(y, bind_typ (subst_cset x (`cset_fvar` u) C1 # subst_ct x (`cset_fvar` u) T1))] ++ map (subst_cb x (`cset_fvar` u)) Δ ++ Γ)
         with (map (subst_cb x (`cset_fvar` u)) ([(y, bind_typ (C1 # T1))] ++ Δ) ++ Γ)
           by reflexivity.
      rename select (forall x0 : atom, x0 ∉ L -> forall (Γ0 Δ0 : env), _) into IH.
      eapply IH...
      * apply wf_env_typ...
        applys typing_regular Typ.
      * rewrite concat_assoc.
        apply wf_typ_weaken_head...
      * eapply wf_env_subst_cb...
        eapply wf_env_typ...
        applys typing_regular Typ.
  - Case "typing_tabs".
    rewrite subst_cset_cv_commutes_with_susbt_ve.
    pick fresh Y and apply typing_tabs.
    + eapply wf_typ_subst_cb... 
    + apply subst_ct_pure_type...
    + rename select (forall X : atom, X ∉ L -> _ ⊢ open_te _ _ : open_tt _ _) into e1Typ.
      specialize (e1Typ Y ltac:(clear - Fr; fsetdec)).
      assert (Neq : x <> Y) by (clear - Fr; fsetdec).
      rewrite_env (map (subst_cb x (`cset_fvar` u)) ([(Y, bind_sub V)] ++ Δ) ++ Γ).
      rewrite subst_ve_open_te_var.
      2-3: auto.
      rewrite subst_ct_open_tt_var.
      2-3: auto.
      rename select (forall X : atom, X ∉ L -> forall (Γ0 Δ0 : env), _) into IH.
      eapply IH...
      * apply wf_env_sub...
      * applys typing_regular e1Typ.
      * eapply wf_env_subst_cb...
        eapply wf_env_sub...
  - Case "typing_tapp".
    assert (Ifx0 : (if x0 == x then var_f u else var_f x0) = (var_f (if x0 == x then u else x0)))
      by (destruct_if; reflexivity).
    rewrite Ifx0.
    rewrite subst_ct_open_tt...
    2: eapply bind_typ_notin_fv_tt with (S := C # R) (Γ := Δ ++ [(x, bind_typ (C # R))] ++ Γ)...
    apply typing_tapp with (Q := subst_ct x (`cset_fvar` u) Q) (C := subst_cset x (`cset_fvar` u) C0).
    + replace (subst_cset x (`cset_fvar` u) C # ∀ [subst_ct x (`cset_fvar` u) Q] subst_ct x (`cset_fvar` u) T)
         with (subst_ct x (`cset_fvar` u) (C # ∀ [Q] T))
           by reflexivity.
      rewrite <- Ifx0.
      eapply IHTyp...
      applys typing_regular Typ.
    + apply sub_through_subst_ct with (CU := C) (U := R)...
  - Case "typing_box".
    assert (Ifx0 : (if x0 == x then var_f u else var_f x0) = (var_f (if x0 == x then u else x0)))
      by (destruct_if; reflexivity).
    rewrite Ifx0.
    rewrite subst_cset_empty.
    eapply typing_box.
    + replace (subst_cset x (`cset_fvar` u) C0 # subst_ct x (`cset_fvar` u) R0)
         with (subst_ct x (`cset_fvar` u) (C0 # R0))
           by reflexivity.
      rewrite <- Ifx0.
      eapply IHTyp...
      applys typing_regular Typ.
    + rename select (_ ⊆ _) into Subset.
      rewrite dom_concat in Subset |- *.
      rewrite dom_map.
      simpl in Subset.
      intros y yIn.
      unfold subst_cset in yIn.
      assert (WfC0R0 : (Δ ++ [(x, bind_typ (C # R))] ++ Γ) ⊢ (C0 # R0) wf) by applys typing_regular Typ.
      assert (WfC0 : (Δ ++ [(x, bind_typ (C # R))] ++ Γ) ⊢ₛ C0 wf) by (inversion WfC0R0; assumption).
      destruct WfC0; csetsimpl.
      destruct_set_mem x fvars.
      * destruct (AtomSet.F.union_1 yIn).
        -- assert (y = u) by fsetdec; subst.
           apply binds_In in Binds.
           fsetdec.
        -- fsetdec.
      * fsetdec.
  - Case "typing_unbox".
    assert (Ifx0 : (if x0 == x then var_f u else var_f x0) = (var_f (if x0 == x then u else x0)))
      by (destruct_if; reflexivity).
    rewrite Ifx0.
    apply typing_unbox.
    + replace ({} # (□ subst_cset x (`cset_fvar` u) C0 # subst_ct x (`cset_fvar` u) R0))
         with (subst_ct x (`cset_fvar` u) ({} # (□ C0 # R0))).
      2: {
        simpl.
        f_equal...
        apply subst_cset_empty.
      }
      rewrite <- Ifx0.
      eapply IHTyp...
      applys typing_regular Typ.
    + eapply wf_cset_over_subst... 
  - Case "typing_sub".
    apply typing_sub with (S := subst_ct x (`cset_fvar` u) S).
    + eapply IHTyp...
    + apply sub_through_subst_ct with (CU := C) (U := R)...
Qed.

Lemma typing_inv_app : forall Γ (f x : atom) T,
  Γ ⊢ (f @ x) : T ->
  exists C D Q U, Γ ⊢ f : (C # (∀ (D # Q) U))
               /\ Γ ⊢ x : (D # Q)
               /\ Γ ⊢ (open_ct U (`cset_fvar` x)) <: T.
Proof with eauto*.
  intros * Typ.
  forwards (WfEnv & _ & WfT): typing_regular Typ.
  dependent induction Typ.
  - Case "typing_app".
    repeat eexists...
    apply sub_reflexivity...
  - Case "typing_sub".
    rename select (Γ ⊢ S <: T) into Sub.
    assert (WfS : Γ ⊢ S wf) by applys sub_regular Sub.
    destruct (IHTyp f x ltac:(reflexivity) WfEnv WfS) as [C [D [Q [U [fTyp [xTyp Sub']]]]]].
    repeat eexists...
    apply sub_transitivity_type with (Q := S)...
Qed.

Lemma typing_inv_tapp : forall Γ (x : atom) V T,
  Γ ⊢ (x @ [V]) : T ->
  exists C R U, Γ ⊢ x : (C # (∀ [R] U))
             /\ Γ ⊢ V <: R
             /\ Γ ⊢ (open_tt U V) <: T.
Proof with eauto*.
  intros * Typ.
  dependent induction Typ.
  - Case "typing_tapp".
    exists C, Q, T.
    repeat split...
    forwards (WfEnv & _ & WfCQT): typing_regular Typ.
    inversion WfCQT; subst.
    apply sub_reflexivity.
    1: assumption.
    inversion select (Γ ⊢ (∀ [Q] T) wf); subst.
    rename select (forall X : atom, X ∉ L -> _ ⊢ _ wf) into WfT.
    pick fresh Y and specialize WfT.
    replace (open_tt T V)
       with (subst_tt Y V (open_tt T Y))
         by (symmetry; apply subst_tt_intro; fsetdec).
         rewrite_env (map (subst_tb Y V) ∅ ++ Γ).
    eapply wf_typ_subst_tb...
    + applys sub_pure_type...
    + apply ok_cons...
  - Case "typing_sub".
    destruct (IHTyp x V eq_refl) as [C [R [U [fTyp [xTyp Sub]]]]].
    exists C, R, U.
    repeat split...
    apply sub_transitivity_type with (Q := S)...
Qed.

Lemma typing_inv_box : forall Γ x T,
  Γ ⊢ (box x) : T ->
  exists C R, Γ ⊢ x : (C # R)
           /\ `cset_fvars` C ⊆ dom Γ
           /\ Γ ⊢ ({} # □ (C # R)) <: T.
Proof with eauto*.
  intros * Typ.
  forwards (WfEnv & _ & WfT): typing_regular Typ.
  dependent induction Typ...
  - Case "typing_box".
    exists C, R.
    repeat split...
    apply sub_reflexivity...
  - Case "typing_sub".
    rename select (Γ ⊢ S <: T) into Sub.
    assert (WfS : Γ ⊢ S wf) by applys sub_regular Sub.
    destruct (IHTyp x eq_refl WfEnv WfS) as [C [R [xTyp [xSubΓ CRsubS]]]].
    exists C, R.
    repeat split...
    apply sub_transitivity_type with (Q := S)...
Qed.

Lemma typing_inv_unbox : forall Γ C x T,
  Γ ⊢ (C ⟜ x) : T ->
  exists R, Γ ⊢ x : ({} # (□ (C # R)))
         /\ Γ ⊢ (C # R) <: T.
Proof with eauto*.
  intros * Typ.
  forwards (WfEnv & _ & WfT): typing_regular Typ.
  dependent induction Typ...
  - Case "typing_unbox".
    exists R.
    repeat split...
    apply sub_reflexivity...
  - Case "typing_sub".
    rename select (Γ ⊢ S <: T) into Sub.
    assert (WfS : Γ ⊢ S wf) by applys sub_regular Sub.
    destruct (IHTyp _ _ eq_refl WfEnv WfS) as [R [xTyp CRsubS]].
    exists R.
    repeat split...
    apply sub_transitivity_type with (Q := S)...
Qed.

Lemma typing_through_open_ve_typing : forall Γ (x y : atom) U e T,
  y ∉ (fv_ct T `u`A fv_ve e `u`A fv_ce e) ->
  ([(y, bind_typ U)] ++ Γ) ⊢ (open_ve e y (`cset_fvar` y)) : T ->
  Γ ⊢ x : U ->
  Γ ⊢ (open_ve e x (`cset_fvar` x)) : T.
Proof with eauto*.
  intros * NotIn Typ xTyp.
  assert (WfEnv : ([(y, bind_typ U)] ++ Γ) ⊢ wf) by applys typing_regular Typ.
  inversion WfEnv; subst.
  destruct (typing_var_implies_binds_typ _ _ _ _ xTyp) as [D [Q [Binds [xsubC [WfD [QsubR PureR]]]]]].
  assert (Neq : x <> y).
  { enough (x ∈ dom Γ) by fsetdec.
    eapply binds_In, Binds.
  }
  rewrite_env (map (subst_cb y (`cset_fvar` x)) ∅ ++ Γ).
  replace (open_ve e x (`cset_fvar` x))
     with (subst_ve y x (`cset_fvar` x) (open_ve e y (`cset_fvar` y)))
       by (rewrite <- subst_ve_intro; auto).
  replace T
     with (subst_ct y (`cset_fvar` x) T)
       by (rewrite <- subst_ct_fresh; auto).
  eapply typing_through_subst_ve with (C := `cset_fvar` x) (R := Q).
  - eapply typing_narrowing_typ with (D := C) (Q := R)...
    apply sub_capt...
    applys sub_pure_type QsubR...
  - eapply typing_var...
Qed.

Lemma typing_through_open_ve_typing_open : forall Γ (x y : atom) U e T,
  y ∉ (fv_ct T `u`A fv_ve e `u`A fv_ce e) ->
  ([(y, bind_typ U)] ++ Γ) ⊢ (open_ve e y (`cset_fvar` y)) : (open_ct T (`cset_fvar` y)) ->
  Γ ⊢ x : U ->
  Γ ⊢ (open_ve e x (`cset_fvar` x)) : open_ct T (`cset_fvar` x).
Proof with eauto*.
  intros * NotIn Typ xTyp.
  assert (WfEnv : ([(y, bind_typ U)] ++ Γ) ⊢ wf) by applys typing_regular Typ.
  inversion WfEnv; subst.
  destruct (typing_var_implies_binds_typ _ _ _ _ xTyp) as [D [Q [Binds [xsubC [WfD [QsubR PureR]]]]]].
  assert (Neq : x <> y).
  { enough (x ∈ dom Γ) by fsetdec.
    eapply binds_In, Binds.
  }
  rewrite_env (map (subst_cb y (`cset_fvar` x)) ∅ ++ Γ).
  replace (open_ve e x (`cset_fvar` x))
     with (subst_ve y x (`cset_fvar` x) (open_ve e y (`cset_fvar` y)))
       by (rewrite <- subst_ve_intro; auto).
  replace (open_ct T (`cset_fvar` x))
     with (subst_ct y (`cset_fvar` x) (open_ct T (`cset_fvar` y)))
       by (rewrite <- subst_ct_intro; auto).
  eapply typing_through_subst_ve with (C := `cset_fvar` x) (R := Q).
  - eapply typing_narrowing_typ with (D := C) (Q := R)...
    apply sub_capt...
    applys sub_pure_type QsubR...
  - eapply typing_var...
Qed.

Lemma typing_through_open_te : forall Γ (Y : atom) e T P Q,
  Y ∉ (fv_tt T `u`A fv_ct T `u`A fv_te e `u`A fv_ce e) ->
  ([(Y, bind_sub Q)] ++ Γ) ⊢ (open_te e Y) : (open_tt T Y) ->
  Γ ⊢ P <: Q ->
  Γ ⊢ (open_te e P) : (open_tt T P).
Proof with eauto*.
  intros * NotIn Typ Sub.
  rewrite_env (map (subst_tb Y P) ∅ ++ Γ).
  replace (open_te e P)
     with (subst_te Y P (open_te e Y))
     by (symmetry; apply subst_te_intro; clear - NotIn; fsetdec).
  replace (open_tt T P)
     with (subst_tt Y P (open_tt T Y))
     by (symmetry; apply subst_tt_intro; clear - NotIn; fsetdec).
  apply typing_through_subst_te with (Q := Q)...
Qed.

Lemma preservation : forall Σ Σ' V,
  state_typing Σ V ->
  Σ --> Σ' ->
  state_typing Σ' V.
Proof with eauto*.
  intros * [S Γ E e C1 R1 C2 R2 StoreTyp EvalTyp Typ] Red.
  forwards (WfEnv & WfC1R1 & WfC2R2): eval_typing_regular EvalTyp.
  dependent induction Red.
  - Case "red_lift".
    inversion EvalTyp; subst.
    rename select (forall x, x ∉ L -> _ ⊢ _ : _) into Typ'.
    eapply typing_state with (Γ := [(x, bind_typ (C1 # R1))] ++ Γ).
    + apply typing_store_cons...
      rewrite <- store_typing_preserves_dom with (S := S)...
    + rewrite_nil_concat.
      apply eval_typing_weakening...
      apply wf_env_typ...
      rewrite <- store_typing_preserves_dom with (S := S)...
    + pick fresh y and specialize Typ'.
      assert (x ∉ dom Γ) by (rewrite <- store_typing_preserves_dom with (S := S); assumption).
      assert (WfEnv' : ([(x, bind_typ (C1 # R1))] ++ Γ) ⊢ wf) by (apply wf_env_typ; eauto* ).
      eapply typing_through_open_ve_typing with (y := y) (U := C1 # R1).
      * simpl; clear - Fr; fsetdec.
      * apply typing_weakening.
        1: assumption.
        repeat apply wf_env_typ...
        apply wf_typ_weaken_head...
      * apply typing_sub with (S := `cset_fvar` x # R1).
        1: apply typing_var with (C := C1)...
        apply sub_capt.
        -- eapply subcapt_var...
           apply subcapt_reflexivity.
           apply wf_cset_weaken_head...
        -- apply sub_reflexivity...
           apply wf_typ_weaken_head...
        -- inversion WfC1R1; subst...
        -- inversion WfC1R1; subst...
  - Case "red_let_var".
    inversion EvalTyp; subst.
    rename select (forall x, x ∉ L -> _ ⊢ _ : _) into Typ'.
    eapply typing_state with (Γ := Γ)...
    pick fresh y and specialize Typ'.
    eapply typing_through_open_ve_typing with (y := y)...
  - Case "red_let_val".
    destruct (typing_inv_let _ _ _ _ Typ) as [D [Q [vTyp [L kTyp]]]].
    assert (x ∉ dom Γ) by (rewrite <- store_typing_preserves_dom with (S := S); assumption).
    assert (WfDQ : Γ ⊢ (D # Q) wf) by applys typing_regular vTyp.
    assert (WfEnv' : ([(x, bind_typ (D # Q))] ++ Γ) ⊢ wf) by (apply wf_env_typ; eauto* ).
    eapply typing_state with (Γ := [(x, bind_typ (D # Q))] ++ Γ).
    + apply typing_store_cons...
    + rewrite_nil_concat.
      apply eval_typing_weakening...
    + pick fresh y and specialize kTyp.
      eapply typing_through_open_ve_typing with (y := y) (U := D # Q).
      * clear - Fr; simpl; fsetdec.
      * apply typing_weakening.
        1: assumption.
        eapply wf_env_typ...
        apply wf_typ_weaken_head...
      * apply typing_sub with (S := `cset_fvar` x # Q).
        1: apply typing_var with (C := D)...
        apply sub_capt.
        -- eapply subcapt_var...
           apply subcapt_reflexivity.
           apply wf_cset_weaken_head...
        -- apply sub_reflexivity...
           apply wf_typ_weaken_head...
        -- inversion WfDQ; subst...
        -- inversion WfDQ; subst...
  - Case "red_let_exp".
    destruct (typing_inv_let _ _ _ _ Typ) as [D [Q [vTyp [L kTyp]]]].
    assert (WfDQ : Γ ⊢ (D # Q) wf) by applys typing_regular vTyp.
    eapply typing_state with (Γ := Γ)...
  - Case "red_app".
    destruct (typing_inv_app _ _ _ _ Typ) as [C [D [Q [T [fTyp [xTyp T2SubT]]]]]].
    rename select (stores S f _) into fStores.
    destruct (stores_preserves_typing _ _ _ _ _ _ StoreTyp fStores fTyp) as [D' [Q' [absTyp [fBinds [e0subD QsubP]]]]].
    simpl in absTyp, e0subD.
    destruct (typing_inv_abs _ _ _ _ absTyp (D # Q) T (exp_cv e0)) as [T1subU0 [S2 [L Ret]]].
    1: {
      assert (PureQ' : pure_type Q').
      { enough (WfD'Q' : Γ ⊢ (D' # Q') wf) by (inversion WfD'Q'; auto).
        eapply wf_typ_from_binds_typ...
      }
      apply sub_capt...
      - apply subcapt_reflexivity...
      - applys sub_pure_type QsubP...
    }
    pick fresh z and specialize Ret.
    destruct Ret as [e0Typ [WfT2 S2SubT2]].
    eapply typing_state with (Γ := Γ)...
    apply typing_sub with (S := open_ct S2 (`cset_fvar` x)).
    + eapply typing_through_open_ve_typing_open with (y := z) (U := D # Q).
      * clear - Fr.
        repeat (destruct (AtomSetNotin.elim_notin_union Fr) as [? Fr']; clear Fr; rename Fr' into Fr).
        enough (z ∉ fv_ct (open_ct S2 (`cset_fvar` x))) by fsetdec.
        apply notin_open_ct_rec_fv_ct.
        fsetdec.
      * rewrite_nil_concat.
        destruct (proj1 (sub_capt_type _ _ _ T1subU0) ltac:(eauto)) as [D'' [Q'' Eq]]; subst.
        apply typing_narrowing_typ with (D := D'') (Q := Q'')...
      * assumption.
    + apply sub_transitivity_type with (Q := open_ct T (`cset_fvar` x))...
      rewrite_env (map (subst_cb z (`cset_fvar` x)) ∅ ++ Γ).
      replace (open_ct S2 (`cset_fvar` x))
         with (subst_ct z (`cset_fvar` x) (open_ct S2 (`cset_fvar` z)))
           by (symmetry; apply subst_ct_intro; clear - Fr; fsetdec).
      replace (open_ct T (`cset_fvar` x))
         with (subst_ct z (`cset_fvar` x) (open_ct T (`cset_fvar` z)))
           by (rewrite <- subst_ct_intro; auto).
      eapply sub_through_subst_ct...
      destruct (typing_var_implies_binds_typ _ _ _ _ xTyp) as [D'' [Q'' [Binds [xsubD _]]]].
      apply xsubD.
  - Case "red_tapp".
    destruct (typing_inv_tapp _ _ _ _ Typ) as [C [R' [U' [xTyp [VsubQ VsubT]]]]].
    destruct (stores_preserves_typing _ _ _ _ _ _ StoreTyp H xTyp) as [D [Q [tabsTyp [xBinds [e0subD QsubP]]]]].
    simpl in tabsTyp, e0subD.
    assert (PureQ : pure_type Q).
    { enough (WfDQ : Γ ⊢ (D # Q) wf) by (inversion WfDQ; assumption).
      eapply wf_typ_from_binds_typ...
    }
    assert (e0Qsube0subU' : Γ ⊢ (exp_cv e0 # Q) <: (exp_cv e0 # ∀ [R'] U')).
    { apply sub_capt...
      - apply subcapt_reflexivity...
      - applys sub_pure_type QsubP...
    }
    destruct (typing_inv_tabs _ _ _ _ tabsTyp R' U' (exp_cv e0) e0Qsube0subU') as [T1SubU0 [S2 [L Ret]]].
    pick fresh Z and specialize Ret.
    destruct Ret as [WfS2 S2subT2].
    eapply typing_state with (Γ := Γ)...
    apply typing_sub with (S := open_tt U' R)...
    eapply typing_through_open_te with (Y := Z)...
  - Case "red_open".
    destruct (typing_inv_unbox _ _ _ _ Typ) as [R [xTyp CRsubC1R1]].
    rename select (stores S x _) into xStores.
    destruct (stores_preserves_typing _ _ _ _ _ _ StoreTyp xStores xTyp) as [D' [Q' [boxTyp [xBinds [ysubD QsubP]]]]].
    destruct (typing_inv_box _ _ _ boxTyp) as [D [Q [yTyp [CsubΓ BoxCRsubT]]]].
    simpl in boxTyp, ysubD, BoxCRsubT.
    eapply typing_state with (Γ := Γ)...
    apply typing_sub with (S := D # Q)...
    inversion BoxCRsubT; subst.
    assert (Γ ⊢ (□ D # Q) <: (□ C # R)).
    { apply sub_transitivity_type with (Q := Q')... }
    inversion select (Γ ⊢ (□ _) <: (□ _)); subst.
    apply sub_transitivity_type with (Q := C # R)...
Qed.

Lemma binds_implies_store : forall S Γ x T,
  S ∷ Γ ->
  binds x (bind_typ T) Γ ->
  exists v, stores S x v.
Proof with eauto*.
  intros * StoreTyp Binds.
  induction StoreTyp; binds_cases Binds.
  - Case "x <> x0".
    rename select (binds x _ _) into Binds.
    destruct (IHStoreTyp Binds) as [w Stores].
    exists w.
    apply binds_tail...
  - SCase "x = x0".
    exists v.
    apply binds_head...
Qed.

(* ********************************************************************** *)
(** ** Canonical forms (14) *)

Lemma canonical_form_abs : forall Γ v C U1 U2,
  no_type_bindings Γ ->
  value v ->
  Γ ⊢ v : (C # (∀ (U1) U2)) ->
  exists S1 e, v = λ (S1) e
             /\ Γ ⊢ U1 <: S1.
Proof with eauto*.
  intros * NTB Val Typ.
  remember (∀ (U1) U2).
  revert U1 U2 Heqt.
  assert (WfEnv : Γ ⊢ wf) by applys typing_regular Typ.
  dependent induction Typ; intros U1 U2 Eq; subst; try solve [ inversion Val | inversion Eq ].
  - Case "typing_abs".
    inversion Eq; subst.
    exists (C0 # R), e1.
    repeat split...
    eapply sub_reflexivity...
  - Case "typing_sub".
    destruct (proj2 (sub_capt_type _ _ _ H) ltac:(eauto)) as [D [Q Eq]]; subst.
    inversion select (_ ⊢ _ <: _); subst.
    inversion select (_ ⊢ _ <: (∀ (_) _)); subst.
    + rename select (binds X (bind_sub U) Γ) into Binds.
      contradict Binds; apply (NTB X U).
    + destruct (IHTyp D NTB Val (∀ (C1 # R1) T1) eq_refl WfEnv (C1 # R1) T1 eq_refl) as [S' [e' [Eq Sub]]].
      exists S', e'.
      repeat split...
      apply sub_transitivity_type with (Q := C1 # R1)...
Qed.

Lemma canonical_form_tabs : forall Γ v C U1 U2,
  no_type_bindings Γ ->
  value v ->
  Γ ⊢ v : (C # ∀ [U1] U2) ->
  exists S1 e, v = Λ [S1] e
            /\ Γ ⊢ U1 <: S1.
Proof with eauto*.
  intros * NTB Val Typ.
  remember (∀ [U1] U2).
  revert U1 U2 Heqt.
  assert (WfEnv : Γ ⊢ wf) by applys typing_regular Typ.
  dependent induction Typ; intros U1 U2 Eq; subst; try solve [ inversion Val | inversion Eq ].
  - Case "typing_tabs".
    inversion Eq; subst.
    exists U1, e1.
    repeat split...
    eapply sub_reflexivity...
  - Case "typing_sub".
    destruct (proj2 (sub_capt_type _ _ _ H) ltac:(eauto)) as [D [Q Eq]]; subst.
    inversion select (_ ⊢ _ <: _); subst.
    inversion select (_ ⊢ _ <: (∀ [_] _)); subst.
    + rename select (binds X (bind_sub U) Γ) into Binds.
      contradict Binds; apply (NTB X U).
    + destruct (IHTyp D NTB Val (∀ [R1] T1) eq_refl WfEnv R1 T1 eq_refl) as [S' [e' [Eq Sub]]].
      exists S', e'.
      repeat split...
      apply sub_transitivity_type with (Q := R1)...
Qed.

Lemma canonical_form_box : forall Γ v D C R,
  no_type_bindings Γ ->
  value v ->
  Γ ⊢ v : (D # (□ C # R)) ->
  exists x, v = box x.
Proof with eauto*.
  intros * NTB Val Typ.
  remember (D # (□ C # R)).
  forwards (WfEnv & _ & Wft): typing_regular Typ.
  assert (Sub : Γ ⊢ t <: (D # (□ C # R))).
  { rewrite <- Heqt.
    apply sub_reflexivity...
  }
  clear Heqt.
  revert R Sub.
  dependent induction Typ; intros R' Sub; subst; try solve [ inversion Val | inversion Sub; inversion select (Γ ⊢ _ <: (□ _)) ].
  - Case "typing_box".
    exists x.
    repeat split...
  - Case "typing_sub".
    assert (Γ ⊢ S <: (D # (□ C # R'))).
    { apply sub_transitivity_type with (Q := T)... }
    destruct (proj2 (sub_capt_type _ _ _ H0) ltac:(eauto)) as [D' [Q' Eq]]; subst.
    inversion select (Γ ⊢ (D' # Q') <: (D # (□ C # R'))); subst.
    inversion select (Γ ⊢ Q' <: (□ C # R')); subst.
    + rename select (binds X (bind_sub U) Γ) into Binds.
      contradict Binds; apply (NTB X U).
    + assert (WfDBT1 : Γ ⊢ (D' # (□ T1)) wf) by applys sub_regular H0.
      destruct (IHTyp NTB Val WfEnv WfDBT1 R') as [e' Sub']...
Qed.

Lemma progress : forall Σ V, 
  state_typing Σ V ->
  state_final Σ \/ exists Σ', Σ --> Σ'.
Proof with eauto*.
  intros * [S Γ E e C1 R1 C2 R2 StoreTyp EvalTyp Typ].
  assert (NTB : no_type_bindings Γ) by applys store_typing_no_type_bindings StoreTyp.
  eremember (C1 # R1) as T.
  forwards (WfEnv & _ & WfT): typing_regular Typ.
  assert (Γ ⊢ T <: (C1 # R1)).
  { rewrite <- HeqT; apply sub_reflexivity... }
  clear HeqT.
  generalize dependent R1.
  generalize dependent C1.
  dependent induction Typ; intros C' R' Sub.
  - Case "typing_var".
    inversion EvalTyp; subst.
    + left; apply final_state, answer_var.
    + right.
      exists ⟨ S | E0 | open_ve k x (`cset_fvar` x) ⟩.
      destruct (binds_implies_store _ _ _ _ StoreTyp H0) as [v Stores].
      eapply red_let_var...
  - Case "typing_abs".
    assert (Val : value (exp_abs (C # R) e1)).
    { apply value_abs.
      apply expr_abs with (L := L).
      * eapply type_from_wf_typ, H.
      * intros x NotIn.
        rename select (forall x : atom, x ∉ L -> _ ⊢ _ : _) into Typ.
        specialize (Typ x NotIn).
        applys typing_regular Typ.
    }
    inversion EvalTyp; subst.
    + left; apply final_state, answer_val, Val.
    + right.
      pick fresh z for (dom S).
      exists ⟨ [(z, store (λ (C # R) e1))] ++ S | E0 | open_ve k z (`cset_fvar` z) ⟩.
      apply red_lift, Fr.
      apply Val.
  - Case "typing_app".
    right.
    destruct (typing_var_implies_binds_typ _ _ _ _ Typ1) as [Cf [Rf [fBinds [fsubC [WfCf [RfsubDQT PureDQT]]]]]].
    destruct (typing_var_implies_binds_typ _ _ _ _ Typ2) as [Cx [Rx [xBinds [xsubD [WfCx [RxsubQ PureQ]]]]]].
    destruct (binds_implies_store _ _ _ _ StoreTyp fBinds) as [abs absStores].
    destruct (binds_implies_store _ _ _ _ StoreTyp xBinds) as [arg argStores].
    destruct (stores_preserves_typing _ _ _ _ _ _ StoreTyp absStores Typ1) as [Df [Qf [absTyp [fBinds' [absSubCf QfsubDQT]]]]].
    destruct (stores_preserves_typing _ _ _ _ _ _ StoreTyp argStores Typ2) as [Dx [Qx [argTyp [xBinds' [argSubCx QxsubQ]]]]].
    apply typing_sub with (T := exp_cv abs # (∀ ((D # Q)) T)) in absTyp.
    2: {
      apply sub_capt...
      - apply subcapt_reflexivity...
      - enough (WfDfQf : Γ ⊢ (Df # Qf) wf) by (inversion WfDfQf; assumption).
        eapply wf_typ_from_binds_typ...
    }
    assert (absValue : value abs) by (eapply stores_implies_value; eauto).
    destruct (canonical_form_abs _ _ _ _ _ NTB absValue absTyp) as [S1 [e [Eq DQsubS1]]].
    rewrite Eq in *.
    assert (absValue' : value (λ (S1) e)).
    { inversion absValue; subst... }
    exists ⟨ S | E | open_ve e x (`cset_fvar` x) ⟩.
    eapply red_app...
  - Case "typing_let".
    right.
    pick fresh z for (dom S).
    assert (k_scope : scope k).
    { econstructor.
      intros x NotIn.
      rename select (forall x : atom, x ∉ L -> _ ⊢ _ : _) into Typ'.
      specialize (Typ' x NotIn).
      applys typing_regular Typ'.
    }
    exists ⟨ S | k :: E | e ⟩.
    apply red_let_exp, k_scope.
  - Case "typing_tabs".
    assert (Val : value (exp_tabs V0 e1)).
    { apply value_tabs.
      apply expr_tabs with (L := L)...
      intros x NotIn.
      rename select (forall X : atom, X ∉ L -> _ ⊢ _ : _) into Typ.
      specialize (Typ x NotIn).
      applys typing_regular Typ.
    }
    inversion EvalTyp; subst.
    + left; apply final_state, answer_val, Val.
    + right.
      pick fresh z for (dom S).
      exists ⟨ [(z, store (Λ [V0] e1))] ++ S | E0 | open_ve k z (`cset_fvar` z) ⟩.
      apply red_lift, Fr.
      apply Val.
  - Case "typing_tapp".
    right.
    destruct (typing_var_implies_binds_typ _ _ _ _ Typ) as [Cx [Rx [xBinds [xsubC [WfCx [RxsubQT PureQT]]]]]].
    destruct (binds_implies_store _ _ _ _ StoreTyp xBinds) as [tabs tabsStores].
    destruct (stores_preserves_typing _ _ _ _ _ _ StoreTyp tabsStores Typ) as [Dx [Qx [tabsTyp [fBinds' [tabsSubCx QfsubQT]]]]].
    apply typing_sub with (T := exp_cv tabs # (∀ [Q] T)) in tabsTyp.
    2: {
      apply sub_capt...
      - apply subcapt_reflexivity...
      - applys sub_pure_type QfsubQT...
    }
    assert (tabsValue : value tabs) by (eapply stores_implies_value; eauto).
    destruct (canonical_form_tabs _ _ _ _ _ NTB tabsValue tabsTyp) as [S1 [e [Eq DQsubS1]]].
    rewrite Eq in *.
    assert (tabsValue' : value (Λ [S1] e)).
    { inversion tabsValue; subst... }
    exists ⟨ S | E | open_te e P ⟩.
    eapply red_tapp...
    assert (PureQ : pure_type Q) by (inversion PureQT; assumption).
    applys sub_pure_type H...
  - Case "typing_box".
    assert (Val : value (box x)).
    { apply value_box... }
    inversion EvalTyp; subst.
    + left; apply final_state, answer_val, Val.
    + right.
      pick fresh z for (dom S).
      exists ⟨ [(z, store (box x))] ++ S | E0 | open_ve k z (`cset_fvar` z) ⟩.
      apply red_lift, Fr.
      apply Val.
  - Case "typing_unbox".
    right.
    destruct (typing_var_implies_binds_typ _ _ _ _ Typ) as [Cx [Rx [xBinds [xsubC [WfCx [RxsubQT PureQT]]]]]].
    destruct (binds_implies_store _ _ _ _ StoreTyp xBinds) as [box' boxStores].
    destruct (stores_preserves_typing _ _ _ _ _ _ StoreTyp boxStores Typ) as [Dx [Qx [boxTyp [xBinds' [boxSubCx QxsubQT]]]]].
    apply typing_sub with (T := exp_cv box' # (□ C # R)) in boxTyp.
    2: {
      apply sub_capt...
      - apply subcapt_reflexivity...
      - applys sub_pure_type QxsubQT...
    }
    assert (boxValue : value box') by (eapply stores_implies_value; eauto).
    destruct (canonical_form_box _ _ _ _ _ NTB boxValue boxTyp) as [y Eq].
    rewrite Eq in *.
    assert (boxValue' : value (box y)).
    { inversion boxValue; subst... }
    exists ⟨ S | E | y ⟩.
    eapply red_open...
  - Case "typing_sub".
    eapply IHTyp...
    + eapply eval_typing_sub with (S1 := T) (T1 := C2 # R2)...
      eapply sub_reflexivity...
      applys eval_typing_regular EvalTyp.
    + apply sub_transitivity_type with (Q := T)...
Qed.
