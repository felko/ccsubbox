Require Import Coq.Program.Equality.
Require Import TaktikZ.
Require Import Lia.

Require Import CCsub_Subcapt.
Require Import CCsub_Subtyping.
Require Import CCsub_Typing.
Require Import CCsub_Substitution.

Set Nested Proofs Allowed.

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

Lemma no_type_bindings_cons : forall E x T,
  no_type_bindings E ->
  no_type_bindings ([(x, bind_typ T)] ++ E).
Proof with eauto*.
  intros * NTB.
  intros y U.
  intros Binds.
  binds_cases Binds.
  apply (NTB y U), H.
Qed.

Lemma no_type_bindings_strengthening : forall F E,
  ok (F ++ E) ->
  no_type_bindings (F ++ E) ->
  no_type_bindings E.
Proof with eauto*.
  intros * Ok NTB.
  intros X U Binds.
  eapply binds_weaken_at_head in Binds...
  apply (NTB X U Binds).
Qed.

Lemma store_typing_no_type_bindings : forall S E,
  store_typing S E ->
  no_type_bindings E.
Proof with eauto*.
  intros * StoreTyp.
  induction StoreTyp.
  - easy.
  - intros X U Binds.
    binds_cases Binds.
    applys IHStoreTyp H1.
Qed.

Lemma wf_env_bound_implies_wf_typ : forall E x T,
  wf_env E ->
  bound x T E ->
  wf_typ_in E T.
Proof with eauto*.
  intros * WfEnv Bound.
  induction WfEnv.
  - Case "wf_env_empty".
    destruct Bound; inversion H.
  - Case "wf_env_sub".
    destruct Bound.
    + inversion H1; subst.
      destruct (x == X)...
      rewrite_env (empty ++ [(X, bind_sub T0)] ++ E).
      apply wf_typ_in_weakening...
      apply ok_cons...
    + inversion H1; subst.
      destruct (x == X).
      * inversion H3; subst; clear H3.
        rewrite_env (empty ++ [(X, bind_sub T)] ++ E).
        apply wf_typ_in_weakening...
        apply ok_cons...
      * rewrite_env (empty ++ [(X, bind_sub T0)] ++ E).
        apply wf_typ_in_weakening...
        apply ok_cons... 
  - Case "wf_env_typ".
    destruct Bound.
    + inversion H1; subst.
      destruct (x == x0); subst.
      * inversion H3; subst; clear H3.
        rewrite_env (empty ++ [(x0, bind_typ T)] ++ E).
        apply wf_typ_weakening with (Ap := dom E) (Am := dom E).
        -- apply H.
        -- apply ok_cons...
        -- repeat rewrite dom_concat.
           fsetdec.
        -- repeat rewrite dom_concat.
           fsetdec.
      * rewrite_env (empty ++ [(x0, bind_typ T0)] ++ E).
        apply wf_typ_in_weakening...
        apply ok_cons...
    + inversion H1; subst.
      destruct (x == x0); subst.
      * inversion H3; subst; clear H3.
      * rewrite_env (empty ++ [(x0, bind_typ T0)] ++ E).
        apply wf_typ_in_weakening...
        apply ok_cons... 
Qed.

Lemma sub_capt_inversion : forall E C P T,
  sub E (typ_capt C P) T ->
  exists D Q, T = typ_capt D Q
           /\ subcapt E C D
           /\ sub_pre E P Q.
Proof with eauto*.
  intros * Sub; inversion Sub...
Qed.

Lemma typing_var_inversion' : forall E (x : atom) T,
  no_type_bindings E ->
  typing E x T ->
  exists C P D Q, T = typ_capt D Q
              /\ sub_pre E P Q
              /\ subcapt E (`cset_fvar` x) D
              /\ binds x (bind_typ (typ_capt C P)) E.
Proof with eauto*.
  intros * NTB Typ.
  dependent induction Typ...
  - exfalso.
    assert (WfX : wf_typ_in E X) by (apply wf_env_bound_implies_wf_typ with (x := x); auto).
    inversion WfX; subst.
    contradict H2.
    apply NTB.
  - exists C, P, (`cset_fvar` x), P.
    repeat split...
    apply sub_pre_reflexivity with (Ap := dom E) (Am := dom E)...
    enough (WfCP : wf_typ_in E (typ_capt C P)) by (inversion WfCP; auto).
    apply wf_env_bound_implies_wf_typ with (x := x)...
    apply subcapt_reflexivity with (A := dom E)...
    apply wf_cset_from_binds with (b := typ_capt C P)...
  - destruct (IHTyp x NTB) as [C [P [D [Q [Eq [PSubQ [xSubD Binds]]]]]]]...
    subst.
    destructs sub_capt_inversion H as [C' [P' [Eq [DSubC' QSubP']]]].
    subst.
    exists C, P, C', P'.
    repeat split...
    + apply sub_pre_transitivity with (Q := Q)...
      eapply pretype_from_wf_pretyp with (E := E) (Ap := dom E) (Am := dom E).
      enough (WfDQ : wf_typ_in E (typ_capt D Q)) by (inversion WfDQ; auto).
      applys typing_regular Typ.
    + apply subcapt_transitivity with (C2 := D)...
Qed.

Ltac impossible_typing Typ :=
  clear - Typ;
  repeat match type of Typ with
  | typing ?E ?e ?T =>
    let S := fresh "S" in
    eremember T as S eqn:HeqS;
    assert (Sub : sub E S T) by (subst; eapply sub_reflexivity; eauto*);
    clear HeqS;
    dependent induction Typ;
      [ inversion Sub
      | (* cannot name IH in the dependent induction tactic, so we need to match *)
        match goal with 
        | H : sub ?E S ?T, IH : forall _ _, e = _ -> _ |- _ =>
            eapply IH; [ eauto | eapply sub_transitivity with (Q := T); eauto* ]; trivial
        end ]
  end.

Lemma sub_left_capt_inversion : forall E T C P,
  no_type_bindings E ->
  sub E T (typ_capt C P) ->
  exists D Q, T = typ_capt D Q.
Proof with eauto*.
  intros * NTB Sub.
  dependent induction Sub...
  contradict H.
  apply NTB.
Qed.

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

Lemma stores_preserves_typing : forall S E x v v_value C P,
  store_typing S E ->
  stores S x v v_value ->
  typing E x (typ_capt C P) ->
  exists D Q, typing E v (typ_capt (free_for_cv v) Q)
         /\ binds x (bind_typ (typ_capt D Q)) E
         /\ subcapt E (free_for_cv v) D
         /\ sub_pre E Q P.
Proof with eauto*.
  intros * StoreTyp xStores.
  revert C P.
  induction StoreTyp; intros C0 P0 Typ; inversion xStores.
  destruct (x == x0); inversion H2; subst.
  - Case "x = x0".
    destruct (values_have_precise_captures _ _ _ v_value H) as [Q [TypQ QSubT]].
    assert (WfEnv : wf_env ([(x0, bind_typ T)] ++ E)) by applys typing_regular Typ.
    assert (NTB : no_type_bindings E) by applys store_typing_no_type_bindings StoreTyp.
    assert (WfT : wf_typ_in E T) by (inversion WfEnv; subst; auto).
    destructs inversion_toplevel_type NTB WfT as [D [R Eq]].
    exists D, R.
    repeat split.
    + rewrite_env (empty ++ [(x0, bind_typ T)] ++ E).
      apply typing_weakening...
      apply typing_sub with (S := typ_capt (free_for_cv v) Q)...
      rewrite Eq in QSubT.
      inversion QSubT; subst.
      apply sub_capt...
      apply subcapt_reflexivity with (A := dom E)...
      fsetdec.
    + rewrite Eq. apply binds_head... 
    + apply subcapt_transitivity with (C2 := cv T)...
      * apply capture_prediction...
        rewrite_env (empty ++ [(x0, bind_typ T)] ++ E).
        apply typing_weakening...
      * rewrite Eq in WfEnv |- *.
        rewrite_env (empty ++ [(x0, bind_typ (typ_capt D R))] ++ E).
        apply subcapt_weakening...
        apply subcapt_reflexivity with (A := dom E)...
        inversion WfEnv; subst.
        inversion H6; subst...
        fsetdec.
    + destruct (sub_capt_inversion _ _ _ _ QSubT) as [D' [R' [Eq' [CSubD QSubR]]]]; subst.
      symmetry in Eq'; inversion Eq'; subst; clear Eq'.
      apply sub_pre_transitivity with (Q := R).
      * eapply pretype_from_wf_pretyp.
        applys sub_pre_regular QSubR.
      * rewrite_env (empty ++ [(x0, bind_typ (typ_capt D R))] ++ E).
        apply sub_pre_weakening...
        apply sub_pre_reflexivity with (Ap := dom E) (Am := dom E)...
        all: fsetdec.
      * clear  - Typ WfEnv NTB.
        dependent induction Typ.
        -- inversion H0; subst.
           destruct (x0 == x0); try (contradict n; reflexivity); clear e.
           inversion H2; subst; clear H2.
           rewrite_env (empty ++ [(x0, bind_typ (typ_capt C P0))] ++ E).
           apply sub_pre_weakening...
           apply sub_pre_reflexivity with (Ap := dom E) (Am := dom E)...
           all: fsetdec.
        -- destruct (sub_left_capt_inversion _ _ _ _ (no_type_bindings_cons E x0 (typ_capt D R) NTB) H) as [C' [P' Eq]].
           apply sub_pre_transitivity with (Q := P')...
           ++ clear - H Eq; subst.
              eapply pretype_from_wf_pretyp.
              enough (WfC'P' : wf_typ_in ([(x0, bind_typ (typ_capt D R))] ++ E) (typ_capt C' P')) by (inversion WfC'P'; eauto).
              applys sub_regular H.
           ++ clear - H Eq; subst.
              inversion H; subst...
  - Case "x <> x0".
    destructs typing_var_strengthen Typ n as [R [Typ' [Sub' NotIn]]].
    assert (NTB : no_type_bindings ([(x0, bind_typ T)] ++ E)) by
      apply no_type_bindings_cons, (store_typing_no_type_bindings _ _ StoreTyp).
    destructs sub_left_capt_inversion NTB Sub' as [D [Q Eq]]; subst.
    destruct (IHStoreTyp H2 D Q Typ') as [C' [P' [Typ'' [Binds [vSubD QSubP]]]]]. 
    exists C', P'.
    rewrite_env (empty ++ [(x0, bind_typ T)] ++ E).
    repeat split.
    + apply typing_weakening...
    + apply binds_tail... 
    + apply subcapt_weakening...
    + inversion Sub'; subst.
      apply sub_pre_transitivity with (Q := Q).
      * eapply pretype_from_wf_pretyp.
        applys sub_pre_regular QSubP.
      * apply sub_pre_weakening...
      * apply H9.
Qed.

Lemma eval_typing_sub : forall E K S1 S2 T1 T2,
  no_type_bindings E ->
  sub E S2 S1 ->
  eval_typing E K S1 T1 ->
  sub E T1 T2 ->
  eval_typing E K S2 T2.
Proof with eauto*.
  intros * NTB S2SubS1 EvalTyp T1SubT2.
  revert S2 T2 S2SubS1 T1SubT2.
  induction EvalTyp; intros S2 T2 S2SubT USubT2.
  - Case "typing_eval_nil".
    apply typing_eval_nil...
    apply sub_transitivity with (Q := T)... 
    apply sub_transitivity with (Q := U)...
  - Case "typing_eval_cons".
    eapply typing_eval_cons with (U := U) (L := L)...
    + intros x NotIn.
      rewrite_env (empty ++ [(x, bind_typ S2)] ++ E).
      eapply typing_narrowing_typ_aux with (Q := T)...
      destruct (sub_regular _ _ _ S2SubT) as [_ [WfS2 WfT]].
      inversion WfS2; subst.
      contradict H0; apply NTB.
      inversion WfT; subst.
      contradict H2; apply NTB.
      constructor.
    + apply IHEvalTyp...
      apply sub_reflexivity with (Ap := dom E) (Am := dom E)...
      applys eval_typing_regular EvalTyp.
Qed.

Lemma eval_typing_weakening : forall E F G E' T U,
  eval_typing (G ++ E) E' T U ->
  wf_env (G ++ F ++ E) ->
  eval_typing (G ++ F ++ E) E' T U.
Proof with eauto*.
  intros * Typ WfEnv.
  induction Typ.
  - Case "typing_eval_nil".
    apply typing_eval_nil...
    apply sub_weakening...
  - Case "typing_eval_cons".
    apply typing_eval_cons with (L := L `union` dom (G ++ F ++ E)) (U := U).
    + intros x x_fresh.
      assert (k_typing : typing (([(x, bind_typ T)] ++ G) ++ E) (open_ve k x (`cset_fvar` x)) U) by (apply (H x); eauto).
      eapply typing_weakening with (F := F) in k_typing.
      * SSCase "typing".
        apply k_typing.
      * SSCase "well formedness".
        simpl_env.
        apply wf_env_typ...
        assert (wf_env_xTGE : wf_env (([(x, bind_typ T)] ++ G) ++ E)).
        { eapply typing_regular, k_typing. }
        assert (wf_typ_xTGE_T : wf_typ_in (([(x, bind_typ T)] ++ G) ++ E) T).
        { apply (wf_typ_from_wf_env_typ x) in wf_env_xTGE.
          simpl_env.
          replace ((fix app (l m : env) {struct l} : env :=
                      match l with
                      | nil => m
                      | a :: l1 => a :: app l1 m
                      end) G E) with (G ++ E) in wf_env_xTGE by reflexivity.
          rewrite_env (empty ++ [(x, bind_typ T)] ++ G ++ E).
          apply wf_typ_in_weakening...
          apply ok_cons...
          apply ok_from_wf_env.
          apply wf_env_strengthening with (F := [(x, bind_typ T)]).
          applys typing_regular k_typing.
        }
        simpl_env in *.
        apply wf_typ_in_weakening with (F := F).
        -- apply (wf_typ_from_wf_env_typ x)...
        -- apply ok_from_wf_env...
    + assumption.
Qed.

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

Lemma store_typing_preserves_dom : forall S E,
  store_typing S E ->
  dom S = dom E.
Proof with eauto*.
  intros * StoreTyp.
  induction StoreTyp...
  repeat rewrite dom_concat; simpl.
  rewrite IHStoreTyp...
Qed.

Lemma subst_cset_cv_var_commutes_with_subst_vv : forall x u v,
  subst_cset x (`cset_fvar` u) (free_for_cv_var v)
  = free_for_cv_var (subst_vv x u v).
Proof with eauto*.
  unfold subst_cset.
  destruct v; simpl;
    [ destruct (a == x); subst; destruct_set_mem x {x}A
    | destruct_set_mem x {}A
    ]; csetdec.
Qed.

Lemma subst_cset_cv_commutes_with_susbt_ve : forall x u e,
    subst_cset x (`cset_fvar` u) (free_for_cv e)
  = free_for_cv (subst_ve x u (`cset_fvar` u) e).
Proof with auto using subst_cset_cv_var_commutes_with_subst_vv.
  induction e; simpl...
  all: rewrite subst_cset_union;
       f_equal...
Qed.

Lemma typing_through_subst_ve : forall F E x T U e (u : atom),
  typing (F ++ [(x, bind_typ U)] ++ E) e T ->
  binds u (bind_typ U) E ->
  typing (map (subst_cb x (`cset_fvar` u)) F ++ E)
         (subst_ve x u (`cset_fvar` u) e)
         (subst_ct x (`cset_fvar` u) T).
Local Ltac hint ::=
  eauto 4 using wf_env_subst_cb, typing_cv, subst_ct_fresh, subst_cpt_fresh, wf_typ_from_binds_typ, notin_fv_wf_pretyp.
Proof with hint.
  intros * Typ Binds.
  eremember (F ++ [(x, bind_typ U)] ++ E) as E'.
  generalize dependent F.
  induction Typ; intros F Eq; subst; simpl.
  - Case "typing_var_tvar".
    destruct (x0 == x); subst.
    + SCase "x0 = x".
      binds_cases H0.
      * clear - Fr0; simpl in Fr0; exfalso; fsetdec.
      * inversion H1; subst; clear H1 H0.
        apply typing_var_tvar.
        -- apply wf_env_subst_cb with (Q := X)...
           eapply wf_cset_from_binds...
        -- apply binds_tail.
           apply Binds.
           rewrite dom_map.
           apply ok_from_wf_env in H.
           eapply tail_not_in_head with (E := [(x, bind_typ X)] ++ E)...
           apply binds_In in Binds.
           rewrite dom_concat.
           fsetdec.
      * contradict H2.
        clear - H Binds.
        apply binds_fresh.
        apply ok_from_wf_env, fresh_mid_head in H.
        apply H.
    + SCase "x0 <> x".
      binds_cases H0.
      * apply typing_var_tvar...
        eapply wf_env_subst_cb with (Q := U)...
        eapply wf_cset_from_binds...
      * apply typing_var_tvar...
        eapply wf_env_subst_cb with (Q := U)...
        eapply wf_cset_from_binds...
        apply binds_head.
        replace (bind_typ X) with (subst_cb x (`cset_fvar` u) (bind_typ X)) by reflexivity.
        apply binds_map, H2.
  - Case "typing_var".
    destruct (x0 == x); subst.
    + SCase "x0 = x".
      binds_cases H0.
      * clear - Fr0; simpl in Fr0; exfalso; fsetdec.
      * inversion H1; subst; clear H1 H0.
        unfold subst_cset.
        destruct_set_mem x {x}A.
        2: clear - xIn; exfalso; fsetdec.
        clear xIn.
        replace ({x}A `\`A x) with {}A by fsetdec.
        replace (`cset_fvar` u `u` {}) with (`cset_fvar` u) by csetdec.
        apply typing_var with (C := C)...
        -- apply wf_env_subst_cb with (Q := typ_capt C P)...
           eapply wf_cset_from_binds...
        -- rewrite <- subst_cpt_fresh...
           ++ apply binds_tail...
              apply binds_In in Binds.
              apply ok_from_wf_env in H.
              apply ok_remove_mid in H.
              eapply tail_not_in_head with (E := E)...
           ++ apply wf_pretyp_in_notin_fv_cpt with (E := E).
              ** apply wf_env_weaken_head in H.
                 inversion H; subst.
                 inversion H4...
              ** eapply fresh_mid_tail with (F := F) (a := bind_typ (typ_capt C P)).
                 apply ok_from_wf_env, H.
      * contradict H2.
        clear - H Binds.
        apply binds_fresh.
        apply ok_from_wf_env, fresh_mid_head in H.
        apply H.
    + SCase "x0 <> x".
      binds_cases H0.
      * rewrite <- subst_cset_fresh with (x := x) (C1 := `cset_fvar` x0) (C2 := `cset_fvar` u),
                <- subst_cpt_fresh with (x := x) (t := P) (c := `cset_fvar` u).
        -- apply typing_var with (C := C)...
           apply wf_env_subst_cb with (Q := U)...
           eapply wf_cset_from_binds...
        -- apply wf_pretyp_in_notin_fv_cpt with (E := E).
           ++ enough (WfCP : wf_typ_in E (typ_capt C P)) by (inversion WfCP; auto).
               apply wf_env_bound_implies_wf_typ with (x := x0)...
           ++ apply fresh_mid_tail with (F := F) (a := bind_typ U).
              apply ok_from_wf_env, H.
        -- clear - n; fsetdec.
      * rewrite <- subst_cset_fresh with (x := x) (C1 := `cset_fvar` x0) (C2 := `cset_fvar` u).
        -- apply typing_var with (C := subst_cset x (`cset_fvar` u) C)...
           apply wf_env_subst_cb with (Q := U)...
           ++ eapply wf_cset_from_binds...
           ++ apply binds_head.
              replace (bind_typ (typ_capt (subst_cset x (`cset_fvar` u) C) (subst_cpt x (`cset_fvar` u) P))) with (subst_cb x (`cset_fvar` u) (bind_typ (typ_capt C P))) by reflexivity.
              apply binds_map...
        -- fsetdec.
  - Case "typing_abs".
    assert (WfEnv : wf_env (F ++ [(x, bind_typ U)] ++ E)). {
      pick fresh z for L.
      pose proof (H1 z Fr).
      enough (WfE' : wf_env ([(z, bind_typ V)] ++ F ++ [(x, bind_typ U)] ++ E)) by (inversion WfE'; auto).
      applys typing_regular H3.
    }
    rewrite subst_cset_cv_commutes_with_susbt_ve.
    pick fresh y and apply typing_abs.
    + eapply wf_typ_in_subst_cset...
      eapply wf_cset_from_binds...
    + specialize (H0 y ltac:(clear - Fr; fsetdec)).
      assert (NotIn : x `~in`A dom F /\ x `~in`A dom E /\ x <> y).
      { apply ok_from_wf_env in WfEnv as OkEnv.
        repeat split.
        - apply fresh_mid_head in OkEnv; apply OkEnv.
        - apply fresh_mid_tail in OkEnv; apply OkEnv.
        - clear - Fr; fsetdec. 
      }
      replace (dom (map (subst_cb x (`cset_fvar` u)) F ++ E))
         with (dom (F ++ [(x, bind_typ U)] ++ E) `\`A x).
      2: {
        clear - NotIn.
        repeat rewrite dom_concat.
        rewrite dom_map.
        simpl.
        fsetdec.
      }
      replace ((dom (F ++ [(x, bind_typ U)] ++ E) `\`A x) `u`A {y}A)
         with ((dom (F ++ [(x, bind_typ U)] ++ E) `u`A {y}A) `\`A x).
      2: {
        clear - NotIn.
        repeat rewrite dom_concat.
        simpl.
        fsetdec.
      }
      replace ([(y, bind_typ (subst_ct x (`cset_fvar` u) V))] ++ map (subst_cb x (`cset_fvar` u)) F ++ E)
         with (map (subst_cb x (`cset_fvar` u)) ([(y, bind_typ V)] ++ F) ++ E)
         by reflexivity.
      rewrite subst_ct_open_ct_var.
      * apply wf_typ_subst_cb with (Q := U).
        -- apply H0.
        -- apply wf_cset_extra.
           ++ eapply wf_cset_from_binds...
           ++ clear; repeat rewrite dom_concat; fsetdec.
        -- apply wf_cset_extra.
           ++ eapply wf_cset_from_binds...
           ++ clear; repeat rewrite dom_concat; fsetdec.
        -- simpl; apply ok_cons...
        -- apply ok_cons...
      * auto using NotIn.
      * trivial.
    + specialize (H2 y ltac:(clear - Fr; fsetdec) ([(y, bind_typ V)] ++ F) ltac:(reflexivity)).
      assert (NotIn : x `~in`A dom F /\ x `~in`A dom E /\ x <> y).
      { apply ok_from_wf_env in WfEnv as OkEnv.
        repeat split.
        - apply fresh_mid_head in OkEnv; apply OkEnv.
        - apply fresh_mid_tail in OkEnv; apply OkEnv.
        - clear - Fr; fsetdec. 
      }
      replace ([(y, bind_typ (subst_ct x (`cset_fvar` u) V))] ++ map (subst_cb x (`cset_fvar` u)) F ++ E)
         with (map (subst_cb x (`cset_fvar` u)) ([(y, bind_typ V)] ++ F) ++ E)
         by reflexivity.
      rewrite subst_ct_open_ct_var,
              subst_ve_open_ve_var...
  - Case "typing_app".
    assert (Neq: x0 <> x) by admit.
    rewrite <- subst_ct_open_ct_var.
    assert (Iff : (if f == x then var_f u else var_f f) = var_f (if f == x then u else f))
       by (destruct_if; reflexivity).
    assert (Ifx0 : (if x0 == x then var_f u else var_f x0) = (var_f (if x0 == x then u else x0)))
       by (destruct_if; reflexivity).
    rewrite Iff, Ifx0.
    replace (`cset_fvar` x0) with (`cset_fvar` (if x0 == x then u else x0)).
    apply typing_app with (T1 := subst_ct x (`cset_fvar` u) T1) (Cf := subst_cset x (`cset_fvar` u) Cf).
    + simpl in IHTyp1.
      rewrite Iff in IHTyp1.
      apply IHTyp1...
    + simpl in IHTyp2.
      rewrite Ifx0 in IHTyp2.
      apply IHTyp2...
    + destruct (x0 == x); subst...
      contradict Neq; reflexivity.
    + apply Neq.
    + trivial.
  - Case "typing_let".
    pick fresh y and apply typing_let.
    + apply IHTyp...
    + rewrite subst_ve_open_ve_var...
      replace ([(y, bind_typ (subst_ct x (`cset_fvar` u) T1))] ++ map (subst_cb x (`cset_fvar` u)) F ++ E)
         with (map (subst_cb x (`cset_fvar` u)) ([(y, bind_typ T1)] ++ F) ++ E)
         by reflexivity.
      apply H0...
  - Case "typing_tabs".
    assert (WfEnv : wf_env (F ++ [(x, bind_typ U)] ++ E)). {
      pick fresh Z for L.
      pose proof (H1 Z Fr).
      enough (WfE' : wf_env ([(Z, bind_sub V)] ++ F ++ [(x, bind_typ U)] ++ E)) by (inversion WfE'; auto).
      applys typing_regular H3.
    }
    rewrite subst_cset_cv_commutes_with_susbt_ve.
    pick fresh Y and apply typing_tabs.
    + eapply wf_typ_in_subst_cset...
      eapply wf_cset_from_binds...
    + specialize (H0 Y ltac:(clear - Fr; fsetdec)).
      assert (NotIn : x `~in`A dom F /\ x `~in`A dom E /\ x <> Y).
      { apply ok_from_wf_env in WfEnv as OkEnv.
        repeat split.
        - apply fresh_mid_head in OkEnv; apply OkEnv.
        - apply fresh_mid_tail in OkEnv; apply OkEnv.
        - clear - Fr; fsetdec. 
      }
      replace (dom (map (subst_cb x (`cset_fvar` u)) F ++ E))
        with (dom (F ++ [(x, bind_typ U)] ++ E) `\`A x).
      2: {
        clear - NotIn.
        repeat rewrite dom_concat.
        rewrite dom_map.
        simpl.
        fsetdec.
      }
      replace ((dom (F ++ [(x, bind_typ U)] ++ E) `\`A x) `u`A {Y}A)
        with ((dom (F ++ [(x, bind_typ U)] ++ E) `u`A {Y}A) `\`A x).
      2: {
        clear - NotIn.
        repeat rewrite dom_concat.
        simpl.
        fsetdec.
      }
      replace ([(Y, bind_sub (subst_ct x (`cset_fvar` u) V))] ++ map (subst_cb x (`cset_fvar` u)) F ++ E)
        with (map (subst_cb x (`cset_fvar` u)) ([(Y, bind_sub V)] ++ F) ++ E)
        by reflexivity.
      rewrite subst_ct_open_tt_var.
      * apply wf_typ_subst_cb with (Q := U).
        -- apply H0.
        -- apply wf_cset_extra.
          ++ eapply wf_cset_from_binds...
          ++ clear; repeat rewrite dom_concat; fsetdec.
        -- apply wf_cset_extra.
          ++ eapply wf_cset_from_binds...
          ++ clear; repeat rewrite dom_concat; fsetdec.
        -- simpl; apply ok_cons...
        -- apply ok_cons...
      * auto using NotIn.
      * trivial.
    + specialize (H2 Y ltac:(clear - Fr; fsetdec) ([(Y, bind_sub V)] ++ F) ltac:(reflexivity)).
      assert (NotIn : x `~in`A dom F /\ x `~in`A dom E /\ x <> Y).
      { apply ok_from_wf_env in WfEnv as OkEnv.
        repeat split.
        - apply fresh_mid_head in OkEnv; apply OkEnv.
        - apply fresh_mid_tail in OkEnv; apply OkEnv.
        - clear - Fr; fsetdec. 
      }
      replace ([(Y, bind_sub (subst_ct x (`cset_fvar` u) V))] ++ map (subst_cb x (`cset_fvar` u)) F ++ E)
        with (map (subst_cb x (`cset_fvar` u)) ([(Y, bind_sub V)] ++ F) ++ E)
        by reflexivity.
      rewrite subst_ct_open_tt_var,
              subst_ve_open_te_var...
  - Case "typing_tapp".
    assert (Neq : x0 <> x) by admit.
    assert (Ifx0 : (if x0 == x then var_f u else var_f x0) = (var_f (if x0 == x then u else x0)))
      by (destruct_if; reflexivity).
    rewrite Ifx0.
    rewrite subst_ct_open_tt.
    apply typing_tapp with (T1 := subst_ct x (`cset_fvar` u) T1) (C := subst_cset x (`cset_fvar` u) C).
    + rewrite <- Ifx0.
      apply IHTyp...
    + apply sub_through_subst_ct with (U := U)...
      apply subcapt_var with (T := U)...
      apply subcapt_reflexivity with (A := dom E).
      * apply cv_wf.
        apply wf_env_bound_implies_wf_typ with (x := u)...
      * clear; fsetdec.
    + trivial.
    + eapply bind_typ_notin_fv_tt with (S := U) (E := F ++ [(x, bind_typ U)] ++ E)...
  - Case "typing_sub".
    apply typing_sub with (S := subst_ct x (`cset_fvar` u) S)...
    apply sub_through_subst_ct with (U := U)...
    apply subcapt_var with (T := U)...
    apply subcapt_reflexivity with (A := dom E).
    * apply cv_wf.
      apply wf_env_bound_implies_wf_typ with (x := u)...
    * clear; fsetdec.
Admitted.

Lemma typing_through_subst_ve_typing : forall F E x T U e (u : atom),
  no_type_bindings E ->
  typing (F ++ [(x, bind_typ U)] ++ E) e T ->
  typing E u U ->
  typing (map (subst_cb x (`cset_fvar` u)) F ++ E)
         (subst_ve x u (`cset_fvar` u) e)
         (subst_ct x (`cset_fvar` u) T).
Local Ltac hint ::=
  eauto 4 using wf_env_subst_cb, typing_cv, subst_ct_fresh, subst_cpt_fresh, wf_typ_from_binds_typ, notin_fv_wf_pretyp.
Proof with hint.
  intros * NTB Typ uTyp.
  assert (Ok : ok (F ++ [(x, bind_typ U)] ++ E)) by (apply ok_from_wf_env; applys typing_regular Typ).
  destruct (typing_var_inversion' _ _ _ NTB uTyp) as [D [Q [D' [Q' [Eq [QSubQ' [xSubD' uBinds]]]]]]]; subst.
  eremember (F ++ [(x, bind_typ (typ_capt D' Q'))] ++ E) as E'.
  generalize dependent F.
  induction Typ; intros F Eq; subst; simpl.
  - Case "typing_var_tvar".
    destruct (x0 == x); subst.
    + SCase "x0 = x".
      binds_cases H0.
      * clear - Fr0; simpl in Fr0; exfalso; fsetdec.
      * apply binds_In in H2.
        assert (x `~in`A dom F) by (eapply fresh_mid_head; eauto).
        clear - H0 H2; fsetdec.
    + SCase "x0 <> x".
      binds_cases H0.
      * assert (WfX : wf_typ_in E X) by (apply wf_env_bound_implies_wf_typ with (x := x0); auto).
        inversion WfX; subst.
        contradict H2.
        apply NTB.
      * assert (x0 <> u).
        { intros eq; subst.
          apply binds_In in uBinds.
          apply binds_In in H2.
          enough (u `~in`A dom F) by fsetdec.
          eapply tail_not_in_head...
          simpl.
          fsetdec.
        }
        eapply typing_var_tvar...
        apply binds_head.
        replace (bind_typ X) with (subst_cb x (`cset_fvar` u) (bind_typ X))...
  - Case "typing_var".
    destruct (x0 == x); subst.
    + SCase "x0 = x".
      binds_cases H0.
      * clear - Fr0; simpl in Fr0; exfalso; fsetdec.
      * inversion H1; subst; clear H1 H0.
        rewrite <- subst_cpt_fresh.
        2: {
          apply wf_pretyp_notin_fv_cpt with (E := E) (Ap := dom E) (Am := dom E)...
          eapply fresh_mid_tail...
        }
        unfold subst_cset.
        destruct_set_mem x {x}A.
        2: clear - xIn; exfalso; fsetdec.
        clear xIn.
        replace ({x}A `\`A x) with {}A by fsetdec.
        replace (`cset_fvar` u `u` {}) with (`cset_fvar` u) by csetdec.
        apply typing_sub with (S := typ_capt (`cset_fvar` u) Q).
        -- apply typing_var with (C := D)...
        -- rewrite_env (empty ++ map (subst_cb x (`cset_fvar` u)) F ++ E).
           apply sub_weakening...
           2: eapply wf_env_subst_cb...
           apply sub_capt...
           apply subcapt_reflexivity with (A := dom E)...
           fsetdec.
      * apply binds_In in H2.
        assert (x `~in`A dom F) by (eapply fresh_mid_head; eauto).
        clear - H0 H2; fsetdec.
    + SCase "x0 <> x".
      binds_cases H0.
      * rewrite <- subst_cset_fresh with (x := x) (C1 := `cset_fvar` x0) (C2 := `cset_fvar` u),
                <- subst_cpt_fresh with (x := x) (t := P) (c := `cset_fvar` u).
        -- apply typing_var with (C := C)...
        -- apply wf_pretyp_in_notin_fv_cpt with (E := E).
           ++ enough (WfCP : wf_typ_in E (typ_capt C P)) by (inversion WfCP; auto).
               apply wf_env_bound_implies_wf_typ with (x := x0)...
           ++ apply fresh_mid_tail with (F := F) (a := bind_typ (typ_capt D' Q')).
              apply ok_from_wf_env, H.
        -- clear - n; fsetdec.
      * rewrite <- subst_cset_fresh with (x := x) (C1 := `cset_fvar` x0) (C2 := `cset_fvar` u)...
        apply typing_var with (C := subst_cset x (`cset_fvar` u) C)...
        apply binds_head.
        replace (bind_typ (typ_capt (subst_cset x (`cset_fvar` u) C) (subst_cpt x (`cset_fvar` u) P))) with (subst_cb x (`cset_fvar` u) (bind_typ (typ_capt C P))) by reflexivity.
        apply binds_map...
  - Case "typing_abs".
    assert (WfEnv : wf_env (F ++ [(x, bind_typ (typ_capt D' Q'))] ++ E)). {
      pick fresh z for L.
      pose proof (H1 z Fr).
      enough (WfE' : wf_env ([(z, bind_typ V)] ++ F ++ [(x, bind_typ (typ_capt D' Q'))] ++ E)) by (inversion WfE'; auto).
      applys typing_regular H3.
    }
    rewrite subst_cset_cv_commutes_with_susbt_ve.
    pick fresh y and apply typing_abs.
    + eapply wf_typ_in_subst_cset...
    + specialize (H0 y ltac:(clear - Fr; fsetdec)).
      assert (NotIn : x `~in`A dom F /\ x `~in`A dom E /\ x <> y).
      { apply ok_from_wf_env in WfEnv as OkEnv.
        repeat split.
        - apply fresh_mid_head in OkEnv; apply OkEnv.
        - apply fresh_mid_tail in OkEnv; apply OkEnv.
        - clear - Fr; fsetdec. 
      }
      replace (dom (map (subst_cb x (`cset_fvar` u)) F ++ E))
         with (dom (F ++ [(x, bind_typ (typ_capt D' Q'))] ++ E) `\`A x).
      2: {
        clear - NotIn.
        repeat rewrite dom_concat.
        rewrite dom_map.
        simpl.
        fsetdec.
      }
      replace ((dom (F ++ [(x, bind_typ (typ_capt D' Q'))] ++ E) `\`A x) `u`A {y}A)
         with ((dom (F ++ [(x, bind_typ (typ_capt D' Q'))] ++ E) `u`A {y}A) `\`A x).
      2: {
        clear - NotIn.
        repeat rewrite dom_concat.
        simpl.
        fsetdec.
      }
      replace ([(y, bind_typ (subst_ct x (`cset_fvar` u) V))] ++ map (subst_cb x (`cset_fvar` u)) F ++ E)
         with (map (subst_cb x (`cset_fvar` u)) ([(y, bind_typ V)] ++ F) ++ E)
         by reflexivity.
      rewrite subst_ct_open_ct_var.
      * apply wf_typ_subst_cb with (Q := typ_capt D' Q').
        -- apply H0.
        -- apply wf_cset_extra.
           ++ eapply wf_cset_from_binds...
           ++ clear; repeat rewrite dom_concat; fsetdec.
        -- apply wf_cset_extra.
           ++ eapply wf_cset_from_binds...
           ++ clear; repeat rewrite dom_concat; fsetdec.
        -- simpl; apply ok_cons...
        -- apply ok_cons...
      * auto using NotIn.
      * trivial.
    + assert (Ok' : ok ([(y, bind_typ V)] ++ F ++ [(x, bind_typ (typ_capt D' Q'))] ++ E)) by (apply ok_cons; auto).
      specialize (H2 y ltac:(clear - Fr; fsetdec) Ok' ([(y, bind_typ V)] ++ F) ltac:(reflexivity)).
      assert (NotIn : x `~in`A dom F /\ x `~in`A dom E /\ x <> y).
      { apply ok_from_wf_env in WfEnv as OkEnv.
        repeat split.
        - apply fresh_mid_head in OkEnv; apply OkEnv.
        - apply fresh_mid_tail in OkEnv; apply OkEnv.
        - clear - Fr; fsetdec. 
      }
      replace ([(y, bind_typ (subst_ct x (`cset_fvar` u) V))] ++ map (subst_cb x (`cset_fvar` u)) F ++ E)
         with (map (subst_cb x (`cset_fvar` u)) ([(y, bind_typ V)] ++ F) ++ E)
         by reflexivity.
      rewrite subst_ct_open_ct_var,
              subst_ve_open_ve_var...
  - Case "typing_app".
    assert (Neq : x0 <> x) by admit.
    assert (Iff : (if f == x then var_f u else var_f f) = var_f (if f == x then u else f))
      by (destruct_if; reflexivity).
    assert (Ifx0 : (if x0 == x then var_f u else var_f x0) = (var_f (if x0 == x then u else x0)))
      by (destruct_if; reflexivity).
    rewrite Iff, Ifx0.
    rewrite <- subst_ct_open_ct_var.
    replace (`cset_fvar` x0) with (`cset_fvar` (if x0 == x then u else x0)).
    apply typing_app with (T1 := subst_ct x (`cset_fvar` u) T1) (Cf := subst_cset x (`cset_fvar` u) Cf).
    + simpl in IHTyp1.
      rewrite Iff in IHTyp1.
      apply IHTyp1...
    + simpl in IHTyp2.
      rewrite Ifx0 in IHTyp2.
      apply IHTyp2...
    + destruct (x0 == x); subst...
      contradict Neq; reflexivity.
    + apply Neq.
    + trivial.
  - Case "typing_let".
    pick fresh y and apply typing_let.
    + apply IHTyp...
    + rewrite subst_ve_open_ve_var...
      replace ([(y, bind_typ (subst_ct x (`cset_fvar` u) T1))] ++ map (subst_cb x (`cset_fvar` u)) F ++ E)
         with (map (subst_cb x (`cset_fvar` u)) ([(y, bind_typ T1)] ++ F) ++ E)
         by reflexivity.
      apply H0...
  - Case "typing_tabs".
    assert (WfEnv : wf_env (F ++ [(x, bind_typ (typ_capt D' Q'))] ++ E)). {
      pick fresh Z for L.
      pose proof (H1 Z Fr).
      enough (WfE' : wf_env ([(Z, bind_sub V)] ++ F ++ [(x, bind_typ (typ_capt D' Q'))] ++ E)) by (inversion WfE'; auto).
      applys typing_regular H3.
    }
    rewrite subst_cset_cv_commutes_with_susbt_ve.
    pick fresh Y and apply typing_tabs.
    + eapply wf_typ_in_subst_cset...
    + specialize (H0 Y ltac:(clear - Fr; fsetdec)).
      assert (NotIn : x `~in`A dom F /\ x `~in`A dom E /\ x <> Y).
      { apply ok_from_wf_env in WfEnv as OkEnv.
        repeat split.
        - apply fresh_mid_head in OkEnv; apply OkEnv.
        - apply fresh_mid_tail in OkEnv; apply OkEnv.
        - clear - Fr; fsetdec. 
      }
      replace (dom (map (subst_cb x (`cset_fvar` u)) F ++ E))
        with (dom (F ++ [(x, bind_typ (typ_capt D' Q'))] ++ E) `\`A x).
      2: {
        clear - NotIn.
        repeat rewrite dom_concat.
        rewrite dom_map.
        simpl.
        fsetdec.
      }
      replace ((dom (F ++ [(x, bind_typ (typ_capt D' Q'))] ++ E) `\`A x) `u`A {Y}A)
        with ((dom (F ++ [(x, bind_typ (typ_capt D' Q'))] ++ E) `u`A {Y}A) `\`A x).
      2: {
        clear - NotIn.
        repeat rewrite dom_concat.
        simpl.
        fsetdec.
      }
      replace ([(Y, bind_sub (subst_ct x (`cset_fvar` u) V))] ++ map (subst_cb x (`cset_fvar` u)) F ++ E)
        with (map (subst_cb x (`cset_fvar` u)) ([(Y, bind_sub V)] ++ F) ++ E)
        by reflexivity.
      rewrite subst_ct_open_tt_var.
      * apply wf_typ_subst_cb with (Q := typ_capt D' Q').
        -- apply H0.
        -- apply wf_cset_extra.
          ++ eapply wf_cset_from_binds...
          ++ clear; repeat rewrite dom_concat; fsetdec.
        -- apply wf_cset_extra.
          ++ eapply wf_cset_from_binds...
          ++ clear; repeat rewrite dom_concat; fsetdec.
        -- simpl; apply ok_cons...
        -- apply ok_cons...
      * auto using NotIn.
      * trivial.
    + assert (Ok' : ok ([(Y, bind_sub V)] ++ F ++ [(x, bind_typ (typ_capt D' Q'))] ++ E)) by (apply ok_cons; auto).
      specialize (H2 Y ltac:(clear - Fr; fsetdec) Ok' ([(Y, bind_sub V)] ++ F) ltac:(reflexivity)).
      assert (NotIn : x `~in`A dom F /\ x `~in`A dom E /\ x <> Y).
      { apply ok_from_wf_env in WfEnv as OkEnv.
        repeat split.
        - apply fresh_mid_head in OkEnv; apply OkEnv.
        - apply fresh_mid_tail in OkEnv; apply OkEnv.
        - clear - Fr; fsetdec. 
      }
      replace ([(Y, bind_sub (subst_ct x (`cset_fvar` u) V))] ++ map (subst_cb x (`cset_fvar` u)) F ++ E)
        with (map (subst_cb x (`cset_fvar` u)) ([(Y, bind_sub V)] ++ F) ++ E)
        by reflexivity.
      rewrite subst_ct_open_tt_var,
              subst_ve_open_te_var...
  - Case "typing_tapp".
    assert (Ifx0 : (if x0 == x then var_f u else var_f x0) = (var_f (if x0 == x then u else x0)))
      by (destruct_if; reflexivity).
    rewrite Ifx0.
    rewrite subst_ct_open_tt.
    apply typing_tapp with (T1 := subst_ct x (`cset_fvar` u) T1) (C := subst_cset x (`cset_fvar` u) C).
    + rewrite <- Ifx0.
      apply IHTyp...
    + apply sub_through_subst_ct with (U := typ_capt D' Q')...
    + trivial.
    + eapply bind_typ_notin_fv_tt with (S := typ_capt D' Q') (E := F ++ [(x, bind_typ (typ_capt D' Q'))] ++ E)...
  - Case "typing_sub".
    apply typing_sub with (S := subst_ct x (`cset_fvar` u) S)...
    apply sub_through_subst_ct with (U := typ_capt D' Q')...
Admitted.

Lemma typing_through_open_ve_typing : forall E (x y : atom) U e T,
  no_type_bindings E ->
  y `~in`A (fv_ct T `u`A fv_ve e `u`A fv_ce e) ->
  typing ([(y, bind_typ U)] ++ E) (open_ve e y (`cset_fvar` y)) (open_ct T (`cset_fvar` y)) ->
  typing E x U ->
  typing E (open_ve e x (`cset_fvar` x)) (open_ct T (`cset_fvar` x)).
Proof with eauto*.
  intros * NTB NotIn Typ xTyp.
  assert (WfEnv : wf_env ([(y, bind_typ U)] ++ E)) by applys typing_regular Typ.
  assert (Neq : x <> y).
  { inversion WfEnv; subst.
    enough (x `in`A dom E) by fsetdec.
    clear - xTyp.
    dependent induction xTyp.
    - apply binds_In in H0...
    - apply binds_In in H0...
    - apply IHxTyp...  
  }
  rewrite_env (map (subst_cb y (`cset_fvar` x)) empty ++ E).
  replace (open_ve e x (`cset_fvar` x))
     with (subst_ve y x (`cset_fvar` x) (open_ve e y (`cset_fvar` y)))
     by (rewrite <- subst_ve_intro; auto).
  replace (open_ct T (`cset_fvar` x))
     with (subst_ct y (`cset_fvar` x) (open_ct T (`cset_fvar` y)))
     by (rewrite <- subst_ct_intro; auto).
  apply typing_through_subst_ve_typing with (U := U)...
Qed.

Lemma typing_through_open_te : forall E (Y : atom) e T P Q,
  no_type_bindings E ->
  Y `~in`A (fv_tt T `u`A fv_ct T `u`A fv_te e `u`A fv_ce e) ->
  typing ([(Y, bind_sub Q)] ++ E) (open_te e Y) (open_tt T Y) ->
  sub E P Q ->
  `cset_uvar` (cv P) <> true ->
  typing E (open_te e P) (open_tt T P).
Proof with eauto*.
  intros * NTB NotIn Typ Sub NotUniv.
  rewrite_env (map (subst_tb Y P) empty ++ E).
  replace (open_te e P)
     with (subst_te Y P (open_te e Y))
     by (symmetry; apply subst_te_intro; clear - NotIn; fsetdec).
  replace (open_tt T P)
     with (subst_tt Y P (open_tt T Y))
     by (symmetry; apply subst_tt_intro; clear - NotIn; fsetdec).
  apply typing_through_subst_te with (Q := Q)...
Qed.

Lemma typing_inv_app : forall E (f x : atom) T,
  no_type_bindings E ->
  typing E (exp_app f x) T ->
  exists C T1 T2, typing E f (typ_capt C (typ_arrow T1 T2))
    /\ typing E x T1
    /\ sub E (open_ct T2 (`cset_fvar` x)) T.
Proof with eauto*.
  intros * NTB Typ.
  dependent induction Typ.
  - Case "typing_app".
    exists Cf, T1, T2.
    repeat split...
    destructs typing_regular Typ1 as [WfEnv [_ WfCfT1T2]].
    inversion WfCfT1T2; subst.
    inversion H5; subst.
    apply sub_reflexivity with (Ap := dom E) (Am := dom E)...
    pick fresh z and specialize H7.
    replace (open_ct T2 (`cset_fvar` x))
       with (subst_ct z (`cset_fvar` x) (open_ct T2 (`cset_fvar` z))).
    replace (dom E) with (dom E `\`A z).
    replace (wf_typ E (dom E `\`A z)) with (wf_typ E (dom ([(z, bind_typ T1)] ++ E) `\`A z)).
    rewrite_env (map (subst_cb z (`cset_fvar` x)) empty ++ E).
    eapply wf_typ_subst_cb with (Q := T1); csetsimpl...
    + replace ({z}A `u`A dom E) with (dom E `u`A {z}A) by (clear; fsetdec).
      apply H7.
    + apply wf_cset_set_weakening with (A := dom E).
      2: fsetdec.
      destructs typing_var_inversion' NTB Typ2 as [C [P [_ [_ [_ [_ [_ Binds]]]]]]].
      eapply wf_cset_from_binds...
    + destructs typing_var_inversion' NTB Typ2 as [C [P [_ [_ [_ [_ [_ Binds]]]]]]].
      eapply wf_cset_from_binds...
    + f_equal.
      simpl.
      clear; fsetdec.
    + assert (z `~in`A dom E) by (clear - Fr; fsetdec).
      clear - H; fsetdec.
    + symmetry.
      apply subst_ct_intro.
      clear - Fr; fsetdec.     
  - destruct (IHTyp f x NTB eq_refl) as [C [T1 [T2 [fTyp [xTyp Seq]]]]].
    exists C, T1, T2.
    repeat split...
    apply sub_transitivity with (Q := S)...
Qed.

Lemma typing_tapp_inversion : forall E (x : atom) U T,
  no_type_bindings E ->
  typing E (exp_tapp x U) T ->
  exists C T1 T2, typing E x (typ_capt C (typ_all T1 T2))
    /\ sub E U T1
    /\ sub E (open_tt T2 U) T.
Proof with eauto*.
  intros * NTB Typ.
  dependent induction Typ.
  - Case "typing_tapp".
    exists C, T1, T2.
    repeat split...
    destructs typing_regular Typ as [WfEnv [_ WfCT1T2]].
    inversion WfCT1T2; subst.
    inversion H6; subst.
    apply sub_reflexivity with (Ap := dom E) (Am := dom E)...
    pick fresh Z and specialize H8.
    replace (open_tt T2 U)
       with (subst_tt Z U (open_tt T2 Z)).
    replace (dom E) with (dom ([(Z, bind_sub T1)] ++ E) `\`A Z).
    rewrite_env (map (subst_tb Z U) empty ++ E).
    assert (WfU : wf_typ E ({Z}A `u`A dom E) ({Z}A `u`A dom E) U).
    { rewrite_env (empty ++ empty ++ E).
      eapply wf_typ_weakening with (Ap := dom E) (Am := dom E)...
      applys sub_regular H.
      all: simpl; clear; fsetdec.
    }
    eapply wf_typ_subst_tb with (Q := T1); csetsimpl...
    + replace ({Z}A `u`A dom E) with (dom E `u`A {Z}A) by (clear; fsetdec).
      apply H8.
    + simpl.
      assert (Z `~in`A dom E) by (clear - Fr; fsetdec).
      clear - H0.
      fsetdec.
    + symmetry.
      apply subst_tt_intro.
      clear - Fr; fsetdec.     
  - destruct (IHTyp x U NTB eq_refl) as [C [T1 [T2 [fTyp [xTyp Seq]]]]].
    exists C, T1, T2.
    repeat split...
    apply sub_transitivity with (Q := S)...
Qed.

Lemma preservation : forall s s' V,
  state_typing s V ->
  red s s' ->
  state_typing s' V.
Ltac hint :=
    eauto using wf_cset_set_weakening, no_type_bindings_cons.
Proof with hint.
  intros * [S K e E T U StoreTyp EvalTyp Typ] Red.
  assert (WfEnv : wf_env E) by applys eval_typing_regular EvalTyp.
  assert (NTB : no_type_bindings E) by applys store_typing_no_type_bindings StoreTyp.
  dependent induction Red.
  - Case "red_lift".
    inversion EvalTyp; subst.
    assert (x `~in`A dom E) by (rewrite <- (store_typing_preserves_dom _ _ StoreTyp); assumption).
    eapply typing_state with (E := [(x, bind_typ T)] ++ E) (T := U0).
    + apply typing_store_cons...
    + rewrite_env (empty ++ [(x, bind_typ T)] ++ E).
      apply eval_typing_weakening with (F := [(x, bind_typ T)])...
      apply wf_env_typ...
      applys typing_regular Typ.
    + pick fresh y and specialize H5.
      assert (type_U0 : type U0).
      { enough (WfU : wf_typ_in E U0) by applys type_from_wf_typ WfU.
        applys eval_typing_regular H6.
      }
      rewrite open_ct_rec_type with (k := 0) (C := `cset_fvar` x)...
      apply typing_through_open_ve_typing with (y := y) (U := T).
      * apply no_type_bindings_cons...
      * clear - Fr; fsetdec.
      * apply typing_weakening.
        unfold open_ct.
        rewrite <- open_ct_rec_type...
        assert (WfT : wf_typ_in E T).
        { enough (WfE : wf_env ([(y, bind_typ T)] ++ E)) by (inversion WfE; auto).
          applys typing_regular H5.
        }
        apply wf_env_typ.
        -- apply wf_env_typ...
        -- rewrite_env (empty ++ [(x, bind_typ T)] ++ E).
           apply wf_typ_in_weakening...
           apply ok_cons...
        -- rewrite dom_concat; simpl; clear - Fr; fsetdec.
      * destruct T.
        -- apply typing_sub with (S := typ_capt (`cset_fvar` x) p).
           ++ eapply typing_var...
           ++ assert (Wfcp : wf_typ_in E (typ_capt c p)) by applys typing_regular Typ.
              inversion Wfcp; subst.
              apply sub_capt...
              ** eapply subcapt_var...
                 cbn [cv].
                 apply subcapt_reflexivity with (A := dom ([(x, bind_typ (typ_capt c p))] ++ E)).
                 2: fsetdec.
                 rewrite_env (empty ++ [(x, bind_typ (typ_capt c p))] ++ E).
                 apply wf_cset_in_weakening...
                 apply ok_cons...
              ** apply sub_pre_reflexivity with (Ap := dom ([(x, bind_typ (typ_capt c p))] ++ E)) (Am := dom ([(x, bind_typ (typ_capt c p))] ++ E))...
                 2,3: fsetdec.
                 rewrite_env (empty ++ [(x, bind_typ (typ_capt c p))] ++ E).
                 apply wf_pretyp_in_weakening...
                 apply ok_cons...
        -- enough (Wfn : wf_typ_in E n) by inversion Wfn.
           applys typing_regular Typ.
        -- assert (Wfa : wf_typ_in E a) by applys typing_regular Typ.
           inversion Wfa; subst.
           contradict H3.
           apply NTB. 
  - Case "red_let_var".
    inversion EvalTyp; subst.
    eapply typing_state with (E := E) (T := U0)...
    pick fresh z and specialize H5.
    assert (type_U0 : type U0).
    { enough (WfU : wf_typ_in E U0) by applys type_from_wf_typ WfU.
      applys eval_typing_regular H6.
    }
    rewrite open_ct_rec_type with (k := 0) (C := `cset_fvar` x)...
    apply typing_through_open_ve_typing with (y := z) (U := T)...
    destructs typing_var_inversion' NTB Typ as [C [P [D [Q [Eq [PSubQ [xSubD Binds]]]]]]]; subst.
    destructs stores_preserves_typing StoreTyp H Typ as [B [R [vTyp [Binds' [vSubB RSubQ]]]]].
    assert (bind_typ (typ_capt B R) = bind_typ (typ_capt C P)) by applys binds_unique Binds' Binds.
    inversion H0; subst; clear H0.
    unfold open_ct.
    rewrite <- open_ct_rec_type...
  - Case "red_let_val".
    assert (x `~in`A dom E) by (rewrite <- (store_typing_preserves_dom _ _ StoreTyp); assumption).
    destructs typing_inv_let Typ as [T1 [eTyp [L kTyp]]].
    eapply typing_state with (E := [(x, bind_typ T1)] ++ E) (T := T).
    + apply typing_store_cons...
    + rewrite_env (empty ++ [(x, bind_typ T1)] ++ E).
      apply eval_typing_weakening...
      apply wf_env_typ...
      applys typing_regular eTyp.
    + pick fresh z and specialize kTyp.
      assert (type_T : type T).
      { enough (WfT : wf_typ_in E T) by applys type_from_wf_typ WfT.
        applys typing_regular Typ.
      }
      rewrite open_ct_rec_type with (k := 0) (C := `cset_fvar` x)...
      eapply typing_through_open_ve_typing with (y := z) (U := T1)...
      * apply typing_weakening.
        unfold open_ct.
        rewrite <- open_ct_rec_type...
        assert (WfT1 : wf_typ_in E T1) by applys typing_regular eTyp.
        repeat apply wf_env_typ...
        rewrite_env (empty ++ [(x, bind_typ T1)] ++ E).
        apply wf_typ_in_weakening...
        apply ok_cons...
      * assert (wf_typ_in E T1) by applys typing_regular eTyp.
        inversion H1; subst.
        -- contradict H2; apply NTB.
        -- apply typing_sub with (S := typ_capt (`cset_fvar` x) P)...
           apply sub_capt.
           ++ eapply subcapt_var...
              cbn [cv].
              rewrite_env (empty ++ [(x, bind_typ (typ_capt C P))] ++ E).
              apply subcapt_weakening.
              2: apply wf_env_typ...
              apply subcapt_reflexivity with (A := dom E)...
              clear; fsetdec.
           ++ rewrite_env (empty ++ [(x, bind_typ (typ_capt C P))] ++ E).
              apply sub_pre_weakening.
              2: apply wf_env_typ...
              apply sub_pre_reflexivity with (Ap := dom E) (Am := dom E)...
              all: clear; fsetdec. 
  - Case "red_let_exp".
    destructs typing_inv_let Typ as [T1 [eTyp [L kTyp]]].
    eapply typing_state with (E := E) (T := T1)...
    eapply typing_eval_cons...
  - Case "red_app".
    destructs typing_inv_app NTB Typ as [C [T1 [T2 [fTyp [xTyp T2SubT]]]]].
    destructs stores_preserves_typing StoreTyp H fTyp as [D [Q [absTyp [fBinds [e0SubD QSubP]]]]].
    simpl in absTyp, e0SubD.
    destruct (typing_inv_abs _ _ _ _ absTyp T1 T2 (free_for_cv e0)) as [T1SubU0 [S2 [L ?]]].
    + apply sub_capt...
      apply subcapt_reflexivity with (A := dom E)...
      clear; fsetdec.
    + pick fresh z and specialize H1.
      destruct H1 as [e0Typ [WfT2 S2SubT2]].
      eapply typing_state with (E := E) (T := open_ct T2 (`cset_fvar` x))...
      * eapply eval_typing_sub...
        apply sub_reflexivity with (Ap := dom E) (Am := dom E)...
        applys eval_typing_regular EvalTyp.
        all: clear; fsetdec.
      * apply typing_sub with (S := open_ct S2 (`cset_fvar` x)).
        -- apply typing_through_open_ve_typing with (y := z) (U := U0)...
        -- rewrite_env (map (subst_cb z (`cset_fvar` x)) empty ++ E).
           replace (open_ct S2 (`cset_fvar` x))
              with (subst_ct z (`cset_fvar` x) (open_ct S2 (`cset_fvar` z)))
              by (symmetry; apply subst_ct_intro; clear - Fr; fsetdec).
           replace (open_ct T2 (`cset_fvar` x))
              with (subst_ct z (`cset_fvar` x) (open_ct T2 (`cset_fvar` z)))
              by (symmetry; apply subst_ct_intro; clear - Fr; fsetdec).
           eapply sub_through_subst_ct...
           clear - xTyp NTB.
           destructs typing_var_inversion' NTB xTyp as [C [P [D [Q [Eq [PSubQ [xSubD Binds]]]]]]].
           subst.
           simpl...
  - Case "red_tapp". 
    destructs typing_tapp_inversion NTB Typ as [C [T1 [T2 [xTyp [T0SubT1 T2SubT]]]]].
    destructs stores_preserves_typing StoreTyp H xTyp as [D [Q [tabsTyp [xBinds [e0SubD QSubP]]]]].
    simpl in tabsTyp, e0SubD.
    destruct (typing_inv_tabs _ _ _ _ tabsTyp T1 T2 (free_for_cv e0)) as [T1SubU0 [S2 [L ?]]].
    + apply sub_capt...
      apply subcapt_reflexivity with (A := dom E)...
      clear; fsetdec.
    + pick fresh z and specialize H1.
      destruct H1 as [WfS2 S2SubT2].
      eapply typing_state with (E := E) (T := open_tt T2 T0)...
      * eapply eval_typing_sub...
        apply sub_reflexivity with (Ap := dom E) (Am := dom E)...
        applys eval_typing_regular EvalTyp.
        all: clear; fsetdec.
      * apply typing_through_open_te with (Y := z) (P := T0) (Q := T1)...
        admit.
Admitted.

Lemma binds_implies_store : forall S E x T,
  store_typing S E ->
  binds x (bind_typ T) E ->
  exists v v_value, stores S x v v_value.
Proof with eauto*.
  intros * StoreTyp Binds.
  induction StoreTyp.
  - Case "typing_store_nil".
    inversion Binds.
  - Case "typing_store_cons".
    binds_cases Binds.
    + SCase "x in E".
      destruct (IHStoreTyp H1) as [w [w_value Stores]].
      exists w, w_value.
      apply binds_tail...
    + SCase "x = x0".
      exists v, v_value.
      apply binds_head...
Qed.

(* ********************************************************************** *)
(** ** Canonical forms (14) *)

Lemma canonical_form_abs' : forall E v C U1 U2,
  no_type_bindings E ->
  value v ->
  typing E v (typ_capt C (typ_arrow U1 U2)) ->
  exists S1 e, v = exp_abs S1 e
             /\ sub E U1 S1
             /\ exists L, forall x, x `~in`A L ->
                  typing ([(x, bind_typ S1)] ++ E) (open_ve e x (`cset_fvar` x)) (open_ct U2 (`cset_fvar` x)).
Proof with eauto*.
  intros * NTB Val Typ.
  remember (typ_arrow U1 U2).
  revert U1 U2 Heqp.
  assert (WfEnv : wf_env E) by applys typing_regular Typ.
  dependent induction Typ; intros U1 U2 Eq; subst; try solve [ inversion Val | inversion Eq ].
  - inversion Eq; subst.
    exists U1, e1.
    repeat split...
    eapply sub_reflexivity...
  - inversion H; subst.
    + contradict H0; apply (NTB X U).
    + inversion H5; subst.
      destruct (IHTyp C1 NTB Val (typ_arrow S1 S2) eq_refl WfEnv S1 S2 eq_refl) as [S' [e' [Eq [Sub [L' ?]]]]].
      exists S', e'.
      repeat split...
      * apply sub_transitivity with (Q := S1)...
      * exists (L `u`A L').
        intros x NotIn.
        rewrite_env (empty ++ [(x, bind_typ S')] ++ E).
        apply typing_sub with (S := open_ct S2 (`cset_fvar` x))...
        admit.
Admitted.

Lemma canonical_form_tabs' : forall E v C U1 U2,
  no_type_bindings E ->
  value v ->
  typing E v (typ_capt C (typ_all U1 U2)) ->
  exists S1 e, v = exp_tabs S1 e
             /\ sub E U1 S1
             /\ exists L, forall X, X `~in`A L ->
                  typing ([(X, bind_sub S1)] ++ E) (open_te e X) (open_tt U2 X).
Proof with eauto*.
  intros * NTB Val Typ.
  remember (typ_all U1 U2).
  revert U1 U2 Heqp.
  assert (WfEnv : wf_env E) by applys typing_regular Typ.
  dependent induction Typ; intros U1 U2 Eq; subst; try solve [ inversion Val | inversion Eq ].
  - inversion Eq; subst.
    exists U1, e1.
    repeat split...
    eapply sub_reflexivity...
  - inversion H; subst.
    + contradict H0; apply (NTB X U).
    + inversion H5; subst.
      destruct (IHTyp C1 NTB Val (typ_all S1 S2) eq_refl WfEnv S1 S2 eq_refl) as [S' [e' [Eq [Sub [L' ?]]]]].
      exists S', e'.
      repeat split...
      * apply sub_transitivity with (Q := S1)...
      * exists (L `u`A L').
        intros X NotIn.
        apply typing_sub with (S := open_tt S2 X)...
        specialize (H11 X ltac:(clear - NotIn; fsetdec)).
        rewrite_env (empty ++ [(X, bind_sub S')] ++ E).
        eapply sub_narrowing with (Q := U1)...
        admit.
Admitted.

Lemma progress : forall s V, 
  state_typing s V ->
  state_final s \/ exists s', red s s'.
Proof with eauto*.
  intros * [S K e E T U StoreTyp EvalTyp Typ].
  assert (NTB : no_type_bindings E) by applys store_typing_no_type_bindings StoreTyp.
  induction Typ.
  - Case "typing_var_tvar".
    assert (WfX : wf_typ_in E X) by (apply wf_env_bound_implies_wf_typ with (x := x); eauto).
    inversion WfX; subst.
    contradict H2.
    apply NTB.
  - Case "typing_var".
    inversion EvalTyp; subst.
    + left; apply final_state, answer_var.
    + right.
      exists ⟨ S | K0 | open_ve k x (`cset_fvar` x) ⟩.
      destructs binds_implies_store StoreTyp H0 as [v [v_value Stores]].
      eapply red_let_var...
  - Case "typing_abs".
    assert (Val : value (exp_abs V0 e1)).
    { apply value_abs.
      apply expr_abs with (L := L).
      * eapply type_from_wf_typ, H.
      * intros x NotIn.
        specialize (H1 x NotIn).
        applys typing_regular H1.
    }
    inversion EvalTyp; subst.
    + left; apply final_state, answer_val, Val.
    + right.
      pick fresh z for (dom S).
      exists ⟨ [(z, store (exp_abs V0 e1) Val)] ++ S | K0 | open_ve k z (`cset_fvar` z) ⟩.
      apply red_lift, Fr.
  - Case "typing_app".
    right.
    destructs typing_var_inversion' NTB Typ1 as [C [P [D [Q [Eq [PSubQ [fSubD Binds]]]]]]].
    inversion Eq; subst; clear Eq.
    destructs binds_implies_store StoreTyp Binds as [abs [absValue Stores]].
    destructs stores_preserves_typing StoreTyp Stores Typ1 as [Cf [Qf [absTyp [fBinds [absSubCf QfSubT1T2]]]]].
    eapply typing_sub in absTyp.
    2: apply sub_capt...
    destructs canonical_form_abs' NTB absValue absTyp as [U0 [e [Eq [T1SubU [L ?]]]]]; subst.
    exists ⟨ S | K | open_ve e x (`cset_fvar` x) ⟩.
    destructs typing_var_inversion' NTB Typ2 as [C' [P' [D' [Q' [Eq [P'SubQ' [xSubD' Binds']]]]]]].
    destructs binds_implies_store StoreTyp Binds' as [v [v_value Stores']].
    eapply red_app...
  - Case "typing_let".
    right.
    pick fresh z for (dom S).
    assert (k_scope : scope k).
    { econstructor.
      intros x NotIn.
      specialize (H x NotIn).
      applys typing_regular H.
    }
    exists ⟨ S | cont k k_scope :: K | e ⟩.
    apply red_let_exp.
  - Case "typing_tabs".
    assert (Val : value (exp_tabs V0 e1)).
    { apply value_tabs.
      apply expr_tabs with (L := L).
      * eapply type_from_wf_typ, H.
      * intros x NotIn.
        specialize (H1 x NotIn).
        applys typing_regular H1.
    }
    inversion EvalTyp; subst.
    + left; apply final_state, answer_val, Val.
    + right.
      pick fresh z for (dom S).
      exists ⟨ [(z, store (exp_tabs V0 e1) Val)] ++ S | K0 | open_ve k z (`cset_fvar` z) ⟩.
      apply red_lift, Fr.
  - Case "typing_tabs".
    right.
    destructs typing_var_inversion' NTB Typ as [C' [P' [D' [Q' [Eq [P'SubQ' [xSubD' Binds]]]]]]].
    inversion Eq; subst; clear Eq.
    destructs binds_implies_store StoreTyp Binds as [abs [tabsValue Stores]].
    destructs stores_preserves_typing StoreTyp Stores Typ as [Cf [Qf [tabsTyp [xBinds [tabsSubCf QfSubT1T2]]]]].
    eapply typing_sub in tabsTyp.
    2: apply sub_capt...
    destructs canonical_form_tabs' NTB tabsValue tabsTyp as [U0 [e [Eq [T1SubU [L ?]]]]]; subst.
    exists ⟨ S | K | open_te e T ⟩.
    eapply red_tapp...
  - Case "typing_sub".
    apply IHTyp...
    eapply eval_typing_sub with (S1 := T) (T1 := U)...
    eapply sub_reflexivity...
    applys eval_typing_regular EvalTyp.
    all: clear; fsetdec.
  Qed.