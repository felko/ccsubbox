Require Import Coq.Program.Equality.
Require Import TaktikZ.

Require Import CCsub_Subcapt.
Require Import CCsub_Subtyping.
Require Import CCsub_Typing.
Require Import CCsub_Substitution.

Set Nested Proofs Allowed.

(* States *)

Inductive store_frame : Type :=
  | store v : value v -> store_frame.

Definition store_ctx : Type := list (atom * store_frame).
Definition stores (S : store_ctx) (x : atom) (v : exp) (v_value : value v) : Prop :=
    binds x (store v v_value) S.

Inductive scope (e : exp) : Type :=
  | mk_scope L : (forall x, x `notin` L -> expr (open_ve e x (`cset_fvar` x))) -> scope e.

Inductive eval_frame : Type :=
  | cont e : scope e -> eval_frame.

Definition eval_ctx : Type := (list eval_frame).

Inductive state : Type :=
  | mk_state : store_ctx -> eval_ctx -> exp -> state.

Notation "⟨ S | E | e ⟩" := (mk_state S E e) (at level 1).

Inductive state_final : state -> Prop :=
  | final_state : forall S a,
      answer a ->
      state_final ⟨ S | nil | a ⟩.

Inductive store_typing : store_ctx -> env -> Prop :=
  | typing_store_nil : store_typing nil nil
  | typing_store_cons : forall x T v v_value S E,
      store_typing S E ->
      typing E v T ->
      x `notin` dom E ->
      store_typing ([(x, store v v_value)] ++ S) ([(x, bind_typ T)] ++ E).

Inductive eval_typing (E : env) : eval_ctx -> typ -> typ -> Prop :=
  | typing_eval_nil : forall T U,
      wf_env E ->
      sub E T U ->
      eval_typing E nil T U
  | typing_eval_cons : forall L k (k_scope : scope k) K T U V,
      (forall x, x `notin` L ->
        typing ([(x, bind_typ T)] ++ E) (open_ve k x (`cset_fvar` x)) U) ->
      eval_typing E K U V ->
      eval_typing E (cont k k_scope :: K) T V.

Inductive state_typing : state -> typ -> Prop :=
  | typing_state : forall S K e E T U,
      store_typing S E ->
      eval_typing E K T U ->
      typing E e T ->
      state_typing ⟨ S | K | e ⟩ U.

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

(*
Lemma typing_state_free_tvar : forall S E,
  store_typing S E ->
  no_type_bindings E.
Proof with eauto.
  intros. unfold no_type_bindings; intros.
  induction H...
  * intro. binds_cases H...
  * intro.s 
Qed.
*)

Fixpoint env_fv_ct (F : env) {struct F} : atoms :=
  match F with
  | nil => {}A
  | (_, bind_typ T) :: F' => (fv_ct T) `u`A (env_fv_ct F')
  | (_, bind_sub T) :: F' => (fv_ct T) `u`A (env_fv_ct F')
  end.

Lemma stores_unique : forall S x v1 v1_value v2 v2_value,
  stores S x v1 v1_value ->
  stores S x v2 v2_value ->
  v1 = v2.
Proof with eauto*.
  intros * stores1 stores2.
  unfold stores, binds in *.
  rewrite stores1 in stores2.
  inversion stores2...
Qed.

Lemma wf_cset_notin_fvars : forall x E A C,
  wf_cset E A C ->
  x `~in`A dom E ->
  x `~in`A (`cset_fvars` C).
Proof with eauto*.
  intros * WfC NotIn.
  induction WfC.
  enough (fvars `c`A dom E) by fsetdec.
  intros y yIn.
  destruct (H y ltac:(fsetdec)) as [T [B|B]]; eapply binds_In...
Qed.

Lemma wf_typ_notin_fv_ct : forall x E Ap Am T,
  wf_typ E Ap Am T ->
  x `~in`A dom E ->
  x `~in`A fv_ct T
with wf_pretyp_notin_fv_cpt : forall x E Ap Am P,
  wf_pretyp E Ap Am P ->
  x `~in`A dom E ->
  x `~in`A fv_cpt P.
Proof with eauto*.
{ intros * WfT NotIn.
  induction WfT; simpl.
  - fsetdec.
  - assert (x `~in`A (`cset_fvars` C)) by (applys wf_cset_notin_fvars; eauto*).
    assert (x `~in`A fv_cpt P) by (applys wf_pretyp_notin_fv_cpt; eauto*).
    fsetdec.
}
{ intros * WfP NotIn.
  induction WfP; simpl.
  - fsetdec.
  - assert (x `~in`A fv_ct T1) by (applys wf_typ_notin_fv_ct; eauto*).
    pick fresh y and specialize H0.
    assert (x `~in`A fv_ct T2).
    { eapply notin_fv_ct_open_ct.
      eapply wf_typ_notin_fv_ct.
      apply H0.
      simpl.
      assert (x <> y) by (clear - Fr; fsetdec).
      clear Fr.
      fsetdec.
    }
    clear - H1 H2.
    fsetdec.
  - assert (x `~in`A fv_ct T1) by (applys wf_typ_notin_fv_ct; eauto*).
    pick fresh y and specialize H0.
    assert (x `~in`A fv_ct T2).
    { eapply notin_fv_ct_open_tt.
      eapply wf_typ_notin_fv_ct.
      apply H0.
      simpl.
      assert (x <> y) by (clear - Fr; fsetdec).
      clear Fr.
      fsetdec.
    }
    clear - H1 H2.
    fsetdec.
}
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

Lemma wf_typ_in_notin_fv_ct : forall x E T,
  wf_typ_in E T ->
  x `~in`A dom E ->
  x `~in`A fv_ct T
with wf_pretyp_in_notin_fv_cpt : forall x E P,
  wf_pretyp_in E P ->
  x `~in`A dom E ->
  x `~in`A fv_cpt P.
Proof with eauto*.
{ intros * WfT NotIn.
  eapply wf_typ_notin_fv_ct with (E := E) (Ap := dom E) (Am := dom E)...
}
{ intros * WfP NotIn.
  eapply wf_pretyp_notin_fv_cpt with (E := E) (Ap := dom E) (Am := dom E)...
}
Qed.

(*
Lemma typing_of_var_comes_from_binds : forall E (x : atom) T,
  typing E x T ->
  exists S, binds x (bind_typ S) E /\ sub E S T.
Proof with eauto using sub_reflexivity, sub_transitivity.
  intros * Typ.
  destruct (typing_regular _ _ _ Typ) as [_ [_ WfT]].
  dependent induction Typ.
  - Case "typing_var_tvar".
    exists X; split...
  - Case "typing_var".
    exists (typ_capt C P); split...
    assert (WfC : wf_cset_in E C).
    { enough (WfCP : wf_typ_in E (typ_capt C P)) by (inversion WfCP; eauto* ).
      applys wf_env_binds_typ_implies_wf_typ H H0.
    }
    apply sub_capt.
    + inversion WfC; subst.
      admit.
    + eapply sub_pre_reflexivity...
      inversion WfT...
      all: clear; fsetdec.
  - Case "typing_sub".
    destruct (IHTyp x) as [R [x_binds_R sub_R]]...
    exists R; split.
    + apply x_binds_R.
    + apply sub_transitivity with (Q := S)...
Admitted.
*)

(* TODO: move to infrastructure *)
Lemma notin_open_ve_rec_fv_ve : forall k y z C e,
  y `notin` (fv_ve e `union` singleton z) ->
  y `notin` fv_ve (open_ve_rec k z C e).
Proof with eauto*.
  intros * y_notin_e_z.
  generalize dependent k.
  induction e; intros k; simpl in *;
  repeat match goal with
  | v : var |- _ =>
      destruct v; simpl in *; eauto*;
      destruct (k === n); eauto*
  | |- y `notin` (_ `union` _) => apply notin_union
  | IH : y `notin` _ -> forall k, _ |- _ => apply IH; eauto*
  end.
Qed.

Lemma notin_open_te_rec_fv_ve : forall k y z e,
  y `notin` (fv_ve e `union` singleton z) ->
  y `notin` fv_ve (open_te_rec k z e).
Proof with eauto*.
  intros * y_notin_e_z.
  generalize dependent k.
  induction e; intros k; simpl in *;
  repeat match goal with
  | v : var |- _ =>
      destruct v; simpl in *; eauto*;
      destruct (k === n); eauto*
  | |- y `notin` (_ `union` _) => apply notin_union
  | IH : y `notin` _ -> forall k, _ |- _ => apply IH; eauto*
  end.
Qed.

Lemma sub_implies_subcapt_cv : forall E S T,
  sub E S T ->
  subcapt E (cv S) (cv T).
Proof with eauto*.
  intros * Sub.
  induction Sub; simpl.
  - apply subcapt_reflexivity with (A := dom E)...
    constructor.
    + intros x xIn.
      assert (x = X) by fsetdec; subst; clear xIn.
      inversion H0; subst.
      exists U.
      apply bound_sub, H2.
    + inversion H0; subst.
      fsetdec.
  - eapply subcapt_tvar with (T := U)...
  - assumption.
Qed.

Lemma binds_wf : forall E x T,
  wf_env E ->
  binds x (bind_typ T) E ->
  wf_typ E (dom E `\`A x) (dom E `\`A x) T.
Proof with eauto*.
  intros * WfE Binds.
  induction WfE; simpl.
  - inversion Binds.
  - rewrite_env (empty ++ [(X, bind_sub T0)] ++ E).
    assert (x <> X).
    { inversion Binds.
      destruct (x == X)... }
    replace (({X}A `u`A dom E) `\`A x) with ((dom E `\`A x) `u`A {X}A) by fsetdec.
    apply wf_typ_weakening with (Ap := dom E `\`A x) (Am := dom E `\`A x).
    + apply IHWfE.
      inversion Binds.
      destruct (x == X)...
    + apply ok_cons...
    + fsetdec.
    + fsetdec.
  - inversion Binds.
    destruct (x == x0); subst.
    + inversion H2; subst.
      replace (({x0}A `u`A dom E) `\`A x0) with (dom E) by fsetdec.
      rewrite_env (empty ++ [(x0, bind_typ T)] ++ E).
      apply wf_typ_weakening with (Ap := dom E) (Am := dom E)...
      apply ok_cons...
    + rewrite_env (empty ++ [(x0, bind_typ T0)] ++ E).
      replace (({x0}A `u`A dom E) `\`A x) with ((dom E `\`A x) `u`A {x0}A) by fsetdec.
      apply wf_typ_weakening with (Ap := dom E `\`A x) (Am := dom E `\`A x).
      * apply IHWfE...
      * apply ok_cons...
      * fsetdec.
      * fsetdec.
Qed.

Lemma wf_cset_notin_fvars_atoms : forall E Ap x C,
  wf_cset E Ap C ->
  x `~in`A Ap ->
  x `~in`A (`cset_fvars` C).
Proof with eauto*.
  intros * WfC NotIn.
  inversion WfC; subst...
Qed.

Lemma wf_typ_notin_cv : forall E Ap Am x T,
  wf_typ E Ap Am T ->
  x `~in`A Ap ->
  x `~in`A (`cset_fvars` (cv T)).
Proof with eauto*.
  intros * WfT NotIn.
  induction WfT; simpl...
  apply wf_cset_notin_fvars_atoms with (E := E) (Ap := Ap)...
Qed.

(*
Lemma subcapt_notin_fvars : forall E C D x,
  wf_env E ->
  subcapt E C D ->
  x `~in`A (`cset_fvars` D) ->
  `* in` D \/ x `~in`A (`cset_fvars` C).
Proof with eauto*.
  intros * WfE Subcapt NotIn.
  induction Subcapt; subst; simpl in *.
  - left...
  - right...
  - left...
  - destruct (IHSubcapt WfE NotIn).
    + left...
    + right.
      enough (x <> x0) by fsetdec.
      intros eq; subst.
      assert (WfT : wf_typ E (dom E `\`A x0) (dom E `\`A x0) T) by (applys binds_wf WfE H; eauto* ).
      assert ()
      

Lemma sub_notin_fv_ct : forall E S T x,
  sub E S T ->
  x `~in`A fv_ct T ->
  x `~in`A fv_ct S
with sub_pre_notin_fv_ctp : forall E P Q x,
  sub_pre E P Q ->
  x `~in`A fv_cpt P ->
  x `~in`A fv_cpt Q.
Proof with eauto*.
{ intros * Sub NotIn.
  induction Sub; simpl in *.
  - apply notin_empty.
  - apply notin_empty.
  - apply notin_union.
    +  
}
{ intros * Sub NotIn.
  Guarded.

}
*)

Lemma typing_strengthening : forall F E x U e T,
  x `~in`A (fv_cctx F `u`A fv_ct T `u`A fv_ve e) ->
  typing (F ++ [(x, bind_typ U)] ++ E) e T ->
  typing (F ++ E) e T.
Proof with eauto*.
  intros * NotIn Typ.
  assert (x `~in`A (dom E `u`A dom F `u`A fv_cctx F `u`A fv_ct T `u`A fv_ve e)).
  { assert (WfEnv : wf_env (F ++ [(x, bind_typ U)] ++ E)) by applys typing_regular Typ.
    assert (OkEnv : ok (F ++ [(x, bind_typ U)] ++ E)) by (apply ok_from_wf_env; assumption).
    enough (x `~in`A (dom E `u`A dom F)) by (clear - H NotIn; fsetdec).
    clear NotIn Typ WfEnv.
    dependent induction OkEnv; induction F; inversion x; subst.
    - fsetdec.
    - rewrite dom_concat in H.
      simpl in *.
      assert (x1 <> x0) by (clear - H; fsetdec).
      enough (x1 `~in`A (dom E `u`A dom F)) by fsetdec.
      eapply IHOkEnv...
  } 
  clear NotIn; rename H into NotIn.
  dependent induction Typ; simpl in NotIn.
  - Case "typing_var_tvar".
    assert (x <> x0) by (clear - NotIn; fsetdec).
    apply typing_var_tvar.
    + apply wf_env_strengthening_typ with (x := x) (T := U)...
    + apply binds_remove_mid_cons with (y := x) (b := bind_typ U)...
  - Case "typing_var".
    assert (x <> x0) by (clear - NotIn; fsetdec).
    apply typing_var with (C := C).
    + apply wf_env_strengthening_typ with (x := x) (T := U)...
    + apply binds_remove_mid_cons with (y := x) (b := bind_typ U)...
  - Case "typing_abs".
    pick fresh y and apply typing_abs.
    + unfold wf_typ_in.
      apply wf_typ_in_strengthen_typ with (x := x) (U := U).
      * clear - NotIn; fsetdec.
      * apply H.
    + rewrite_env (([(y, bind_typ V)] ++ F) ++ E).
      replace (dom (F ++ E) `u`A {y}A) with ((dom (F ++ [(x, bind_typ U)] ++ E) `u`A {y}A) `\`A x).
      replace (dom (F ++ E)) with (dom (F ++ [(x, bind_typ U)] ++ E) `\`A x).
      eapply wf_typ_strengthen_typ.
      * rewrite dom_concat; simpl.
        assert (x <> y) by (clear - Fr; fsetdec).
        clear - NotIn H3.
        repeat apply notin_union.
        -- fsetdec.
        -- fsetdec.
        -- fsetdec.
        -- eapply notin_open_ct_rec_fv_ct...
      * apply H0.
        clear - Fr; fsetdec.
      * repeat rewrite dom_concat.
        clear - NotIn.
        notin_simpl; simpl.
        clear - H H1.
        fsetdec.
      * repeat rewrite dom_concat.
        assert (x <> y) by (clear - Fr; fsetdec).
        clear - NotIn H3.
        notin_simpl; simpl.
        clear - H H3 H1.
        fsetdec.
    + rewrite_env (([(y, bind_typ V)] ++ F) ++ E).
      apply H2 with (x0 := y) (x1 := x) (U0 := U).
      * clear - Fr; fsetdec.
      * reflexivity.
      * repeat rewrite dom_concat.
        assert (x <> y) by (clear - Fr; fsetdec).
        clear - NotIn H3.
        notin_simpl; simpl.
        repeat apply notin_union.
        -- apply H.
        -- apply notin_singleton, H3.
        -- apply notin_empty.
        -- apply H1.
        -- apply H2.
        -- apply H0.
        -- apply notin_open_ct_rec_fv_ct.
           clear - H3 H7; fsetdec.
        -- apply notin_open_ve_rec_fv_ve.
           clear - H5 H3; fsetdec.
  - Case "typing_app".
    apply typing_app with (T1 := T1) (Cf := Cf).
    + apply IHTyp1 with (x0 := x) (U0 := U).
      reflexivity.
      simpl.
      assert (WfFE : wf_env (F ++ E)).
      { apply wf_env_strengthening_typ with (x := x) (T := U)...
        applys typing_regular Typ1.
      }
      assert (exists Cf', subcapt (F ++ E) Cf' Cf /\ x `~in`A (`cset_fvars` Cf')).
      { eremember (typ_capt Cf (typ_arrow T1 T2)) as TFun.
        assert (Sub : sub (F ++ E) TFun (typ_capt Cf (typ_arrow T1 T2))).
        { subst.
          eapply sub_reflexivity with (Ap := dom (F ++ E)) (Am := dom (F ++ E))...
          apply wf_typ_in_strengthen_typ with (x := x) (U := U).
          admit.
          admit.
        }
        clear - NotIn Sub Typ1.
        generalize dependent Sub.
        dependent induction Typ1.
        - intros Sub.
          exists (`cset_fvar` f).
          split...
          eapply subcapt_var with (T := X).
          + apply binds_remove_mid_cons in H0...
          + eapply subcapt_tvar.
            * admit.
            * admit.  
        - exists (`cset_fvar` f).
          split...
          inversion Sub; subst...
        - intros Sub.
          assert (Sub' : sub (F ++ E) S T).
          { eapply sub_strengthening with (x := x) (U := U).
            - repeat apply notin_union.
              + clear - NotIn; fsetdec.
              + admit.
              + assert (wf_typ_in (F ++ E) T) by applys sub_regular Sub.
                apply wf_typ_notin_fv_ct with (E := F ++ E) (Ap := dom (F ++ E)) (Am := dom (F ++ E))...
            - assumption.
          }
          admit. 
          (* eapply IHTyp1 with (F0 := F) (E0 := E)... *)
      }
      assert (WfCf : wf_cset_in (F ++ [(x, bind_typ U)] ++ E) Cf).
      { enough (WfCapt : wf_typ_in (F ++ [(x, bind_typ U)] ++ E) (typ_capt Cf (typ_arrow T1 T2))) by (inversion WfCapt; eauto* ).
        applys typing_regular Typ1.
      }
      inversion WfCf; subst.
      clear - NotIn H0.
      repeat rewrite dom_concat in H0.
      simpl in H0 |- *.
      repeat apply notin_union...
      * notin_simpl.
        admit.
      * admit.
      * eapply notin_fv_ct_open_ct with (C := `cset_fvar` x0)...
    + apply IHTyp2 with (x1 := x) (U0 := U).
      reflexivity.
      clear - NotIn.
      simpl.
      repeat apply notin_union...
      admit.
  - Case "typing_let".
    pick fresh y and apply typing_let.
    + apply IHTyp with (x0 := x) (U0 := U).
      reflexivity.
      repeat apply notin_union...
      admit.  
    + rewrite_env (([(y, bind_typ T1)] ++ F) ++ E).
      apply H0 with (x0 := y) (x1 := x) (U0 := U).
      * clear - Fr; fsetdec.
      * reflexivity.
      * repeat rewrite dom_concat.
        assert (x <> y) by (clear - Fr; fsetdec).
        clear - NotIn H1.
        notin_simpl; simpl.
        repeat apply notin_union.
        -- apply H.
        -- apply notin_singleton, H1.
        -- apply notin_empty.
        -- apply H2.
        -- admit.
        -- apply H0.
        -- apply H3.
        -- apply notin_open_ve_rec_fv_ve.
           clear - H6 H1; fsetdec.
  - Case "typing_tabs".
    pick fresh Y and apply typing_tabs.
    + apply wf_typ_in_strengthen_typ with (x := x) (U := U).
      * clear - NotIn; fsetdec.
      * assumption.
    + rewrite_env (([(Y, bind_sub V)] ++ F) ++ E).
      replace (dom (F ++ E)) with (dom (F ++ [(x, bind_typ U)] ++ E) `\`A x).
      eapply wf_typ_strengthen_typ.
      * rewrite dom_concat; simpl.
        assert (x <> Y) by (clear - Fr; fsetdec).
        clear - NotIn H3.
        repeat apply notin_union.
        -- fsetdec.
        -- fsetdec.
        -- fsetdec.
        -- eapply notin_open_tt_rec_fv_ct...
      * apply H0.
        clear - Fr; fsetdec.
      * repeat rewrite dom_concat.
        clear - NotIn.
        notin_simpl; simpl.
        clear - H H1.
        fsetdec.
    + rewrite_env (([(Y, bind_sub V)] ++ F) ++ E).
      apply H2 with (X := Y) (x0 := x) (U0 := U).
      * clear - Fr; fsetdec.
      * reflexivity.
      * repeat rewrite dom_concat.
        assert (x <> Y) by (clear - Fr; fsetdec).
        clear - NotIn H3.
        notin_simpl; simpl.
        repeat apply notin_union.
        -- apply H.
        -- apply notin_singleton, H3.
        -- apply notin_empty.
        -- apply H1.
        -- apply H2.
        -- apply H0.
        -- apply notin_open_tt_rec_fv_ct.
           simpl.
           clear - H3 H7; fsetdec.
        -- apply notin_open_te_rec_fv_ve.
           clear - H5 H3; fsetdec.
  - Case "typing_tapp".
    apply typing_tapp with (C := C) (T1 := T1).
    + apply IHTyp with (x1 := x) (U0 := U).
      reflexivity.
      assert (WfC : wf_cset_in (F ++ [(x, bind_typ U)] ++ E) C).
      { enough (WfCapt : wf_typ_in (F ++ [(x, bind_typ U)] ++ E) (typ_capt C (typ_all T1 T2))) by (inversion WfCapt; eauto* ).
        applys typing_regular Typ.
      }
      inversion WfC; subst.
      clear - NotIn H1.
      repeat rewrite dom_concat in H1.
      simpl in H1 |- *.
      repeat apply notin_union.
      * fsetdec.
      * fsetdec.
      * fsetdec.
      * admit.
      * admit.
      * eapply notin_fv_ct_open_tt with (U := T)...
      * fsetdec.
    + apply sub_strengthening with (x := x) (U := U).
      2: assumption.
      clear - NotIn.
      repeat apply notin_union.
      * fsetdec.
      * admit.
      * admit.
  - Case "typing_sub".
    apply typing_sub with (S := S).
    + apply IHTyp with (x0 := x) (U0 := U).
      reflexivity.
      repeat apply notin_union.
      * fsetdec.
      * fsetdec.
      * fsetdec.
      * admit.
      * fsetdec.
    + apply sub_strengthening with (x := x) (U := U).
      2: assumption.
      repeat apply notin_union.
      * fsetdec.
      * admit.
      * fsetdec.
Admitted.

Lemma typing_var_inversion : forall E (x : atom) T,
  typing E x T ->
     (exists C P, binds x (bind_typ (typ_capt C P)) E /\ sub E (typ_capt (`cset_fvar` x) P) T)
  \/ (exists X : atom, binds x (bind_typ X) E /\ sub E X T).
Proof with eauto*.
  intros * Typ.
  dependent induction Typ.
  - Case "typing_var_tvar".
    right.
    exists X.
    split...
    apply sub_refl_tvar...
    apply wf_env_bound_implies_wf_typ with (x := x)...
  - Case "typing_capt".
    left.
    exists C, P.
    split...
    apply sub_reflexivity with (Ap := dom E) (Am := dom E)...
    apply wf_typ_capt.
    + apply wf_concrete_cset.
      * intros y yIn; assert (y = x) by (clear - yIn; fsetdec); subst...
      * enough (x `in`A dom E) by fsetdec.
        eapply binds_In... 
    + enough (WfCP : wf_typ_in E (typ_capt C P)) by (inversion WfCP; eauto*).
      apply wf_env_bound_implies_wf_typ with (x := x)...
  - Case "typing_sub".
    destruct (IHTyp x eq_refl) as [[C [P [xBinds Sub]]] | [X [xBinds Sub]]].
    + left.
      exists C, P.
      split...
      apply sub_transitivity with (Q := S)...
    + right.
      exists X.
      split...
      apply sub_transitivity with (Q := S)...
Qed.

Lemma sub_capt_inversion : forall E C P T,
  sub E (typ_capt C P) T ->
  exists D Q, T = typ_capt D Q
           /\ subcapt E C D
           /\ sub_pre E P Q.
Proof with eauto*.
  intros * Sub; inversion Sub...
Qed.

Inductive binds_sub_trans : atom -> cap -> pretyp -> env -> Prop :=
  | binds_sub_trans_concrete : forall E X C P,
      binds X (bind_sub (typ_capt C P)) E ->
      binds_sub_trans X C P E
  | binds_sub_trans_indirect : forall E (X Y : atom) C P,
      binds X (bind_sub Y) E ->
      binds_sub_trans Y C P E ->
      binds_sub_trans X C P E.

Inductive binds_typ_trans : atom -> cap -> pretyp -> env -> Prop :=
  | binds_typ_trans_concrete : forall E x C P,
      binds x (bind_typ (typ_capt C P)) E ->
      binds_typ_trans x C P E
  | binds_typ_trans_indirect : forall E (x X : atom) C P,
      binds x (bind_typ X) E ->
      binds_sub_trans X C P E ->
      binds_typ_trans x C P E.

Hint Constructors binds_sub_trans binds_typ_trans : core.

Lemma binds_sub_trans_weakening : forall G F E X C P,
  ok (G ++ F ++ E) ->
  binds_sub_trans X C P (G ++ E) ->
  binds_sub_trans X C P (G ++ F ++ E).
Proof with eauto*.
  intros * OkGFE Binds.
  dependent induction Binds...
Qed.

(*
Lemma sub_var_capt_inversion : forall E (X : atom) C P,
  sub E X (typ_capt C P) ->
  exists D Q, binds_sub_trans X D Q E
           /\ subcapt E D C
           /\ sub_pre E Q P.
Proof with eauto*.
  intros * Sub.
  assert (WfEnv : wf_env E) by applys sub_regular Sub.
  generalize dependent X.
  induction WfEnv; intros X0 Sub; inversion Sub; subst.
  - inversion H0.
  - destruct (X0 == X); subst.
    + inversion H2; subst.
      destruct (X == X); try (contradict n; reflexivity).
      inversion H3; subst.
      clear e H3 H2.
      admit.
    + 
*)

(*
Lemma typing_var_capt_inversion : forall E (x : atom) C P,
  typing E x (typ_capt C P) ->
  exists D Q, binds x (bind_typ (typ_capt D Q)) E
           /\ subcapt E (`cset_fvar` x) C
           /\ sub_pre E P Q.
Proof with eauto*.
  intros * Typ.
  dependent induction Typ.
  - exists C0, P.
    repeat split...
    + apply subcapt_reflexivity with (A := dom E)...
      econstructor.
      * intros z zIn; assert (z = x) by (clear - zIn; fsetdec); subst...
      * enough (x `in`A dom E) by fsetdec.
        apply binds_In with (a := bind_typ (typ_capt C0 P))...
    + apply sub_pre_reflexivity with (Ap := dom E) (Am := dom E)...
      enough (WfC0P : wf_typ_in E (typ_capt C0 P)) by (inversion WfC0P; eauto* ).
      apply wf_env_bound_implies_wf_typ with (x := x)...
  - 
  eremember (typ_capt C P) as T.
  assert (Sub : sub E T (typ_capt C P)).
  { subst; apply sub_reflexivity with (Ap := dom E) (Am := dom E)...
    applys typing_regular Typ.
  }
  clear HeqT.
  dependent induction Typ.
  - Case "typing_var_tvar".
    exists C, P.
    repeat split...
    + apply binds_typ_trans_indirect with (X := X)...
      apply binds_sub_trans_concrete.
  - exists C0, P.
    repeat split...
    + apply subcapt_reflexivity with (A := dom E)...
      constructor.
      * intros z zIn; assert (z = x) by (clear - zIn; fsetdec); subst; clear zIn...
      * enough (x `in`A dom E) by fsetdec; apply binds_In with (a := bind_typ (typ_capt C0 P))...
    + apply sub_pre_reflexivity with (Ap := dom E) (Am := dom E)...
      enough (WfC0P : wf_typ_in E (typ_capt C0 P)) by (inversion WfC0P; eauto* ).
      apply wf_env_bound_implies_wf_typ with (x := x)...
  - 
*)

(*
Lemma typing_var_induction : forall E (x : atom) T,
  typing E x T ->
  (exists P, sub E (typ_capt (`cset_fvar` x) P) T).
Proof with eauto*.
  intros * Typ.
  dependent induction Typ.
  -  
*)

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

Lemma subcapt_binds : forall x C P E D,
  wf_env E ->
  wf_cset_in E C ->
  wf_pretyp_in E P ->
  x `~in`A (`cset_fvars` D) ->
  subcapt ([(x, bind_typ (typ_capt C P))] ++ E) (`cset_fvar` x) D ->
  subcapt E C D.
Proof with eauto*.
  intros * WfE WfC WfP NotIn Sub.
  dependent induction Sub.
  - Case "subcapt_universal".
    apply subcapt_universal...
    apply wf_concrete_cset.
    + intros z zIn.
      inversion H; subst.
      destruct (H5 z ltac:(fsetdec)) as [T [B|B]]; binds_cases B...
    + inversion H; subst.
      rewrite dom_concat in H6; simpl in H6.
      fsetdec.
  - Case "subcapt_in".
    inversion WfC; subst.
    admit.
    (* eapply subcapt_set.
    assert (x0 = x1) by (apply singleton_set_eq, x); subst; clear x H1.
    apply subcapt_transitivity with (C2 := `cset_fvar` x1)... *)
  - Case "subcapt_in_univ".
    admit.
  - Case "subcapt_var".
    admit.
  - Case "subcapt_set".
    admit.
Admitted.

Lemma idk : forall x C P E T, 
  sub ([(x, bind_typ (typ_capt C P))] ++ E) (typ_capt (`cset_fvar` x) P) T ->
  sub E (typ_capt C P) T.
Proof with eauto*.
  intros * Sub.
  assert (WfEnv : wf_env ([(x, bind_typ (typ_capt C P))] ++ E)) by applys sub_regular Sub.
  inversion WfEnv; subst; clear WfEnv.
  inversion H3; subst; clear H3.
  rename H2 into WfE.
  rename H4 into NotIn.
  rename H7 into WfC.
  rename H8 into WfP.
  dependent induction Sub.
  apply sub_capt.
  - admit.
  - admit.
Admitted.

Lemma sub_tvar_inversion : forall E T (X : atom),
  sub E T X ->
  exists Y : atom, T = X \/ binds Y (bind_sub X) E.
Proof with eauto*.
  intros * Sub.
  dependent induction Sub...
  destruct (IHSub X ltac:(reflexivity)) as [Y [Eq | Binds]]; subst.
  - exists X0. right. apply H.
  - exists Y. right. apply Binds.
  Unshelve.
  apply X.
Qed.

Lemma sub_pre_arrow_inversion : forall E T1 T2 P,
  sub_pre E (typ_arrow T1 T2) P ->
  P = typ_top
  \/ (exists S1 S2 L, P = typ_arrow S1 S2
     /\ sub E S1 T1
     /\ (forall x, x `~in`A L ->
           sub ([(x, bind_typ S1)] ++ E)
               (open_ct T2 (`cset_fvar` x))
               (open_ct S2 (`cset_fvar` x)))).
Proof with eauto*.
  intros * Sub.
  dependent induction Sub...
  right.
  exists T0, T3, L.
  repeat split...
Qed.

Lemma sub_capt_arrow_inversion : forall E C T1 T2 T,
  sub E (typ_capt C (typ_arrow T1 T2)) T ->
  exists D, T = typ_capt D typ_top
  \/ (exists S1 S2 L, T = typ_capt D (typ_arrow S1 S2)
     /\ subcapt E C D
     /\ sub E S1 T1
     /\ (forall x, x `~in`A L ->
          sub ([(x, bind_typ S1)] ++ E)
              (open_ct T2 (`cset_fvar` x))
              (open_ct S2 (`cset_fvar` x)))).
Proof with eauto*.
  intros * Sub.
  dependent induction Sub.
  destruct (sub_pre_arrow_inversion _ _ _ _ H0) as [Eq | [S1 [S2 [L [Eq [S1SubT1 T2SubS2]]]]]]; subst.
  - exists C2...
  - exists C2.
    right.
    exists S1, S2.
    repeat split...
Qed.

Lemma typing_abs_implies_sub_arrow : forall E U e T,
  typing E (exp_abs U e) T ->
  exists T1 T2, typing E (exp_abs U e) (typ_capt (free_for_cv e) (typ_arrow T1 T2))
             /\ sub E (typ_capt (free_for_cv e) (typ_arrow T1 T2)) T.
Proof with eauto*.
  intros * Typ.
  assert (WfEnv : wf_env E) by applys typing_regular Typ.
  assert (WfCV : wf_cset_in E (free_for_cv (exp_abs U e))).
  { eapply typing_cv... }
  simpl in WfCV.
  dependent induction Typ.
  - exists U, T1.
    split...
    apply sub_reflexivity with (Ap := dom E) (Am := dom E)...
  - destruct (IHTyp U e ltac:(reflexivity) WfEnv WfCV) as [T1 [T2 Sub]].
    exists T1, T2.
    split...
    apply sub_transitivity with (Q := S)...
Qed.

(*
Lemma typing_abs_all_impossible : forall E U e C T1 T2,
  ~ typing E (exp_abs U e) (typ_capt C (typ_all T1 T2)).
Proof with eauto*.
  intros * Typ.
  dependent induction Typ.

Lemma typing_val_inversion_aux : forall E v T,
  value v ->
  typing E v T ->
  exists C P, T = typ_capt C P
  /\ (P = typ_top
   \/ (exists T1 T2, P = typ_arrow T1 T2)
   \/ (exists T1 T2, P = typ_all T1 T2)).
Proof with eauto*.
  intros * Val Typ.
  assert (WfEnv : wf_env E) by applys typing_regular Typ.
  assert (WfCV : wf_cset_in E (free_for_cv v)) by applys typing_cv Typ.
  inversion Val; subst.
  - dependent induction Typ...
    + exists (free_for_cv e1), (typ_arrow T0 T1).
      repeat split...
    + destruct (IHTyp T0 e1 ltac:(reflexivity) Val WfEnv WfCV H0) as [C [P [EqS [EqP | [[T2 [T3 EqP]] | [T2 [T3 EqP]]]]]]]; subst.
      * inversion H; subst.
        inversion H6; subst.
        exists C2, typ_top...
      * inversion H; subst.
        inversion H6; subst.
        -- exists C2, typ_top...
        -- exists C2, (typ_arrow T1 T4)...
      * inversion Typ; subst.
        inversion H6; subst.
        -- exists  
  - dependent induction Typ...
    exists (free_for_cv e1), (typ_all T0 T1)...

Lemma typing_val_inversion : forall E v T,
  value v ->
  typing E v T ->
  exists C P, typing E v (typ_capt C P)
  /\ sub E T (typ_capt C P)
  /\ ((exists T1 T2, P = typ_arrow T1 T2)
   \/ (exists T1 T2, P = typ_all T1 T2)).
Proof with eauto*.
  intros * Val Typ.
  assert (WfEnv : wf_env E) by applys typing_regular Typ.
  assert (WfCV : wf_cset_in E (free_for_cv v)) by applys typing_cv Typ.
  inversion Val; subst.
  - dependent induction Typ...
    + exists (free_for_cv e1), (typ_arrow T0 T1).
      repeat split...
      apply sub_reflexivity with (Ap := dom E) (Am := dom E)...
    + destruct (IHTyp T0 e1 ltac:(reflexivity) Val WfEnv WfCV H0) as [C [P [Typ' [Sub' [[T2 [T3 Eq]] | [T2 [T3 Eq]]]]]]]; subst.
      * repeat eexists.
  - dependent induction Typ...
    exists (free_for_cv e1), (typ_all T0 T1)...
Qed.
*)

Lemma typing_var_concrete_tvar_impossible : forall E x C P (X : atom),
  binds x (bind_typ (typ_capt C P)) E ->
  ~ typing E x X.
Proof with eauto*.
  intros * Binds Typ.
  dependent induction Typ...
  dependent induction H...
Qed.

Lemma typing_lift_cpt_to_capt : forall E e C P,
  typing E e (typ_capt C P) ->
  exists Q, typing E e (typ_capt (C `u` cset_set (fv_cpt P) {}N false) Q)
         /\ sub_pre E Q P
         /\ (fv_cpt Q) `disjoint` (fv_ve e).
Proof with eauto*.
  (* REVIEW: is this true? *)
Abort.

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

Lemma binds_typ_implies_binds_capt : forall E x T,
  no_type_bindings E ->
  wf_env E ->
  binds x (bind_typ T) E ->
  exists C P, T = typ_capt C P.
Proof with eauto*.
  intros * NTB WfEnv Binds.
  destruct T.
  - exists c, p...
  - enough (Wfn : wf_typ_in E n) by inversion Wfn.
    apply wf_env_bound_implies_wf_typ with (x := x)...
  - assert (Wfa : wf_typ_in E a) by (apply wf_env_bound_implies_wf_typ with (x := x); auto).
    inversion Wfa; subst.
    contradict H0.
    apply (NTB a U).
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

Lemma stores_preserves_typing : forall S E x v v_value C P,
  store_typing S E ->
  stores S x v v_value ->
  typing E x (typ_capt C P) ->
  exists D Q, typing E v (typ_capt (free_for_cv v) Q)
         /\ binds x (bind_typ (typ_capt D Q)) E
         /\ subcapt E (free_for_cv v) D
         /\ sub_pre E Q P.
Proof with eauto*.
  intros * StoreTyp xStores Typ.
  induction StoreTyp; inversion xStores.
  destruct (x == x0); inversion H2; subst.
  - Case "x = x0".
    destruct (values_have_precise_captures _ _ _ v_value H) as [Q [TypQ QSubT]].
    assert (WfEnv : wf_env ([(x0, bind_typ T)] ++ E)) by applys typing_regular Typ.
    assert (NTB : no_type_bindings E) by applys store_typing_no_type_bindings StoreTyp.
    destruct (binds_typ_implies_binds_capt ([(x0, bind_typ T)] ++ E) x0 T (no_type_bindings_cons E x0 T NTB) WfEnv ltac:(apply binds_head; auto)) as [D [R Eq]].
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
      (*
      assert (RSubP : sub_pre ([(x0, bind_typ (typ_capt D R))] ++ E) R P).
      { clear - Typ.
        dependent induction Typ.
        - inversion H0; subst.
          destruct (x0 == x0); try (contradict n; reflexivity).
          inversion H2; subst.
          clear e H2.
          apply sub_pre_reflexivity with (Ap := dom ([(x0, bind_typ (typ_capt C0 P))] ++ E)) (Am := dom ([(x0, bind_typ (typ_capt C0 P))] ++ E))...
          enough (WfC0P : wf_typ_in ([(x0, bind_typ (typ_capt C0 P))] ++ E) (typ_capt C0 P)) by (inversion WfC0P; auto).
          apply wf_env_bound_implies_wf_typ with (x := x0)...
        - inversion H; subst.
          dependent induction H.
          + contradict Typ; eapply typing_var_concrete_tvar_impossible...
          + assert (WfEnv : wf_env ([(x0, bind_typ (typ_capt D R))] ++ E)) by applys typing_regular Typ.
            inversion WfEnv; subst.
            assert (RSubP1 : sub_pre ([(x0, bind_typ (typ_capt D R))] ++ E) R P1) by (eapply IHTyp with (x1 := x0) (C := C1); auto).
            assert (x0 `~in`A fv_cpt P1).
            { eapply wf_pretyp_notin_fv_cpt with (E := E) (Ap := dom E) (Am := dom E).
              - rewrite_env (empty ++ E).
                apply wf_pretyp_in_strengthen_typ with (x := x0) (U := typ_capt D R).
                + csetsimpl.
                  apply notin_union.
                  * admit.
                  * apply H7. 
                + applys sub_pre_regular RSubP1.
              - apply H7.
            }
            apply sub_pre_transitivity with (Q := P1).
            * eapply pretype_from_wf_pretyp.
              applys sub_pre_regular H5.
            * eapply IHTyp with (x1 := x0) (C := C1)...
            * apply wf_typ_notin_fv_ct with (x := x0) in H6; simpl in H6...
      }
      *)
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
           rewrite_env (empty ++ [(x0, bind_typ (typ_capt C0 P))] ++ E).
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
    rewrite_env (empty ++ [(x0, bind_typ T)] ++ E) in Typ.
    apply typing_strengthening in Typ.
    destruct (IHStoreTyp H2 Typ) as [D [Q [Typ' [Binds [vSubD QSubP]]]]].
    + exists D, Q.
      rewrite_env (empty ++ [(x0, bind_typ T)] ++ E).
      repeat split.
      * apply typing_weakening...
        apply wf_env_typ...
        applys typing_regular H.
      * auto.
      * apply subcapt_weakening...
        apply wf_env_typ...
        applys typing_regular H.
      * apply sub_pre_weakening...
        apply wf_env_typ...
        applys typing_regular H.
    + csetsimpl.
      repeat apply notin_union...
      * admit.
      * admit.
Admitted.

Lemma eval_typing_regular : forall E K T U,
  eval_typing E K T U ->
  wf_env E /\ wf_typ_in E T /\ wf_typ_in E U.
Proof with eauto*.
  intros * EvalTyp.
  induction EvalTyp; repeat split...
  pick fresh x and specialize H.
  destruct (typing_regular _ _ _ H) as [wf_xTE _].
  inversion wf_xTE; subst...
Qed.

(*
Lemma eval_typing_contravariant : forall E K S T U,
  sub Γ S T ->
  eval_typing E K T U ->
  eval_typing E K S U.
Proof with eauto*.
  intros *.
  intros subT eval_typ.
  generalize dependent T'.
  induction eval_typ; intros T' subT.
  - apply typing_eval_nil...
    apply sub_transitivity with (Q := T)...
  - eapply typing_eval_cons with (L := L) (U := U)...
    intros x x_fresh.
    rewrite_env (empty ++ [(x, bind_typ T')] ++ Γ).
    eapply typing_specializing...
Qed.
*)

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

Lemma wf_capt_from_typing_var : forall E x C P,
  wf_env E ->
  binds x (bind_typ (typ_capt C P)) E ->
  wf_cset_in E C /\ wf_pretyp_in E P.
Proof with eauto*.
  intros * WfEnv xBinds.
  induction WfEnv.
  - Case "wf_env_empty".
    inversion xBinds.
  - Case "wf_env_sub".
    rewrite_env (empty ++ [(X, bind_sub T)] ++ E).
    assert (binds x (bind_typ (typ_capt C P)) E).
    { inversion xBinds.
      destruct_if in H2...
    }
    destruct (IHWfEnv H1) as [WfC WfP].
    split.
    + apply wf_cset_in_weakening...
      apply ok_cons...
    + apply wf_pretyp_in_weakening...
      apply ok_cons...
  - Case "wf_env_typ".
    destruct (x == x0); subst.
    + SCase "x = x0".
      inversion xBinds.
      destruct (x0 == x0); try (contradict n; reflexivity).
      inversion H2; subst.
      rewrite_env (empty ++ [(x0, bind_typ (typ_capt C P))] ++ E).
      split.
      * apply wf_cset_in_weakening.
        inversion H; subst...
        apply ok_cons...
      * apply wf_pretyp_in_weakening...
        apply ok_cons...
    + SCase "x <> x0".
      rewrite_env (empty ++ [(x0, bind_typ T)] ++ E).
      assert (binds x (bind_typ (typ_capt C P)) E).
      { inversion xBinds.
        destruct_if in H2...
      }
      destruct (IHWfEnv H1) as [WfC WfP].
      split.
      * apply wf_cset_in_weakening...
        apply ok_cons...
      * apply wf_pretyp_in_weakening...
        apply ok_cons...
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

Lemma binds_sub_arrow_implies_store_abs : forall S E C TFun T1 T2 f,
  store_typing S E ->
  binds f (bind_typ TFun) E ->
  sub E TFun (typ_capt C (typ_arrow T1 T2)) ->
  exists U e (abs_value : value (exp_abs U e)), stores S f (exp_abs U e) abs_value /\ sub E T1 U.
Proof with eauto*.
  intros * StoreTyp fBinds Sub.
  eremember (typ_arrow T1 T2) as TFun' eqn:EQ.
  induction StoreTyp; inversion fBinds; inversion EQ; subst.
  destruct (f == x).
  - inversion H2; subst...
    unfold stores.
    unfold binds.
    simpl.
    destruct (x == x); [ clear e | contradict n; reflexivity ].
    inversion v_value; subst.
    + inversion H; subst.
      * exists T, e1, v_value.
        inversion Sub; subst.
        split...
        inversion H13; subst...
      * exists T, e1, v_value.
        split...
        rewrite_env (empty ++ [(x, bind_typ TFun)] ++ E).
        apply sub_weakening.
        -- assert (Typ : typing E (exp_abs T e1) (typ_capt C (typ_arrow T1 T2))).
           { apply typing_sub with (S := TFun)...
             rewrite_env (empty ++ [(x, bind_typ TFun)] ++ E) in Sub.
             apply sub_strengthening in Sub.
             - assumption.
             - simpl.
               repeat apply notin_union.
               + clear; fsetdec.
               + inversion Sub; subst.
                 * clear; fsetdec.
                 * destruct (sub_regular _ _ _ H5) as [_ [_ WfTyp]].
                   eapply wf_typ_in_notin_fv_ct...
               + eapply wf_cset_notin_fvars with (E := E) (A := dom E).
                 * admit. 
                 * apply H0.
               + apply wf_typ_in_notin_fv_ct with (E := E).
                 * admit.
                 * apply H0.
               + apply wf_typ_in_notin_fv_ct with (E := E).
                 * admit.
                 * apply H0.
           }
           applys typing_abs_typ_arrow_implies_sub_param Typ.
        -- apply wf_env_typ...
    + assert (tabs_has_type_T1_arr_T2 : typing E (exp_tabs T e1) (typ_capt C (typ_arrow T1 T2))).
      { apply typing_sub with (S := TFun)...
        rewrite_env (empty ++ [(x, bind_typ TFun)] ++ E) in Sub.
        apply sub_strengthening in Sub.
        - apply Sub.
        - destruct (sub_regular _ _ _ Sub) as [WfEnv [WfTFun WfS]].
          inversion WfEnv; inversion WfS. inversion H16; subst.
          repeat apply notin_union.
          + fsetdec.
          + eapply wf_typ_in_notin_fv_ct...
          + admit.
          + admit.
          + admit. 
      }
      admit.
      (* exfalso; impossible_typing tabs_has_type_T1_arr_T2. *)
  - assert (Sub' : sub E TFun (typ_capt C (typ_arrow T1 T2))).
    { rewrite_env (empty ++ [(x, bind_typ T)] ++ E) in Sub.
      apply sub_strengthening in Sub.
      - apply Sub.
      - repeat apply notin_union.
        + fsetdec.
        + admit.
        + admit.
        + admit.
        + admit.     
    }
    destruct IHStoreTyp as [U [e [abs_value [xv_S_stores_f T1_sub_U]]]]...
    exists U, e, abs_value.
    split.
    + rewrite_env ([(x, store v v_value)] ++ S).
      apply binds_tail.
      * trivial.
      * simpl; fsetdec.
    + rewrite_env (empty ++ [(x, bind_typ T)] ++ E).
      apply sub_weakening...
Admitted.

(*
Lemma subcapt_open_cset : forall E k C D c,
  wf_cset_in E c ->
  subcapt E C D ->
  subcapt E (open_cset k C c) (open_cset k D c).
Proof with eauto*.
  intros * Wfc Subcapt.
  unfold open_cset.
  destruct (subcapt_regular _ _ _ Subcapt) as [WfC WfD].
  inversion WfC; subst; rename H into HC, fvars into fvarsC.
  inversion WfD; subst; rename H into HD, fvars into fvarsD.
  destruct_set_mem k c.
    induction Subcapt.
    + csetsimpl.
      Print open_cset.
      replace (`cset_bvars` c `\`N k) with (`cset_bvars` c).
      apply subcapt_universal.
      * inversion H2; subst.
  - eapply subcapt_reflexivity with (A := dom E)...

Lemma sub_open_ct : forall E T C D,
  wf_env E ->
  wf_typ_in E T ->
  subcapt E C D ->
  sub E (open_ct T C) (open_ct T D)
with sub_pre_open_cpt : forall E P C D,
  wf_env E ->
  wf_pretyp_in E P ->
  subcapt E C D ->
  sub_pre E (open_cpt P C) (open_cpt P D).
Proof with eauto*.
{ intros * WfEnv WfTyp Subcapt.
  induction WfTyp; unfold open_ct; simpl.
  - apply sub_refl_tvar...
    apply wf_typ_var with (U := U)...
    applys binds_In X...
  - apply sub_capt.
     
}
{ intros * Sub.
}
*)

Lemma typing_inv_abs : forall E S1 e1 T,
  typing E (exp_abs S1 e1) T ->
  forall U1 U2 C, sub E T (typ_capt C (typ_arrow U1 U2)) ->
    sub E U1 S1
  /\ exists S2, exists L, forall x, x `notin` L ->
    typing ([(x, bind_typ S1)] ++ E) (open_ve e1 x (`cset_fvar` x)) (open_ct S2 (`cset_fvar` x)) /\
    wf_typ ([(x, bind_typ S1)] ++ E) (dom E `union` singleton x) (dom E) (open_ct U2 (`cset_fvar` x)) /\
  sub ([(x, bind_typ U1)] ++ E) (open_ct S2 (`cset_fvar` x)) (open_ct U2 (`cset_fvar` x)).
Proof with auto.
  intros * Htyp.
  dependent induction Htyp; intros U1 U2 C Hsub.
  - Case "typing_abs".
    inversion Hsub; subst.
    inversion select (sub_pre _ _ _); subst.
    split...
    exists T1.
    exists (L `union` L0).
    intros y ?.
    repeat split.
    + apply H1...
    + rewrite_nil_concat.
      eapply wf_typ_ignores_typ_bindings.
      apply H13...
    + trivial...
  - Case "typing_sub".
    eauto using (sub_transitivity T).
Qed.

(*
Lemma typing_narrowing_typ : forall F z U V E e T,
  sub E U V ->
  typing (F ++ [(z, bind_typ V)] ++ E) e T ->
  typing (F ++ [(z, bind_typ U)] ++ E) e T.
Proof with simpl_env; eauto using wf_typ_narrowing_typ, wf_env_narrowing_typ.
  intros * Sub Typ.
  eremember (F ++ [(z, bind_typ V)] ++ E) as G.
  generalize dependent F.
  induction Typ; intros F EQ; subst.
  - Case "typing_var_tvar".
    binds_cases H0.
    + apply typing_var_tvar.
      * eauto using wf_env_narrowing_typ.
      * apply binds_weaken_at_head.
        apply binds_weaken_at_head.
        eauto.
        apply ok_from_wf_env, wf_env_strengthening with (F := F)...
        apply ok_from_wf_env...
    + inversion H1; subst.
      apply typing_sub with (S := U)...
      * rewrite_env (empty ++ (F ++ [(x, bind_typ U)]) ++ E).
        assert (WfU : wf_typ_in E U) by applys sub_regular Sub.
        inversion WfU; subst.
        -- apply typing_var_tvar...
        -- apply typing_sub with (S := typ_capt (`cset_fvar` x) P).
           ++ apply typing_var with (C := C)...
           ++ apply sub_capt...
              ** eapply subcapt_var with (T := typ_capt C P)...
                 simpl.
                 rewrite_env (empty ++ (F ++ [(x, bind_typ (typ_capt C P))]) ++ E).
                 eapply subcapt_reflexivity with (A := dom (empty ++ (F ++ [(x, bind_typ (typ_capt C P))]) ++ E)).
                 eapply wf_cset_in_weakening...
                 repeat rewrite dom_concat...
                 clear; fsetdec.
              ** rewrite_env (empty ++ (F ++ [(x, bind_typ (typ_capt C P))]) ++ E).
                 eapply sub_pre_reflexivity with (Ap := dom E) (Am := dom E)...
                 rewrite_env (empty ++ (F ++ [(x, bind_typ (typ_capt C P))]) ++ E).
                 eapply wf_pretyp_weakening with (Ap := dom E) (Am := dom E)...
                 all: clear; fsetdec.
      * rewrite_env (empty ++ (F ++ [(x, bind_typ U)]) ++ E).
        apply sub_weakening...
    + apply typing_var_tvar...
  - Case "typing_var".
    binds_cases H0.
    + apply typing_var with (C := C).
      * eauto using wf_env_narrowing_typ.
      * simpl in Fr0.
        assert (x <> z) by (clear - Fr0; fsetdec); clear Fr0.
        apply binds_tail... 
    + inversion H1; subst; clear H1.
      inversion Sub; subst.
      * apply typing_sub with (S := X).
        -- apply typing_var_tvar...
        -- eapply sub_trans_tvar with (U := U0).
           ++ apply binds_tail.
              apply binds_tail.
              apply H0.
              simpl.
              ** enough (X <> x) by fsetdec.
                 intros eq; subst.
                 assert (ok ([(x, bind_typ (typ_capt C P))] ++ E)).
                 { apply wf_env_strengthening in H.
                   apply ok_from_wf_env, H.
                 }
                 inversion H2; subst.
                 assert (x `in`A dom E) by applys binds_In H0.
                 apply (H7 H3).
              ** assert (ok (F ++ E)).
                 { assert (ok (F ++ [(x, bind_typ (typ_capt C P))] ++ E)) by applys ok_from_wf_env H.
                   eapply ok_remove_mid, H2.
                 }
                 assert (X `in`A dom E) by applys binds_In H0.
                 eapply tail_not_in_head with (E := E)...
           ++ admit.
      * apply typing_sub with (S := typ_capt (`cset_fvar` x) P1).
        -- apply typing_var with (C := C1)...
        -- apply sub_capt.
           ++ apply subcapt_reflexivity with (A := dom (F ++ [(x, bind_typ (typ_capt C1 P1))] ++ E)).
              ** apply wf_concrete_cset...
                 --- intros z zIn.
                     assert (z = x) by (clear - zIn; fsetdec); subst; clear zIn.
                     exists (typ_capt C1 P1).
                     apply bound_typ...
                 --- clear; fsetdec.
              ** clear; fsetdec.
           ++ rewrite_env (empty ++ (F ++ [(x, bind_typ (typ_capt C1 P1))]) ++ E).
              apply sub_pre_weakening...
    + assert (WfU : wf_typ_in E U) by applys sub_regular Sub.
      inversion WfU; subst.
      * apply typing_sub with (S := typ_capt (`cset_fvar` x) P).
        -- apply typing_var with (C := C)...
        -- apply sub_capt...
           ++ eapply subcapt_var with (T := typ_capt C P)...
              simpl; simpl_env.
              admit.
           ++ rewrite_env (empty ++ (F ++ [(z, bind_typ X)]) ++ E).
              eapply sub_pre_reflexivity with (Ap := dom (F ++ [(z, bind_typ X)] ++ E)) (Am := dom (F ++ [(z, bind_typ X)] ++ E))...
              rewrite_env (F ++ empty) in H2.
              apply binds_weaken with (F := [(z, bind_typ X)] ++ E) in H2.
              simpl_env in H2.
              eapply wf_env_narrowing_typ with (U := X) in H...
              destruct (wf_capt_from_typing_var _ _ _ _ H H2).
              unfold wf_pretyp_in in H4.
              replace (dom F `u`A {z}A `u`A dom E) with (dom (F ++ [(z, bind_typ X)] ++ E)).
              apply H4.
              repeat rewrite dom_concat; simpl; clear; fsetdec.
              apply ok_from_wf_env...
              all: clear; fsetdec.
      * apply typing_sub with (S := typ_capt (`cset_fvar` x) P0).
        -- apply typing_var with (C := C0)...
           apply binds_tail.
           apply binds_head.
           apply binds_singleton.
  - Case "typing_abs".
    pick fresh x and apply typing_abs.
    rewrite_env (([(x, bind_typ V)] ++ F) ++ [(z, bind_typ P)] ++ E).
    apply H0...
  - Case "typing_tabs".
    pick fresh X and apply typing_tabs.
    rewrite_env (([(X, bind_sub V)] ++ F) ++ [(z, bind_typ P)] ++ E).
    apply H0...
  - Case "typing_tapp".
    apply typing_tapp with (T1 := T1).
    apply IHe_T...
    apply sub_specializing with (Q := Q)...
  - Case "typing_let".
    pick fresh x and apply typing_let...
    rewrite_env (([(x, bind_typ T1)] ++ F) ++ [(z, bind_typ P)] ++ E).
    apply H0...
  - Case "typing_sub".
    apply typing_sub with (S := S)...
    apply sub_specializing with (Q := Q)...
Qed.
*)

(*
Lemma eval_typing_sub : forall E K S T U,
  sub E S T ->
  eval_typing E K T U ->
  eval_typing E K S U.
Proof with eauto*.
  intros *.
  intros Sub EvalTyp.
  generalize dependent S.
  induction EvalTyp; intros S Sub.
  - apply typing_eval_nil...
    apply sub_transitivity with (Q := T)...
  - eapply typing_eval_cons with (L := L) (U := U)...
    intros x x_fresh.
    rewrite_env (empty ++ [(x, bind_typ S)] ++ E).
    eapply typing_narrowing_typ_aux...
    admit.
Admitted.
*)
(*
Lemma typing_arrow_inversion : forall E f C T1 T2,
  typing E f (typ_capt C (typ_arrow T1 T2)) ->
  exists U e L,
    True. *)

Tactic Notation "destructs" constr(E) :=
  destruct ltac:(applys E).
Tactic Notation "destructs" constr(E) "as" simple_intropattern(P) :=
  destruct ltac:(applys E) as P.
Tactic Notation "destructs" constr(E0) constr(A1) :=
  destructs (>> E0 A1).
Tactic Notation "destructs" constr(E0) constr(A1) "as" simple_intropattern(P) :=
  destructs (>> E0 A1) as P.
Tactic Notation "destructs" constr(E0) constr(A1) constr(A2) :=
  destructs (>> E0 A1 A2).
Tactic Notation "destructs" constr(E0) constr(A1) constr(A2) "as" simple_intropattern(P) :=
  destructs (>> E0 A1 A2) as P.
Tactic Notation "destructs" constr(E0) constr(A1) constr(A2) constr(A3) :=
  destructs (>> E0 A1 A2 A3).
Tactic Notation "destructs" constr(E0) constr(A1) constr(A2) constr(A3) "as" simple_intropattern(P) :=
  destructs (>> E0 A1 A2 A3) as P.
Tactic Notation "destructs" constr(E0) constr(A1) constr(A2) constr(A3) constr(A4) "as" simple_intropattern(P) :=
  destructs (>> E0 A1 A2 A3 A4) as P.
Tactic Notation "destructs" constr(E0) constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) "as" simple_intropattern(P) :=
  destructs (>> E0 A1 A2 A3 A4 A5) as P.
Tactic Notation "destructs" constr(E0) constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) constr(A6) "as" simple_intropattern(P) :=
  destructs (>> E0 A1 A2 A3 A4 A5 A6) as P.

Lemma binds_sub_arrow_implies_store_abs' : forall S E C P T1 T2 f,
  store_typing S E ->
  binds f (bind_typ (typ_capt C P)) E ->
  f `~in`A (fv_ct T1 `u`A fv_ct T2) ->
  sub_pre E P (typ_arrow T1 T2) ->
  exists U e (abs_value : value (exp_abs U e)), stores S f (exp_abs U e) abs_value /\ sub E T1 U.
Proof with eauto*.
  intros * StoreTyp fBinds NotIn Sub.
  induction StoreTyp; inversion fBinds; subst.
  destruct (f == x).
  - inversion H2; subst; clear H2.
    unfold stores.
    unfold binds.
    simpl.
    destruct (x == x); [ clear e | contradict n; reflexivity ].
    inversion v_value; subst.
    + inversion H; subst.
      * exists T, e1, v_value.
        inversion Sub; subst.
        split...
      * exists T, e1, v_value.
        split...
        rewrite_env (empty ++ [(x, bind_typ (typ_capt C P))] ++ E).
        apply sub_weakening.
        -- assert (Typ : typing E (exp_abs T e1) (typ_capt C (typ_arrow T1 T2))).
           { apply typing_sub with (S := typ_capt C P)...
             rewrite_env (empty ++ [(x, bind_typ (typ_capt C P))] ++ E) in Sub.
             apply sub_pre_strengthening in Sub.
             - apply sub_capt...
               apply subcapt_reflexivity with (A := dom E)...
             - simpl.
               repeat apply notin_union...
               destruct (sub_regular _ _ _ H3) as [_ [_ WfTyp]].
               eapply wf_pretyp_in_notin_fv_cpt...
           }
           applys typing_abs_typ_arrow_implies_sub_param Typ.
        -- apply wf_env_typ...
    + assert (Typ : typing E (exp_tabs T e1) (typ_capt C (typ_arrow T1 T2))).
      { apply typing_sub with (S := typ_capt C P)...
        rewrite_env (empty ++ [(x, bind_typ (typ_capt C P))] ++ E) in Sub.
        apply sub_pre_strengthening in Sub.
        - apply sub_capt...
          apply subcapt_reflexivity with (A := dom E)...
        - destruct (sub_pre_regular _ _ _ Sub) as [WfEnv [WfTFun WfS]].
          simpl.
          repeat apply notin_union...
          inversion WfEnv; inversion H6; subst.
          eapply wf_pretyp_in_notin_fv_cpt...
      }
      exfalso.
      destructs typing_regular Typ as [WfEnv [_ WfArr]].
      clear - WfEnv WfArr Typ.
      eremember (exp_tabs T e1) as abs.
      eremember (typ_capt C (typ_arrow T1 T2)) as arr.
      assert (Sub : sub E arr (typ_capt C (typ_arrow T1 T2))) by (subst; apply sub_reflexivity with (Ap := dom E) (Am := dom E); eauto* ).
      clear Heqarr.
      induction Typ; inversion Heqabs; subst.
      inversion Sub; inversion H9.
      apply IHTyp...
      apply sub_transitivity with (Q := T0)...
  - assert (Sub' : sub_pre E P (typ_arrow T1 T2)).
    { rewrite_env (empty ++ [(x, bind_typ T)] ++ E) in Sub.
      apply sub_pre_strengthening in Sub.
      - apply Sub.
      - repeat apply notin_union.
        + fsetdec.
        + apply wf_pretyp_in_notin_fv_cpt with (E := E)...
          enough (WfCP : wf_typ_in E (typ_capt C P)) by (inversion WfCP; eauto* ).
          apply wf_env_bound_implies_wf_typ with (x := f)...
        + fold fv_ct.
          admit.
        + fold fv_ct.
          admit.
    }
    destruct IHStoreTyp as [U [e [abs_value [xv_S_stores_f T1_sub_U]]]]...
    exists U, e, abs_value.
    split.
    + rewrite_env ([(x, store v v_value)] ++ S).
      apply binds_tail.
      * trivial.
      * simpl; fsetdec.
    + rewrite_env (empty ++ [(x, bind_typ T)] ++ E).
      apply sub_weakening...
Admitted.

Lemma subst_vv_open_vv : forall x u k y v,
  y <> x ->
  subst_vv x u (open_vv k y v) = open_vv k y (subst_vv x u v).
Proof with eauto*.
  intros * Neq.
  destruct v; simpl.
  - destruct (a == x); simpl...
  - destruct (k === n); simpl...
    destruct (y == x); simpl; subst...
Qed.

Lemma subst_ve_open_ve_rec : forall e x y u c1 c2 k,
  y <> x ->
  capt c1 ->
  subst_ve x u c1 (open_ve_rec k y c2 e) =
    open_ve_rec k y (subst_cset x c1 c2) (subst_ve x u c1 e).
Proof with auto using subst_vv_open_vv, subst_ct_open_ct_rec.
  intros * Neq Capt.
  revert k.
  induction e; intros k; simpl; f_equal...
  Check subst_cset_open_cset_rec.
  Check subst_ct_open_ct_rec.
  admit.
  admit.
  admit.
Admitted.

(*
Lemma subcapt_through_subst_ct : forall E S1 C1 C2 x y,
  wf_env E ->
  y `~in`A dom E ->
  binds x (bind_typ S1) E ->
  subcapt E (open_cset 0 (`cset_fvar` x) C1) C2 ->
  subcapt ([(y, bind_typ S1)] ++ E) (open_cset 0 (`cset_fvar` y) C1) C2.
Proof with eauto*.
  intros * WfEnv NotIn Binds Subcapt.
  dependent induction Subcapt.
  - Case "subcapt_universal".
    apply subcapt_universal.
    + rewrite_env (empty ++ [(y, bind_typ S1)] ++ E).
      apply wf_cset_in_weakening...
      apply ok_cons...
    + inversion H0; subst.
      unfold open_cset in H1 |- *.
      dependent induction C1; simpl in *; simpl_env.
      destruct_set_mem 0 t0.
      * rewrite cset_concrete_union in H1 |- *.
        inversion H1; subst.
        assert (t0 `c`N {0}N).
        { clear - OIn H6.
          intros k kIn.
          destruct (k === 0); subst.
          - clear; fsetdec.
          - assert (k `in`N ({}N `u`N t0 `\`N 0)).
            { apply NatSet.F.union_3.
              apply NatSet.F.remove_2...
            }
            rewrite <- H6 in H.
            exfalso.
            clear - H.
            destruct (NatSetProperties.Dec.F.empty_iff k)...
        }
        clear H6.
        econstructor.
        -- intros z zIn.
           destructs AtomSet.F.union_1 zIn.
           ++ assert (z = y) by (clear - H4; fsetdec); subst...
           ++ destruct (H2 z ltac:(fsetdec)) as [T [Bound | Bound]].
              ** exists T.
                 apply bound_typ, binds_tail...
                 simpl.
                 fsetdec.
              ** exists T.
                 apply bound_sub, binds_tail...
                 simpl.
                 fsetdec.
        -- simpl.
           fsetdec.
      * rewrite <- H1.
        rewrite_env (empty ++ [(y, bind_typ S1)] ++ E).
        apply wf_cset_in_weakening...
        apply ok_cons...
  - Case "subcapt_in".
    inversion H0; subst.
    unfold open_cset in x |- *.
    dependent induction C1; simpl in *; simpl_env.
    destruct_set_mem 0 t0.
    * rewrite cset_concrete_union in x |- *.
      inversion x; subst.
      simpl in x |- *; simpl_env.
      assert (t0 `c`N {0}N).
      { clear - OIn H4.
        intros k kIn.
        destruct (k === 0); subst.
        - clear; fsetdec.
        - assert (k `in`N ({}N `u`N t0 `\`N 0)).
          { apply NatSet.F.union_3.
            apply NatSet.F.remove_2...
          }
          rewrite <- H4 in H.
          exfalso.
          clear - H.
          destruct (NatSetProperties.Dec.F.empty_iff k)...
      }
      clear H4.
      constructor...
      -- rewrite_env (empty ++ [(y, bind_typ S1)] ++ E).
         apply wf_cset_in_weakening...
         apply ok_cons...
      -- intros z zIn.
         destruct (AtomSetProperties.Dec.)
         eapply subcapt_var. 



Lemma sub_through_subst_ct : forall E S1 T2 x y U,
  y `~in`A dom E ->
  binds x (bind_typ S1) E ->
  sub E (open_ct T2 (`cset_fvar` x)) U ->
  sub ([(y, bind_typ S1)] ++ E) (open_ct T2 (`cset_fvar` y)) U
with sub_pre_through_subst_cpt : forall E S1 P2 x y Q,
  y `~in`A dom E ->
  binds x (bind_typ S1) E ->
  sub_pre E (open_cpt P2 (`cset_fvar` x)) Q ->
  sub_pre ([(y, bind_typ S1)] ++ E) (open_cpt P2 (`cset_fvar` y)) Q.
Proof with eauto*.
{ intros * NotIn Binds Sub.
  assert (WfEnv : wf_env E) by applys sub_regular Sub.
  dependent induction Sub.
  - Case "sub_refl_tvar".
    unfold open_ct in x |- *.
    induction T2; simpl in x |- *; simpl_env; subst...
    inversion x; subst.
    apply sub_refl_tvar.
    + apply wf_env_typ...
      apply wf_env_bound_implies_wf_typ with (x := x0)...
    + rewrite_env (empty ++ [(y, bind_typ S1)] ++ E).
      apply wf_typ_in_weakening...
      apply ok_cons...
  - Case "sub_trans_tvar".
    unfold open_ct in x |- *.
    induction T2; simpl in x |- *; simpl_env; subst...
    inversion x; subst.
    eapply sub_trans_tvar with (U := U).
    + apply binds_tail...
      simpl.
      enough (a `in`A dom E) by fsetdec.
      apply binds_In with (a := bind_sub U), H.
    + rewrite_env (empty ++ [(y, bind_typ S1)] ++ E).
      apply sub_weakening...
      apply wf_env_typ...
      apply wf_env_bound_implies_wf_typ with (x := x0)...
  - Case "sub_capt".
    unfold open_ct in x |- *.
    induction T2; simpl in x |- *; simpl_env; subst...
    inversion x; subst.
    apply sub_capt.
    + apply wf_env_typ...
      apply wf_env_bound_implies_wf_typ with (x := x0)...
    + rewrite_env (empty ++ [(y, bind_typ S1)] ++ E).
      apply wf_typ_in_weakening...
      apply ok_cons... 

Lemma eval_typing_through_subst_ct : forall E K S1 T2 U x y,
  y `~in`A dom E ->
  binds x (bind_typ S1) E ->
  eval_typing E K (open_ct T2 (`cset_fvar` x)) U ->
  eval_typing ([(y, bind_typ S1)] ++ E) K (open_ct T2 (`cset_fvar` y)) U.
Proof with eauto*.
  intros * NotIn Binds EvalTyp.
  assert (WfEnv : wf_env E) by applys eval_typing_regular EvalTyp.
  dependent induction EvalTyp.
  - Case "typing_eval_nil".
    apply typing_eval_nil.
    + apply wf_env_typ...
      apply wf_env_bound_implies_wf_typ with (x := x)...
    + rewrite_env ([(y, bind_typ S1)] ++ E).
*)
(*
Lemma typing_through_subst_ve : forall U E F x T e u C,
  typing (F ++ [(x, bind_typ U)] ++ E) e T ->
  x `~in`A fv_cctx F ->
  binds u (bind_typ U) E ->
  typing (F ++ E) (subst_ve x u C e) T.
Proof with simpl_env;
           eauto 4 using wf_typ_strengthen,
                         wf_env_strengthening,
                         sub_strengthening.
  intros * Typ NotIn uBinds.
  eremember (F ++ [(x, bind_typ U)] ++ E) as E'.
  generalize dependent F.
  induction Typ; intros F EQ NotIn; subst; simpl subst_ve.
  - Case "typing_var_tvar".
    destruct (x0 == x); subst.
    + SCase "x0 = x".
      binds_get H0.
      inversion H2; subst.
      rewrite_env (empty ++ F ++ E).
      apply typing_weakening...
      apply wf_env_strengthening_typ in H...
    + SCase "x0 <> x".
      binds_cases H0.
      eauto using wf_env_strengthening_typ.
      eauto using wf_env_strengthening_typ.
    - Case "typing_var".
      destruct (x0 == x); subst.
      + SCase "x0 = x".
        binds_get H0.
        inversion H2; subst; clear H2.
        rewrite_env (empty ++ F ++ E).
        apply typing_weakening...
        apply wf_env_strengthening_typ in H...
        admit.
        admit.
      + SCase "x0 <> x".
        binds_cases H0.
        admit.
        admit.
  - Case "typing_abs".
    pick fresh y and apply typing_abs.
    unfold open_ve.
    rewrite subst_ve_open_ve_var...
    rewrite <- concat_assoc.

    (** Now we can apply the induction hypothesis. *)

    apply H0...

  (** The remaining cases in this proof are straightforward, given
      everything that we have pointed out above. *)

  Case "typing_app".
    rewrite (if_hoist (f == x) u f var_f).
    rewrite (if_hoist (x0 == x) u x0 var_f).
    apply typing_app with (T1 := T1).
    SCase "callee".
      rewrite <- (if_hoist (f == x) u f var_f).
      apply IHTypT1...
    SCase "argument".
      rewrite <- (if_hoist (x0 == x) u x0 var_f).
      apply IHTypT2...

  Case "typing_tabs".
    pick fresh Y and apply typing_tabs.
    rewrite subst_ve_open_te_var...
    rewrite <- concat_assoc.
    apply H0...

  Case "typing_tapp".
    rewrite (if_hoist (x0 == x) u x0 var_f).
    apply typing_tapp with (T1 := T1).
    SCase "callee".
      rewrite <- (if_hoist (x0 == x) u x0 var_f).
      apply IHTypT...
    SCase "type argument".
      eauto using sub_strengthening.

  Case "typing_let".
    pick fresh y and apply typing_let...
    unfold open_ve.
    rewrite subst_ve_open_ve_var...
    rewrite <- concat_assoc.
    apply H0...

  Case "typing_pair".
    rewrite (if_hoist (x1 == x) u x1 var_f).
    rewrite (if_hoist (x2 == x) u x2 var_f).
    apply typing_pair.
    SCase "first element".
      rewrite <- (if_hoist (x1 == x) u x1 var_f).
      apply IHTypT1...
    SCase "second element".
      rewrite <- (if_hoist (x2 == x) u x2 var_f).
      apply IHTypT2...

  Case "typing_fst".
    rewrite (if_hoist (x0 == x) u x0 var_f).
    apply typing_fst with (T2 := T2).
    rewrite <- (if_hoist (x0 == x) u x0 var_f).
    apply IHTypT...

  Case "typing_snd".
    rewrite (if_hoist (x0 == x) u x0 var_f).
    apply typing_snd with (T1 := T1).
    rewrite <- (if_hoist (x0 == x) u x0 var_f).
    apply IHTypT...
Qed.
*)

Lemma eval_typing_open : forall E K T U V x y,
  eval_typing E K (open_ct T (`cset_fvar` x)) U ->
  eval_typing ([(y, bind_typ V)] ++ E) K (open_ct T (`cset_fvar` y)) U.
Proof with eauto*.
  intros * EvalTyp.
  inversion EvalTyp; subst.
  admit.
  admit.
Admitted.

Lemma store_typing_preserves_dom : forall S E,
  store_typing S E ->
  dom S = dom E.
Proof with eauto*.
  intros * StoreTyp.
  induction StoreTyp...
  repeat rewrite dom_concat; simpl.
  rewrite IHStoreTyp...
Qed.

Lemma bound_notin_fv_cctx_implies_notin_ct : forall F x y T,
  ok F ->
  bound y T F ->
  x `~in`A fv_cctx F ->
  x `~in`A fv_ct T.
Proof with eauto*.
  intros * Ok Bound NotIn.
  induction F; simpl in NotIn.
  - inversion Bound; inversion H.
  - destruct a as [z b].
    replace ((z, b) :: F) with ([(z, b)] ++ F) in * by reflexivity.
    destruct Bound as [Binds | Binds].
    all: binds_cases Binds;
         [ simpl in Fr;
           inversion Ok; subst;
           apply IHF; auto;
           destruct b; fsetdec
         | subst; fsetdec
         ].
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

(*
Lemma wf_cset_through_subst_cset : forall F x u U E A C,
  wf_env (F ++ [(x, bind_typ U)] ++ E) ->
  wf_cset (F ++ [(x, bind_typ U)] ++ E) A C ->
  binds u (bind_typ U) E ->
  x `~in`A fv_cctx F ->
  wf_cset (F ++ E) (A `\`A x) (subst_cset x (`cset_fvar` u) C).
Proof with eauto*.
  intros * WfEnv WfC Binds NotIn.
  inversion WfC; subst.
  unfold subst_cset.
  destruct_set_mem x fvars; csetsimpl.
  - destruct_set_mem u A.
    + constructor.
      * intros z zIn.
        admit.
      * enough (x <> u) by fsetdec.
        admit.
    + assert (x <> u).
      { apply ok_from_wf_env in WfEnv as OkEnv.
        apply binds_In in Binds.
        enough (x `~in`A dom E) by fsetdec.
        apply fresh_mid_tail in OkEnv...
      }
      apply wf_cset_strengthen_typ with (U := U).
      * enough (x <> u) by fsetdec...
      * constructor.
        -- intros z zIn.
           destruct_set_mem z fvars.
           ++ apply (H z ltac:(fsetdec)).
           ++ destruct (z == u); subst.
              ** exists U...
              ** exfalso; fsetdec.
        -- intros z zIn.
           destruct (z == u); subst.
           ++  
      replace ({u}A `u`A fvars `\`A x) with (({u}A `u`A fvars) `\`A x) by fsetdec.
      
      * 
      * constructor. 

Lemma wf_typ_through_subst_ct : forall F x u U E Ap Am T,
  wf_env (F ++ [(x, bind_typ U)] ++ E) ->
  wf_typ (F ++ [(x, bind_typ U)] ++ E) Ap Am T ->
  binds u (bind_typ U) E ->
  x `~in`A fv_cctx F ->
  wf_typ (F ++ E) (Ap `\`A x) (Am `\`A x) (subst_ct x (`cset_fvar` u) T)
with wf_pretyp_through_subst_cpt : forall F x u U E Ap Am P,
  wf_env (F ++ [(x, bind_typ U)] ++ E) ->
  wf_pretyp (F ++ [(x, bind_typ U)] ++ E) Ap Am P ->
  binds u (bind_typ U) E ->
  x `~in`A fv_cctx F ->
  wf_pretyp (F ++ E) (Ap `\`A x) (Am `\`A x) (subst_cpt x (`cset_fvar` u) P).
Proof with eauto*.
{ intros * WfEnv WfT Binds NotIn.
  eremember (F ++ [(x, bind_typ U)] ++ E) as E'.
  generalize dependent F.
  induction WfT; intros F Eq NotIn; subst; simpl.
  - binds_cases H.
    + apply wf_typ_var with (U := U0)...
      enough (X <> x) by fsetdec.
      simpl in Fr0; clear - Fr0; fsetdec.
    + apply wf_typ_var with (U := U0)...
      enough (X <> x) by fsetdec.
      apply binds_In in H2.
      enough (x `~in`A dom F) by fsetdec.
      apply ok_from_wf_env in WfEnv.
      apply fresh_mid_head in WfEnv...
  - apply wf_typ_capt...
    + apply wf_cset_strengthen_typ with (U := U).
      * unfold subst_cset.
        destruct_set_mem x (`cset_fvars` C).
        -- simpl.
           enough (x <> u) by fsetdec.
           apply binds_In in Binds.
           enough (x `~in`A dom E) by fsetdec.
           apply ok_from_wf_env in WfEnv.
           apply fresh_mid_tail in WfEnv.
           assumption.
        -- apply xIn.
      * 
*)

Lemma subst_ve_open_ve : forall (e : exp) (x y u : atom) (c1 c2 : cap),
  y <> x ->
  capt c1 ->
  subst_ve x u c1 (open_ve e y c2) =
  open_ve (subst_ve x u c1 e) y (subst_cset x c1 c2).
Proof with auto*.
  intros.
  unfold open_ve.
  apply subst_ve_open_ve_rec...
Qed.

Lemma subst_ve_open_ve_var : forall (x y u : atom) c e,
  y <> x ->
  expr u ->
  capt c ->
  open_ve (subst_ve x u c e) y (`cset_fvar` y) =
  subst_ve x u c (open_ve e y (`cset_fvar` y)).
Proof with auto*.
  intros x y u c e Neq Wu Wc.
  unfold open_ve.
  rewrite subst_ve_open_ve_rec...
  simpl.
  destruct (y == x)...

  unfold subst_cset; simpl.
  destruct_set_mem x (`cset_fvar` y)...
  fsetdec.
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
    assert (Neq : x0 <> x) by admit.
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
    + destruct (x0 == x)...
      contradict e.
      apply Neq.
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

Lemma typing_through_open_ve : forall E x y U e T,
  y `~in`A (fv_ct T `u`A fv_ve e `u`A fv_ce e) ->
  typing ([(y, bind_typ U)] ++ E) (open_ve e y (`cset_fvar` y)) (open_ct T (`cset_fvar` y)) ->
  binds x (bind_typ U) E ->
  typing E (open_ve e x (`cset_fvar` x)) (open_ct T (`cset_fvar` x)).
Proof with eauto*.
  intros * NotIn Typ Binds.
  assert (WfEnv : wf_env ([(y, bind_typ U)] ++ E)) by applys typing_regular Typ.
  assert (Neq : x <> y).
  { inversion WfEnv; subst.
    enough (x `in`A dom E) by fsetdec.
    apply binds_In in Binds...
  }
  rewrite_env (map (subst_cb y (`cset_fvar` x)) empty ++ E).
  replace (open_ve e x (`cset_fvar` x))
     with (subst_ve y x (`cset_fvar` x) (open_ve e y (`cset_fvar` y)))
     by (rewrite <- subst_ve_intro; auto).
     replace (open_ct T (`cset_fvar` x))
     with (subst_ct y (`cset_fvar` x) (open_ct T (`cset_fvar` y)))
     by (rewrite <- subst_ct_intro; auto).
  apply typing_through_subst_ve with (U := U)...
Qed.

Lemma typing_inv_let : forall E e k T,
  typing E (exp_let e k) T ->
  exists U,
       typing E e U
    /\ exists L, forall x, x `~in`A L ->
         typing ([(x, bind_typ U)] ++ E) (open_ve k x (`cset_fvar` x)) T.
Proof with eauto*.
  intros * Typ.
  dependent induction Typ...
  destruct (IHTyp e k ltac:(reflexivity)) as [U [eTyp [L kTyp]]].
  exists U.
  split...
  exists (L `u`A dom E).
  intros y NotIn.
  specialize (kTyp y ltac:(clear - NotIn; fsetdec)).
  apply typing_sub with (S := S)...
  rewrite_env (empty ++ [(y, bind_typ U)] ++ E).
  apply sub_weakening...
  apply wf_env_typ...
  applys typing_regular eTyp. 
Qed.

Lemma typing_inv_abs' : forall E U e C P,
  no_type_bindings E ->
  typing E (exp_abs U e) (typ_capt C P) ->
  exists T1 T2,
     sub_pre E (typ_arrow T1 T2) P
  /\ sub E T1 U
  /\ exists L, forall x, x `~in`A L ->
        typing ([(x, bind_typ T1)] ++ E) (open_ve e x (`cset_fvar` x))
          (open_ct T2 (`cset_fvar` x))
     /\ wf_typ ([(x, bind_typ T1)] ++ E) (dom E `u`A {x}A) 
          (dom E) (open_ct T2 (`cset_fvar` x))
     /\ sub ([(x, bind_typ T1)] ++ E) (open_ct T2 (`cset_fvar` x))
          (open_ct T2 (`cset_fvar` x)).
Proof with eauto*.
  intros * NTB Typ.
  assert (WfEnv : wf_env E) by applys typing_regular Typ.
  dependent induction Typ.
  - Case "typing_abs".
    repeat eexists.
    + apply sub_pre_reflexivity with (Ap := dom E) (Am := dom E)...
    + apply sub_reflexivity with (Ap := dom E) (Am := dom E)...
    + (* REVIEW: how to use instantiate? *)
      Unshelve. 2: apply (L `u`A dom E).
      apply (H1 x ltac:(clear - H3; fsetdec)).
    + apply (H0 x ltac:(clear - H3; fsetdec)).
    + apply sub_reflexivity with (Ap := dom ([(x, bind_typ U)] ++ E)) (Am := dom E)...
      replace (dom ([(x, bind_typ U)] ++ E)) with (dom E `u`A {x}A) by (clear; simpl; fsetdec).
      apply (H0 x ltac:(clear - H3; fsetdec)).
      clear; simpl; fsetdec.
  - Case "typing_sub".
    destructs sub_left_capt_inversion NTB H as [D [Q Eq]].
    destruct (IHTyp U e D Q NTB ltac:(reflexivity) Eq WfEnv) as [T1 [T2 [T1T2SubQ [T1SubU [L' ?]]]]].
    exists T1, T2.
    repeat split...
    apply sub_pre_transitivity with (Q := Q).
    + apply pretype_from_wf_pretyp with (E := E) (Ap := dom E) (Am := dom E)...
      applys sub_pre_regular T1T2SubQ.
    + apply T1T2SubQ.
    + subst.
      inversion H; subst...
Qed.

Lemma store_typing_regular : forall S E,
  store_typing S E ->
  wf_env E.
Proof with eauto*.
  intros * StoreTyp.
  induction StoreTyp...
  apply wf_env_typ...
  applys typing_regular H.
Qed.

(*
Lemma type_of_abs_is_capt_top_or_arrow : forall E U e T,
  typing E (exp_abs U e) *)

Lemma store_abs_inversion : forall E S f U e abs_value,
  store_typing S E ->
  stores S f (exp_abs U e) abs_value ->
  exists C P T1 T2,
     typing E (exp_abs U e) (typ_capt C P)
  /\ sub_pre E (typ_arrow T1 T2) P
  /\ sub E T1 U.
Proof with eauto*.
  intros * StoreTyp Stores.
  induction StoreTyp; inversion Stores; subst; rename H into Typ, H0 into NotIn.
  destruct (f == x); subst.
  - Case "f = x".
    clear IHStoreTyp.
    inversion H2; subst; clear H2.
    clear Stores.
    assert (WfEnv : wf_env ([(x, bind_typ T)] ++ E)).
    { apply wf_env_typ.
      - applys typing_regular Typ.
      - applys typing_regular Typ.
      - apply NotIn.
    }
    destruct (values_have_precise_captures _ _ _ abs_value Typ) as [P [Typ' Sub']].
    simpl in *; simpl_env in *.
    destruct (sub_capt_inversion _ _ _ _ Sub') as [D [Q [Eq [CSubD PSubQ]]]]; subst.
    assert (NTB : no_type_bindings E) by applys store_typing_no_type_bindings StoreTyp.
    destruct (typing_inv_abs' E U e (free_for_cv e) P NTB Typ') as [T1 [T2 [T1T2SubP [T1SubU [L ?]]]]].
    rewrite_env (empty ++ [(x, bind_typ (typ_capt D Q))] ++ E).
    repeat eexists.
    + apply typing_weakening... 
    + apply sub_pre_weakening...
    + apply sub_weakening...
  - Case "f <> x".
    destruct (IHStoreTyp H2) as [C [P [T1 [T2 [Typ' [T1T2SubP T1SubU]]]]]].
    rewrite_env (empty ++ [(x, bind_typ T)] ++ E).
    assert (WfT : wf_typ_in E T) by applys typing_regular Typ.
    assert (WfEnv : wf_env ([(x, bind_typ T)] ++ E)) by (apply wf_env_typ; auto).
    repeat eexists.
    + apply typing_weakening...
    + apply sub_pre_weakening...
    + apply sub_weakening...
Qed.

Lemma sub_pre_arrow_inversion' : forall E P T1 T2,
  sub_pre E P (typ_arrow T1 T2) ->
  exists S1 S2, P = typ_arrow S1 S2
             /\ sub E T1 S1
             /\ exists L, forall x, x `~in`A L ->
                    sub ([(x, bind_typ T1)] ++ E) (open_ct S2 (`cset_fvar` x)) (open_ct T2 (`cset_fvar` x)).
Proof with eauto*.
  intros * Sub.
  dependent induction Sub.
  exists S1, S2...
Qed.

Check typing_app.

Lemma typing_inv_app : forall E (f x : atom) T2,
  typing E (exp_app f x) T2 ->
  exists C S1 S2, typing E f (typ_capt C (typ_arrow S1 S2))
               /\ typing E x S1.
Proof with eauto*.
  intros * Typ.
  dependent induction Typ.
  - Case "typing_app".
    clear IHTyp1 IHTyp2.
    exists Cf, T1, T2.
    repeat split...
  - Case "typing_sub".
    destruct (IHTyp f x ltac:(reflexivity)) as [C [S1 [S2 [fTyp xTyp]]]]...
Qed.

(*
Lemma red_app_inversion : forall S E f x e T1 T2 v (v_value : value v) (abs_value : value (exp_abs T1 e)),
  store_typing S E ->
  stores S f (exp_abs T1 e) abs_value ->
  stores S x v v_value ->
  typing E (exp_app f x) T2 ->
     typing E v T1
  /\ typing E (exp_abs T1 e) (typ_capt (free_for_cv e) (typ_arrow T1 T2)).
Proof with eauto*.
  intros * StoreTyp fStores xStores TypApp.
  assert (NTB : no_type_bindings E) by applys store_typing_no_type_bindings StoreTyp.
  dependent induction TypApp.
  - clear IHTypApp1 IHTypApp2.
    rename TypApp1 into fTyp, TypApp2 into xTyp.
    rename Cf into C.
    destructs typing_var_inversion' NTB fTyp as [Cf [Pf [Df [Qf [Eqf [PfSubQf fBinds]]]]]]; subst.
    destructs typing_var_inversion' NTB xTyp as [Cx [Px [Dx [Qx [Eqx [PxSubQx xBinds]]]]]]; subst.
    inversion Eqf; subst; clear Eqf.
    destructs sub_pre_arrow_inversion' PfSubQf as [S1 [S2 [Eq [T1SubS1 [L ?]]]]]; subst.
    destructs stores_preserves_typing StoreTyp xStores xTyp as [Rx [vTyp RxSubQx]].
    destructs stores_preserves_typing StoreTyp fStores fTyp as [Rf [absTyp RfSubQf]].
    simpl in *; simpl_env in *.
    destructs sub_pre_arrow_inversion' RfSubQf as [R1 [R2 [Eq [DQSubR1 [L' ?]]]]]; subst.
    assert (sub E (typ_capt (free_for_cv e) (typ_arrow R1 R2))
                  (typ_capt (free_for_cv e) (typ_arrow (typ_capt Dx Qx) R2))).
    { apply sub_capt.
      - apply subcapt_reflexivity with (A := dom E)...
      - inversion RfSubQf; subst.
        apply sub_arrow with (L := L0 `u`A dom E)...
        + intros z zIn.
          specialize (H10 z ltac:(clear - zIn; fsetdec)).
          rewrite_env (empty ++ [(z, bind_typ (typ_capt Dx Qx))] ++ E).
          eapply wf_typ_narrowing_typ_base with (V := R1)...
          apply ok_cons...
        + intros z zIn.
          apply sub_reflexivity with (Ap := dom ([(z, bind_typ (typ_capt Dx Qx))] ++ E)) (Am := dom ([(z, bind_typ (typ_capt Dx Qx))] ++ E))...
          specialize (H11 z ltac:(clear - zIn; fsetdec)).
          applys sub_regular H11.
    }
    destruct (typing_inv_abs _ _ _ _ absTyp (typ_capt Dx Qx) R2 (free_for_cv e) H1) as [DxQxSubT1 [Q2 [L'' ?]]].
    split.
    + apply typing_sub with (S := typ_capt (free_for_cv v) Rx)...
      apply sub_transitivity with (Q := typ_capt Dx Qx)...
      apply sub_capt...
      admit.
    +   
*)

Inductive red : state -> state -> Prop :=
  | red_lift : forall x v (v_value : value v) k (k_scope : scope k) S K,
      x `~in`A dom S ->
      red ⟨ S | cont k k_scope :: K | v ⟩
          ⟨ [(x, store v v_value)] ++ S | K | open_ve k x (`cset_fvar` x) ⟩
  | red_let_var : forall (x y : atom) v (v_value : value v) k (k_scope : scope k) S K,
      stores S x v v_value ->
      red ⟨ S | cont k k_scope :: K | x ⟩
          ⟨ S | K | open_ve k x (`cset_fvar` x) ⟩
  | red_let_val : forall x v (v_value : value v) k (k_scope : scope k) S K,
      x `~in`A dom S ->
      red ⟨ S | K | exp_let v k ⟩
          ⟨ [(x, store v v_value)] ++ S | K | open_ve k x (`cset_fvar` x) ⟩
  | red_let_exp : forall e k (k_scope : scope k) S K,
      red ⟨ S | K | exp_let e k ⟩
          ⟨ S | cont k k_scope :: K | e ⟩
  | red_app : forall f x y U e v (v_value : value v) (abs_value : value (exp_abs U e)) S K,
      stores S f (exp_abs U e) abs_value ->
      stores S x v v_value ->
      y `~in`A dom S ->
      red ⟨ S | K | exp_app f x ⟩
          ⟨ [(y, store v v_value)] ++ S | K | open_ve e y (`cset_fvar` y) ⟩
  | red_tapp : forall x T U e (tabs_value : value (exp_tabs U e)) S K,
      stores S x (exp_tabs U e) tabs_value ->
      type T ->
      red ⟨ S | K | exp_tapp x T ⟩
          ⟨ S | K | open_te e T ⟩.

Lemma preservation : forall s s' V,
  state_typing s V ->
  red s s' ->
  state_typing s' V.
Ltac hint :=
    eauto using wf_cset_set_weakening.
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
      apply typing_through_open_ve with (y := y) (U := T).
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
      * apply binds_head...
  - Case "red_let_var".
    inversion EvalTyp; subst.
    destructs typing_var_inversion' NTB Typ as [C [P [D [Q [Eq [PSubQ [xSubD Binds]]]]]]]; subst.
    destructs stores_preserves_typing StoreTyp H Typ as [B [R [vTyp [Binds' [vSubB RSubQ]]]]].
    assert (bind_typ (typ_capt B R) = bind_typ (typ_capt C P)) by applys binds_unique Binds' Binds.
    inversion H1; subst; clear H1.
    eapply typing_state with (E := E) (T := U0)...
    assert (type_U0 : type U0).
    { enough (WfU : wf_typ_in E U0) by applys type_from_wf_typ WfU.
      applys eval_typing_regular H6.
    }
    rewrite open_ct_rec_type with (k := 0) (C := `cset_fvar` x)...
    apply typing_through_open_ve with (y := y) (U := typ_capt C P)...
    unfold open_ct.
    rewrite <- open_ct_rec_type...
    apply typing_weakening.
    rewrite_env (empty ++ [(z, bind_typ (typ_capt C P))] ++ E).
    apply typing_narrowing_typ with (Q := typ_capt D Q)...
    apply sub_capt...
    admit.
    destructs typing_var_inversion' NTB Typ as [C [P [D [Q [Eq [PSubQ Binds]]]]]]; subst.
  - Case "red_let_val".
    assert (x `~in`A dom E) by (rewrite <- (store_typing_preserves_dom _ _ StoreTyp); assumption).
    destructs typing_inv_let Typ as [T1 [eTyp [L kTyp]]].
    eapply typing_state with (E := [(x, bind_typ T1)] ++ E) (T := T).
    * apply typing_store_cons...
    * rewrite_env (empty ++ [(x, bind_typ T1)] ++ E).
      apply eval_typing_weakening...
      apply wf_env_typ...
      applys typing_regular eTyp.
    * pick fresh z and specialize kTyp.
      assert (type_T : type T).
      { enough (WfT : wf_typ_in E T) by applys type_from_wf_typ WfT.
        applys typing_regular Typ.
      }
      rewrite open_ct_rec_type with (k := 0) (C := `cset_fvar` x)...
      eapply typing_through_open_ve with (y := z) (U := T1)...
      apply typing_weakening.
      unfold open_ct.
      rewrite <- open_ct_rec_type...
      assert (WfT1 : wf_typ_in E T1) by applys typing_regular eTyp.
      repeat apply wf_env_typ...
      rewrite_env (empty ++ [(x, bind_typ T1)] ++ E).
      apply wf_typ_in_weakening...
      apply ok_cons...
  - Case "red_let_exp".
    destructs typing_inv_let Typ as [T1 [eTyp [L kTyp]]].
    eapply typing_state with (E := E) (T := T1)...
    eapply typing_eval_cons...
  - Case "red_app".
    destructs stores_preserves_typing
    eapply typing_state with (E := )

    eapply typing_state with (E := E) (T := T)...
    destructs store_abs_inversion StoreTyp H as [C [P [T1 [T2 [TypAbs [T1T2SubP T1SubU]]]]]].
    destructs typing_inv_abs' NTB TypAbs as [S1 [S2 [S1S2SubP [S1SubU0 [L ?]]]]].
    pick fresh z and specialize H1.
    destruct H1 as [eTyp [WfS2 Sub]].
    assert (type_T : type T).
    { enough (WfT : wf_typ_in E T) by applys type_from_wf_typ WfT.
      applys typing_regular Typ.
    }
    rewrite open_ct_rec_type with (k := 0) (C := `cset_fvar` x)...
    eapply typing_through_open_ve with (y := z) (U := S1)...
    eapply binds_fresh.
    admit.
    destruct (P2 x) as [? ?]...
    rewrite (subst_ee_intro x)...
    rewrite_env (empty ++ E).
    apply (typing_through_subst_ee T).
      apply (typing_sub S2)...
        rewrite_env (empty ++ [(x, bind_typ T)] ++ E).
        apply sub_weakening...
      eauto.
    


  induction Typ.
  - Case "typing_var".
    inversion EvalTyp; subst.
    + SCase "typing_eval_nil".
      specialize (Red {}A); inversion Red; subst; inversion v_value.
    + SCase "typing_eval_cons".
      specialize (Red (dom E `u`A L)); inversion Red; subst.
      * SSCase "red_lift".
        inversion v_value.
      * SSCase "red_let_var".
        apply typing_state with (E := E) (T := U0)...
        -- apply typing_store_cons...
           eapply stores_preserves_typing...
        -- rewrite_env (empty ++ [(y, bind_typ X)] ++ E).
           apply eval_typing_weakening...
           apply wf_env_typ...
           destruct (typing_regular _ _ _ (H1 y (ltac:(fsetdec)))) as [wf_xT_Γ _].
           inversion wf_xT_Γ; subst...
  - Case "typing_capt".
    inversion EvalTyp; subst.
    + SCase "typing_eval_nil".
      specialize (Red {}A); inversion Red; subst; inversion v_value.
    + SCase "typing_eval_cons".
      specialize (Red (dom E `u`A L)); inversion Red; subst.
      * SSCase "red_lift".
        inversion v_value.
      * SSCase "red_let_var".
        destructs wf_capt_from_typing_var H H0 as [WfC WfP]...
        apply typing_state with (E := [(y, bind_typ (typ_capt (`cset_fvar` x) P))] ++ E) (T := U0).
        -- apply typing_store_cons...
           eapply stores_preserves_typing...
        -- rewrite_env (empty ++ [(y, bind_typ (typ_capt (`cset_fvar` x) P))] ++ E).
           apply eval_typing_weakening...
           apply wf_env_typ...
           constructor...
           constructor...
           ++ intros z zIn; assert (z = x) by (clear - zIn; fsetdec); subst; clear zIn...
           ++ enough (x `in`A dom E) by fsetdec.
              apply binds_In with (a := bind_typ (typ_capt C P))... 
        -- rewrite_env (empty ++ [(y, bind_typ (typ_capt (`cset_fvar` x) P))] ++ E).
           specialize (H1 y ltac:(fsetdec)).
           apply H1.
  - Case "typing_abs".
    inversion EvalTyp; subst.
    + SCase "typing_eval_nil".
      specialize (Red {}A); inversion Red.
    + SCase "typing_eval_cons".
      specialize (Red (dom E `union` L0)); inversion Red; subst.
      specialize (H3 x ltac:(clear - H11; fsetdec)).
      apply typing_state with (E := [(x, bind_typ (typ_capt (free_for_cv e1) (typ_arrow V0 T1)))] ++ E) (T := U0); simpl.
      * SSCase "store_typing".
        apply typing_store_cons.
        -- assumption.
        -- eapply typing_abs...
        -- clear - H11; fsetdec.
      * SSCase "eval_typing".
        rewrite_env (empty ++ [(x, bind_typ (typ_capt (free_for_cv e1) (typ_arrow V0 T1)))] ++ E).
        apply eval_typing_weakening...
        applys typing_regular H3.
      * SSCase "typing".
        apply H3.
  - Case "typing_app".
    clear IHTyp1 IHTyp2.
    destructs typing_var_inversion Typ1 as [[C [P [fBinds fPSubArr]]] | [X [fBiEnds XSubArr]]].
    + assert (PSubT1T2 : sub_pre E P (typ_arrow T1 T2)) by (inversion fPSubArr; subst; eauto* ).
      (* REVIEW: I don't think the following holds but:
         We have `Γ ⊢ f : C (∀ (x : T1) → T2 x)`
         If `f ∈ (fv_ct T1 ∪ fv_ct T2)`, we could possibly remove `f` from the
         capture sets of `T1` and `T2` and lift the dependency on `f` by
         `Γ ⊢ C <: C ∪ {f}` so that `Γ ⊢ f : (C ∪ {f}) (∀ (x : T1) → T2' x)`
         where `T1'` and `T2'` are `T1` and `T2` where the dependency on `f`
         has been removed.
      *)
      assert (NotIn : f `~in`A (fv_ct T1 `u`A fv_ct T2)).
      { admit. }
      destruct (binds_sub_arrow_implies_store_abs' _ _ _ _ _ _ _ StoreTyp fBinds NotIn PSubT1T2) as [S1 [e [abs_value [fStores T1SubS1]]]].
      assert (AbsTyp : typing E (exp_abs S1 e) (typ_capt Cf (typ_arrow T1 T2))) by applys stores_preserves_typing StoreTyp fStores Typ1.
      destruct (typing_inv_abs _ _ _ _ AbsTyp T1 T2 Cf) as [P1 [S2 [L' P2]]].
      eapply sub_reflexivity with (Ap := dom E) (Am := dom E)...
      1,2: clear; fsetdec.
      specialize (Red (dom E `u`A L')); inversion Red; subst.
      * SCase "red_lift".
        inversion v_value.
      * SCase "red_app".
        eapply typing_state with (E := E) (T := open_ct T2 (`cset_fvar` x))...
        destruct (P2 y)...
           
        apply typing_sub with (S := open_ct S2 (`cset_fvar` x)). 
        Search (typing _ (open_ve _ _ _) (open_ct _ _)).
    inversion EvalTyp; subst.
    + SCase "typing_eval_nil".
      specialize (Red {}A); inversion Red; subst.
    + SCase "typing_eval_cons".
      admit.


    destruct (typing_of_var_comes_from_binds _ _ _ Typ1) as [TFun [fBinds SsubT]].
    destruct (binds_sub_arrow_implies_store_abs _ _ _ _ _ _ _ StoreTyp fBinds SsubT) as [U' [e [abs_value [S_stores_abs T1_sub_U]]]].
    assert (abs_typing : typing E (exp_abs U' e) (typ_capt Cf (typ_arrow T1 T2))).
    { apply stores_preserves_typing with (S := S) (E := E) (x := f) (v_value := abs_value)... }
    destruct (typing_inv_abs _ _ _ _ abs_typing T1 T2 Cf) as [P1 [S2 [L' P2]]].
    eapply sub_reflexivity...
    1,2: clear; fsetdec.
    inversion EvalTyp; subst.
    + SCase "final".
      specialize (Red (dom E `u`A L' `u`A fv_ct S2 `u`A (`cset_fvars` (cv U')) `u`A fv_ve (open_ve e x (cv U')))); inversion Red; subst.
      assert (arg_typing : typing E v T1).
      { eapply stores_preserves_typing with (x := x) (v_value := v_value)... }
      assert (exp_abs U' e = exp_abs U0 e0) by applys stores_unique S_stores_abs H7.
      inversion H2; subst.
      clear H2.
      eapply typing_state with (E := E) (T := open_ct T2 (cv T1')); simpl.
      * SSCase "store_typing".
        assumption.
      * SSCase "eval_typing".
        apply typing_eval_nil...
      * SSCase "typing".
        destruct (P2 x) as [xU_E_e_S2 [WfS2 S2subV]]...
        rewrite_env (empty ++ E).
        apply typing_sub with (S := open_ct S2 (cv U0))...
        -- apply typing_strengthening with (x := x) (U := U0).
           ++ clear - H9; repeat apply notin_union...
              apply notin_open_ct_rec_fv_ct with (c := cv U0).
              fsetdec.
           ++ admit.
        -- admit.   
    + SCase "cont".
      specialize (Red (dom E `u`A L `u`A L' `u`A fv_ve (open_ve e x Cf))); inversion Red; subst.
      * SSCase "red_lift".
        inversion v_value.
      * SSCase "red_app".
        assert (arg_typing : typing E v T1).
        { eapply stores_preserves_typing with (x := x) (v_value := v_value)... }
        eapply typing_state with (E := E) (T := open_ct T2 (cv T1')); simpl...
        assert (exp_abs U' e = exp_abs U1 e0) by applys stores_unique S_stores_abs H7.
        inversion H2; subst.
        clear H2.
        destruct (P2 x ltac:(fsetdec)).
        rewrite_env (empty ++ E).
        apply typing_sub with (S := open_ct S2 (cv T1')).
        -- apply typing_strengthening with (x := x) (U := U1).
           ++ clear - H9; repeat apply notin_union...
              all: admit.
           ++ admit.
        -- admit.
  - Case "typing_let".
    specialize (Red (dom E `union` L)); inversion Red; subst.
    * SSCase "red_lift".
      inversion v_value.
    * SSCase "red_let_var".
      eapply typing_state with (E := [(x, bind_typ T1)] ++ E) (T := T2); simpl.
      -- apply typing_store_cons...
      -- rewrite_env (empty ++ [(x, bind_typ T1)] ++ E).
         assert (WfEnv : wf_env ([(x, bind_typ T1)] ++ E)) by applys typing_regular (H x ltac:(fsetdec)).
         inversion WfEnv; subst.
         apply eval_typing_weakening...
      -- apply H...
    * SSCase "red_let_exp".
      eapply typing_state with (E := E) (T := T1); simpl.
      -- assumption.
      -- apply typing_eval_cons with (L := L) (U := T2)...
      -- assumption.
  - Case "typing_tabs".
    inversion EvalTyp; subst.
    + SCase "typing_eval_nil".
      specialize (Red {}A); inversion Red.
    + SCase "typing_eval_cons".
      specialize (Red (dom E `union` L0)); inversion Red; subst.
      specialize (H3 x ltac:(clear - H11; fsetdec)).
      apply typing_state with (E := [(x, bind_typ (typ_capt (free_for_cv e1) (typ_all V0 T1)))] ++ E) (T := U0); simpl.
      * SSCase "store_typing".
        apply typing_store_cons.
        -- assumption.
        -- eapply typing_tabs...
        -- clear - H11; fsetdec.
      * SSCase "eval_typing".
        rewrite_env (empty ++ [(x, bind_typ (typ_capt (free_for_cv e1) (typ_all V0 T1)))] ++ E).
        apply eval_typing_weakening...
        applys typing_regular H3.
      * SSCase "typing".
        apply H3.
  - Case "typing_tapp".
    admit.
  - Case "typing_sub".
    apply IHTyp...
    apply eval_typing_contravariant.
Admitted.   

  inversion Step; subst; inversion TypState; subst.
  all: try rename select (typing _ _ _ T) into Typ.
  all: try rename select (typing _ _ _ T0) into Typ.
  all: try rename select (typing_ctx _ _ _ T) into TypCtx.
  all: try rename select (typing_ctx _ _ _ T0) into TypCtx.

  Local Ltac solve_it_ctx := dependent induction TypCtx; hint; repeat (econstructor; hint).
  Local Ltac solve_it_typ := dependent induction Typ; hint; repeat (econstructor; hint).

  - Case "step-app".
    solve_it_typ.
  - Case "step-tapp".
    solve_it_typ.
    admit. (* T1 not universal, T <: T1 --> T not universal *)
  - Case "step-fun->arg".
    solve_it_ctx.
  - Case "step-throw".
    solve_it_typ.
  - Case "step-handler->arg".
    solve_it_ctx.
  - Case "step-app".
    assert (no_type_bindings empty) by (eauto using typing_ctx_free_tvar).
    dependent induction TypCtx...

    rename select (typing _ _ (exp_abs _ _) _) into TypAbs.
    forwards (Sub & S2 & L & TypingX): typing_inv_abs TypAbs T1 T2 C...
    1: { eauto using sub_reflexivity. }

    pick fresh x.
    destruct (TypingX x) as (TypingX' & Wf & SubS2).
    1: { notin_solve. }

    eapply typ_step...
    rewrite (subst_ee_intro x) by notin_solve.
    rewrite (subst_ct_intro x) by notin_solve.
    assert (wf_typ_in empty T1') as WfTypV by eauto.
    assert (wf_typ_in empty T1)  as WfTypT by eauto.
    (**
      E - environment
      x - fresh atom
      v - argument/value
      e0 - body of abstraction (\lambda T e0)
    *)
    forwards (C' & P' & ?): inversion_toplevel_type WfTypV; subst...
    forwards (C'' & P'' & ?): inversion_toplevel_type WfTypT; subst...

    eapply typing_through_subst_ee' with (Ap := dom empty `union` singleton x) (Am := dom empty); trivial.
    3,4: simpl_env; clear_frees; fsetdec.
    (* 3: notin_solve. *)
    + (* typing *)
      rewrite_nil_concat.
      eapply typing_narrowing_typ...
      eapply typing_sub...
      rewrite_nil_concat.
      eapply typing_narrowing_typ...
    + rewrite_nil_concat.
      eapply wf_typ_narrowing_typ_base with (V := T); simpl_env...
    + (* wf_cset free_for_cv *)
      rename select (typing empty _ v _) into TypV.
      forwards WfFvV: typing_cv TypV...
    + inversion WfTypV. (* wf_cset C *)
      rename select (wf_cset empty _ C') into WfC.
      applys wf_cset_set_weakening WfC...
  - Case "step-tapp".
    dependent induction TypCtx...
    econstructor...

    rename select (typing _ _ (exp_tabs _ _) _) into TypTabs.
    forwards (Sub & S2 & L & TypingX): typing_inv_tabs TypTabs T0 T3.
    1: { eauto using sub_reflexivity. }

    pick fresh x.
    destruct (TypingX x) as [Typ' SubS2]...
    rewrite (subst_te_intro x)...
    rewrite (subst_tt_intro x)...
    rewrite_env (map (subst_tb x T2) empty ++ empty).
    apply (typing_through_subst_te T0)...
  - assert (no_type_bindings empty) by (eauto using typing_ctx_free_tvar).
    Notation "#H" := CCsub_Definitions.H.
    dependent induction Typ...
    unfold Signatures.singleton_list.
    pick fresh x.
    rename H2 into HH'.
    forwards HH: HH' x. 1: { notin_solve. }
    note (wf_env ((x, bind_typ (typ_capt {*} (typ_ret T))) :: empty)).
    note (wf_typ_in empty (typ_capt {*} (typ_ret T))) as WfTypRet.
    rename select (wf_pretyp empty _ _ (typ_ret T)) into WfT.
    rewrite_env (empty ++ [(x, bind_typ (typ_capt {*} (typ_ret T)))] ++ empty) in HH.
    replace Q with (nil ++ Q) in HH...
    apply (typing_weakening_sig [(l, bind_sig (typ_capt {*} (typ_ret T)))]) in HH.
    2: {
      Signatures.simpl_env.
      assert (wf_sig Q). {
        pick fresh y for L.
        eapply typing_regular_sig.
        applys HH' y; trivial.
      }
      econstructor; simpl; trivial.
      (* - (* here we need to know that T is wellformed in the empty environment. *) *)
      (*   admit. *)
      - forwards EQ: typing_ctx_calculates_bound_capabilities TypCtx.
        rewrite EQ.
        lsetdec.
    }
    rename HH into HH''.
    forwards HH: typing_narrowing_typ (`cset_lvar` l) (typ_ret T) HH''. 1: {
      constructor.
      - apply subcapt_universal...
      - eapply sub_pre_reflexivity...
    }
    apply typing_through_subst_ee with (u := (exp_lvar l)) in HH.
    2: { eauto. }
    2: {
      simpl free_for_cv.
      eapply typing_lvar...
      Signatures.simpl_env.
      assert (wf_sig Q). {
        pick fresh y for L.
        eapply typing_regular_sig.
        applys HH' y; trivial.
      }
      econstructor; simpl; trivial.
      (* - (* here we need to know that T is wellformed in the empty environment. *) *)
      (*   admit. *)
      - forwards EQ: typing_ctx_calculates_bound_capabilities TypCtx.
        rewrite EQ.
        lsetdec.
    }
    simpl in HH; simpl_env in HH; unfold Signatures.singleton_list in HH.
    rewrite <- subst_ee_intro in HH by notin_solve.
    rewrite <- subst_ct_fresh in HH. 2: {
      (* inversion WfTypRet. *)
      assert (x `~in`A dom empty). {
        assert (wf_env ([(x, bind_typ (typ_capt {*} (typ_ret T)))] ++ empty)) as HA by eauto.
        inversion HA; trivial.
      }
      enough (x `~in`A (fv_tt T `u`A fv_ct T)) by notin_solve.
      applys notin_fv_wf_pretyp WfT; trivial.
    }

    eapply typ_step...
    + eapply typing_ctx_reset...
      * destruct (`cset_uvar` (cv T)) eqn:EQ...
        enough (empty |-sc {*} <: cv T) by contradiction.
        constructor.
        2: exact EQ.
        assert (wf_typ_in empty T) by eauto.
        eapply cv_wf...
      * forwards EQ: typing_ctx_calculates_bound_capabilities TypCtx.
        rewrite EQ.
        lsetdec.
  - dependent induction TypCtx...
    clear IHTypCtx.
    econstructor...
    applys typing_strengthening_sig_absent_label Typ.
    applys label_absent_from_cv_is_absent_from_fv Typ; trivial.
  - dependent induction TypCtx...
    clear IHTypCtx.
    dependent induction H0.
    + inversion H; subst.
      1: {
        rename select (typing _ _ (exp_lvar l) _) into HH.
        forwards (? & ? & ?): typing_inversion_lvar HH.
        congruence.
       }
      inversion select (sub_pre _ _ (typ_ret Targ)); subst.
      applys IHtyping l T1 C1...
    + econstructor...
  - solve_it_ctx.
  - solve_it_ctx.
  - solve_it_ctx.
  - solve_it_ctx.
  - solve_it_ctx.
  - dependent induction TypCtx...
    rename select (typing _ _ (exp_lvar l1) _) into TypLvar.
    clear IHTypCtx.
    dependent induction TypLvar.
    1: {
      inversion select (sub _ S _); subst.
      1: {
        rename select (typing _ _ (exp_lvar l1) _) into HH.
        forwards (? & ? & ?): typing_inversion_lvar HH.
        congruence.
      }
      inversion select (sub_pre _ _ (typ_ret R)); subst.
      applys IHTypLvar T l2 T1...
    }
    assert (Signatures.binds l1 (bind_sig (typ_capt C0 (typ_ret R))) Q) as BndL1. {
      rename select (Signatures.binds l1 _ _) into HA.
      Signatures.binds_cases HA...
    }
    econstructor...
    + rename select (typing _ _ v R) into TypV.
      applys typing_strengthening_sig_absent_label TypV.
      applys label_absent_from_cv_is_absent_from_fv TypV; trivial.
      * applys extract_nontopness BndL1...
      * assert (l2 `~in`L fv_lt (typ_capt C0 (typ_ret R))). {
          applys notin_fv_ld_is_notin_fv_lt_of_bind_sig BndL1...
        }
        simpl in *.
        destruct R; simpl in *; lsetdec.
  - dependent induction TypCtx...
    clear IHTypCtx.

    rename select (typing _ _ (exp_lvar l) _) into TypLvar.
    dependent induction TypLvar.
    + inversion select (sub _ S _); subst.
      1: {
        rename select (typing _ _ (exp_lvar l) _) into HH.
        forwards (? & ? & ?): typing_inversion_lvar HH.
        congruence.
      }
      inversion select (sub_pre _ _ (typ_ret R)); subst.
      applys IHTypLvar T l TypCtx T1...
    + rename select (Signatures.binds _ _ _) into BndA.
      assert (Signatures.binds l (bind_sig (typ_capt {*} (typ_ret T)))
                               ([(l, bind_sig (typ_capt {*} (typ_ret T)))] ++ Q)) as BndA' by eauto.
      forwards EQ: binds_sig_unique BndA BndA'.
      inversion EQ; subst; clear EQ BndA'.
      rename select (typing _ _ v T) into TypV.
      forwards: typing_strengthening_sig_absent_label TypV.
      1: {
        applys label_absent_from_cv_is_absent_from_fv TypV...
      }
      econstructor...
Admitted.

(* ********************************************************************** *)
(** * #<a name="progress"></a># Progress *)

(* ********************************************************************** *)
(** ** Progress (16) *)

Lemma canonical_form_lvar : forall e Q C R,
  value e ->
  empty @ Q |-t e ~: (typ_capt C (typ_ret R)) ->
  exists l, e = exp_lvar l.
Proof with eauto.
  intros * Val Typ.
  dependent induction Typ; try solve [inversion Val]...
  inversion select (sub _ S _); subst.
  1: {
    inversion select (binds _ _ empty).
  }
  inversion select (sub_pre _ _ (typ_ret R)); subst.
  eapply IHTyp...
Qed.

Lemma progress_value_step : forall v k,
  value v ->
  typing_state empty 〈 v | k 〉 ->
  done 〈 v | k 〉 \/ exists s2, 〈 v | k 〉 --> s2.
Proof with eauto.
  intros * Val Typ.
  inversion Typ; subst.
  dependent induction H2.
  - left; constructor...
  - right...
  - forwards (V & e1 & ?): canonical_form_abs H0...
    subst.
    right...
  - forwards (V & e1 & ?): canonical_form_tabs H3...
    subst.
    right...
  - right...
  - forwards (? & ?): canonical_form_lvar H3...
  - forwards (? & ?): canonical_form_lvar H0...
    subst.
    right...
  - eauto.
Qed.

Lemma progress_step : forall s1,
  typing_state empty s1 ->
  done s1 \/ exists s2, s1 --> s2.
Proof with eauto.
  intros * Typ.
  inversion Typ; subst.
  2: {
    dependent induction H...
    - dependent induction H1...
      2: {
        inversion H1.
      }
      inversion select (sub _ S _); subst.
      1: {
        rename select (typing _ _ (exp_lvar l) _) into HH.
        forwards (? & ? & ?): typing_inversion_lvar HH.
        congruence.
      }
      inversion select (sub_pre _ _ (typ_ret R)); subst.
      applys IHtyping l C1 T1...
    - right.
      destruct (l0 ==== l); subst.
      + eexists.
        apply step_unwind_match_frame.
      + eexists...
  }
  dependent induction H0.
  - inversion select (binds _ _ _).
  - inversion select (binds _ _ _).
  - assert (value (exp_abs V e1)). {
      assert (empty @ Q |-t (exp_abs V e1) ~: (typ_capt (free_for_cv e1) (typ_arrow V T1))). {
        econstructor...
      }
      eauto.
    }
    eapply progress_value_step...
  - right...
  - assert (value (exp_tabs V e1)). {
      assert (empty @ Q |-t (exp_tabs V e1) ~: (typ_capt (free_for_cv e1) (typ_all V T1))). {
        econstructor...
      }
      eauto.
    }
    eapply progress_value_step...
  - right...
  - apply IHtyping...
    applys typing_ctx_sub H1...
  - pick fresh label l for (Signatures.dom (bound_capabilities k)
                                           `u`L fv_ld (bound_capabilities k)
                                           `u`L `cset_lvars` (cv T1)).
    right; eexists.
    eapply step_try with (l := l).
    all: lsetdec.
  - right...
  - assert (value (exp_lvar l)) by eauto.
    eapply progress_value_step...
Qed.
