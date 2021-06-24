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

Lemma typing_ctx_free_tvar : forall E k T,
  E |-ctx k ~: T ->
  no_type_bindings E.
Proof with eauto.
  intros. unfold no_type_bindings; intros.
  induction H...
  * intro. binds_cases H...
  * intro. binds_cases H0...
Qed.

Lemma non_derivation_implies_absence: forall Q E T v a,
  value v ->
  `cset_uvar` (cv T) = false ->
  a `~in`A `cset_fvars` (cv T) ->
  typing ([(a, bind_lab Q)] ++ E) v T ->
  ~ a A`in` (free_for_cv v).
Proof with eauto.
  intros * Val NonDerivation1 NonDerivation2 Typ.
  destruct_set_mem a (`cset_fvars` (free_for_cv v)).
  2: trivial.
  assert (subcapt ([(a, bind_lab Q)] ++ E) (`cset_fvar` a) (cv T)). {
    forwards (U & HA1 & HA2): values_have_precise_captures Typ...
    inversion HA2; subst; simpl.
    apply (subcapt_transitivity (free_for_cv v))...
    note (wf_cset_in ([(a, bind_lab Q)] ++ E) (free_for_cv v)).
    rename select (_ = (free_for_cv v)) into EQ.
    rewrite <- EQ in aIn.
    eapply subcapt_in ...
    admit.                  (* wf_cset *)
  }
  dependent induction H.
  - rewrite <- x in NonDerivation1.
    congruence.
  - rewrite <- x in NonDerivation2.
    assert (x0 `in`A {x0}A) as HA by fsetdec.
    rewrite x1 in HA.
    assert (x0 = a) by fsetdec.
    subst; clear HA. clear x1.
    exfalso;fsetdec.
  - assert (x0 `in`A {x0}A) as HA by fsetdec.
    rewrite x in HA.
    assert (x0 = a) by fsetdec.
    subst; clear HA. clear x.
    admit.
  - assert (x0 `in`A {x0}A) as HA by fsetdec.
    rewrite x in HA.
    assert (x0 = a) by fsetdec.
    subst; clear HA. clear x.
    admit.                      (* same as the admit above *)
  - applys H1 a a T E Q...
    fsetdec.
Admitted.

Fixpoint env_fv_ct (F : env) {struct F} : atoms :=
  match F with
  | nil => {}A
  | (_, bind_typ T) :: F' => (fv_ct T) `u`A (env_fv_ct F')
  | (_, bind_sub T) :: F' => (fv_ct T) `u`A (env_fv_ct F')
  | (_, bind_lab T) :: F' => (fv_ct T) `u`A (env_fv_ct F')
  end.

Lemma typing_strengthening_lab_aux: forall F a Q E v T,
  ~ a `in`A fv_ee v ->
  ~ a `in`A fv_ce v ->
  wf_typ_in E T ->           (* implies a notin fv_ct T *)
  a `~in`A env_fv_ct F ->    (* new definition *)
  typing (F ++ [(a, bind_lab Q)] ++ E) v T ->
  typing (F ++ E) v T.
Proof.
  admit.
Admitted.

(* a : {*} Return[Unit] ⊢ (λx. ((λy. ()) (λ(z : {a} Top). z))) : {} Unit *)
Lemma typing_strengthening_lab: forall a Q E v T,
  ~ a `in`A `cset_fvars` (free_for_cv v) ->
  wf_typ_in E T ->           (* implies a notin fv_ct T *)
  typing ([(a, bind_lab Q)] ++ E) v T ->
  typing E v T.
Proof.
  admit.                    (* cannot be shown inductively *)
Admitted.

Lemma preservation : forall e e',
  typing_state e ->
  step e e' ->
  typing_state e'.
Proof with simpl_env; eauto using typing_ctx_sub, wf_cset_set_weakening.
  intros * Typ Step.
  inversion Step; subst.
  - Case "step-app".
    inversion Typ; subst.
    dependent induction H2...
    econstructor...
    econstructor...
  - Case "step-tapp".
    inversion Typ; subst.
    dependent induction H2...
    econstructor...
    econstructor...
  - Case "step-fun->arg".
    inversion Typ; subst.
    dependent induction H2...
    econstructor...
    econstructor...
  - Case "step-throw".
    inversion Typ; subst.
    dependent induction H2...
    econstructor...
    econstructor...
  - Case "step-handler->arg".
    inversion Typ; subst...
    dependent induction H2...
    econstructor...
    econstructor...
  - Case "step-app".
    inversion Typ; subst...
    assert (no_type_bindings E) by (eauto using typing_ctx_free_tvar).
    dependent induction H2...

    destruct (typing_inv_abs _ _ _ _ H0 T1 T2 C ltac:(eauto using sub_reflexivity))
      as (Sub & S2 & L & TypingX)...

    pick fresh x.

    destruct (TypingX x) as (TypingX' & Wf & SubS2)...

    eapply typ_step...
    rewrite (subst_ee_intro x)...
    rewrite (subst_ct_intro x)...
    assert (wf_typ_in E T1') as WfTypV by eauto.
    assert (wf_typ_in E T1)  as WfTypT by eauto.
    (**
      E - environment
      x - fresh atom
      v - argument/value
      e0 - body of abstraction (\lambda T e0)
    *)
    forwards (C' & P' & ?): inversion_toplevel_type WfTypV; subst...
    forwards (C'' & P'' & ?): inversion_toplevel_type WfTypT; subst...

    eapply typing_through_subst_ee' with (Ap := dom E `union` singleton x) (Am := dom E)...
    + (* typing *)
      rewrite_nil_concat.
      eapply typing_narrowing_typ...
      eapply typing_sub...
      rewrite_nil_concat.
      eapply typing_narrowing_typ...
    + rewrite_env (empty ++ [(x, bind_typ (typ_capt C' P'))] ++ E).
      eapply wf_typ_narrowing_typ_base with (V := T); simpl_env...
    + (* wf_cset free_for_cv *)
      rename select (typing E v _) into TypV.
      forwards WfFvV: typing_cv TypV...
    + (* wf_cset C *)
      assert (wf_cset_in E C') as WfC by eauto...

  - Case "step-tapp".
    inversion Typ; subst...
    dependent induction H1...
    econstructor...

    destruct (typing_inv_tabs _ _ _ _ H2 T0 T3 _ ltac:(eauto using sub_reflexivity))
      as (Sub & S2 & L & TypingX).

    pick fresh x.
    destruct (TypingX x) as [Typ' SubS2]...
    rewrite (subst_te_intro x)...
    rewrite (subst_tt_intro x)...
    rewrite_env (map (subst_tb x T2) empty ++ E).
    apply (typing_through_subst_te T0)...
  - inversion Typ; subst...
    assert (no_type_bindings E) by (eauto using typing_ctx_free_tvar).
    eapply typ_step...
    eapply typing_ctx_reset...
    dependent induction H3...
    + admit.
  - inversion Typ; subst...
    dependent induction H2...
    econstructor...
    admit.
  - inversion Typ; subst...
    dependent induction H2...
    econstructor...
  - inversion Typ; subst...
    dependent induction H2...
    econstructor...
  - inversion Typ; subst...
    dependent induction H2...
    econstructor...
  - inversion Typ; subst...
    dependent induction H2...
    econstructor...
  - inversion Typ; subst...
    admit.
  - inversion Typ; subst.
    dependent induction H2...
    rename select (binds a _ _) into BndA.
    assert (binds a (bind_lab (typ_capt {*} (typ_exc T)))
                  ([(a, bind_lab (typ_capt {*} (typ_exc T)))] ++ E)) as HA by eauto.
    forwards EQ: binds_unique HA BndA.
    inversion EQ; subst; clear EQ HA.
    econstructor...
    rename select (typing _ v _) into TypA.
    assert (`cset_uvar` (cv Teff) = false) as NonDerivation1 by admit.
    assert (a `~in`A `cset_fvars` (cv Teff)) as NonDerivation2 by admit.
    assert (value v) by admit.
    forwards: non_derivation_implies_absence TypA...
    rewrite_env (empty ++ [(a, bind_lab (typ_capt {*} (typ_exc Teff)))] ++ E) in TypA.
Admitted.

(* ********************************************************************** *)
(** * #<a name="progress"></a># Progress *)

(* ********************************************************************** *)
(** ** Progress (16) *)

Lemma progress_step : forall s1,
  typing_state s1 ->
  done s1 \/ exists s2, s1 --> s2.
Proof with eauto.
  intros * Typ.
  inversion Typ; subst.
  remember empty. generalize dependent Heql.
  rename select (typing l e T) into Typ'.
  dependent induction Typ'; intros EQ; subst...
  - inversion select (binds _ _ _).
  - inversion select (binds _ _ _).
  - inversion Typ; subst.
    assert (value (exp_abs V e1))...
    inversion H; subst...
    + left...
      constructor...
    + right.
      destruct (canonical_form_abs _ _ _ _ H5 H8) as [S [ E1 EQ ] ]; subst...
  - inversion Typ; subst.
    assert (value (exp_tabs V e1))...
    inversion H; subst...
    + left...
      constructor...
    + right.
      destruct (canonical_form_abs _ _ _ _ H5 H8) as [S [ E1 EQ ] ]; subst...
  - apply IHTyp'...
    eapply ctx_typing_narrowing...
Qed.
