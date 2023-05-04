Require Import Coq.Program.Equality.
Require Import TaktikZ.
Require Import LibTactics.
Require Export CCsub_Hints.
Require Import CCsub_Subcapt.
Require Import CCsub_Subtyping.

(* ********************************************************************** *)
(** * #<a name="typing"></a># Properties of typing *)

(* ********************************************************************** *)
(** ** Weakening (5) *)
Lemma typing_weakening : forall Γ Θ Δ e T,
  (Δ ++ Γ) ⊢ e : T ->
  (Δ ++ Θ ++ Γ) ⊢ wf ->
  (Δ ++ Θ ++ Γ) ⊢ e : T.
Proof with simpl_env;
           eauto using wf_typ_weakening,
                       wf_typ_from_wf_env_typ,
                       wf_typ_from_wf_env_sub,
                       sub_weakening,
                       subcapt_weakening.
  intros * Typ.
  remember (Δ ++ Γ).
  generalize dependent Δ.
  induction Typ; intros Δ EQ Ok; subst...
  - Case "typing_abs".
    pick fresh X and apply typing_abs...
    lapply (H0 X); [intros K | auto].
    simpl_env in *.
    rewrite <- concat_assoc.
    apply H1...
  - Case "typing_let".
    pick fresh X and apply typing_let...
    lapply (H X); [intros K | auto].
    simpl_env in *.
    rewrite <- concat_assoc.
    apply (H0 X)...
    apply wf_env_typ...
    destructs typing_regular Typ as [WfEnv [Expr WfTyp]].
    constructor.
    + apply wf_cset_weakening... 
    + apply wf_typ_weakening...
      inversion WfTyp...
    + enough (Typ' : type (C1 # T1)) by (inversion Typ'; subst; [ inversion H1 | auto ]).
      eapply type_from_wf_typ, WfTyp.
  - Case "typing_tabs".
    pick fresh X and apply typing_tabs...
    lapply (H1 X); [intros K | auto].
    simpl_env in *.
    rewrite <- concat_assoc.
    apply H2...
  - Case "typing_box".
    apply typing_box...
    simpl_env in H.
    fsetdec.
  - Case "typing_unbox".
    apply typing_unbox...
    apply wf_cset_weakening... 
Qed.


(************************************************************************ *)
(** ** Narrowing for typing (7) *)

Lemma typing_narrowing : forall Q Δ Γ X P e T,
  Γ ⊢ P <: Q ->
  (Δ ++ [(X, bind_sub Q)] ++ Γ) ⊢ e : T ->
  (Δ ++ [(X, bind_sub P)] ++ Γ) ⊢ e : T.
Proof with eauto using wf_env_narrowing, wf_typ_ignores_sub_bindings, sub_narrowing, subcapt_narrowing.
  intros * PsubQ Typ.
  assert (PureP : pure_type P).
  { enough (PureQ : pure_type Q) by (applys sub_pure_type PsubQ; eauto* ).
    forwards (WfEnv & _): typing_regular Typ.
    apply wf_env_tail in WfEnv.
    inversion WfEnv...
  }
  assert (WfEnv : wf_env (Δ ++ [(X, bind_sub P)] ++ Γ)). {
    apply wf_env_narrowing with (V := Q)...
    applys typing_regular Typ.
  }
  remember (Δ ++ [(X, bind_sub Q)] ++ Γ).
  generalize dependent Δ.
  induction Typ; intros Δ EQ WfEnv; subst.
  - Case "typing_var".
    binds_cases H0...
  - Case "typing_abs".
    pick fresh y and apply typing_abs...
    rewrite <- concat_assoc.
    apply H1...
    econstructor...
  - Case "typing_app".
    eapply typing_app...
  - Case "typing_let".
    pick fresh y and apply typing_let...
    rewrite_parenthesise_binding.
    apply H0...
    apply wf_env_typ...
    apply wf_typ_ignores_sub_bindings with (V := Q).
    applys typing_regular Typ.
  - Case "typing_tabs".
    pick fresh Y and apply typing_tabs...
    rewrite <- concat_assoc.
    apply H2...
    apply wf_env_sub...
  - Case "typing_tapp".
    eapply typing_tapp...
  - Case "typing_box".
    apply typing_box...
    simpl_env in *; assumption.
  - Case "typing_unbox".
    apply typing_unbox...
    eapply wf_cset_narrowing...
  - Case "typing_sub".
    apply typing_sub with (S := S)... 
Qed.

(* REVIEW: not needed anymore: we have a strict distinction between pure and capt type
           even though the raw syntax encompasses both 
Inductive syn_cat_agree : typ -> typ -> Prop :=
| syn_cat_agree_tvar : forall (X Y : atom),
    syn_cat_agree X Y
| syn_cat_agree_concrete : forall C P D U,
    syn_cat_agree (typ_capt C P) (typ_capt D U). *)

Lemma sub_of_tvar : forall Γ P (X : atom),
  Γ ⊢ P <: X ->
  exists (Y : atom), P = Y.
Proof.
  intros * Sub.
  assert (PureP : pure_type P).
  { applys sub_pure_type Sub.
    constructor.
  }
  dependent induction Sub...
  * exists X; trivial.
  * inversion PureP.
Qed.

(*
Lemma typing_narrowing_typ_aux : forall Q Γ Δ X P e T,
  (Δ ++ [(X, bind_typ Q)] ++ Γ) ⊢ e : T ->
  Γ ⊢ P <: Q ->
  syn_cat_agree P Q ->
  (Δ ++ [(X, bind_typ P)] ++ Γ) ⊢ e : T.
Proof with simpl_env; eauto using
    wf_env_narrowing_typ, wf_typ_ignores_typ_bindings, sub_narrowing_typ,
    sub_weakening, type_from_wf_typ.
  intros *. intros HT HSub HAg.
  assert (type P) as Htype by eauto*.
  dependent induction HT...
  (* typing_var_tvar *)
  - destruct (x == X) eqn:HX; subst...
    + binds_cases H0; simpl_env in *; try notin_solve...
      inversion H1; subst...
      lets (Y & HP): sub_of_tvar HSub; subst... (* lets signifies that all arguments are applied *)
      eapply typing_sub...
      * eapply typing_var_tvar...
      * rewrite_env (empty ++ (F ++ [(X, bind_typ Y)]) ++ E).
        apply sub_weakening...
    + eapply typing_var_tvar...
  (* typing_var *)
  - destruct (x == X) eqn:HX; subst...
    + dependent induction P; inversion Htype; subst...
      * binds_get H0; inversion H2; subst...
        eapply typing_sub.
        ** eapply typing_var...
        ** rewrite_env (empty ++ (F ++ [(X, bind_typ (typ_capt c p))]) ++ E).
           apply sub_capt.
           ++ eapply subcapt_reflexivity with (A := singleton X)...
              econstructor...
              intros X' HX'; assert (X = X') by fsetdec; subst.
              exists (typ_capt c p); constructor...
              all: clear; fsetdec.
           ++ apply sub_pre_weakening...
              inversion HSub...
      * rename select (binds X _ _) into HH.
        binds_get HH; inversion select (bind_typ _ = bind_typ _); subst...
        inversion HAg.
    + eapply typing_var...
  - assert (wf_env (F ++ [(X, bind_typ P)] ++ E)). {
      pick fresh z for L.
      forwards HA: H1 z Fr; simpl_env in HA.
      forwards (? & ? & ?): typing_regular HA...
    }
    pick fresh y and apply typing_abs...
    + simpl_env in *.
      rewrite_parenthesise_binding.
      eapply wf_typ_narrowing_typ_base...
    + rewrite_parenthesise_binding.
      eapply H2...
  - assert (wf_env (F ++ [(X, bind_typ P)] ++ E)). {
      pick fresh z for L.
      forwards HA: H z Fr; simpl_env in HA.
      forwards (? & ? & ?): typing_regular HA...
    }
    pick fresh y and apply typing_let...
    rewrite_parenthesise_binding.
    eapply H0...
  - assert (wf_env (F ++ [(X, bind_typ P)] ++ E)). {
      pick fresh z for L.
      forwards HA: H1 z Fr; simpl_env in HA.
      forwards (? & ? & ?): typing_regular HA...
    }
    pick fresh y and apply typing_tabs...
    + simpl_env in *.
      rewrite_parenthesise_binding.
      eapply wf_typ_narrowing_typ_base...
    + rewrite_parenthesise_binding.
      eapply H2...
Qed.
*)

(*
Lemma typing_narrowing_typ_tvars : forall (X Y : atom) E F x e T,
  typing (F ++ [(x, bind_typ X)] ++ E) e T ->
  sub E Y X ->
  typing (F ++ [(x, bind_typ Y)] ++ E) e T.
Proof with eauto.
  intros.
  eapply typing_narrowing_typ_aux...
  constructor.
Qed.
*)

Lemma typing_narrowing_typ : forall D Q Γ Δ X C P e T,
  (Δ ++ [(X, bind_typ (D # Q))] ++ Γ) ⊢ e : T ->
  Γ ⊢ (C # P) <: (D # Q) ->
  (Δ ++ [(X, bind_typ (C # P))] ++ Γ) ⊢ e : T.
Proof with eauto*.
  intros * Typ Sub.
  assert (CsubD_PsubQ_WfC_WfD_PureP_PureQ : Γ ⊢ₛ C <: D /\ Γ ⊢ P <: Q /\ Γ ⊢ₛ C wf /\ Γ ⊢ₛ D wf /\ pure_type P /\ pure_type Q).
  { dependent induction Sub...
    destruct (IHSub D Q {} U)...
    repeat split...
    - assert (WfEU : Γ ⊢ ({} # U) wf) by (applys sub_regular Sub; assumption ).
      inversion WfEU; subst.
      rename select (Γ ⊢ U wf) into WfU.
      apply sub_transitivity with (Q := U).
      + eapply type_from_wf_typ...
      + apply sub_tvar...
      + applys IHSub...
    - intros x xIn; exfalso; clear - xIn; fsetdec.
  }
  destruct CsubD_PsubQ_WfC_WfD_PureP_PureQ as [CsubD [PsubQ [WfC [WfD [PureP PureQ]]]]].
  dependent induction Typ.
  - Case "typing_var".
    rename select (binds _ _ _) into Binds.
    binds_cases Binds; simpl_env in *.
    + eapply typing_var...
      eapply wf_env_narrowing_typ...
    + injection H1 as ReqQ C0eqD; subst.
      apply typing_sub with (S := `cset_fvar` x # P).
      * apply typing_var with (C := C)...
        eapply wf_env_narrowing_typ...
      * apply sub_capt...
        -- apply subcapt_reflexivity...
           econstructor; intros y yIn; assert (y = x) by fsetdec; subst; clear yIn...
        -- rewrite_env (∅ ++ (Δ ++ [(x, bind_typ (C # P))]) ++ Γ).
           apply sub_weakening...
           simpl_env.
           eapply wf_env_narrowing_typ...
    + apply typing_var with (C := C0)...
      eapply wf_env_narrowing_typ...
  - Case "typing_abs".
    pick fresh y and apply typing_abs...
    + simpl_env in *.
      eapply wf_typ_ignores_typ_bindings...
    + rewrite_parenthesise_binding.
      eapply H1...
  - Case "typing_app".
    eapply typing_app...
  - Case "typing_let".
    pick fresh y and apply typing_let...
    rewrite_parenthesise_binding.
    eapply H0...
  - Case "typing_tabs".
    pick fresh Y and apply typing_tabs...
    + simpl_env in *.
      eapply wf_typ_ignores_typ_bindings...
    + rewrite_parenthesise_binding.
      eapply H2...
  - Case "typing_tapp".
    eapply typing_tapp...
    eapply sub_narrowing_typ...
  - Case "typing_box".
    apply typing_box...
    simpl_env in *...
  - Case "typing_unbox".
    apply typing_unbox...
    eapply wf_cset_narrowing_typ...
    apply ok_from_wf_env.
    eapply wf_env_narrowing_typ...
    applys typing_regular Typ.
  - Case "typing_sub".
    apply typing_sub with (S := S)...
    eapply sub_narrowing_typ...
Qed.

(* ********************************************************************** *)
(** ** Inversion of typing (13) *)

Lemma typing_inv_abs : forall Γ S1 e1 T,
  Γ ⊢ (λ (S1) e1) : T ->
  forall U1 U2 C, Γ ⊢ T <: (C # (∀ (U1) U2)) ->
     Γ ⊢ U1 <: S1
  /\ exists S2, exists L, forall x, x ∉ L ->
    ([(x, bind_typ S1)] ++ Γ) ⊢ (open_ve e1 x (`cset_fvar` x)) : (open_ct S2 (`cset_fvar` x)) /\
    ([(x, bind_typ S1)] ++ Γ) ⊢ (open_ct U2 (`cset_fvar` x)) wf /\
    ([(x, bind_typ U1)] ++ Γ) ⊢ (open_ct S2 (`cset_fvar` x)) <: (open_ct U2 (`cset_fvar` x)).
Proof with auto.
  intros * Typ.
  dependent induction Typ; intros U1 U2 D Sub.
  - Case "typing_abs".
    inversion Sub; subst.
    inversion select (_ ⊢ _ <: _); subst.
    split...
    exists T1.
    exists (L `u`A L0).
    intros y ?.
    rename select (forall x : atom, x ∉ L0 -> _) into Sub'.
    specialize (Sub' y ltac:(fsetdec)).
    repeat split...
    + applys sub_regular Sub'.
    + rewrite_nil_concat.
      eapply sub_narrowing_typ with (CQ := C) (Q:= R)...
  - Case "typing_sub".
    eauto using (sub_transitivity T).
Qed.

Lemma typing_inv_tabs : forall Γ S1 e1 T,
  Γ ⊢ (Λ [S1] e1) : T ->
  forall U1 U2 C, Γ ⊢ T <: (C # (∀ [U1] U2)) ->
     Γ ⊢ U1 <: S1
  /\ exists S2, exists L, forall X, X ∉ L ->
       ([(X, bind_sub U1)] ++ Γ) ⊢ (open_te e1 X) : (open_tt S2 X) /\
       ([(X, bind_sub U1)] ++ Γ) ⊢ (open_tt S2 X) <: (open_tt U2 X).
Proof with simpl_env; auto.
  intros * Typ.
  dependent induction Typ; intros U1 U2 D Sub.
  - Case "typing_tabs".
    inversion Sub; subst.
    inversion select (_ ⊢ _ <: _); subst.
    split...
    exists T1.
    exists (L `union` L0).
    intros Y ?.
    repeat split...
    rewrite_nil_concat.
    + eapply typing_narrowing with (Q := S1)...
    + rename select (forall X : atom, X ∉ L0 -> _) into Sub'.
      specialize (Sub' Y ltac:(fsetdec)).
      rewrite_nil_concat.
      apply sub_narrowing with (Q := S1)...
  - Case "typing_sub".
    eauto using (sub_transitivity T).
Qed.

Lemma typing_inv_let : forall Γ e k T,
  Γ ⊢ (let= e in k) : T ->
  exists C R,
       Γ ⊢ e : (C # R)
    /\ exists L, forall x, x ∉ L ->
         ([(x, bind_typ (C # R))] ++ Γ) ⊢ (open_ve k x (`cset_fvar` x)) : T.
Proof with eauto*.
  intros * Typ.
  dependent induction Typ...
  destruct (IHTyp e k ltac:(reflexivity)) as [C [R [eTyp [L kTyp]]]].
  exists C, R.
  split...
  exists (L `u`A dom Γ).
  intros y NotIn.
  specialize (kTyp y ltac:(clear - NotIn; fsetdec)).
  apply typing_sub with (S := S)...
  rewrite_env (∅ ++ [(y, bind_typ (C # R))] ++ Γ).
  apply sub_weakening...
  apply wf_env_typ...
  applys typing_regular eTyp. 
Qed.