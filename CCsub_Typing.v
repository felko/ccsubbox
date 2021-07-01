Require Import Coq.Program.Equality.
Require Import TaktikZ.
Require Export CCsub_Hints.
Require Import CCsub_Subcapt.
Require Import CCsub_Subtyping.

(* ********************************************************************** *)
(** * #<a name="typing"></a># Properties of typing *)


(* ********************************************************************** *)
(** ** Weakening (5) *)
Lemma wf_typ_return_typing_handle_forall_hint : forall L E Q e T1, 
  (forall x : atom,
    x `~in`A L ->
    [(x, bind_typ (typ_capt {*} (typ_ret T1)))] ++ E @ Q
    |-t open_ee e x (`cset_fvar` x) ~: T1) ->
  wf_typ_in E T1.
Proof with eauto.
  intros.
  pick fresh x. specialize (H x ltac:(eauto))...
  forwards [WfEnv _] : typing_regular H...
  apply wf_typ_from_wf_env_typ in WfEnv...
  inversion WfEnv; subst...
  inversion H6; subst...
Qed.
Lemma wf_typ_return_from_typing_handle : forall x L E Q e T1, 
  x `~in`A L ->
  [(x, bind_typ (typ_capt {*} (typ_ret T1)))] ++ E @ Q
    |-t open_ee e x (`cset_fvar` x) ~: T1 ->
  wf_typ_in E T1.
Proof with eauto.
  intros.
  forwards [WfEnv _] : typing_regular H0...
  apply wf_typ_from_wf_env_typ in WfEnv...
  inversion WfEnv; subst...
  inversion H7; subst...
Qed.
Hint Resolve wf_typ_return_typing_handle_forall_hint : core.

Lemma typing_weakening : forall E F G Q e T,
  typing (G ++ E) Q e T ->
  wf_env (G ++ F ++ E) ->
  typing (G ++ F ++ E) Q e T.
Proof with simpl_env;
           eauto using wf_typ_weakening,
                       wf_typ_in_weakening,
                       wf_typ_from_wf_env_typ,
                       wf_typ_from_wf_env_sub,
                       sub_weakening,
                       subcapt_weakening.
  intros * Typ.
  remember (G ++ E).
  generalize dependent G.
  induction Typ; intros G EQ Ok; subst...
  - Case "typing_abs".
    pick fresh X and apply typing_abs...
    + lapply (H0 X); [intros K | auto].
      simpl_env in *.
      rewrite <- concat_assoc.
      eapply wf_typ_weakening.
      * apply K.
      * trivial...
      * clear_frees; fsetdec.
      * clear_frees; fsetdec.
    + lapply (H1 X); [intros K | auto].
      simpl_env in *.
      rewrite <- concat_assoc.
      apply (H2 X)...
  - Case "typing_tabs".
    pick fresh X and apply typing_tabs...
    + lapply (H0 X); [intros K | auto].
      simpl_env in *.
      rewrite <- concat_assoc.
      eapply wf_typ_weakening.
      * apply K.
      * trivial...
      * clear_frees; fsetdec.
      * clear_frees; fsetdec.
    + lapply (H1 X); [intros K | auto].
      simpl_env in *.
      rewrite <- concat_assoc.
      apply (H2 X)...
  - Case "typing_handle".
    pick fresh X and apply typing_handle...
    + lapply (H X); [intros K | auto].
      simpl_env in *.
      rewrite <- concat_assoc.
      apply (H0 X)...
    + intro Contra.
      pick fresh x.
      specialize (H x ltac:(notin_solve)) as Wf2...
      eapply subcapt_strengthening in Contra...
      apply cv_wf...
  - Case "typing_do_ret".
    eapply typing_do_ret...
Qed.


(************************************************************************ *)
(** ** Narrowing for typing (7) *)

Lemma typing_narrowing : forall Q E F X P QQ e T,
  sub E P Q ->
  typing (F ++ [(X, bind_sub Q)] ++ E) QQ e T ->
  typing (F ++ [(X, bind_sub P)] ++ E) QQ e T.
Proof with eauto using wf_env_narrowing, wf_typ_narrowing, sub_narrowing, subcapt_narrowing.
  intros * PsubQ Typ.
  remember (F ++ [(X, bind_sub Q)] ++ E).
  generalize dependent F.
  induction Typ; intros F EQ; subst...
  - Case "typing_var".
    binds_cases H1...
    constructor...
  - Case "typing_var".
    binds_cases H1...
    eapply typing_var...
  - Case "typing_abs".
    assert (wf_env (F ++ [(X, bind_sub P)] ++ E)). {
      pick fresh y for L.
      forwards (P0 & _): typing_regular (H1 y Fr).
      inversion P0; subst...
    }
    pick fresh y and apply typing_abs...
    + rewrite_parenthesise_binding.
      simpl_env in H0...
      eapply wf_typ_narrowing_base; simpl_env...
    + rewrite <- concat_assoc.
      apply H2...
  - Case "typing_tabs".
    assert (wf_env (F ++ [(X, bind_sub P)] ++ E)). {
      pick fresh y for L.
      forwards (P0 & _): typing_regular (H1 y Fr).
      inversion P0; subst...
    }
    pick fresh Y and apply typing_tabs...
    + rewrite_parenthesise_binding.
      simpl_env in H0...
      eapply wf_typ_narrowing_base; simpl_env...
    + rewrite <- concat_assoc.
      apply H2...
  - Case "typing_handle".
    assert (wf_env (F ++ [(X, bind_sub P)] ++ E)). {
      pick fresh y for L.
      forwards (P0 & _): typing_regular (H y Fr).
      inversion P0; subst...
    }
    pick fresh y and apply typing_handle...
    rewrite_parenthesise_binding.
    simpl_env in H0...
    intro ScUniv.
    eapply subcapt_widening_univ in ScUniv...
  - Case "typing_do_ret".
    eapply typing_do_ret...
Qed.


Inductive syn_cat_agree : typ -> typ -> Prop :=
| syn_cat_agree_tvar : forall (X Y : atom),
    syn_cat_agree X Y
| syn_cat_agree_concrete : forall C P D U,
    syn_cat_agree (typ_capt C P) (typ_capt D U)
.


Lemma sub_of_tvar : forall E P (X : atom),
  sub E P X ->
  exists (Y : atom), P = Y.
Proof.
  intros * H.
  dependent induction H...
  * exists X; trivial.
  * exists X0; trivial.
Qed.

Lemma typing_narrowing_typ_aux : forall Q E F X P QQ e T,
  typing (F ++ [(X, bind_typ Q)] ++ E) QQ e T ->
  sub E P Q ->
  syn_cat_agree P Q ->
  typing (F ++ [(X, bind_typ P)] ++ E) QQ e T.
Proof with simpl_env; eauto using
    wf_env_narrowing_typ, wf_typ_narrowing_typ, sub_narrowing_typ,
    sub_weakening, type_from_wf_typ.
  intros *. intros HT HSub HAg.
  assert (type P) as Htype by eauto*.
  dependent induction HT...
  (* typing_var_tvar *)
  - destruct (x == X) eqn:HX; subst...
    + binds_cases H1; simpl_env in *; try notin_solve...
      inversion H2; subst...
      lets (Y & HP): sub_of_tvar HSub; subst... (* lets signifies that all arguments are applied *)
      eapply typing_sub...
      * eapply typing_var_tvar...
      * rewrite_env (empty ++ (F ++ [(X, bind_typ Y)]) ++ E).
        apply sub_weakening...
    + eapply typing_var_tvar...
  (* typing_var *)
  - destruct (x == X) eqn:HX; subst...
    + dependent induction P; inversion Htype; subst...
      * binds_get H1; inversion H3; subst...
        eapply typing_sub.
        ** eapply typing_var...
        ** rewrite_env (empty ++ (F ++ [(X, bind_typ (typ_capt c p))]) ++ E).
           apply sub_capt.
           ++ eapply subcapt_reflexivity with (A := singleton X)...
              econstructor...
              intros X' HX'; assert (X = X') by fsetdec; subst.
              exists (typ_capt c p); constructor...
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
      forwards HA: H1 z Fr; simpl_env in HA.
      forwards (? & ? & ?): typing_regular HA...
    }
    pick fresh y and apply typing_tabs...
    + simpl_env in *.
      rewrite_parenthesise_binding.
      eapply wf_typ_narrowing_typ_base...
    + rewrite_parenthesise_binding.
      eapply H2...
  - assert (wf_env (F ++ [(X, bind_typ P)] ++ E)). {
      pick fresh z for L.
      forwards (? & ? & ?): typing_regular (H z Fr)...
    }
    pick fresh y and apply typing_handle...
    + rewrite_parenthesise_binding.
      eapply H0...
    + intro ScUniv. eapply subcapt_widening_typ_univ in ScUniv...
  - eapply typing_do_ret...
Qed.

Lemma typing_narrowing_typ_tvars : forall (X Y : atom) E F Q x e T,
  typing (F ++ [(x, bind_typ X)] ++ E) Q e T ->
  sub E Y X ->
  typing (F ++ [(x, bind_typ Y)] ++ E) Q e T.
Proof with eauto.
  intros.
  eapply typing_narrowing_typ_aux...
  constructor.
Qed.

Lemma typing_narrowing_typ : forall Q E F X C P QQ e T,
  typing (F ++ [(X, bind_typ Q)] ++ E) QQ e T ->
  sub E (typ_capt C P) Q ->
  typing (F ++ [(X, bind_typ (typ_capt C P))] ++ E) QQ e T.
Proof with eauto.
  intros* ? Hsub.
  inversion Hsub; subst.
  eapply typing_narrowing_typ_aux...
  constructor.
Qed.


(* ********************************************************************** *)
(** ** Inversion of typing (13) *)

Lemma typing_inv_abs : forall E Q S1 e1 T,
  typing E Q (exp_abs S1 e1) T ->
  forall U1 U2 C, sub E T (typ_capt C (typ_arrow U1 U2)) ->
     sub E U1 S1
  /\ exists S2, exists L, forall x, x `notin` L ->
    typing ([(x, bind_typ S1)] ++ E) Q (open_ee e1 x (`cset_fvar` x)) (open_ct S2 (`cset_fvar` x)) /\
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

Lemma typing_inv_tabs : forall E Q S1 e1 T,
  typing E Q (exp_tabs S1 e1) T ->
  forall U1 U2 C, sub E T (typ_capt C (typ_all U1 U2)) ->
     sub E U1 S1
  /\ exists S2, exists L, forall X, X `notin` L ->
     typing ([(X, bind_sub U1)] ++ E) Q (open_te e1 X) (open_tt S2 X)
     /\ sub ([(X, bind_sub U1)] ++ E) (open_tt S2 X) (open_tt U2 X).
Proof with simpl_env; auto.
  intros * Htyp.
  dependent induction Htyp; intros U1 U2 C Hsub.
  - Case "typing_abs".
    inversion Hsub; subst.
    inversion select (sub_pre _ _ _); subst.
    split...
    exists T1.
    exists (L `union` L0).
    intros y ?.
    repeat split...
    rewrite_env (empty ++ [(y, bind_sub U1)] ++ E).
    eapply typing_narrowing with (Q := S1)...
  - Case "typing_sub".
    eauto using (sub_transitivity T).
Qed.


Lemma typing_weakening_sig : forall Q2 E Q1 Q3 e T,
  typing E (Q1 ++ Q3) e T ->
  wf_sig (Q1 ++ Q2 ++ Q3) ->
  typing E (Q1 ++ Q2 ++ Q3) e T.
Proof with eauto.
  intros * Typ Wf.
  dependent induction Typ; solve_obvious.
  - eapply typing_lvar with (C := C)...
    apply Signatures.binds_weaken...
    (* ok from wf_sig *)
    admit.
Admitted.
