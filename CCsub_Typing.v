Require Import Coq.Program.Equality.
Require Import TaktikZ.
Require Export CCsub_Hints.
Require Import CCsub_Subcapt.
Require Import CCsub_Subtyping.

(* ********************************************************************** *)
(** * #<a name="typing"></a># Properties of typing *)


(* ********************************************************************** *)
(** ** Weakening (5) *)

Lemma typing_weakening : forall E F G e T,
  typing (G ++ E) e T ->
  wf_env (G ++ F ++ E) ->
  typing (G ++ F ++ E) e T.
Proof with simpl_env;
           eauto using wf_typ_weakening,
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
Qed.


(************************************************************************ *)
(** ** Narrowing for typing (7) *)

Lemma typing_narrowing : forall Q E F X P e T,
  sub E P Q ->
  typing (F ++ [(X, bind_sub Q)] ++ E) e T ->
  typing (F ++ [(X, bind_sub P)] ++ E) e T.
Proof with eauto 6 using wf_env_narrowing, wf_typ_narrowing, sub_narrowing, subcapt_narrowing.
  intros Q E F X P e T PsubQ Typ.
  remember (F ++ [(X, bind_sub Q)] ++ E).
  generalize dependent F.
  induction Typ; intros F EQ; subst...
  - Case "typing_var".
    binds_cases H0...
  - Case "typing_var".
    binds_cases H0...
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

Lemma typing_narrowing_typ_aux : forall Q E F X P e T,
  typing (F ++ [(X, bind_typ Q)] ++ E) e T ->
  sub E P Q ->
  syn_cat_agree P Q ->
  typing (F ++ [(X, bind_typ P)] ++ E) e T.
Proof with simpl_env; eauto using
    wf_env_narrowing_typ, wf_typ_narrowing_typ, sub_narrowing_typ,
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
           ++ apply sub_pre_weakening...
              inversion HSub...
      * binds_get H0; inversion H2; subst...
        inversion HAg.
    + eapply typing_var...
  - assert (wf_env (F ++ [(X, bind_typ P)] ++ E)). {
      pick fresh z for L.
      pose proof (H1 z Fr)...
    }
    pick fresh y and apply typing_abs...
    + simpl_env in *.
      rewrite_parenthesise_binding.
      eapply wf_typ_narrowing_typ_base...
    + rewrite_parenthesise_binding.
      eapply H2...
  - assert (wf_env (F ++ [(X, bind_typ P)] ++ E)). {
      pick fresh z for L.
      pose proof (H1 z Fr)...
    }
    pick fresh y and apply typing_tabs...
    + simpl_env in *.
      rewrite_parenthesise_binding.
      eapply wf_typ_narrowing_typ_base...
    + rewrite_parenthesise_binding.
      eapply H2...
Qed.

Lemma typing_narrowing_typ_tvars : forall (X Y : atom) E F x e T,
  typing (F ++ [(x, bind_typ X)] ++ E) e T ->
  sub E Y X ->
  typing (F ++ [(x, bind_typ Y)] ++ E) e T.
Proof with eauto.
  intros.
  eapply typing_narrowing_typ_aux...
  constructor.
Qed.

Lemma typing_narrowing_typ : forall Q E F X C P e T,
  typing (F ++ [(X, bind_typ Q)] ++ E) e T ->
  sub E (typ_capt C P) Q ->
  typing (F ++ [(X, bind_typ (typ_capt C P))] ++ E) e T.
Proof with eauto.
  intros* ? Hsub.
  inversion Hsub; subst.
  eapply typing_narrowing_typ_aux...
  constructor.
Qed.


(* ********************************************************************** *)
(** ** Inversion of typing (13) *)

Lemma typing_inv_abs : forall E S1 e1 T,
  typing E (exp_abs S1 e1) T ->
  forall U1 U2 C, sub E T (typ_capt C (typ_arrow U1 U2)) ->
     sub E U1 S1
  /\ exists S2, exists L, forall x, x `notin` L ->
    typing ([(x, bind_typ S1)] ++ E) (open_ee e1 x (`cset_fvar` x)) (open_ct S2 (`cset_fvar` x)) /\
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

Lemma typing_inv_tabs : forall E S1 e1 T,
  typing E (exp_tabs S1 e1) T ->
  forall U1 U2 C, sub E T (typ_capt C (typ_all U1 U2)) ->
     sub E U1 S1
  /\ exists S2, exists L, forall X, X `notin` L ->
     typing ([(X, bind_sub U1)] ++ E) (open_te e1 X) (open_tt S2 X)
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