(** Type-safety proofs for Fsub.

    Authors: Brian Aydemir and Arthur Chargu\u00e9raud, with help from
    Aaron Bohannon, Jeffrey Vaughan, and Dimitrios Vytiniotis.

    In parentheses are given the label of the corresponding lemma in
    the appendix (informal proofs) of the POPLmark Challenge.

    Table of contents:
      - #<a href="##subtyping">Properties of subtyping</a>#
      - #<a href="##typing">Properties of typing</a>#
      - #<a href="##preservation">Preservation</a>#
      - #<a href="##progress">Progress</a># *)

Require Import Coq.Program.Equality.
Require Export Fsub_Hints.

Set Nested Proofs Allowed.

Local Ltac hint := idtac.

Local Lemma cheat : forall A, A.
Admitted.

Local Lemma cheat_with : forall A B, A -> B.
Admitted.


(** Dealing with cv -- as a fixpoint is problematic. *)
Inductive cvx : env -> typ -> captureset -> Prop :=
  (** Looking up in the environment; we ask that T is wf in the environment
      and that the environment is well formed so lookup is well defined. *)
  | cvx_typ_var : forall (X : atom) T E CT,
    binds X (bind_sub T) E ->
    wf_env E ->
    cvx E T CT ->
    cvx E (typ_fvar X) CT
  | cvx_typ_capt : forall E C P,
    wf_env E ->
    wf_pretyp_in E P ->
    wf_cset_in E C ->
    cvx E (typ_capt C P) C.


(* HINT: we had problems formalizing a version with Ap and Am since then the
   IH requires us to show wf_typ Ap Am, while we only have wf_typ_in E.
 *)
Lemma cv_unique_shrink : forall Y B E T C,
  wf_env ([(Y, B)] ++ E) ->
  wf_typ_in E T ->
  cvx ([(Y, B)] ++ E) T C ->
  cvx E T C.
Proof.
  intros*.
  intros HwfE HwfT Hcv.

  assert (type T). eapply type_from_wf_typ; eauto.

  dependent induction Hcv.
  * assert (X <> Y). {
      inversion HwfT; subst.
      assert (X `in` dom E).
      eapply binds_In. apply H6.
      inversion HwfE; subst; notin_solve.
    }
    apply cvx_typ_var with (T := T).
    unfold binds in H. unfold get in H. simpl in H.
    destruct (X == Y) eqn:HXY; subst; trivial.
    easy.

    inversion HwfE; trivial.
    eapply IHHcv with (Y0 := Y) (B0 := B).
    inversion HwfT; subst.
  
    {
      pose proof H7.
      unfold binds in H. unfold binds in H7.
      simpl in *.
      destruct (X == Y); subst; try easy.
      rewrite H in H7; inversion H7; subst.
      simpl_env in *.
      eapply wf_typ_from_binds_sub.
      inversion H0; trivial.
      apply H3.
    }
    trivial.
    trivial.
    eapply type_from_wf_typ.
    eapply wf_typ_from_binds_sub.
    apply HwfE. apply H.
  * inversion HwfT; subst. constructor; trivial.
    inversion H; trivial.
Qed.

Lemma cv_unique : forall E T C1 C2,
  wf_env E ->
  wf_typ_in E T ->
  cvx E T C1 ->
  cvx E T C2 ->
  C1 = C2.
Proof with eauto*.
  intros E; induction E; intros T; induction T; intros...
  - inversion H1; inversion H2; subst...
  - exfalso. inversion H0.
  - exfalso.
    inversion H0...
    inversion H7...
  - inversion H1...
    inversion H2...
  - inversion H0.
  - destruct a as [Y B].
    simpl_env in *.
    destruct (Y == a0); subst...
    + inversion H2; subst...
      inversion H1; subst...
      apply IHE with (T := T)...
      {inversion H5; trivial. }
      {binds_cases H4; subst; simpl_env in *; try notin_solve...
        inversion H; trivial. }
      {
        binds_cases H4; subst; simpl_env in *; try notin_solve...
        binds_cases H6; subst; simpl_env in *; try notin_solve...
        inversion H6; subst...

        eapply cv_unique_shrink.
        apply H8.
        inversion H. trivial.
        trivial.
      }
      {
        binds_cases H4; subst; simpl_env in *; try notin_solve...
        binds_cases H6; subst; simpl_env in *; try notin_solve...
        inversion H6; subst...

        eapply cv_unique_shrink.
        apply H8.
        inversion H. trivial.
        trivial.
      }
    + inversion H1; subst...
      inversion H2; subst...
      apply IHE with (T := a0)...
      {inversion H5; trivial. }
      {binds_cases H4; subst; simpl_env in *; try notin_solve...
       }
      {
        eapply cv_unique_shrink.
        apply H5.
        binds_cases H4. eapply wf_typ_var.
        apply H3.
        apply H1.
      }
      {
        eapply cv_unique_shrink.
        apply H5.
        binds_cases H4. eapply wf_typ_var.
        apply H3.
        apply H2.
      }
Qed.

Lemma capt_from_cv : forall E T C,
    cv E T C -> capt C.
Proof with eauto.
  intros.
  assert (wf_cset_in E C) as HA by auto.
  eapply capt_from_wf_cset...
Qed.

Lemma binding_uniq_from_ok : forall (F E : env) x b,
  ok (F ++ ([(x, b)]) ++ E) ->
  x `notin` (dom F `union` dom E).
Proof.
  intros.
  induction F.
  - simpl_env in *.
    inversion H; subst; eauto.
  - inversion H; subst.
    specialize (IHF ltac:(auto)).
    simpl_env in *.
    notin_solve.
Qed.

Lemma binding_uniq_from_wf_env : forall F E x b,
  wf_env (F ++ ([(x, b)]) ++ E) ->
  x `notin` (dom F `union` dom E).
Proof.
  intros.
  apply ok_from_wf_env in H.
  eapply binding_uniq_from_ok; eauto.
Qed.

Hint Resolve capt_from_cv : core.

(* ********************************************************************** *)
(** * #<a name="subtyping"></a># Properties of subtyping *)

(* ********************************************************************** *)
(** ** Weakening (2) *)

Lemma cv_weakening_head : forall E F T C,
    cv E T C ->
    wf_env (F ++ E) ->
    cv (F ++ E) T C.
Proof with eauto using cv_regular.
  intros E F T C Hcv.
  induction F...

  intros; destruct a; simpl_env in *...
  pose proof (cv_regular E T C Hcv).
  assert (wf_env (F ++ E)).
    inversion H...
  specialize (IHF H1).
  destruct T...
  * inversion IHF; subst...
    constructor; rewrite_env (empty ++ [(a, b)] ++ (F ++ E))...
    eapply wf_pretyp_weakening...
    eapply wf_cset_weakening...
  * inversion Hcv...
  * apply cv_env_irrel...
    destruct H0 as [_ [Ha _]].
    (** from wellformedness -- later *)
    assert (a0 `in` dom E). {
      inversion Ha; subst.
      eapply binds_In...
    }
    inversion H; rewrite dom_concat in *; fsetdec.
Qed.

Lemma cv_weakening : forall E F G T C,
  cv (G ++ E) T C ->
  wf_env (G ++ F ++ E) ->
  cv (G ++ F ++ E) T C.
Proof with eauto using cv_regular, cv_weakening_head.
  intros E F G T C Hcv Hwf.
  dependent induction Hcv...
  * induction G...
    (* base case *)
    {
      simpl_env in *.
      rewrite x in *.
      apply cv_weakening_head...
      rewrite <- x in *.
      constructor...
    }

    destruct a as [Y B]; simpl_env in *...
    destruct (Y == X); subst...
    {
      rewrite x in *.
      inversion x; subst...
      specialize (IHHcv E G).
      constructor...
      apply IHHcv...
      inversion Hwf...
    }
    {
      rewrite x in *.
      inversion x; subst...
      specialize (IHHcv E G).
      constructor...
      apply IHHcv...
      inversion Hwf...
    }
  * rewrite x in *.
    destruct G.
    + apply cv_weakening_head with (F := empty ++ F)...
      destruct E; simpl_env in *.
      -- inversion x...
      -- inversion x; subst...
         simpl_env in *...
    + destruct p. simpl_env in *.
      inversion x; subst...
      apply cv_env_irrel...
      apply IHHcv...
      inversion x...
      inversion Hwf...
  * apply cv_typ_capt...
    + apply wf_pretyp_weakening with (Ap := dom (G ++ E)) (Am := dom (G ++ E))...
      all : repeat rewrite dom_concat...
    + apply wf_cset_weakening with (A := dom (G ++ E))...
      all : repeat rewrite dom_concat...
Qed.

Lemma captures_weakening : forall E F G xs x,
  captures (G ++ E) xs x ->
  wf_env (G ++ F ++ E) ->
  captures (G ++ F ++ E) xs x.
Proof with auto.
  intros E F G xs x Hcap Hwf.
  remember (G ++ E).
  remember (G ++ F ++ E).
  induction Hcap.
  - apply captures_in...
  - apply captures_var with (T := T) (ys := ys) ; subst...
    apply cv_weakening...
    unfold AtomSet.F.For_all.
    intros.
    apply H2...
Qed.

Lemma subcapt_weakening : forall E F G C1 C2,
  subcapt (G ++ E) C1 C2 ->
  wf_env (G ++ F ++ E) ->
  subcapt (G ++ F ++ E) C1 C2.
Proof with eauto using wf_cset_weakening.
  intros E F G C1 C2 Hsc Hwf.
  remember (G ++ E).
  remember (G ++ F ++ E).
  induction Hsc ; subst...
  apply subcapt_set...
  unfold AtomSet.F.For_all.
  intros.
  apply captures_weakening...
Qed.

Lemma sub_weakening : forall E F G S T,
  sub (G ++ E) S T ->
  wf_env (G ++ F ++ E) ->
  sub (G ++ F ++ E) S T
with sub_pre_weakening : forall E F G S T,
  sub_pre (G ++ E) S T ->
  wf_env (G ++ F ++ E) ->
  sub_pre (G ++ F ++ E) S T.
Proof with simpl_env; eauto using wf_typ_weakening, wf_pretyp_weakening, cv_weakening, subcapt_weakening, wf_cset_weakening.
------
  intros E F G S T Sub Ok.
  remember (G ++ E).
  generalize dependent G.
  induction Sub; intros G Ok EQ; subst.
  - Case "sub_refl_tvar".
    apply sub_refl_tvar...
  - Case "sub_trans_tvar".
    apply (sub_trans_tvar U)...
  - apply sub_capt...
------
  intros E F G S T Sub Ok.
  remember (G ++ E).
  generalize dependent G.
  induction Sub; intros G Ok EQ; subst.
  - Case "sub_top".
    apply sub_top...
  - Case "sub_arrow".
    pick fresh Y and apply sub_arrow...
    + rewrite <- concat_assoc.
      eapply wf_typ_weakening...
    + rewrite <- concat_assoc.
      eapply wf_typ_weakening...
    + rewrite <- concat_assoc.
      apply sub_weakening...
  - Case "sub_all".
    pick fresh Y and apply sub_all...
    + rewrite <- concat_assoc.
      eapply wf_typ_weakening...
    + rewrite <- concat_assoc.
      eapply wf_typ_weakening...
    + rewrite <- concat_assoc.
      apply sub_weakening...
Qed.

(* ********************************************************************** *)
(** ** Reflexivity (1) *)

(*
  opening capture sets in types preserves well-formedness. *)
Lemma open_ct_wf_typ : forall E Ap Am T C,
  wf_typ E Ap Am T -> wf_typ E Ap Am (open_ct T C).
Proof with eauto using type_from_wf_typ.
  intros *.
  intros H.
  closed_type...
Qed.


(* capture set substitution does not affect subtyping

  depends on opening in the context
    binds X (bind_sub U) E -> binds X (bind_sub (open_ct U C)) E
 *)
Lemma open_ct_sub : forall E S T C,
  wf_env E ->
  sub E S T ->
  sub E (open_ct S C) (open_ct T C).
Proof with auto using open_ct_wf_typ.
  intros E S T C Eok H.
  inversion H ; simpl ; closed_type ; subst...
Qed.

(* TODO move to CaptureSets. *)
Lemma cset_subset_reflexivity (c : captureset) : cset_subset_prop c c.
Proof with auto.
  rewrite cset_subset_iff.
  unfold cset_subset_dec.
  destruct c...
  assert (AtomSet.F.subset t t = true). { rewrite <- AtomSetFacts.subset_iff. fsetdec. }
  assert (NatSet.F.subset t0 t0 = true). { rewrite <- NatSetFacts.subset_iff. fnsetdec. }
  intuition.
Qed.

Lemma subcapt_reflexivity : forall E A C,
  wf_env E ->
  (* We need as a precondition that C is locally closed! *)
  wf_cset E A C ->
  AtomSet.F.Subset A (dom E) ->
  subcapt E C C.
Proof with auto.
  intros *.
  intros Ok Closed Hsubset.
  destruct C...
  - assert (t0 = {}N). { inversion Closed... }
    subst.
    apply subcapt_set...
    + apply wf_cset_set_weakening with (A := A)...
    + apply wf_cset_set_weakening with (A := A)...
    + unfold AtomSet.F.For_all. intros.
      apply captures_in...
Qed.

(* unversals can't be subcaptres of concrete capture sets. *)
Lemma cset_universal_subset : forall tf tb,
  cset_subset_prop cset_universal (cset_set tf tb) ->
  False.
Proof with auto.
  intros tf tb H.
  inversion H...
Qed.

(* if we have a subcapture of a concrete capture set, it has to be
   concrete as well. *)
Lemma subcapt_exists : forall E C tf tb,
  subcapt E C (cset_set tf tb) ->
  exists tf' tb', C = cset_set tf' tb'.
Proof with auto.
  intros E C tf tb H.
  remember (cset_set tf tb).
  induction H.
  - inversion Heqc.
  - exists xs. exists {}N...
Qed.

Lemma cv_exists_in : forall E T,
  wf_env E ->
  wf_typ_in E T ->
  exists C, cv E T C.
Proof with eauto.
  induction E; induction T; intros; try inversion H0; try inversion H; subst...
  - inversion H5.
  - simpl_env in *.
    binds_cases H5.
    + destruct (a0 == X0).
      * subst.
        specialize (IHE T H8 H9) as [C' H'].
        exists C'. apply cv_typ_var...
      * assert (wf_typ_in E a0). { inversion H0; subst... }
        specialize (IHE a0 H8 H2) as [C' H'].
        exists C'. apply cv_env_irrel...
    + inversion H3; subst.
      specialize (IHE T H8 H9) as [C' H'].
      exists C'. apply cv_typ_var...
  - simpl_env in *.
    assert (wf_typ_in E a0). { inversion H0; subst... binds_cases H6... }
    specialize (IHE a0 H8 H1) as [C' H'].
    exists C'. apply cv_env_irrel...
    assert (a0 `in` dom E)...
    inversion H1; subst.
    eapply binds_In...
Qed.

Lemma wf_env_weaken_head : forall E F,
  wf_env (F ++ E) ->
  wf_env E.
Proof with eauto*.
  intros E F Hwf.
  induction F...
  inversion Hwf...
Qed.


Lemma captures_transitivity : forall E xs ys x,
  (* E |- {x} <: {ys} *)
  captures E ys x ->
  (* E |- {ys} <: {xs} *)
  AtomSet.F.For_all (captures E xs) ys ->
  (* E |- {x} <: {xs} *)
  captures E xs x.
Proof with auto.
  intros E xs ys x Hc Hall.
  remember ys.
  generalize dependent ys.
  remember xs.
  generalize dependent xs.
  remember x.
  generalize dependent x.
  induction Hc ; intros ; subst...
  eapply captures_var.
  apply H.
  apply H0.
  unfold AtomSet.F.For_all. intros.
  eapply H2...
Qed.

Lemma subcapt_transitivity : forall E C1 C2 C3,
  wf_env E ->
  subcapt E C1 C2 ->
  subcapt E C2 C3 ->
  subcapt E C1 C3.
Proof with auto.
  intros E C1 C2 C3 Ok H12 H23.
  remember C1.
  remember C2.
  pose proof (subcapt_regular _ _ _ H23) as [_ Wf].
  assert (capt C3). { auto. }
  inversion H12.
  - Case "subcapt_universal".
    destruct C3... exfalso. subst. inversion H23.
  - Case "subcapt_set".
    subst.
    remember C3.
    destruct C3. subst...
    inversion H; subst.
    inversion H3. inversion H3; subst.
    subst.
    inversion H23; subst.
    eapply subcapt_set...
    unfold AtomSet.F.For_all. intros.
    apply captures_transitivity with (ys := ys)...
Qed.

Lemma sub_reflexivity : forall E Ap Am T,
  wf_env E ->
  wf_typ E Ap Am T ->
  AtomSet.F.Subset Ap (dom E) ->
  AtomSet.F.Subset Am (dom E) ->
  sub E T T
with sub_pre_reflexivity : forall E Ap Am T,
  wf_env E ->
  wf_pretyp E Ap Am T ->
  AtomSet.F.Subset Ap (dom E) ->
  AtomSet.F.Subset Am (dom E) ->
  sub_pre E T T.
Proof with eauto using subcapt_reflexivity, wf_typ_set_weakening.
------
  intros *.
  intros Ok Wf HsubsetAp HsubsetAm.
  induction Wf.
  (* eauto and econstructor is still broken... hence we need to proof this manually *)
  - apply sub_refl_tvar.
    auto.
    eapply wf_typ_var with (U := U)...
  - apply sub_capt...
------
  intros *.
  intros Ok Wf HsubsetAp HsubsetAm.
  induction Wf.
  - apply sub_top...
  - apply sub_arrow with (L := L `union` dom E)...
    intros; eapply sub_reflexivity...
  - apply sub_all with (L := L `union` dom E)...
    intros; eapply sub_reflexivity...
Qed.

Lemma extract_bind_cv_from_var_cv : forall X E U C,
  binds X (bind_sub U) E ->
  cv E X C ->
  cv E U C.
Proof with eauto using cv_weakening_head.
  intros *. intros Hbinds Hcv.
  dependent induction Hcv.
  - subst.
    pose proof Hbinds as H'.
    unfold binds in H'.
    simpl in H'.
    destruct (X == X); try easy.
    injection H'.
    intros.
    subst...
  - pose proof Hbinds as H'.
    unfold binds in H'.
    simpl in H'.
    destruct (X == Y).
    + subst.
      easy.
    + apply cv_weakening_head...
Qed.

(* Subtyping implies subcapturing *)
Lemma sub_implies_subcapt : forall E A1 A2 S T C D,
  sub E S T ->
  AtomSet.F.Subset A1 (dom E) ->
  AtomSet.F.Subset A2 (dom E) ->
  wf_cset E A1 C ->
  wf_cset E A2 D ->
  cv E S C ->
  cv E T D ->
  subcapt E C D.
Local Ltac hint ::=
  eauto using subcapt_reflexivity, cv_weakening_head, extract_bind_cv_from_var_cv.
Proof with hint.
  intros *.
  intros Hsub HssetA1 HssetA2 WfC WfD HcvC HcvD.

  induction Hsub; destruct C; destruct D; try solve [inversion HcvC; inversion HcvD; subst; hint].
  - pose proof (cv_unique _ _ _ _ H H0 HcvC HcvD) as Eq; inversion Eq...
  - pose proof (cv_unique _ _ _ _ H H0 HcvC HcvD) as Eq; inversion Eq...
  (* Alex: leaving these here in case the hint breaks... *)
  (* - pose proof (cv_unique _ _ _ _ H H0 HcvC HcvD) as Eq; inversion Eq... *)
  (* - apply IHHsub... *)
  (* - econstructor... *)
  (* - inversion HcvC; subst. *)
  (*   assert (T0 = U). { *)
  (*     rewrite_env (empty ++ [(X, bind_sub T0)] ++ E0) in H. *)
  (*     apply binds_mid_eq in H... *)
  (*     inversion H... *)
  (*   } *)
  (*   inversion HcvD; subst... *)
  (*   inversion H4; subst. *)
  (*   + assert (T0 = U). { apply binds_mid_eq in H... inversion H... } *)
  (*     subst... *)
  (*   + apply IHHsub... *)
  (* - inversion HcvC. inversion HcvD. subst... *)
  (* - inversion HcvC. inversion HcvD. subst... *)
Qed.

(* ********************************************************************** *)
(** ** Narrowing and transitivity (3) *)

Lemma cv_narrowing : forall S G Z Q E P C1 C2,
  sub E P Q ->
  cv (G ++ [(Z, bind_sub Q)] ++ E) S C2 ->
  cv (G ++ [(Z, bind_sub P)] ++ E) S C1 ->
  subcapt (G ++ [(Z, bind_sub P)] ++ E) C1 C2.
Proof with auto.
  intros S G Z Q E P C1 C2 HSub HCv2 HCv1.
  (*remember (G ++ [(Z, bind_sub Q)] ++ E).*)
  generalize dependent C1.
  generalize dependent C2.
  generalize dependent G.
  induction HSub; intros; subst.
  -
    (* Given a valid capture set derivation, we can construct another
        one when we weaken the environment.

        Probably should be a lemma.*)
    assert (exists C3, cv (G ++ [(Z, bind_sub X)] ++ E) S C3). {
      eapply cv_exists_in...
    }
    inversion H1 as [C3 H2].
    epose proof (cv_unique _ _ _ _ _ _ HCv1 HCv2) as Eq; inversion Eq...
    eapply subcapt_reflexivity with (A := dom (G ++ [(Z, bind_sub X)] ++ E))...
  - (*by definition. *)
    admit.
  - (*by defininition. *)
    admit.
    (*
  - (* inductively use T1 <: T2 *)
    admit.
  -
    (** Now we need show that there is a C3 such that
       cv (G ++ [(Z, bind_sub T2)] ++ E) S C3 *)
    assert (exists C3, cv (G ++ [(Z, bind_sub T2)] ++ E) S C3). {
      apply cv_exists...
      (** two wellformedness conditions.  Probably need to strengthen
          conditions. *)
      admit.
      admit.
    }
    inversion H0 as [C3 H1].
    (* inductively, use subtyping judgement. *)
    specialize (IHHSub G C3 H1 C1 HCv1).
    (* now we need to show that C3 <: C2 and apply subcapt_transitivity,
      as cv (type_capt C T2) = C \cup cv T2 *)
    admit.
    *)
Admitted.

(* needed for sub_narrowing_typ *)
Lemma cv_narrowing_typ : forall S G x Q E P C,
  sub E P Q ->
  ok (G ++ [(x, bind_typ Q)] ++ E) ->
  cv (G ++ [(x, bind_typ Q)] ++ E) S C ->
  cv (G ++ [(x, bind_typ P)] ++ E) S C.
Proof with auto.
  intros *.
  intros HSub Ok HCv.
  remember (G ++ [(x, bind_typ Q)] ++ E). generalize dependent G.
  induction HCv ; intros ; subst...
  destruct (X == x) ; subst.
  (* - (* this can't happen, x is a variable not a type. *) *)
  (*   binds_get H. *)
  (* - apply cv_typ_var with (T := T)... *)
  (*   (* X <>x, bindings unchanged. *) *)
  (*   binds_cases H. *)
  (*   + apply binds_tail. apply binds_tail... trivial. *)
  (*   + apply binds_head... *)
Admitted.

(* Alex: subcapt_narrowing should be true so this one should be true as well,
 it's just a pain to prove it *)
Lemma captures_narrowing : forall F Z P Q E xs x,
  wf_env (F ++ [(Z, bind_sub P)] ++ E) ->
  sub E P Q ->
  captures (F ++ [(Z, bind_sub Q)] ++ E) xs x ->
  captures (F ++ [(Z, bind_sub P)] ++ E) xs x.
Proof with eauto using wf_cset_narrowing, wf_env_narrowing, cv_narrowing.
  intros F Z P Q E xs x Ok Sub H.
  remember (F ++ [(Z, bind_sub Q)] ++ E). generalize dependent F.
  (* TODO here we get the premise x `in` ys from the definition of captures.
     this can't work.
   *)
  induction H; intros; subst...
  - assert (x <> Z). {
      unfold not. intros.
      binds_cases H.
      * subst. unfold dom in Fr0. fsetdec.
      * subst.
        assert (ok (F ++ [(Z, bind_sub P)] ++ E)) by auto.
        exfalso.
        pose proof (fresh_mid_head _ _ _ _ _ H).
        pose proof (binds_In _ _ _ _ H5)...
    }

    eapply captures_var with (ys := ys) (T := T)...
    (*  This is the tricky case! *)
    + assert (wf_env (F ++ [(Z, bind_sub Q)] ++ E)) as HwfNarr...
      destruct (cv_exists_in (F ++ [(Z, bind_sub P)] ++ E) T) as [D HD]... {
        eapply wf_typ_from_binds_typ...
      }
      assert (subcapt (F ++ [(Z, bind_sub P)] ++ E) D (cset_set ys {}N)) as HscD. {
        eapply cv_narrowing...
      }
      (*
        cv T  = xs0
        forall x in xs0. captures ys x
        cv (F ++ [(Z, bind_sub Q)] ++ E) T = ys
            ^^^^^^^^^^^^^^^^^^^^^^^^^^^
                old env
        -------
        cv T = ys
      *)
      admit.

    + unfold AtomSet.F.For_all in *. intros.
      apply H2...
Admitted.

Lemma captures_narrowing_typ : forall F X P Q E xs x,
  ok (F ++ [(X, bind_typ Q)] ++ E) ->
  sub E P Q ->
  captures (F ++ [(X, bind_typ Q)] ++ E) xs x ->
  captures (F ++ [(X, bind_typ P)] ++ E) xs x.
Proof with eauto using wf_cset_narrowing_typ, wf_env_narrowing_typ, cv_narrowing_typ.
  intros F X P Q E xs x Ok Sub H.
  remember (F ++ [(X, bind_typ Q)] ++ E). generalize dependent F.
  induction H; intros; subst.
  - apply captures_in...
  - assert (cv (F ++ [(X, bind_typ P)] ++ E) T (cset_set ys {}N))...
    { destruct (x == X).
      + (* x == X *)
        binds_cases H.
        * eapply captures_var with (T := T).
          apply binds_tail.
          apply binds_tail...
          trivial.
          apply H3.
          unfold AtomSet.F.For_all in *. intros.
          apply H2...
        * inversion H4; subst.
          (* here we could choose our own captureset ys, as long as
             ys <= x
           *)
          eapply captures_var with (ys := ys)...
          2: {
            unfold AtomSet.F.For_all in *. intros.
            apply H2...
          }
          (* then use sub_implies_subcapt *)
          destruct (cv_exists_in E P) as [C CV]...
          { destruct C...
            **

            (* universal *)
                exfalso. admit.
            ** admit.
          }
        * eapply captures_var with (T := T).
          apply binds_head...
          apply H3.
          unfold AtomSet.F.For_all in *. intros.
          apply H2...
      + (* x <> X *)
        eapply captures_var with (T := T).
        { binds_cases H.
          * apply binds_tail.
            apply binds_tail...
            trivial.
          * apply binds_head...
        }
        apply H3.
        unfold AtomSet.F.For_all in *. intros.
        apply H2...
    }

Admitted.


Lemma subcapt_narrowing : forall F E Z P Q C1 C2,
  sub E P Q ->
  ok (F ++ [(Z, bind_sub P)] ++ E) ->
  subcapt (F ++ [(Z, bind_sub Q)] ++ E) C1 C2 ->
  subcapt (F ++ [(Z, bind_sub P)] ++ E) C1 C2.
Proof with eauto using wf_cset_narrowing, wf_env_narrowing.
  intros F E Z P Q C1 C2 SubPQ Ok SubCap.
  remember (F ++ [(Z, bind_sub Q)] ++ E). generalize dependent F.
  admit.
  (* induction SubCap ; intros ; subst... *)
  (* - econstructor... unfold AtomSet.F.For_all. intros. *)
  (*   specialize (H1 x H2). *)
  (*   eapply captures_narrowing... *)
Admitted.

Lemma subcapt_narrowing_typ : forall F E x P Q C1 C2,
  sub E P Q ->
  ok (F ++ [(x, bind_typ P)] ++ E) ->
  subcapt (F ++ [(x, bind_typ Q)] ++ E) C1 C2 ->
  subcapt (F ++ [(x, bind_typ P)] ++ E) C1 C2.
Proof with eauto using wf_cset_narrowing_typ, captures_narrowing_typ.
  intros F E x P Q C1 C2 PsubQ Ok C1subC2.
  remember (F ++ [(x, bind_typ Q)] ++ E). generalize dependent F.
  induction C1subC2 ; intros ; subst...
  - econstructor...
    unfold AtomSet.F.For_all.
    intros.
    specialize (H1 x0 H2)...
Qed.

Definition transitivity_on Q := forall E S T,
  sub E S Q -> sub E Q T -> sub E S T.

Definition transitivity_pre_on Q := forall E S T,
  sub_pre E S Q -> sub_pre E Q T -> sub_pre E S T.

Lemma sub_narrowing_aux : forall Q F E Z P S T,
  transitivity_on Q ->
  sub (F ++ [(Z, bind_sub Q)] ++ E) S T ->
  sub E P Q ->
  sub (F ++ [(Z, bind_sub P)] ++ E) S T
with sub_narrowing_pre_aux : forall Q F E Z P S T,
  transitivity_on Q ->
  sub_pre (F ++ [(Z, bind_sub Q)] ++ E) S T ->
  sub E P Q ->
  sub_pre (F ++ [(Z, bind_sub P)] ++ E) S T.
Proof with simpl_env; eauto using wf_typ_narrowing, wf_env_narrowing,
  wf_pretyp_narrowing, wf_cset_narrowing, subcapt_narrowing.
------
  intros Q F E Z P S T TransQ SsubT PsubQ.
  remember (F ++ [(Z, bind_sub Q)] ++ E). generalize dependent F.
  induction SsubT; intros F EQ; subst.
  - Case "sub_refl_tvar".
    apply sub_refl_tvar...
  - Case "sub_trans_tvar".
    destruct (X == Z); subst.
    + SCase "X = Z".
      apply (sub_trans_tvar P).
        apply binds_tail.
        apply binds_head; apply binds_singleton.
        eapply fresh_mid_head; apply ok_from_wf_env;
          apply (proj1 (sub_regular (F ++ [(Z, bind_sub Q)] ++ E) U T SsubT)).
      apply TransQ.
      SSCase "P <: Q".
        rewrite_env (empty ++ (F ++ [(Z, bind_sub P)]) ++ E).
        apply sub_weakening...
      SSCase "Q <: T".
        binds_get H.
        inversion H1; subst...
    + SCase "X <> Z".
      apply (sub_trans_tvar U)...
  - eapply sub_capt...
------
  intros Q F E Z P S T TransQ SsubT PsubQ.
  remember (F ++ [(Z, bind_sub Q)] ++ E). generalize dependent F.
  induction SsubT; intros F EQ; subst.
  - Case "sub_top".
    apply sub_top...
  - Case "sub_arrow".
    pick fresh Y and apply sub_arrow...
    + rewrite_parenthesise_binding.
      simpl_env in H2.
      eapply wf_typ_narrowing_base...
    + rewrite_parenthesise_binding.
      simpl_env in H3.
      eapply wf_typ_narrowing_base...
    + rewrite <- concat_assoc.
      eapply sub_narrowing_aux...
  - Case "sub_all".
    pick fresh Y and apply sub_all...
    + rewrite_parenthesise_binding.
      simpl_env in H2.
      eapply wf_typ_narrowing_base...
    + rewrite_parenthesise_binding.
      simpl_env in H3.
      eapply wf_typ_narrowing_base...
    + rewrite <- concat_assoc.
      eapply sub_narrowing_aux...
Qed.

Lemma empty_cset_implies_no_captures : forall E xs,
  wf_cset_in E (cset_set xs {}N) ->
  AtomSet.F.For_all (captures E {}) xs ->
  xs = {}.
Proof.
  intros E xs Wf H.
  unfold AtomSet.F.For_all in H.

  destruct (AtomSet.F.is_empty xs) eqn:Heq.
  - rewrite <- AtomSetFacts.is_empty_iff in Heq.
    fsetdec.
  - destruct (AtomSet.F.choose xs) eqn:InEq.
    + pose proof (AtomSet.F.choose_1 InEq).
      admit.
    + admit.
Admitted.

Lemma empty_subcapt_implies_empty_cset : forall E C,
  subcapt E C {}C ->
  C = {}C.
Proof with auto.
  intros.
  inversion H; subst.
  assert (xs = {}). { apply (empty_cset_implies_no_captures E)... }
  subst...
Qed.

Lemma empty_cset_union : forall C1 C2,
  cset_union C1 C2 = {}C ->
  C1 = {}C /\ C2 = {}C.
Proof with eauto.
  intros.
  destruct C1; destruct C2; simpl in H; try discriminate.
  inversion H.
  unfold empty_cset.
  split; f_equal.
  - destruct (AtomSet.F.choose (t `union` t1)) eqn:Eq.
    + assert (AtomSet.F.Equal (t `union` t1) {}) as HA. {
        rewrite H1.
        fsetdec.
      }
      apply AtomSet.F.choose_1 in Eq.
      rewrite HA in Eq.
      exfalso.
      fsetdec.
    + apply AtomSet.F.choose_2 in Eq.
      assert (AtomSet.F.Empty t). {
        unfold AtomSet.F.Empty in *.
        unfold not in *.
        intros.
        apply (Eq a).
        fsetdec.
      }
      fsetdec.
  - destruct (NatSet.F.choose (NatSet.F.union t0 t2)) eqn:Eq.
    + assert (NatSet.F.Equal (NatSet.F.union t0 t2) {}N) as HA. {
        rewrite H2.
        fnsetdec.
      }
      apply NatSet.F.choose_1 in Eq.
      rewrite HA in Eq.
      exfalso.
      fnsetdec.
    + apply NatSet.F.choose_2 in Eq.
      assert (NatSet.F.Empty t0). {
        unfold NatSet.F.Empty in *.
        unfold not in *.
        intros.
        apply (Eq a).
        fnsetdec.
      }
      fnsetdec.
  - destruct (AtomSet.F.choose (t `union` t1)) eqn:Eq.
    + assert (AtomSet.F.Equal (t `union` t1) {}) as HA. {
        rewrite H1.
        fsetdec.
      }
      apply AtomSet.F.choose_1 in Eq.
      rewrite HA in Eq.
      exfalso.
      fsetdec.
    + apply AtomSet.F.choose_2 in Eq.
      assert (AtomSet.F.Empty t1). {
        unfold AtomSet.F.Empty in *.
        unfold not in *.
        intros.
        apply (Eq a).
        fsetdec.
      }
      fsetdec.
  - destruct (NatSet.F.choose (NatSet.F.union t0 t2)) eqn:Eq.
    + assert (NatSet.F.Equal (NatSet.F.union t0 t2) {}N) as HA. {
        rewrite H2.
        fnsetdec.
      }
      apply NatSet.F.choose_1 in Eq.
      rewrite HA in Eq.
      exfalso.
      fnsetdec.
    + apply NatSet.F.choose_2 in Eq.
      assert (NatSet.F.Empty t2). {
        unfold NatSet.F.Empty in *.
        unfold not in *.
        intros.
        apply (Eq a).
        fnsetdec.
      }
      fnsetdec.
Qed.

Lemma sub_narrowing_typ_aux : forall Q F E x P S T,
  transitivity_on Q ->
  sub (F ++ [(x, bind_typ Q)] ++ E) S T ->
  sub E P Q ->
  sub (F ++ [(x, bind_typ P)] ++ E) S T
with sub_narrowing_pretyp_aux : forall Q F E x P S T,
  transitivity_on Q ->
  sub_pre (F ++ [(x, bind_typ Q)] ++ E) S T ->
  sub E P Q ->
  sub_pre (F ++ [(x, bind_typ P)] ++ E) S T.
Proof with simpl_env; eauto using wf_typ_narrowing_typ, wf_pretyp_narrowing_typ,
    wf_env_narrowing_typ, cv_narrowing_typ, subcapt_narrowing_typ, wf_cset_narrowing_typ.
------
  intros Q F E x P S T TransQ SsubT PsubQ.
  remember (F ++ [(x, bind_typ Q)] ++ E). generalize dependent F.
  induction SsubT; intros F EQ; subst.
  - apply sub_refl_tvar...
  - apply sub_trans_tvar with (U := U)...
    binds_cases H.
    + apply binds_tail. apply binds_tail... auto.
    + apply binds_head...
  - apply sub_capt...
------
  intros Q F E x P S T TransQ SsubT PsubQ.
  remember (F ++ [(x, bind_typ Q)] ++ E). generalize dependent F.
  induction SsubT; intros F EQ; subst.
  - eapply sub_top...
  - pick fresh Y and apply sub_arrow...
    + rewrite_parenthesise_binding.
      simpl_env in H2.
      eapply wf_typ_narrowing_typ_base...
    + rewrite_parenthesise_binding.
      simpl_env in H3.
      eapply wf_typ_narrowing_typ_base...
    + rewrite <- concat_assoc.
      eapply sub_narrowing_typ_aux...
  - pick fresh Y and apply sub_all...
    + rewrite_parenthesise_binding.
      simpl_env in H2.
      eapply wf_typ_narrowing_typ_base...
    + rewrite_parenthesise_binding.
      simpl_env in H3.
      eapply wf_typ_narrowing_typ_base...
    + rewrite <- concat_assoc.
      eapply sub_narrowing_typ_aux...
Qed.

(* S <: Q    ->    Q <: T    ->    S <: T*)
Lemma sub_transitivity : forall Q E S T,
  type Q ->
  sub E S Q -> sub E Q T -> sub E S T
with sub_pre_transitivity : forall Q E S T,
  pretype Q ->
  sub_pre E S Q -> sub_pre E Q T -> sub_pre E S T.
Proof with simpl_env; auto.
------
  intros Q E S T W SsubQ QsubT.

  generalize dependent T.
  generalize dependent S.
  generalize dependent E.
  remember Q as Q' in |-.
  generalize dependent Q'.

  induction W; intros Q'' EQ E' S' SsubQ.

  Ltac inductionThenInversion Rel1 Rel2 :=
      induction Rel1; try discriminate; inversion EQ; subst; intros T' Rel2; inversion Rel2; subst.

  (* type_var *)
  - inductionThenInversion SsubQ QsubT; try solve [econstructor; eauto].
  (* type_capt *)
  - inductionThenInversion SsubQ QsubT; try solve [econstructor; eauto].
    apply sub_capt...
    apply subcapt_transitivity with (C2 := C)...
    apply sub_pre_transitivity with (Q := P)...
------
  intros Q E S T W SsubQ QsubT.

  generalize dependent T.
  generalize dependent S.
  generalize dependent E.
  remember Q as Q' in |-.
  generalize dependent Q'.

  induction W; intros Q'' EQ E' S' SsubQ.

  Ltac inductionThenInversion2 Rel1 Rel2 :=
    induction Rel1; try discriminate; inversion EQ; subst; intros T' Rel2; inversion Rel2; subst.

  (* type_top *)
  - inductionThenInversion2 SsubQ QsubT; try solve [econstructor; eauto].

  (*  HERE `sub E S T2` is now missing! *)
  (* type_arrow *)
  - inductionThenInversion2 SsubQ QsubT.
  + eapply sub_top...
    (* wf_typ typ_arrow *)
    pick fresh X and apply wf_typ_arrow...
  + pick fresh Y and apply sub_arrow.
    all: trivial.
    (* SCase "bounds". *)
       auto using (sub_transitivity T1).
       assert (Y `notin` L1) by notin_solve...
       assert (Y `notin` L1) by notin_solve...
    SCase "bodies".
      lapply (H0 Y); [ intros K | auto ].
      assert (Y `notin` L0) by notin_solve.
      assert (Y `notin` L1) by notin_solve.
      apply sub_transitivity with (Q := (open_ct T2 Y))...
      rewrite_env (empty ++ [(Y, bind_typ T0)] ++ E).
      eapply sub_narrowing_typ_aux with (Q := T1)...
      unfold transitivity_on.
      auto using (sub_transitivity T1).
  (* type_all. *)
  - inductionThenInversion2 SsubQ QsubT.
  + apply sub_top...
    pick fresh X and apply wf_typ_all...
  + pick fresh Y and apply sub_all.
    all: trivial.
    SCase "bounds".
      apply sub_transitivity with (Q := T1)...
      assert (Y `notin` L1) by notin_solve...
      assert (Y `notin` L1) by notin_solve...
    SCase "bodies".
      lapply (H0 Y); [ intros K | auto ].
      apply sub_transitivity with (Q := (open_tt T2 Y))...
      rewrite_env (empty ++ [(Y, bind_sub T0)] ++ E).
      apply (sub_narrowing_aux T1)...
      unfold transitivity_on.
      auto using (sub_transitivity T1).
Admitted.

Lemma sub_narrowing : forall Q E F Z P S T,
  sub E P Q ->
  sub (F ++ [(Z, bind_sub Q)] ++ E) S T ->
  sub (F ++ [(Z, bind_sub P)] ++ E) S T.
Proof with auto.
  intros.
  eapply sub_narrowing_aux; eauto.
  unfold transitivity_on. intros.
  eapply sub_transitivity with (Q := Q)...
Qed.

Lemma sub_narrowing_typ : forall E F x P Q S T,
  sub (F ++ [(x, bind_typ Q)] ++ E) S T ->
  sub E P Q ->
  sub (F ++ [(x, bind_typ P)] ++ E) S T.
Proof with eauto using wf_typ_narrowing_typ.
  intros.
  eapply sub_narrowing_typ_aux; eauto.
  unfold transitivity_on. intros.
  eapply sub_transitivity with (Q := Q)...
Qed.

(* ********************************************************************** *)
(** ** Type substitution preserves subtyping (10) *)

Lemma cv_subst_empty : forall S G Z Q E P,
  cv (G ++ [(Z, bind_sub Q)] ++ E) S {}C ->
  cv (map (subst_tb Z P) G ++ E) (subst_tt Z P S){}C.
Proof.
Admitted.

Lemma captures_expansion : forall D2 E x D1,
  captures E D1 x ->
  captures E (D1 `union` D2) x.
Proof with eauto.
  intros *.
  intro H.
  dependent induction H.
  - apply captures_in...
    fsetdec.
  - apply captures_var with (T := T) (ys := ys)...
Qed.

Lemma wf_cset_union : forall E A C D,
  wf_cset E A C ->
  wf_cset E A D ->
  wf_cset E A (cset_union C D).
Proof with eauto.
  intros *.
  intros H1 H2.
  inversion H1; inversion H2; subst; simpl...
  unfold wf_cset_in in *.
  replace (NatSet.F.union _ _) with {}N by fnsetdec.
  constructor...
  unfold allbound_typ in *...
  intros.
  rewrite AtomSetFacts.union_iff in *.
  auto*.
Qed.

Lemma subcapt_expansion : forall E C D1 D2,
  wf_cset_in E D2 ->
  subcapt E C D1 ->
  subcapt E C (cset_union D1 D2).
Proof with eauto using wf_cset_union.
  intros *.
  intros HwfD2 Hsubcapt.
  induction Hsubcapt.
  - simpl.
    destruct D2...
  - destruct D2; simpl...
    inversion HwfD2; subst.
    replace (NatSet.F.union _ _)
      with {}N by fnsetdec.
    apply subcapt_set...
    + (* wf_cset_union doesn't work here, sigh *)
      inversion H; inversion H0; subst.
      unfold wf_cset_in in *.
      constructor...
      unfold allbound_typ in *...
      intros.
      rewrite AtomSetFacts.union_iff in *.
      auto*.
    + unfold AtomSet.F.For_all in *.
      eauto using (captures_expansion t)...
Qed.

Lemma cset_eq_injectivity : forall a1 a2 n1 n2,
    a1 = a2 ->
    n1 = n2 ->
    cset_set a1 n1 = cset_set a2 n2.
Proof.
  intros *. intros EqA EqN.
  rewrite EqA.
  rewrite EqN.
  trivial.
Qed.

Lemma subcapt_union_distributivity : forall E C1 C2 D,
  subcapt E C1 D ->
  subcapt E C2 D ->
  subcapt E (cset_union C1 C2) D.
Proof with eauto using wf_cset_union.
  intros *.
  intros HscC1 HscC2.
  induction HscC1...
  inversion HscC2; subst; simpl.
  replace (NatSet.F.union _ _) with {}N by fnsetdec.
  apply subcapt_set...
  - replace (cset_set (xs `union` xs0) {}N)
      with (cset_union (cset_set xs {}N) (cset_set xs0 {}N)).
    2: apply cset_eq_injectivity; [fsetdec|fnsetdec].
    apply wf_cset_union...
  - unfold AtomSet.F.For_all in *.
    intros.
    rewrite AtomSetFacts.union_iff in *.
    auto*.
Qed.

Lemma cset_union_symmetrical : forall C D,
  cset_union C D = cset_union D C.
Proof with eauto.
  intros.
  destruct C; destruct D; simpl; try easy.
  apply cset_eq_injectivity; [fsetdec|fnsetdec].
Qed.

Lemma union_under_subcapturing : forall E C1 C2 D1 D2,
  subcapt E C1 C2 ->
  subcapt E D1 D2 ->
  subcapt E (cset_union C1 D1) (cset_union C2 D2).
Proof with eauto.
  intros *.
  intros Hsc1 Hsc2.
  apply subcapt_union_distributivity.
  - apply subcapt_expansion...
  - rewrite cset_union_symmetrical.
    apply subcapt_expansion...
Qed.

Lemma cv_through_subst_tt : forall X P Q T E G C D,
  wf_env (G ++ [(X, bind_sub Q)] ++ E) ->
  wf_typ_in (G ++ [(X, bind_sub Q)] ++ E) T ->
  cv (G ++ [(X, bind_sub Q)] ++ E) T C ->
  cv (map (subst_tb X P) G ++ E) (subst_tt X P T) D ->
  sub E P Q ->
  subcapt (map (subst_tb X P) G ++ E) D C.
Proof with eauto.
  intros *. intros Hwf_env Hwf_typ HcvWide HcvNarr Hsub.

  assert (type T) as Typ. { eapply type_from_wf_typ... }

  induction G.
  - simpl_env in *.
    dependent induction HcvWide; subst.
    + unfold subst_tt in HcvNarr. destruct (X == X); try easy.
      eapply sub_implies_subcapt with (A1 := dom E) (A2 := dom E)...
    + unfold subst_tt in HcvNarr. destruct (X0 == X); try easy.
      epose proof (cv_unique _ _ _ _ _ _ HcvWide HcvNarr); subst.
      eapply subcapt_reflexivity...
    + simpl subst_tt in *.
      inversion HcvNarr; subst.
      eapply subcapt_reflexivity...
  (*  lunch break... *)
  - admit.
Admitted.

  (* induction HcvWide; intros G ? HcvNarr; subst... *)

  (* - admit. *)
  (* - admit. *)
  (* - simpl subst_tt in HcvNarr. *)
  (*   inversion HcvNarr; subst. *)
  (*   apply subcapt_reflexivity with (A := dom (map (subst_tb X P) G ++ E))... *)

  (* dependent induction Typ. *)
  (* 2: dependent induction H0. *)
  (* all: intros D Hcv_narrow C0 Hcv_wide. *)
  (* - simpl subst_tt in Hsub. *)
  (*   destruct (X0 == X). *)
  (*   + subst. *)
  (*     eapply extract_bind_cv_from_var_cv in Hcv_wide as HcvQ... *)
  (*     destruct C0... *)
  (*     destruct D... *)

  (* -  *)
  (* - inversion Hcv_wide; subst. *)
  (*   inversion Hcv_narrow; subst. *)
  (*   admit. *)
  (*   (* apply subcapt_split. *)
  (*   apply cset_subset_reflexivity. *) *)
  (* - Case "bvar". *)
  (*   (* What's going on here, why do I get a bvar? Doesn't this mean that T would be simply ill-formed? *) *)
  (*   admit. *)
  (* - Case "fvar". *)
  (*   admit. *)
  (* - inversion Hcv_narrow; subst. *)
  (*   inversion Hcv_wide; subst. *)
  (*   admit. *)
  (*   (* apply subcapt_split. *) *)
  (*   (* apply cset_subset_reflexivity. *) *)
  (* - inversion Hcv_narrow; subst. *)
  (*   inversion Hcv_wide; subst. *)
  (*   admit. *)
  (*   (* apply subcapt_split. *)
  (*   apply cset_subset_reflexivity. *) *)
  (* (* - inversion Hwf_typ; subst. *)
  (*   inversion Hcv_narrow; subst. *)
  (*   inversion Hcv_wide; subst. *)
  (*   specialize (IHT H2 C2 H5 C0 H6). *)
  (*   apply union_under_subcapturing; trivial. *)
  (*   apply subcapt_reflexivity. *)
  (*   apply wf_env_subst_tb with (Q := Q); auto. *) *)
(* Admitted. *)

(* Type substitution preserves subcapturing *)

Lemma captures_through_subst_tt : forall Q E F Z P C x,
  captures (F ++ [(Z, bind_sub Q)] ++ E) C x ->
  wf_typ_in E P ->
  captures (map (subst_tb Z P) F ++ E) C x.
Proof with eauto using wf_env_subst_tb, wf_cset_subst_tb.
  intros *.
  intros H Tp.
  remember  (F ++ [(Z, bind_sub Q)] ++ E).
  generalize dependent F.
  induction H; intros; subst.
  - constructor...
  (* that's the same as in captures_narrowing -> TODO refactor *)
  - assert (x <> Z). {
      unfold not. intros.
      binds_cases H.
      * subst. unfold dom in Fr0. fsetdec.
      * subst. exfalso. admit.
    }
    apply captures_var with (T := T) (ys := ys)...
    admit.
  (* - assert (exists (C3 : captureset),
      cv (subst_tt X P T) (map (subst_tb X P) G ++ E) C3 /\
      subcapt (map (subst_tb X P) G ++ E) C3 C2
           ) as [C3 [C3sub C3eq]]. {
      apply cv_through_subst_tt with (Q := Q)...
      assert (binds X0 (bind_typ T) (G ++ [(X, bind_sub Q)] ++ E)); auto.
      eapply wf_typ_from_binds_typ; auto.
      apply H.
    }
    apply subcapt_var with (C2 := C3) (T := subst_tt X P T)...
    apply subcapt_transitivity with (C2 := C2)...
    apply wf_env_subst_tb with (Q := Q)... *)
Admitted.

Lemma subcapt_through_subst_tt : forall E P Q G X C D,
  wf_env (G ++ [(X, bind_sub Q)] ++ E) ->
  subcapt (G ++ [(X, bind_sub Q)] ++ E) C D ->
  sub E P Q ->
  subcapt (map (subst_tb X P) G ++ E) C D.
Proof with eauto using wf_env_subst_tb, wf_cset_subst_tb, captures_through_subst_tt.
  intros E P Q G X C D Hwf H Hsub.
  remember (G ++ [(X, bind_sub Q)] ++ E).
  induction H; auto.
  subst.
  binds_cases H...
  - constructor...
    (* Alex: requires wf_cset_through_subst_ct *)
    admit.
  - subst.
    constructor...
    (* Same as above... *)
    + admit.
    + admit.
    + unfold AtomSet.F.For_all in *. intros.
      specialize (H1 x H2)...
Admitted.

Lemma sub_through_subst_tt : forall Q E F Z S T P,
  sub (F ++ [(Z, bind_sub Q)] ++ E) S T ->
  sub E P Q ->
  sub (map (subst_tb Z P) F ++ E) (subst_tt Z P S) (subst_tt Z P T).
Proof with
      simpl_env;
      eauto 4 using wf_typ_subst_tb, wf_env_subst_tb, wf_typ_weaken_head.
  intros Q E F Z S T P SsubT PsubQ.
  remember (F ++ [(Z, bind_sub Q)] ++ E).
  generalize dependent F.
  induction SsubT; intros G EQ; subst; simpl subst_tt...

  (* - Case "sub_top".
    eapply sub_top...
    apply cv_subst_empty with (Q := Q)...
    admit.
    admit.
  - Case "sub_refl_tvar".
    destruct (X == Z); subst.
    SCase "X = Z".
      apply sub_reflexivity...
    SCase "X <> Z".
      apply sub_reflexivity...
      inversion H0; subst.
      binds_cases H3...
      apply (wf_typ_var (subst_tt Z P U))...
  - Case "sub_trans_tvar".
    destruct (X == Z); subst.
    SCase "X = Z".
      apply (sub_transitivity Q).
      SSCase "left branch".
        rewrite_env (empty ++ map (subst_tb Z P) G ++ E).
        apply sub_weakening...
      SSCase "right branch".
        rewrite (subst_tt_fresh Z P Q).
          binds_get H.
            inversion H1; subst...
          apply (notin_fv_wf E).
          apply (proj2 (proj2 (sub_regular E P Q PsubQ))).
          eapply fresh_mid_tail; apply ok_from_wf_env;
            apply (proj1 (sub_regular (G ++ [(Z, bind_sub Q)] ++ E) U T SsubT)).
    SCase "X <> Z".
      apply (sub_trans_tvar (subst_tt Z P U))...
      rewrite (map_subst_tb_id E Z P);
        [ | auto | eapply fresh_mid_tail; eauto ].
      binds_cases H...
  (* this case is not worked out in the P&P proof. *)
  - Case "sub_arrow".
    pick fresh X and apply sub_arrow...
    repeat (rewrite <- subst_tt_open_ct)...
    assert (X `notin` L) as XL. { fsetdec. }
    (* assert ([(X, bind_typ T1)] ++ G ++ [(Z, bind_sub Q)] ++ E = G ++ [(Z, bind_sub Q)] ++ E) as Heq. {
      (* JONATHAN: This is bogus! *)
      admit.
    }
    specialize (H0 X XL G Heq).  *)
    rewrite_env (empty ++ [(X, bind_typ (subst_tt Z P T1))] ++ (map (subst_tb Z P) G ++ E)).
    apply sub_weakening.
    (* JONATHAN: We can't apply H0 here! *)
    (* apply H0... *)
    admit.
    simpl_env.
    admit.
  - Case "sub_all".
    pick fresh X and apply sub_all...
    rewrite subst_tt_open_tt_var...
    rewrite subst_tt_open_tt_var...
    rewrite_env (map (subst_tb Z P) ([(X, bind_sub T1)] ++ G) ++ E).
    apply H0...
  - Case "sub_capt".
    apply sub_capt...
    apply subcapt_through_subst_tt with (Q := Q)... *)
Admitted.


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
                       subcapt_weakening,
                       cv_weakening.
  intros E F G e T Typ.
  remember (G ++ E).
  generalize dependent G.
  induction Typ; intros G EQ Ok; subst...
  - Case "typing_abs".
    pick fresh X and apply typing_abs...
    + rewrite_parenthesise_binding.
      (* Alex: uh, I think this'll be easier to prove if we just add a single
      binding as opposed to a complete F... *)
      admit.
    + lapply (H0 X); [intros K | auto].
      admit.
    (* destruct K.     *)
    (* split... *)
    (* rewrite <- concat_assoc. *)
    (* apply wf_typ_weakening... *)
    (* rewrite <- concat_assoc. *)
    (* admit. *)
  - Case "typing_app".
    admit.
  - Case "typing_arrow".
    pick fresh X and apply typing_tabs.
    + admit.
    + admit.
    + lapply (H0 X); [intros K | auto].
      rewrite <- concat_assoc.
      apply (H2 X)...
Admitted.


(************************************************************************ *)
(** ** Narrowing for typing (7) *)

Lemma subst_ct_open_ct_var : forall (x y:atom) c t,
  y <> x ->
  capt c ->
  (open_ct (subst_ct x c t) (cset_fvar y)) = (subst_ct x c (open_ct t (cset_fvar y))).
Proof with auto*.
  intros *; intros Neq Wu.
  unfold open_ct.
  symmetry.
  apply subst_ct_open_ct_rec...
  - constructor.
  - unfold cset_references_fvar.
    unfold cset_all_fvars.
    unfold cset_fvar.
    fsetdec.
Qed.

(* Alex: looking at the subst_tt_open_tt_* chain, there should be a better way to do this... *)
Lemma subst_ct_open_ct : forall x c1 T c2,
  (* not (cset_references_fvar x c2) -> *)
  (* capt c1 -> *)
  subst_ct x c1 (open_ct T c2) = (open_ct (subst_ct x c1 T) (subst_cset x c1 c2)).
Proof with auto*.
  intros *.
  (* intros Hnotin Hc1. *)
  induction T.
  - unfold open_ct, open_ct_rec; simpl.
    fold open_cpt_rec.
    replace (subst_cset x c1 (open_cset 0 c2 c))
      with (open_cset 0 (subst_cset x c1 c2) (subst_cset x c1 c)).
    2: {
      unfold open_cset.
      destruct (cset_references_bvar_dec 0 c) eqn:EQ.
      admit.
      admit.
    }
    admit.
  - admit.
  - admit.
Admitted.

Lemma subst_ct_open_tt : forall x c t1 t2,
  capt c ->
  subst_ct x c (open_tt t1 t2) = (open_tt (subst_ct x c t1) (subst_ct x c t2)).
Proof with auto*.
  intros.
  admit.
Admitted.

Lemma subst_tt_open_ct : forall x C S T,
    type S ->
    open_ct (subst_tt x S T) C = subst_tt x S (open_ct T C).
Proof.
Admitted.

Lemma subst_tt_open_ct_var : forall x y S T,
    type S ->
    open_ct (subst_tt x S T) (cset_fvar y) = subst_tt x S (open_ct T (cset_fvar y)).
Proof.
  intros.
  apply subst_tt_open_ct; auto.
Qed.

Lemma subst_ct_useless_repetition : forall x C D T,
  subst_ct x C (subst_ct x D T) = (subst_ct x D T).
Proof.
Admitted.

(* Alex: well all right, none of these are used now... *)
(* Lemma fv_et_subset_dom_env : forall E T, *)
(*   wf_typ_in E T -> *)
(*   fv_et T `subset` dom E *)
(* with fv_ept_subset_dom_env : forall E P, *)
(*   wf_pretyp_in E P -> *)
(*   fv_ept P `subset` dom E. *)
(* Proof with eauto. *)
(* { intros. *)
(*   assert (type T) as Typ. { *)
(*     apply type_from_wf_typ in H... *)
(*   } *)
(*   induction Typ. *)
(*   - simpl. *)
(*     fsetdec. *)
(*   - simpl. *)
(*     inversion H; subst. *)
(*     match goal with H : wf_pretyp _ _ _ P |- _ => *)
(*       apply fv_ept_subset_dom_env in H *)
(*     end. *)
(*     match goal with H : wf_cset _ _ C |- _ => *)
(*       inversion H; subst; simpl; fsetdec *)
(*     end. *)
(* } *)
(* { *)
(*   intros. *)
(*   assert (pretype P) as Pretyp. { *)
(*     apply pretype_from_wf_pretyp in H... *)
(*   } *)
(*   induction Pretyp; simpl. *)
(*   - fsetdec. *)
(*   - inversion H; subst. *)
(*     pick fresh X. *)
(*     unshelve epose proof (H8 X _) as SpH8... *)
(*     assert (fv_et (open_ct T2 X) `subset` dom E `union` singleton X). *)
(*     (fv_et T2 `subset` dom E) *)

(*     wf_typ *)
(* } *)

(* Lemma self_subst_idempotent : forall F E x T D, *)
(*   wf_env (F ++ [(x, bind_typ T)] ++ E) -> *)
(*   subst_ct x D T = T. *)
(* Proof. *)
(*   (* Plan: *) *)
(*   (*   - fv(T) subset E (should be prove-able using a simple lemma like bindin_uniq_from_* ) *) *)
(*   (*   - therefore x not in fv(t) *) *)
(*   (*   - therefore subst idempotent *) *)
(*   admit. *)
(* Admitted. *)

Lemma cset_subst_self : forall C x,
  subst_cset x C (cset_fvar x) = C.
Proof.
  intros.
  unfold subst_cset.
  destruct (cset_references_fvar_dec x x) eqn:EQ.
  2: {
    unfold cset_references_fvar_dec, cset_fvar in EQ.
    rewrite <- AtomSetFacts.not_mem_iff in EQ.
    exfalso.
    fsetdec.
  }
  unfold cset_remove_fvar, cset_fvar.
  replace (cset_set _ _) with {}C.
  2: {
    apply cset_eq_injectivity; [fsetdec|fnsetdec].
  }
  destruct C; simpl.
  - easy.
  - replace (cset_set _ _) with (cset_set t t0).
    2: {
      apply cset_eq_injectivity; [fsetdec|fnsetdec].
    }
    easy.
Qed.

Lemma wf_cset_remove_fvar : forall A E C x,
  wf_cset E A C ->
  wf_cset E A (cset_remove_fvar x C).
Proof with eauto.
  intros.
  unfold wf_cset_in in *.
  induction H; simpl...
  constructor...
  unfold allbound_typ in *.
  intros.
  apply H.
  fsetdec.
Qed.

Lemma wf_cset_subst_cb : forall Q Ap' Ap F E x C D,
  wf_cset (F ++ [(x, bind_typ Q)] ++ E) Ap C ->
  wf_env (F ++ [(x, bind_typ Q)] ++ E) ->
  wf_cset E Ap' D ->
  Ap' `subset` Ap ->
  Ap' `subset` dom E ->
  ok (map (subst_cb x D) F ++ E) ->
  wf_cset (map (subst_cb x D) F ++ E) (Ap `remove` x) (subst_cset x D C).
Proof with simpl_env; eauto*.
  intros *. intros HwfC HwfEnv HwfD Hsset HApRsnbl Hok.
  destruct C.
  1: { unfold subst_cset; unfold cset_references_fvar_dec... }
  unfold subst_cset; unfold cset_references_fvar_dec.
  apply binding_uniq_from_wf_env in HwfEnv as ?.
  destruct (AtomSet.F.mem x t) eqn:EQ...
  - apply wf_cset_union.
    + rewrite_nil_concat.
      apply wf_cset_weakening with (A := Ap'); simpl_env...
    + unfold cset_remove_fvar; simpl.
      inversion HwfC; subst.
      constructor...
      unfold allbound_typ in *.
      intros.
      destruct (x0 == x).
      * exfalso. fsetdec.
      * assert (x0 `in` t) as HA by fsetdec.
        specialize (H4 x0 HA) as [T HbindsT].
        binds_cases HbindsT...
        exists (subst_ct x D T)...
  - inversion HwfC; subst.
    rewrite <- AtomSetFacts.not_mem_iff in EQ.
    constructor...
    unfold allbound_typ in *.
    intros.
    unshelve epose proof (H4 x0 _) as [T HbindsT]...
    assert (x0 <> x) by fsetdec.
    binds_cases HbindsT...
    exists (subst_ct x D T)...
Qed.

Lemma wf_cset_in_subst_cb : forall Q F E x C D,
  wf_cset_in (F ++ [(x, bind_typ Q)] ++ E) C ->
  wf_env (F ++ [(x, bind_typ Q)] ++ E) ->
  wf_cset_in E D ->
  ok (map (subst_cb x D) F ++ E) ->
  wf_cset_in (map (subst_cb x D) F ++ E) (subst_cset x D C).
Proof with eauto.
  intros.
  assert (x `notin` (dom F `union` dom E)). {
    apply binding_uniq_from_wf_env with (b := bind_typ Q)...
  }
  unfold wf_cset_in in *.
  replace (dom (map (subst_cb x D) F ++ E))
    with ((dom (F ++ [(x, bind_typ Q)] ++ E)) `remove` x) by (simpl_env; fsetdec).
  apply (wf_cset_subst_cb Q (dom E))...
Qed.

(* Substituting the same capture set preserves subcapturing *)
Lemma subcapt_through_subst_cset : forall F x U E C1 C2 D,
  subcapt (F ++ [(x, bind_typ U)] ++ E) C1 C2 ->
  ok (F ++ [(x, bind_typ U)] ++ E) ->
  cv E U D ->
  subcapt (map (subst_cb x D) F ++ E) (subst_cset x D C1) (subst_cset x D C2).
Proof with eauto.
  intros *.
  intros Hsc Hok Hcv.
  destruct C1; destruct C2; subst; simpl subst_cset; try solve [inversion Hsc]...
  1: {
    unfold subst_cset.
    unfold cset_references_fvar_dec.
    constructor.
    apply cv_regular, proj2, proj2 in Hcv.
    destruct (AtomSet.F.mem x t)...
    - apply wf_cset_union.
      + rewrite_nil_concat.
        apply wf_cset_weakening with (A := dom E); simpl_env...
      + unfold cset_remove_fvar; simpl.
        pose proof (subcapt_regular _ _ _ Hsc) as [HA _].
        inversion HA; subst.
        constructor...
        unfold allbound_typ in *.
        intros.
        destruct (x0 == x).
        * exfalso. fsetdec.
        * specialize (H3 x0 ltac:(fsetdec)) as [T HbindsT].
          binds_cases HbindsT...
          exists (subst_ct x D T)...
    - admit.
  }
Admitted.

Lemma subst_cset_across_subcapt : forall E x C D C0 A,
  wf_env E ->
  wf_cset E A C0 ->
  A `subset` dom E ->
  subcapt E C D ->
  subcapt E (subst_cset x C C0) (subst_cset x D C0).
Proof with eauto.
  intros *.
  intros WfEnv Wf Subset Sub.
  remember C0.
  destruct C0...
  - destruct (AtomSet.F.mem x (cset_fvars c)) eqn:InAp.
    * inversion Sub; subst.
      + unfold subst_cset. unfold cset_references_fvar_dec...
      + unfold subst_cset. unfold cset_references_fvar_dec...
    * rewrite <- AtomSetFacts.not_mem_iff in InAp.
      replace (subst_cset x C c) with c.
      replace (subst_cset x D c) with c.
      apply subcapt_reflexivity with (A := A)...
      apply subst_cset_fresh. inversion Wf; subst...
      apply subst_cset_fresh. inversion Wf; subst...
  - destruct (AtomSet.F.mem x (cset_fvars c)) eqn:InAp.
    * inversion Sub; subst.
      + simpl in InAp. unfold subst_cset. unfold cset_references_fvar_dec. rewrite InAp. constructor.
        destruct C...
        simpl. inversion Wf. inversion H. rewrite elim_empty_nat_set. subst.
        admit.
      + simpl in InAp. unfold subst_cset. unfold cset_references_fvar_dec. rewrite InAp.
        inversion Wf; subst.
        simpl. rewrite elim_empty_nat_set. constructor...
        admit.
        admit.
        unfold AtomSet.F.For_all in *; intros.
        (* More set fiddling *)
        admit.
    * rewrite <- AtomSetFacts.not_mem_iff in InAp.
      replace (subst_cset x C c) with c.
      replace (subst_cset x D c) with c.
      apply subcapt_reflexivity with (A := A)...
      apply subst_cset_fresh. unfold fv_cset; subst...
      apply subst_cset_fresh. unfold fv_cset; subst...
Admitted.

Lemma meaning_of : forall E Ap Am x C D T,
  wf_env E ->
  type T ->
  Ap `subset` dom E ->
  Am `subset` dom E ->
  wf_typ E Ap Am T ->
  subcapt E C D ->
  ((x `notin` Am -> sub E (subst_ct x C T) (subst_ct x D T)) /\
   (x `notin` Ap -> sub E (subst_ct x D T) (subst_ct x C T)))
with pre_meaning_of : forall E Ap Am x C D T,
  wf_env E ->
  pretype T ->
  Ap `subset` dom E ->
  Am `subset` dom E ->
  wf_pretyp E Ap Am T ->
  subcapt E C D ->
  ((x `notin` Am -> sub_pre E (subst_cpt x C T) (subst_cpt x D T)) /\
  (x `notin` Ap -> sub_pre E (subst_cpt x D T) (subst_cpt x C T))).
Proof with simpl_env; eauto; fold subst_cpt.
------
  intros *.
  intros HwfE Typ SubAp SubAm HwfT Hsc.
  (* assert (type T) as Typ by auto. *)
  induction Typ; inversion HwfT; subst.
  - simpl. constructor...
  - destruct (pre_meaning_of E Ap Am x C D P HwfE H0 SubAp SubAm H7 Hsc).
    split; intros; constructor...
    + eapply subst_cset_across_subcapt...
    + replace (subst_cset x D C0) with C0.
      replace (subst_cset x C C0) with C0.
      apply subcapt_reflexivity with (A := Ap)...
      apply subst_cset_fresh. inversion H6...
      apply subst_cset_fresh. inversion H6...
------
  intros *.
  intros HwfE Typ SubAp SubAm HwfT Hsc.
  (* assert (pretype T) as Typ by auto. *)
  induction Typ; inversion HwfT; subst.
  - simpl. constructor...
  - (* specializing the hypothesis to the argument type of arrow *)
    destruct (meaning_of E Am Ap x C D T1 HwfE H SubAm SubAp H6 Hsc).
    split; intros.
    + specialize (H2 H3).
      pick fresh y and apply sub_arrow; fold subst_ct...
      rewrite subst_ct_open_ct_var...
      specialize (H7 y).
      (*
       1) we need to know that `Ap subset dom E`
       2) we need to show that subst_ct preserves wellformedness (wf_typ).
       3) then we can apply wf_typ_ignores_typ_bindings
      *)
      apply cheat.
      apply cheat.
      rewrite subst_ct_open_ct_var...
      rewrite subst_ct_open_ct_var...
      (* we cannot call meaning_of on anything that is larger than wf_typ.... *)
      assert (y `notin` L) as NotIn by notin_solve.
      specialize (H0 y NotIn).
      unshelve epose proof (meaning_of
        ([(y, bind_typ (subst_ct x D T1))] ++ E)
        (Ap `union` singleton y)
        Am x C D (open_ct T2 y) _ H0 _ _ _).
      * econstructor...
      (* we need to help fsetdec here a little *)
      * clear Fr. simpl. fsetdec.
      * clear Fr. simpl. fsetdec.
      * rewrite_env (empty ++ [(y, bind_typ (subst_ct x D T1))] ++ E).
        eapply wf_typ_ignores_typ_bindings...
      * destruct H4.
        rewrite_env (empty ++ [(y, bind_typ (subst_ct x D T1))] ++ E).
        apply subcapt_weakening...
        apply H4...
    + specialize (H1 H3).
      pick fresh y and apply sub_arrow; fold subst_ct...
      rewrite subst_ct_open_ct_var...
      specialize (H7 y).
      (*
        1) we need to know that `Ap subset dom E`
        2) we need to show that subst_ct preserves wellformedness (wf_typ).
        3) then we can apply wf_typ_ignores_typ_bindings
      *)
      apply cheat.
      apply cheat.
      rewrite subst_ct_open_ct_var...
      rewrite subst_ct_open_ct_var...
      (* we cannot call meaning_of on anything that is larger than wf_typ.... *)
      assert (y `notin` L) as NotIn by notin_solve.
      specialize (H0 y NotIn).
      unshelve epose proof (meaning_of
        ([(y, bind_typ (subst_ct x C T1))] ++ E)
        (Ap `union` singleton y)
        Am x C D (open_ct T2 y) _ H0 _ _ _).
      * econstructor...
      (* we need to help fsetdec here a little *)
      * clear Fr. simpl. fsetdec.
      * clear Fr. simpl. fsetdec.
      * rewrite_env (empty ++ [(y, bind_typ (subst_ct x C T1))] ++ E).
        eapply wf_typ_ignores_typ_bindings...
      * destruct H4.
        rewrite_env (empty ++ [(y, bind_typ (subst_ct x C T1))] ++ E).
        apply subcapt_weakening...
        apply H5...
  - (* specializing the hypothesis to the argument type of arrow *)
    destruct (meaning_of E Am Ap x C D T1 HwfE H SubAm SubAp H6 Hsc).
    split; intros.
    + specialize (H2 H3).
      pick fresh y and apply sub_all; fold subst_ct...
      rewrite subst_ct_open_tt_var...
      specialize (H7 y).
      (*
       1) we need to know that `Ap subset dom E`
       2) we need to show that subst_ct preserves wellformedness (wf_typ).
       3) then we can apply wf_typ_ignores_typ_bindings
      *)
      apply cheat.
      apply cheat.
      rewrite subst_ct_open_tt_var...
      rewrite subst_ct_open_tt_var...
      (* we cannot call meaning_of on anything that is larger than wf_typ.... *)
      assert (y `notin` L) as NotIn by notin_solve.
      specialize (H0 y NotIn).
      unshelve epose proof (meaning_of
        ([(y, bind_sub (subst_ct x D T1))] ++ E)
        Ap
        Am x C D (open_tt T2 y) _ H0 _ _ _).
      * econstructor...
      (* we need to help fsetdec here a little *)
      * clear Fr. simpl. fsetdec.
      * clear Fr. simpl. fsetdec.
      * rewrite_env (empty ++ [(y, bind_sub (subst_ct x D T1))] ++ E).
        eapply wf_typ_ignores_sub_bindings with (T1 := T1)...
      * destruct H4.
        rewrite_env (empty ++ [(y, bind_sub (subst_ct x D T1))] ++ E).
        apply subcapt_weakening...
        apply H4...
    + specialize (H1 H3).
      pick fresh y and apply sub_all; fold subst_ct...
      rewrite subst_ct_open_tt_var...
      specialize (H7 y).
      (*
        1) we need to know that `Ap subset dom E`
        2) we need to show that subst_ct preserves wellformedness (wf_typ).
        3) then we can apply wf_typ_ignores_typ_bindings
      *)
      apply cheat.
      apply cheat.
      rewrite subst_ct_open_tt_var...
      rewrite subst_ct_open_tt_var...
      (* we cannot call meaning_of on anything that is larger than wf_typ.... *)
      assert (y `notin` L) as NotIn by notin_solve.
      specialize (H0 y NotIn).
      unshelve epose proof (meaning_of
        ([(y, bind_sub (subst_ct x C T1))] ++ E)
        Ap
        Am x C D (open_tt T2 y) _ H0 _ _ _).
      * econstructor...
      (* we need to help fsetdec here a little *)
      * clear Fr. simpl. fsetdec.
      * clear Fr. simpl. fsetdec.
      * rewrite_env (empty ++ [(y, bind_sub (subst_ct x C T1))] ++ E).
        eapply wf_typ_ignores_sub_bindings with (T1 := T1)...
      * destruct H4.
        rewrite_env (empty ++ [(y, bind_sub (subst_ct x C T1))] ++ E).
        apply subcapt_weakening...
        apply H5...
Qed.

Lemma true_meaning_of : forall E Ap Am x C D T,
    wf_env E ->
    type T ->
    Ap `subset` dom E ->
    Am `subset` dom E ->
    wf_typ E Ap Am T ->
    subcapt E C D ->
    x `notin` Am ->
    sub E (subst_ct x C T) (subst_ct x D T).
Proof with eauto.
  intros.
  eapply (proj1 (meaning_of _ Ap Am _ _ _ _ H H0 H1 H2 H3 H4))...
Qed.

(* subst_ct_intro

subst_ct X (open_ct T X) C = open_ct T C

subcapt E C1 C2 ->
sub E (open_ct T2 C1) (open_ct T2 C2) *)

Lemma typing_narrowing : forall Q E F X P e T,
  sub E P Q ->
  typing (F ++ [(X, bind_sub Q)] ++ E) e T ->
  typing (F ++ [(X, bind_sub P)] ++ E) e T.
Proof with eauto 6 using wf_env_narrowing, wf_typ_narrowing, sub_narrowing, subcapt_narrowing, cv_narrowing.
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
      pose proof (typing_regular _ _ _ (H1 y Fr)) as [P0 _].
      inversion P0; subst...
    }
    pick fresh y and apply typing_abs...
    + rewrite_parenthesise_binding.
      simpl_env in H0...
      eapply wf_typ_narrowing_base; simpl_env...
    + rewrite <- concat_assoc.
      apply H2...
  - Case "typing_app".
    (* Alex: requires making use of well-formedness *)
    pose proof (cv_exists_in (F ++ [(X, bind_sub P)] ++ E) T1') as Ex.
    destruct Ex as [Cnarrow HCVnarrow]...
    apply wf_typ_narrowing with (Q := Q)...
    eapply typing_sub with (S := (open_ct T2 Cnarrow))...
    pose proof (cv_narrowing _ _ _ _ _ _ _ _ PsubQ H0 HCVnarrow) as Subcapt.
    specialize (IHTyp1 F ltac:(auto)).
    (* inversion IHTyp1; subst. *)

    pick fresh x.
    rewrite (subst_ct_intro x)...
    replace (open_ct T2 Cv') with (subst_ct x Cv' (open_ct T2 x)).
    2: { symmetry. apply subst_ct_intro... }

    (* requires some inversion lemma
       this will also give us a fresh generator L0 which we should use for the pick fresh above.
     *)
    assert (wf_typ_in (F ++ [(X, bind_sub P)] ++ E) (open_ct T2 x)) as WfTyp. { admit. }
    apply (true_meaning_of
             (F ++ [(X, bind_sub P)] ++ E)
             (dom (F ++ [(X, bind_sub P)] ++ E))
             (dom (F ++ [(X, bind_sub P)] ++ E))
             x Cnarrow Cv' (open_ct T2 x)
          ).
    + auto.
    + eapply type_from_wf_typ...
    + trivial...
    + trivial...
    + trivial.
    + trivial.
    + trivial...
  - Case "typing_tabs".
    assert (wf_env (F ++ [(X, bind_sub P)] ++ E)). {
      pick fresh y for L.
      pose proof (typing_regular _ _ _ (H1 y Fr)) as [P0 _].
      inversion P0; subst...
    }
    pick fresh Y and apply typing_tabs...
    + rewrite_parenthesise_binding.
      simpl_env in H0...
      eapply wf_typ_narrowing_base; simpl_env...
    + rewrite <- concat_assoc.
      apply H2...
Admitted.

(************************************************************************ *)
(** ** Free_for_cv lemmas *)

Lemma subst_commutes_with_free_for_cv : forall x u C e,
    x `notin` (cset_fvars (free_for_cv e)) ->
    (subst_cset x C (free_for_cv e)) = (free_for_cv (subst_ee x u C e)).
Proof with eauto.
  intros *.
  intro Fr.
  induction e.
  - simpl.
    admit.
  - simpl in *.
    admit.
  - apply IHe...
  - simpl in *.
    rewrite <- IHe1...
    rewrite <- IHe2...
    all : admit.
  - apply IHe...
  - apply IHe...
Admitted.

Lemma free_for_cv_subst_ee_cset_irrelevancy: forall x u C D t,
  free_for_cv (subst_ee x u C t) =
  free_for_cv (subst_ee x u D t).
Proof.
  induction t.
  all : simpl; eauto.
  rewrite IHt1.
  rewrite IHt2.
  trivial.
Qed.

Lemma subst_te_idempotent_wrt_free_for_cv : forall e x C,
    free_for_cv (subst_te x C e) = free_for_cv e.
Proof with eauto.
  intros.
  induction e; simpl; eauto.
  rewrite IHe1.
  rewrite IHe2.
  easy.
Qed.

(************************************************************************ *)
(** ** Properties of values *)

Lemma value_therefore_fv_subcapt_cv : forall E t T C,
  value t ->
  typing E t T ->
  cv E T C ->
  subcapt E (free_for_cv t) C.
Proof with subst; simpl; auto.
  intros *.
  intros Hv Htyp Hcv.
  generalize dependent C.
  pose proof (typing_regular _ _ _ Htyp) as [P1 [P2 P3]].
  induction Htyp; intros C0 Hcv; try solve [ inversion Hv ].
  - inversion Hcv...
    apply subcapt_reflexivity with (A := dom E)...
  - inversion Hcv.
    apply subcapt_reflexivity with (A := dom E)...
  - unshelve epose proof (cv_exists_in E S P1 _ ) as [D HcvS]...
    unshelve epose proof (IHHtyp Hv _ _ _ D HcvS)...
    apply subcapt_transitivity with (C2 := D)...
    eapply sub_implies_subcapt with (S := S) (T := T)
                                    (A1 := dom E) (A2 := dom E)...
Qed.

Lemma value_typing_inv : forall E v T,
  value v ->
  typing E v T ->
  exists C, exists P, sub E (typ_capt C P) T.
Proof with eauto using typing_cv.
  intros*.
  intros Val Typ.
  assert (wf_env E) by auto.
  assert (wf_cset_in E (free_for_cv v)) by eauto using typing_cv.
  induction Typ; inversion Val; subst...
  - exists (free_for_cv e1). exists (typ_arrow V T1).
    eapply sub_reflexivity with (Ap := dom E) (Am := dom E)...
  - exists (free_for_cv e1). exists (typ_all V T1).
    eapply sub_reflexivity with (Ap := dom E) (Am := dom E)...
  - destruct IHTyp as [C [P]]...
    exists C. exists P. apply sub_transitivity with (Q := S)...
  - destruct IHTyp as [C [P]]...
    exists C. exists P. apply sub_transitivity with (Q := S)...
Qed.

Lemma values_have_precise_captures : forall E u T,
  value u ->
  typing E u T ->
  exists U, typing E u (typ_capt (free_for_cv u) U) /\ sub E (typ_capt (free_for_cv u) U) T.
Local Ltac hint ::=
    simpl; eauto.
Proof with hint.
  intros *.
  intros Hv Htyp.
  assert (wf_cset_in E (free_for_cv u)) by eauto using typing_cv.
  assert (wf_env E) by auto.
  induction Htyp; try solve [inversion Hv; subst].
  - Case "exp_abs".
    exists (typ_arrow V T1).
    split.
    + simpl; eapply typing_abs...
    + simpl.
      eapply sub_reflexivity with (Ap := dom E) (Am := dom E)...
  - Case "exp_tabs".
    exists (typ_all V T1).
    split.
    + simpl; eapply typing_tabs...
    + simpl.
      eapply sub_reflexivity with (Ap := dom E) (Am := dom E)...
  - unshelve epose proof (IHHtyp _ _ _) as [U [HtypU HsubS]]...
    exists U; eauto using (sub_transitivity S).
Qed.

(************************************************************************ *)
(** ** Substitution preserves typing (8) *)

Lemma wf_env_strengthening : forall F E,
  wf_env (F ++ E) ->
  wf_env E.
Proof with eauto.
  induction F...
  intros.
  inversion H; subst...
Qed.

Lemma wf_typ_through_subst_ct_base : forall U Ap Am F x C E T,
  wf_env (F ++ [(x, bind_typ U)] ++ E) ->
  cv E U C ->
  wf_typ (F ++ [(x, bind_typ U)] ++ E) Ap Am T ->
  wf_typ (map (subst_cb x C) F ++ E) (Ap `remove` x) (Am `remove` x) (subst_ct x C T)
with wf_pretyp_through_subst_cpt_base : forall U Ap Am F x C E P,
  wf_env (F ++ [(x, bind_typ U)] ++ E) ->
  cv E U C ->
  wf_pretyp (F ++ [(x, bind_typ U)] ++ E) Ap Am P ->
  wf_pretyp (map (subst_cb x C) F ++ E) (Ap `remove` x) (Am `remove` x) (subst_cpt x C P).
Proof.
Admitted.

Lemma wf_typ_through_subst_ct : forall F x U C E T,
    wf_env (F ++ [(x, bind_typ U)] ++ E) ->
    cv E U C ->
    wf_typ_in (F ++ [(x, bind_typ U)] ++ E) T ->
    wf_typ_in (map (subst_cb x C) F ++ E) (subst_ct x C T)
with wf_pretyp_through_subst_cpt : forall F x U C E P,
    wf_env (F ++ [(x, bind_typ U)] ++ E) ->
    cv E U C ->
    wf_pretyp_in (F ++ [(x, bind_typ U)] ++ E) P ->
    wf_pretyp_in (map (subst_cb x C) F ++ E) (subst_cpt x C P).
Proof.
  (* Use above. *)
Admitted.

Lemma wf_env_subst_cb : forall Q C x E F,
  wf_env (F ++ [(x, bind_typ Q)] ++ E) ->
  wf_cset_in E C ->
  wf_env (map (subst_cb x C) F ++ E).
Proof.
  (* with eauto 6 using wf_typ_subst_tb *)

  admit.
  (* induction F; intros Wf_env WP; simpl_env; *)
  (*   inversion Wf_env; simpl_env in *; simpl subst_tb... *)
Admitted.

Lemma cv_through_subst_ct : forall F x U E C T D,
    cv (F ++ [(x, bind_typ U)] ++ E) T C ->
    cv E U D ->
    cv (map (subst_cb x D) F ++ E) (subst_ct x D T) (subst_cset x D C).
Proof.
  admit.
Admitted.

Lemma sub_through_subst_ct : forall E F x U C S T,
  sub (F ++ [(x, bind_typ U)] ++ E) S T ->
  cv E U C ->
  sub (map (subst_cb x C) F ++ E) (subst_ct x C S) (subst_ct x C T)
with sub_pre_through_subst_cpt : forall E F x U C P Q,
  sub_pre (F ++ [(x, bind_typ U)] ++ E) Q P ->
  cv E U C ->
  sub_pre (map (subst_cb x C) F ++ E) (subst_cpt x C Q) (subst_cpt x C P).
Proof with eauto.
  { intros *.
    intros Hsub HcvU.
    remember (F ++ [(x, bind_typ U)] ++ E).
    generalize dependent F.
    induction Hsub; intros F EQ; subst.
    - simpl.
      apply sub_refl_tvar...
      + eapply wf_env_subst_cb...
      + unsimpl (subst_ct x C X).
        eapply wf_typ_through_subst_ct...
    - simpl.
      destruct (x == X).
      + SCase "x == X".
        subst.
        binds_get H.
      + SCase "x <> X".
        binds_cases H.
        * assert (x `notin` fv_et U0) as FrXinU0. {
            (* by larger env binding x being wf *)
            apply cheat.
          }
          unshelve epose proof (IHHsub F _) as IHHsub0...
          rewrite <- (subst_ct_fresh x C U0) in IHHsub0...
        * apply sub_trans_tvar with (U := (subst_ct x C U0))...
    - apply sub_capt.
      + eapply subcapt_through_subst_cset...
      + eapply sub_pre_through_subst_cpt...
  }
  { intros *.
    intros Hsub HcvU.
    remember (F ++ [(x, bind_typ U)] ++ E).
    generalize dependent F.
    induction Hsub; intros F EQ; subst.
    - simpl.
      apply sub_top.
      + eapply wf_env_subst_cb...
      + eapply wf_pretyp_through_subst_cpt...
    - pick fresh y for L.
      (* specialize (H0 y Fr). *)
      apply cheat.
    - apply cheat.
  }
Qed.

Local Lemma foo : forall x C e,
    AtomSet.F.In x (cset_fvars (free_for_cv e)) ->
    subst_cset x C (free_for_cv e) = cset_union C (cset_remove_fvar x (free_for_cv e)).
Proof.
Admitted.

Local Lemma bar : forall x C e u,
  AtomSet.F.In x (cset_fvars (free_for_cv e)) ->
  (cset_union C (cset_remove_fvar x (free_for_cv e))) =
        (free_for_cv (subst_ee x u C e)).
Proof.
Admitted.

Hint Extern 1 (wf_pretyp ?E (dom ?E) (dom ?E) ?P) =>
match goal with
| H : typing E _ (typ_capt _ P) |- _ =>
  apply typing_regular in H;
  destruct H as [_ [_ H]];
  inversion H; subst; assumption
end.

Hint Extern 1 (wf_pretyp_in ?E ?P) =>
match goal with
| H : typing E _ (typ_capt _ P) |- _ =>
  apply typing_regular in H;
  destruct H as [_ [_ H]];
  inversion H; subst; assumption
end.

Lemma typing_through_subst_ee : forall P E F x T e u,
  typing (F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E) e T ->
  value u ->
  typing E u (typ_capt (free_for_cv u) P) ->
  typing (map (subst_cb x (free_for_cv u)) F ++ E)
         (subst_ee x u (free_for_cv u) e)
         (subst_ct x (free_for_cv u) T).
Local Ltac hint ::=
  eauto 4 using wf_env_subst_cb, typing_cv.
Proof with hint.
  intros *.
  intros HtypT HvalU HtypU.
  assert (wf_env E) as HwfE. {
    apply wf_env_strengthening
      with (F := (F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))])); simpl_env...
  }
  assert (wf_cset_in E (free_for_cv u)) as HwfFv...
  assert (capt (free_for_cv u)) as HcaptFv. {
    eapply capt_from_wf_cset...
  }
  remember (F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E).
  generalize dependent F.
  induction HtypT; intros F EQ; subst; simpl subst_ee...

  - Case "typing_var_tvar".
    destruct (x0 == x); subst.
    + binds_get H0.
    + simpl.
      binds_cases H0...
      * apply typing_var_tvar...
        apply binds_head.
        replace (bind_typ X) with (subst_cb x (free_for_cv u) (bind_typ X))...
  - Case "typing_var".
    destruct (x0 == x); subst.
    + SCase "x0 = x".
      binds_get H0.
      inversion H2; subst.
      rewrite_nil_concat.
      apply typing_weakening; simpl_env...
      simpl.
      replace (subst_cset x (free_for_cv u) x) with (free_for_cv u).
      2: { trivial; admit. }
      replace (subst_cpt x (free_for_cv u) P) with P.
      2: { admit. }           (* wf_env x,E -> x `notin` fv_ee P *)
      unshelve epose proof
      (values_have_precise_captures E u (typ_capt (free_for_cv u) P) _ _)
        as [? [? ?]]...
    + SCase "x0 <> x".
      binds_cases H0.
      * assert (x `notin` fv_ept P). {
          assert (x `notin` dom E) as HA1. { eapply fresh_mid_tail... }
          unshelve epose proof (wf_typ_from_binds_typ _ _ _ _ H0)...
          assert (wf_pretyp_in E P) as HA2...
          epose proof (notin_fv_wf_pretyp _ _ _ HA2 HA1)...
        }
        replace (subst_ct x C (typ_capt x0 P)) with (typ_capt x0 P).
        2: {
          apply subst_ct_fresh; simpl_env...
        }
        rewrite_nil_concat.
        apply typing_weakening; simpl_env...
        simpl.
        rewrite <- (subst_cset_fresh x)...
        replace (subst_cpt x (free_for_cv u) P0) with P0.
        2: {
          admit.
          (* apply subst_cpt_fresh... *)
        }
        trivial...
      * simpl.
        rewrite <- (subst_cset_fresh x)...
        eapply typing_var...
        (* heavy environment wrangling ahead... *)
        assert (binds x0
                      (bind_typ (subst_ct x (free_for_cv u) (typ_capt C P0)))
                      (map (subst_cb x (free_for_cv u)) F)). {
          replace (bind_typ (subst_ct x (free_for_cv u) (typ_capt C P0)))
            with (subst_cb x (free_for_cv u) (bind_typ (typ_capt C P0))) by auto...
        }
        rewrite <- concat_nil.
        rewrite -> concat_assoc.
        apply binds_weaken.
        ** rewrite -> concat_nil...
        ** rewrite -> concat_nil...

  - Case "typing_abs".
    assert (wf_env (F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E)) as HwfNarrE. {
      pick fresh z for L.
      pose proof (H1 z Fr)...
      enough (wf_env
                ([(z, bind_typ V)] ++ F ++
                                   [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E)) as HwfHugeE...
      inversion HwfHugeE...
    }
    pose proof HwfNarrE as HxUniq.
    apply binding_uniq_from_wf_env in HxUniq.
    assert (wf_typ_in (F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E) V). {
      pick fresh z for L.
      pose proof (H1 z Fr) as HtypE1...
    }

    simpl subst_ct.
    destruct (AtomSet.F.mem x (cset_fvars (free_for_cv e1))) eqn:EqMem.
    + SCase "x in fv e1".
      assert (x `in` cset_fvars (free_for_cv e1)) by (rewrite AtomSetFacts.mem_iff; assumption).
      rewrite foo...
      rewrite bar with (u := u)...
      pick fresh y and apply typing_abs...
      * eapply wf_typ_through_subst_ct...
      * assert (y <> x) by fsetdec.
        rewrite subst_ct_open_ct_var...

        simpl_env in *.
        replace ((dom F `union` dom E) `union` singleton y)
          with (((dom F `union` singleton x `union` dom E) `union` singleton y) `remove` x).
        2: { clear Fr. fsetdec. }
        replace (dom F `union` dom E)
          with ((dom F `union` singleton x `union` dom E) `remove` x).
        2: { clear Fr. fsetdec. }

        rewrite_env (map (subst_cb x (free_for_cv u)) ([(y, bind_typ V)] ++ F) ++ E).
        apply (wf_typ_through_subst_ct_base (typ_capt (free_for_cv u) P)); simpl_env...
      * assert (y <> x) by fsetdec.
        rewrite subst_ee_open_ee_var...
        rewrite subst_ct_open_ct_var...
        rewrite_env (map (subst_cb x (free_for_cv u)) ([(y, bind_typ V)] ++ F) ++ E).
        apply H2...
    + SCase "x not in fv e1".
      assert (x `notin` cset_fvars (free_for_cv e1)) by (rewrite AtomSetFacts.not_mem_iff; assumption).
      rewrite subst_commutes_with_free_for_cv with (u := u)...
      pick fresh y and apply typing_abs...
      * eapply wf_typ_through_subst_ct...
      * assert (y <> x) by fsetdec.
        rewrite subst_ct_open_ct_var...

        simpl_env in *.
        replace ((dom F `union` dom E) `union` singleton y)
          with (((dom F `union` singleton x `union` dom E) `union` singleton y) `remove` x).
        2: { clear Fr. fsetdec. }
        replace (dom F `union` dom E)
          with ((dom F `union` singleton x `union` dom E) `remove` x).
        2: { clear Fr. fsetdec. }

        rewrite_env (map (subst_cb x (free_for_cv u)) ([(y, bind_typ V)] ++ F) ++ E).
        apply (wf_typ_through_subst_ct_base (typ_capt (free_for_cv u) P)); simpl_env...
      * assert (y <> x) by fsetdec.
        rewrite subst_ee_open_ee_var...
        rewrite subst_ct_open_ct_var...
        rewrite_env (map (subst_cb x (free_for_cv u)) ([(y, bind_typ V)] ++ F) ++ E).
        apply H2...

  - Case "typing_app".
    rewrite subst_ct_open_ct...
    simpl subst_ct in IHHtypT1...
    eapply typing_app...
    + eapply sub_through_subst_ct...
    + eapply cv_through_subst_ct...

  - Case "typing_tabs".
    assert (wf_env (F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E)) as HwfNarrE. {
      pick fresh z for L.
      pose proof (H1 z Fr)...
      enough (wf_env
                ([(z, bind_sub V)] ++ F ++
                                   [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E)) as HwfHugeE...
      inversion HwfHugeE...
    }
    pose proof HwfNarrE as HxUniq.
    apply binding_uniq_from_wf_env in HxUniq.
    assert (wf_typ_in (F ++ [(x, bind_typ (typ_capt (free_for_cv u) P))] ++ E) V). {
      pick fresh z for L.
      pose proof (H1 z Fr) as HtypE1...
    }

    simpl subst_ct.
    destruct (AtomSet.F.mem x (cset_fvars (free_for_cv e1))) eqn:EqMem.
    + SCase "x in fv e1".
      assert (x `in` cset_fvars (free_for_cv e1)) by (rewrite AtomSetFacts.mem_iff; assumption).
      rewrite foo...
      rewrite bar with (u := u)...
      pick fresh y and apply typing_tabs...
      * eapply wf_typ_through_subst_ct...
      * assert (y <> x) by fsetdec.
        rewrite subst_ct_open_tt_var...

        simpl_env in *.
        replace ((dom F `union` dom E) `union` singleton y)
          with (((dom F `union` singleton x `union` dom E) `union` singleton y) `remove` x).
        2: { clear Fr. fsetdec. }
        replace (dom F `union` dom E)
          with ((dom F `union` singleton x `union` dom E) `remove` x).
        2: { clear Fr. fsetdec. }

        rewrite_env (map (subst_cb x (free_for_cv u)) ([(y, bind_sub V)] ++ F) ++ E).
        apply (wf_typ_through_subst_ct_base (typ_capt (free_for_cv u) P)); simpl_env...
      * assert (y <> x) by fsetdec.
        rewrite subst_ee_open_te_var...
        rewrite subst_ct_open_tt_var...
        rewrite_env (map (subst_cb x (free_for_cv u)) ([(y, bind_sub V)] ++ F) ++ E).
        apply H2...
    + SCase "x not in fv e1".
      assert (x `notin` cset_fvars (free_for_cv e1)) by (rewrite AtomSetFacts.not_mem_iff; assumption).
      rewrite subst_commutes_with_free_for_cv with (u := u)...
      pick fresh y and apply typing_tabs...
      * eapply wf_typ_through_subst_ct...
      * assert (y <> x) by fsetdec.
        rewrite subst_ct_open_tt_var...

        simpl_env in *.
        replace ((dom F `union` dom E) `union` singleton y)
          with (((dom F `union` singleton x `union` dom E) `union` singleton y) `remove` x).
        2: { clear Fr. fsetdec. }
        replace (dom F `union` dom E)
          with ((dom F `union` singleton x `union` dom E) `remove` x).
        2: { clear Fr. fsetdec. }

        rewrite_env (map (subst_cb x (free_for_cv u)) ([(y, bind_sub V)] ++ F) ++ E).
        apply (wf_typ_through_subst_ct_base (typ_capt (free_for_cv u) P)); simpl_env...
      * assert (y <> x) by fsetdec.
        rewrite subst_ee_open_te_var...
        rewrite subst_ct_open_tt_var...
        rewrite_env (map (subst_cb x (free_for_cv u)) ([(y, bind_sub V)] ++ F) ++ E).
        apply H2...

  - Case "typing_tapp".
    rewrite subst_ct_open_tt...
    eapply typing_tapp.
    + simpl subst_ct in IHHtypT.
      apply IHHtypT...
    + eapply sub_through_subst_ct...
  - Case "typing_sub".
    eapply typing_sub.
    + apply IHHtypT...
    + eapply sub_through_subst_ct...
Admitted.

Lemma typing_narrowing_typ : forall Q E F X P e T,
  typing (F ++ [(X, bind_typ Q)] ++ E) e T ->
  sub E P Q ->
  typing (F ++ [(X, bind_typ P)] ++ E) e T.
Proof.
  trivial; admit.
Admitted.

Lemma typing_through_subst_ee' : forall U E Ap Am x T C e u,
  typing ([(x, bind_typ U)] ++ E) e T ->
  wf_typ ([(x, bind_typ U)] ++ E) Ap Am T ->
  x `notin` Am ->
  Ap `subset` dom ([(x, bind_typ U)] ++ E) ->
  Am `subset` dom ([(x, bind_typ U)] ++ E) ->
  value u ->
  typing E u U ->
  cv E U C ->
  typing E (subst_ee x u (free_for_cv u) e) (subst_ct x C T).
Proof with simpl_env; eauto.
  intros *.
  intros HtypT HwfT Hnotin HApRsnbl HAmRsnbl HvalU HtypU HcvU.
  assert (typing E (subst_ee x u (free_for_cv u) e) (subst_ct x (free_for_cv u) T))
    as Hthrough. {
    apply values_have_precise_captures in HtypU...
    destruct HtypU as [P [HtypP HsubP]].
    rewrite_env (map (subst_cb x (free_for_cv u)) empty ++ E).
    eapply (typing_through_subst_ee P)...
    rewrite_nil_concat.
    eapply typing_narrowing_typ...
  }
  eapply typing_sub.
  apply Hthrough.
  enough (sub ([(x, bind_typ U)] ++ E) (subst_ct x (free_for_cv u) T) (subst_ct x C T)) as HE. {
    rewrite_env (empty ++ [(x, bind_typ U)] ++ E) in HE.
    pose proof (sub_through_subst_ct _ _ _ _ _ _ _ HE HcvU) as HP.

    simpl_env in HP.
    repeat (rewrite subst_ct_useless_repetition in HP).
    apply HP.
  }
  apply true_meaning_of with (Ap := Ap) (Am := Am)...
  apply value_therefore_fv_subcapt_cv with (T := U)...
  rewrite_env (empty ++ [(x, bind_typ U)] ++ E);
    eapply typing_weakening...
  rewrite_env (empty ++ [(x, bind_typ U)] ++ E);
    eapply cv_weakening...
Qed.

(************************************************************************ *)
(** ** Type substitution preserves typing (11) *)

Lemma wf_typ_extract_typ_arrow : forall C E T1 T2,
  wf_typ_in E (typ_capt C (typ_arrow T1 T2)) ->
  exists L, forall x, x `notin` L ->
     wf_typ ([(x, bind_typ T1)] ++ E) (dom E `union` singleton x) (dom E) (open_ct T2 x).
Proof with eauto.
  intros *.
  intro HWf.
  (* type inversion *)
  inversion HWf; subst.
  (* pretype inversion *)
  inversion H5; subst...
Qed.

Lemma typing_extract_typ_arrow : forall E e C T1 T2,
  typing E e (typ_capt C (typ_arrow T1 T2)) ->
  exists L, forall x, x `notin` L ->
     wf_typ ([(x, bind_typ T1)] ++ E) (dom E `union` singleton x) (dom E) (open_ct T2 x).
Proof with eauto.
  intros *.
  intro Htyp.
  apply (wf_typ_extract_typ_arrow C)...
Qed.

Lemma applied_meaning_of : forall E C1 C2 e D S T,
  subcapt E C1 C2 ->
  typing E e (typ_capt D (typ_arrow S T)) ->
  sub E (open_ct T C1) (open_ct T C2).
Proof.
  intros *. intros Hsc Htyp.
  pose proof (typing_extract_typ_arrow _ _ _ _ _ Htyp) as [L HRT].
  pick fresh y.
  replace (open_ct T C1) with (subst_ct y C1 (open_ct T y)).
  replace (open_ct T C2) with (subst_ct y C2 (open_ct T y)).
  2,3: solve [symmetry; apply subst_ct_intro; fsetdec].
  pose proof (typing_regular _ _ _ Htyp) as [_ [_ Reg]].
  inversion Reg.
  match goal with
  | H : wf_pretyp _ _ _ _ |- _ =>
    inversion H
  end.
  subst.
  assert (wf_typ ([(y, bind_typ S)] ++ E)
                  (dom E `union` singleton y) (dom E)
                  (open_ct T y)) by eauto.
  enough (sub ([(y, bind_typ S)] ++ E)
              (subst_ct y C1 (open_ct T y))
              (subst_ct y C2 (open_ct T y))). {
    assert (wf_typ_in E S) as HwfS by assumption.
    unshelve epose proof (cv_exists_in E S _ _) as [C_S ?]; auto.
    rewrite_env (map (subst_cb y C_S) empty ++ E).
    replace (subst_ct y C1 (open_ct T y))
      with (subst_ct y C_S (subst_ct y C1 (open_ct T y))).
    replace (subst_ct y C2 (open_ct T y))
      with (subst_ct y C_S (subst_ct y C2 (open_ct T y))).
    2,3: solve [apply subst_ct_useless_repetition].
    apply sub_through_subst_ct with (U := S); simpl_env; auto.
  }
  eapply true_meaning_of with (Ap := dom E `union` singleton y) (Am := dom E); eauto.
  rewrite_nil_concat.
  apply subcapt_weakening; simpl_env; eauto.
Qed.

Lemma wf_typ_through_subst_tt_base : forall Q Ap Am Ap' Am' F X P E T,
    wf_env (F ++ [(X, bind_sub Q)] ++ E) ->
    sub E P Q ->
    wf_typ (F ++ [(X, bind_sub Q)] ++ E) Ap Am T ->
    wf_typ E Ap' Am' P ->
    Ap' `subset` Ap ->
    Am' `subset` Am ->
    wf_typ (map (subst_tb X P) F ++ E) (Ap `remove` X) (Am `remove` X) (subst_tt X P T)
with wf_pretyp_through_subst_tpt_base : forall Q Ap Am Ap' Am' F X P E R,
    wf_env (F ++ [(X, bind_sub Q)] ++ E) ->
    sub E P Q ->
    wf_pretyp (F ++ [(X, bind_sub Q)] ++ E) Ap Am R ->
    wf_typ E Ap' Am' P ->
    Ap' `subset` Ap ->
    Am' `subset` Am ->
    wf_pretyp (map (subst_tb X P) F ++ E) (Ap `remove` X) (Am `remove` X) (subst_tpt X P R).
Proof with eauto.

(* { intros *. *)
(*   intros HwfEnv Hsub HwfT HwfP HssetAp HssetAm. *)
(*   dependent induction HwfT. *)
(*   - simpl. *)
(*     destruct (X0 == X). *)
(*     + rewrite_nil_concat. *)
(*       apply wf_typ_weakening with (Ap := Ap') (Am := Am')... *)

(* } *)
Admitted.

Lemma wf_typ_through_subst_tt : forall Q F x P E T,
    wf_env (F ++ [(x, bind_sub Q)] ++ E) ->
    sub E P Q ->
    wf_typ_in (F ++ [(x, bind_sub Q)] ++ E) T ->
    wf_typ_in (map (subst_tb x P) F ++ E) (subst_tt x P T)
with wf_pretyp_through_subst_tpt : forall Q F x P E R,
    wf_env (F ++ [(x, bind_sub Q)] ++ E) ->
    sub E P Q ->
    wf_pretyp_in (F ++ [(x, bind_sub Q)] ++ E) R ->
    wf_pretyp_in (map (subst_tb x P) F ++ E) (subst_tpt x P R).
Proof.
  (* Use above. *)
Admitted.

Lemma wf_cset_from_binds : forall b x E,
  wf_env E ->
  binds x (bind_typ b) E ->
  wf_cset_in E x.
Proof.
Admitted.

Lemma captures_from_binds : forall P x C E,
  wf_env E ->
  binds x (bind_typ (typ_capt C P)) E ->
  subcapt E x C.
Proof.
Admitted.

Lemma typing_through_subst_te : forall Q E F Z e T P,
  typing (F ++ [(Z, bind_sub Q)] ++ E) e T ->
  sub E P Q ->
  typing (map (subst_tb Z P) F ++ E) (subst_te Z P e) (subst_tt Z P T).
Proof with simpl_env;
           eauto 6 using wf_env_subst_tb,
                         wf_typ_subst_tb,
                         sub_through_subst_tt.
  intros *.
  intros Typ PsubQ.
  remember (F ++ [(Z, bind_sub Q)] ++ E).
  generalize dependent F.
  induction Typ; intros F EQ; subst;
    simpl subst_te in *; simpl subst_tt in *...
  - Case "typing_var_tvar".
    destruct (X == Z).
    rewrite (map_subst_tb_id E Z P);
      [ | auto | eapply fresh_mid_tail; eauto ].
    + subst.
      binds_cases H0...
      * assert (type P) as TypP...
        destruct TypP.
        -- set (P' := X) in *.
           assert (wf_env (map (subst_tb Z P') F ++ E)) as HA...
           rewrite (map_subst_tb_id E Z P') in HA;
             [ | auto | eapply fresh_mid_tail; eauto ].
           eapply typing_var_tvar...
           apply binds_map with (f := (subst_tb Z P')) in H0.
           simpl in H0.
           destruct (Z == Z); try easy.
           rewrite_env (empty ++ map (subst_tb Z P') F ++ map (subst_tb Z P') E).
           apply binds_weaken...
        -- assert (wf_env (map (subst_tb Z (typ_capt C P)) F ++ E)) as HA...
           rewrite (map_subst_tb_id E Z (typ_capt C P)) in HA;
             [ | auto | eapply fresh_mid_tail; eauto ].
           apply binds_map with (f := (subst_tb Z (typ_capt C P))) in H0.
           assert (binds x (subst_tb Z (typ_capt C P) (bind_typ Z))
                         (empty ++ map (subst_tb Z (typ_capt C P)) F ++
                                map (subst_tb Z (typ_capt C P)) E)) as HAbinds. {
             apply binds_weaken...
           }
           simpl in HAbinds.
           destruct (Z == Z); try easy.
           apply (typing_sub (typ_capt x P))...
           apply wf_typ_from_binds_typ in HAbinds as HAwfP...
           inversion HAwfP; subst.
           match goal with H : wf_pretyp _ _ _ P |- _ =>
             simpl_env in H
           end.
           apply sub_capt.
           ++ destruct C; eauto using wf_cset_from_binds, captures_from_binds.
           ++ apply sub_pre_reflexivity with
                  (Ap := dom (map (subst_tb Z (typ_capt C P)) F ++ map (subst_tb Z (typ_capt C P)) E))
                  (Am := dom (map (subst_tb Z (typ_capt C P)) F ++ map (subst_tb Z (typ_capt C P)) E))...
      * admit.
    + subst.
      apply typing_var_tvar...
      admit.
      (* rewrite (map_subst_tb_id E Z P); *)
      (*   [ | auto | eapply fresh_mid_tail; eauto ]. *)
      (* binds_cases H0... *)
      (* * enough (binds x (subst_tb Z P (bind_typ X)) (map (subst_tb Z P) E))... *)
      (*   simpl in H1... *)
      (*   admit. *)
      (* * admit. *)
  - Case "typing_var".
    admit.
  - Case "typing_abs".
    replace (free_for_cv e1) with (free_for_cv (subst_te Z P e1)).
    2: { rewrite subst_te_idempotent_wrt_free_for_cv... }
    pick fresh y and apply typing_abs.
    + admit.
    + admit.
    + rewrite_env (map (subst_tb Z P) ([(y, bind_typ V)] ++ F) ++ E).
      rewrite subst_te_open_ee_var...
      rewrite subst_tt_open_ct_var...
      unshelve eapply (H2 y _ ([(y, bind_typ V)] ++ F) _)...
  - Case "typing_app".
    unshelve epose proof (IHTyp2 F _)...
    unshelve epose proof (IHTyp1 F _) as SpIHTyp1...
    unshelve epose proof (cv_exists_in (map (subst_tb Z P) F ++ E) (subst_tt Z P T1') _ _) as [D HcvD]...
    assert (wf_typ_in (map (subst_tb Z P) F ++ E)
                      (typ_capt Cf (typ_arrow (subst_tt Z P T1) (subst_tt Z P T2))))...
    unshelve epose proof (cv_exists_in (map (subst_tb Z P) F ++ E) (subst_tt Z P T1) _ _) as [? ?]...
    + apply (wf_typ_through_subst_tt Q)...
    + rewrite <- subst_tt_open_ct...
      apply (typing_sub (open_ct (subst_tt Z P T2) D))...

      eapply applied_meaning_of.
      * apply cv_through_subst_tt with (Q := Q) (T := T1')...
      * apply SpIHTyp1.
  - Case "typing_tabs".
    replace (free_for_cv e1) with (free_for_cv (subst_te Z P e1)).
    2: { rewrite subst_te_idempotent_wrt_free_for_cv... }
    pick fresh Y and apply typing_tabs.
    + admit.
    + admit.
    + rewrite subst_te_open_te_var...
      rewrite subst_tt_open_tt_var...
      rewrite_env (map (subst_tb Z P) ([(Y, bind_sub V)] ++ F) ++ E).
      apply H2...
  - Case "typing_tapp".
    rewrite subst_tt_open_tt...
Admitted.


(* ********************************************************************** *)
(** * #<a name="preservation"></a># Preservation *)


(* ********************************************************************** *)
(** ** Inversion of typing (13) *)

Lemma typing_inv_abs : forall E S1 e1 T,
  typing E (exp_abs S1 e1) T ->
  forall U1 U2 C, sub E T (typ_capt C (typ_arrow U1 U2)) ->
     sub E U1 S1
  /\ exists S2, exists L, forall x, x `notin` L ->
     typing ([(x, bind_typ S1)] ++ E) (open_ee e1 x x) (open_ct S2 x) /\
     wf_typ ([(x, bind_typ S1)] ++ E) (dom E `union` singleton x) (dom E) (open_ct U2 x) /\
     sub ([(x, bind_typ U1)] ++ E) (open_ct S2 x) (open_ct U2 x).
Proof with auto.
  intros *.
  intro Htyp.
  dependent induction Htyp; intros U1 U2 C Hsub.
  - Case "typing_abs".
    inversion Hsub; subst.
    match goal with H : sub_pre _ _ _ |- _ =>
      inversion H; subst
    end.
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
  Admitted.
(*
  intros E S1 e1 T Typ.
  remember (exp_tabs S1 e1).
  generalize dependent e1.
  generalize dependent S1.
  induction Typ; intros S1 e0 EQ U1 U2 Sub; inversion EQ; subst.
  Case "typing_tabs".
    inversion Sub; subst.
    split...
    exists T1.
    exists (L0 `union` L).
    intros Y Fr.
    split...
    rewrite_env (empty ++ [(Y, bind_sub U1)] ++ E).
    apply (typing_narrowing S1)...
  Case "typing_sub".
    auto using (sub_transitivity T).
Qed.
*)


(* ********************************************************************** *)
(** ** Preservation (20) *)

Lemma preservation : forall E e e' T,
  typing E e T ->
  red e e' ->
  typing E e' T.
Proof with simpl_env; eauto.
  intros E e e' T Typ. generalize dependent e'.
  induction Typ; intros e' Red; try solve [ inversion Red; subst; eauto ].
  - Case "typing_app".
    inversion Red; subst...
    + SCase "red_abs".
      destruct (typing_inv_abs _ _ _ _ Typ1 T1 T2 Cf) as [P1 [S2 [L P2]]].
        eapply sub_reflexivity...
      pick fresh x.
      destruct (P2 x ltac:(notin_solve)) as [? [? ?]]...
      rewrite (subst_ee_intro x)...
      rewrite (subst_ct_intro x)...
      apply typing_through_subst_ee'
        with (U := T1')
             (Ap := dom ([(x, bind_typ T1')] ++ E))
             (Am := dom E) ...
      * apply (typing_sub (open_ct S2 x))...
        -- rewrite_nil_concat.
           apply (typing_narrowing_typ T)...
           eauto using (sub_transitivity T1).
        -- rewrite_nil_concat.
           apply (sub_narrowing_typ) with (Q := T1)...
      * replace (singleton x `union` dom E)
          with (dom E `union` singleton x) by (clear Fr; fsetdec)...
        rewrite_nil_concat.
        apply wf_typ_narrowing_typ_base with (V := T)...
  - Case "typing_tapp".
    inversion Red; subst...
    SCase "red_tabs".
    admit.
    (* destruct (typing_inv_tabs _ _ _ _ Typ T1 T2 C) as [P1 [L P2]]. { *)
    (*   eapply sub_reflexivity... *)
    (* } *)
    (* pick fresh X. *)
    (* destruct (P2 X ltac:(notin_solve)) as [S2 ?]... *)
    (* rewrite (subst_te_intro X)... *)
    (* rewrite (subst_tt_intro X)... *)
    (* rewrite_env (map (subst_tb X T) empty ++ E). *)
    (* apply (typing_through_subst_te T1)... *)
Admitted.

(* ********************************************************************** *)
(** * #<a name="progress"></a># Progress *)


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
  induction Typ; intros U1 U2 EQT EQE; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
  Case "typing_sub".
  (*
    inversion H; subst; eauto.
    inversion H0. *)
    admit.
Admitted.

Lemma canonical_form_tabs : forall e U1 U2 C,
  value e ->
  typing empty e (typ_capt C (typ_all U1 U2)) ->
  exists V, exists e1, e = exp_tabs V e1.
Proof.
  intros e U1 U2 C Val Typ.
  remember empty.
  remember (typ_all U1 U2).
  revert U1 U2 Heqp Heql.
  induction Typ; intros U1 U2 EQT EQE; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
  Case "typing_sub".
    (*inversion H; subst; eauto.
    inversion H0.*)
    admit.
Admitted.



(* ********************************************************************** *)
(** ** Progress (16) *)

Lemma progress : forall e T,
  typing empty e T ->
  value e \/ exists e', red e e'.
Proof with eauto.
  intros e T Typ.
  remember empty. generalize dependent Heql.
  assert (Typ' : typing l e T)...
  induction Typ; intros EQ; subst...
  Case "typing_var".
    inversion H0.
  Case "typing_app".
    inversion H0.
    destruct IHTyp1 as [Val1 | [e1' Rede1']]...
    SCase "Val1".
      destruct IHTyp2 as [Val2 | [e2' Rede2']]...
      SSCase "Val2".
        destruct (canonical_form_abs _ _ _ _ Val1 Typ1) as [S [e3 EQ]].
        subst.
        right.
        exists (open_ee e3 e2 (free_for_cv e2))...
  Case "typing_tapp".
    right.
    destruct IHTyp as [Val1 | [e1' Rede1']]...
    SCase "Val1".
      destruct (canonical_form_tabs _ _ _ _ Val1 Typ) as [S [e3 EQ]].
      subst.
      exists (open_te e3 T)...
Qed.
