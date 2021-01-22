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

Require Export Fsub_Lemmas.


(* ********************************************************************** *)
(** * #<a name="subtyping"></a># Properties of subtyping *)

(* used for termination checking *)
Lemma cheat : forall A, A.
Proof.
Admitted.


(* ********************************************************************** *)
(** ** Weakening (2) *)

Lemma cv_strengthening : forall x U E G T C,
    cv (G ++ [(x, bind_typ U)] ++ E) T C ->
    cv (G ++ E) T C.
Proof with auto.
  intros x U E G T C HCv.
  remember (G ++ [(x, bind_typ U)] ++ E).
  induction HCv ; subst...
  apply cv_typ_var with (T := T)...
  binds_cases H...
Qed.

Lemma cv_weakening : forall E F G T C,
    cv (G ++ E) T C ->
    wf_env (G ++ F ++ E) ->
    cv (G ++ F ++ E) T C.
Proof with auto.
  intros E F G T C HCv Hwf2.
  remember (G ++ E).
  induction HCv ; subst...
  apply cv_typ_var with (T := T)...
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
Proof with auto using wf_cset_weakening.
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
Proof with simpl_env; auto using wf_typ_weakening, wf_pretyp_weakening, cv_weakening, subcapt_weakening, wf_cset_weakening.
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
    pick fresh Y and apply sub_arrow.
    apply cheat.
    rewrite <- concat_assoc.
    apply sub_weakening...
  - Case "sub_all".
    pick fresh Y and apply sub_all.
    apply cheat.
    rewrite <- concat_assoc.
    apply sub_weakening...
Qed.

(* ********************************************************************** *)
(** ** Reflexivity (1) *)

(*
  opening capture sets in types preserves well-formedness. *)
Lemma open_ct_wf_typ : forall E T C,
  wf_typ E T -> wf_typ E (open_ct T C).
Proof with auto.
  intros E T C H.
  closed_type.
Qed.


(* capture set substitution does not affect subtyping

  depends on opening in the context
    binds X (bind_sub U) E -> binds X (bind_sub (open_ct U C)) E
 *)
Lemma open_ct_sub : forall E S T C,
  wf_env E ->
  sub E S T -> sub E (open_ct S C) (open_ct T C).
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


Lemma subcapt_reflexivity : forall E C,
  wf_env E ->
  (* We need as a precondition that C is locally closed! *)
  wf_cset E C ->
  subcapt E C C.
Proof with auto.
  intros E C Ok Closed.
  destruct C...
  assert (t0 = {}N). { inversion Closed... }
  subst.
  apply subcapt_set...
  unfold AtomSet.F.For_all. intros.
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

Lemma cv_exists : forall E T,
  wf_env E ->
  wf_typ E T ->
  exists C, cv E T C.
Proof with eauto.
  intros E.
  induction E; intros T; induction T; intros; try inversion H0; try inversion H; subst...
  - inversion H3...
  - simpl_env in *.
    binds_cases H3...
    + assert (wf_typ E a0) by 
        (apply wf_typ_var with (U := U); eauto).
      specialize (IHE a0 H6 H2) as [C' H'].
      inversion H'; subst...
      exists C'.
      eapply cv_typ_var with (T := T0)...
      rewrite_env (empty ++ [(X0, bind_sub T)] ++ E).
      apply cv_weakening...
    + specialize (IHE T H6 H7) as [C' H'].
      exists C'.
      apply cv_typ_var with (T := T)...
      rewrite_env (empty ++ [(a0, bind_sub T)] ++ E).
      apply cv_weakening...
  - simpl_env in *.
    binds_cases H3...
    assert (wf_typ E a0) by (apply wf_typ_var with (U := U); eauto).
    specialize (IHE a0 H6 H2) as [C' H'].
    inversion H'; subst...
    exists C'.
    apply cv_typ_var with (T := T0)...
    rewrite_env (empty ++ [(x, bind_typ T)] ++ E).
    apply cv_weakening...
Qed.

(* Probably not used? Useful in sub implies subcapt *)
Lemma cv_unique : forall T E C1 C2,
  wf_env E ->
  cv E T C1 ->
  cv E T C2 ->
  C1 = C2.
Proof with eauto.
  intros T E C1 C2 Hwf Hcv1 Hcv2.
Admitted.

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

Lemma sub_reflexivity : forall E T,
  wf_env E ->
  wf_typ E T ->
  sub E T T
with sub_pre_reflexivity : forall E T,
  wf_env E ->
  wf_pretyp E T ->
  sub_pre E T T.
Proof with auto using subcapt_reflexivity.
------
  intros E T Ok Wf.
  induction Wf.
  (* eauto and econstructor is still broken... hence we need to proof this manually *)
  - apply sub_refl_tvar...
    eapply wf_typ_var with (U := U)...
  - apply sub_capt...
------
  intros E T Ok Wf.
  induction Wf.
  - apply sub_top...
  - apply sub_arrow with (L := L `union` dom E)...
  - apply sub_all with (L := L `union` dom E)...
Qed.

(* Subtyping implies subcapturing *)
Lemma sub_implies_subcapt : forall E S T C D,
  sub E S T ->
  cv E S C ->
  cv E T D ->
  subcapt E C D.
Proof.
  intros E S T C D Hsub HcvC HcvD.
  induction Hsub...
  (** needs cv_unique *)
  admit.
Admitted.

(* ********************************************************************** *)
(** ** Narrowing and transitivity (3) *)

Lemma cv_narrowing : forall S G Z Q E P C1 C2,
  sub E P Q ->
  cv (G ++ [(Z, bind_sub Q)] ++ E) S C2 ->
  cv (G ++ [(Z, bind_sub P)] ++ E) S C1.
Proof with auto.
Admitted.

Lemma cv_narrowing_fix : forall S G Z Q E P C1 C2,
  sub E P Q ->
  cv (G ++ [(Z, bind_sub Q)] ++ E) S C2 ->
  cv (G ++ [(Z, bind_sub P)] ++ E) S C1 ->
  subcapt E C1 C2.
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
      apply cv_exists...
      (** two wellformedness conditions.  Probably need to strengthen
          conditions. *)
      admit.
      admit.
    }
    inversion H1 as [C3 H2].
    (* Needs subcapt-transitivity -- C1 <: C3 <: C2 *)
    admit.
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
  intros S G x Q E P C HSub Ok HCv.
  remember (G ++ [(x, bind_typ Q)] ++ E). generalize dependent G.
  induction HCv ; intros ; subst...
  destruct (X == x) ; subst.
  - (* this can't happen, x is a variable not a type. *)
    binds_get H.
  - apply cv_typ_var with (T := T)...
    (* X <>x, bindings unchanged. *)
    binds_cases H.
    + apply binds_tail. apply binds_tail... trivial.
    + apply binds_head...
Qed.

(** Again, probably not true, due to cv looking into type bindings. *)
Lemma captures_narrowing : forall F Z P Q E xs x,
  wf_env (F ++ [(Z, bind_sub P)] ++ E) ->
  sub E P Q ->
  captures (F ++ [(Z, bind_sub Q)] ++ E) xs x ->
  captures (F ++ [(Z, bind_sub P)] ++ E) xs x.
Proof with eauto using wf_cset_narrowing, wf_env_narrowing.
  intros F Z P Q E xs x Ok Sub H.
  remember (F ++ [(Z, bind_sub Q)] ++ E). generalize dependent F.
  induction H; intros; subst.
  - apply captures_in...
  - assert (x <> Z). {
      unfold not. intros.
      binds_cases H.
      * subst. unfold dom in Fr0. fsetdec.
      * subst. admit.
    }
    apply captures_var with (T := T) (ys := ys)...
    unfold AtomSet.F.For_all in *. intros.
    admit.
    (*apply H2...*)
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
          eapply captures_var.
          apply binds_tail.
          apply binds_head...
          trivial.
          (* then use sub_implies_subcapt *)
          destruct (cv_exists E P) as [C CV]...
          { destruct C.
            ** (* universal *)
                exfalso. admit.
            ** admit.
          }
          (* apply H3. *)
          unfold AtomSet.F.For_all in *. intros.
          apply H2...
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
  subcapt (F ++ [(Z, bind_sub Q)] ++ E) C1 C2 ->
  subcapt (F ++ [(Z, bind_sub P)] ++ E) C1 C2.
Proof with eauto using wf_cset_narrowing, wf_env_narrowing.
  intros F E Z P Q C1 C2 SubPQ SubCap.
  remember (F ++ [(Z, bind_sub Q)] ++ E). generalize dependent F.
  induction SubCap ; intros ; subst...
  (** Alex: eauto seems to not solve some goals it solved previously? *)
  - admit.
  - apply subcapt_set...
    + admit.
    + admit.
    + unfold AtomSet.F.For_all.
      intros.
      unfold AtomSet.F.For_all in H1.
      specialize (H1 x H2).
      (* requires captures regularity *)
      assert (wf_env (F ++ [(Z, bind_sub Q)] ++ E)). { admit. }
      admit.
Admitted.


Lemma subcapt_narrowing_typ : forall F E x P Q C1 C2,
  sub E P Q ->
  ok (F ++ [(x, bind_typ P)] ++ E) ->
  subcapt (F ++ [(x, bind_typ Q)] ++ E) C1 C2 ->
  subcapt (F ++ [(x, bind_typ P)] ++ E) C1 C2.
Proof with eauto using wf_cset_narrowing_typ.
  intros F E x P Q C1 C2 PsubQ Ok C1subC2.
  remember (F ++ [(x, bind_typ Q)] ++ E). generalize dependent F.
  induction C1subC2 ; intros ; subst...
  - econstructor...
    unfold AtomSet.F.For_all.
    intros.
    unfold AtomSet.F.For_all in H1.
    specialize (H1 x0 H2).
    eapply captures_narrowing_typ with (Q := Q)...
    admit.
Admitted.

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
  - apply sub_capt...
------
  intros Q F E Z P S T TransQ SsubT PsubQ.
  remember (F ++ [(Z, bind_sub Q)] ++ E). generalize dependent F.
  induction SsubT; intros F EQ; subst.
  - Case "sub_top".
    apply sub_top...
  - Case "sub_arrow".
    pick fresh Y and apply sub_arrow...
    rewrite <- concat_assoc.
    eapply sub_narrowing_aux...
  - Case "sub_all".
    pick fresh Y and apply sub_all...
    rewrite <- concat_assoc.
    eapply sub_narrowing_aux...
Qed.

Lemma empty_cset_implies_no_captures : forall E xs,
  wf_cset E (cset_set xs {}N) ->
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

  (* by fsetdec and fnsetdec -- however it crashes at the moment... *)
Admitted.

Lemma subtyping_preserves_empty_cv : forall E S T,
  sub E S T ->
  cv E T {}C ->
  cv E S {}C.
Proof with eauto.
  intros.
  induction H...
  (* - assert (C1 = {}C). {
      assert (C2 = {}C). { inversion H0. destruct (empty_cset_union _ _ H6); subst... }
      subst.
      apply (empty_subcapt_implies_empty_cset E C1)...
    }
    assert (cv E T1 {}C). {
      apply IHsub.
      inversion H0.
      destruct (empty_cset_union _ _ H7); subst...
      replace (cset_union {}C {}C) with {}C...
    }
    replace {}C with (cset_union {}C {}C). subst. econstructor...
    eauto.
    unfold cset_union. simpl.
    rewrite elim_empty_nat_set.
    replace ({} `union` {}) with {}...
    fsetdec.
  - admit. *)
Admitted.

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
    eapply subcapt_narrowing_typ...
    apply cheat.
------
  intros Q F E x P S T TransQ SsubT PsubQ.
  remember (F ++ [(x, bind_typ Q)] ++ E). generalize dependent F.
  induction SsubT; intros F EQ; subst.
  - eapply sub_top...
  - pick fresh Y and apply sub_arrow...
    rewrite <- concat_assoc.
    eapply sub_narrowing_typ_aux...
  - pick fresh Y and apply sub_all...
    rewrite <- concat_assoc.
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
    assert (X `notin` L0)...
    specialize (H2 X H5).
    (* by regularity *)
    assert (wf_typ ([(X, bind_typ T1)] ++ E) (open_ct S2 X))...
    rewrite_env (empty ++ [(X, bind_typ S1)] ++ E).
    eapply wf_typ_narrowing_typ with (C1 := T1).
    trivial.
    assert (wf_env (empty ++ [(X, bind_typ T1)] ++ E)). { auto. }
    pose proof (ok_from_wf_env _ H7).
    inversion H8.
    simpl_env.
    econstructor...
  + pick fresh Y and apply sub_arrow.
    SCase "bounds".
      apply cheat.
    SCase "bodies".
      lapply (H0 Y); [ intros K | auto ].
      assert (Y `notin` L0) by notin_solve.
      assert (Y `notin` L1) by notin_solve.
      specialize (H2 Y H3).
      specialize (H8 Y H4).
      assert (sub ([(Y, bind_typ T0)] ++ E) (open_ct S2 Y) (open_ct T2 Y)). {
        rewrite_env (empty ++ [(Y, bind_typ T0)] ++ E).
        eapply sub_narrowing_typ_aux with (Q := T1)...
        apply cheat.
      }
      assert (type (open_ct T2 Y))...
      (* apply (sub_transitivity _ _ _ _ H7 H5 H8). *)
      apply sub_transitivity with (Q := (open_ct T2 Y))...

      (* rewrite_env (empty ++ [(Y, bind_typ T0)] ++ E).
      eapply sub_narrowing_typ_aux with (Q := T1). *)
      (* unfold transitivity_on.
      auto using (sub_transitivity T1). *)
  (* type_all. *)
  - apply cheat.
  (* - inductionThenInversion2 SsubQ QsubT.
  + apply sub_top...
    pick fresh X and apply wf_typ_all...
    assert (X `notin` L0) by notin_solve.
    specialize (H2 X H5)...
    assert (wf_typ ([(X, bind_sub T1)] ++ E) (open_tt S2 X))...
    (* wf_typ S2 *)
    apply cheat.
  + pick fresh Y and apply sub_all.
    SCase "bounds".
      apply sub_transitivity with (Q := T1)...
    SCase "bodies".
      lapply (H0 Y); [ intros K | auto ].
      apply sub_transitivity with (Q := (open_tt T2 Y))...
      rewrite_env (empty ++ [(Y, bind_sub T0)] ++ E).
      apply (sub_narrowing_aux T1)...
      apply cheat.
      (* unfold transitivity_on.
      auto using (sub_transitivity T1). *) *)
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

Lemma re_cv_through_subst_tt : forall X P Q T E G C,
  wf_env (G ++ [(X, bind_sub Q)] ++ E) ->
  wf_typ (G ++ [(X, bind_sub Q)] ++ E) T ->
  cv (G ++ [(X, bind_sub Q)] ++ E) T C ->
  sub E P Q ->
  exists D : captureset,
    cv (map (subst_tb X P) G ++ E) (subst_tt X P T) D.
Proof.
  intros until 0. intros Hwf_env Hwf_typ H Hsub.
  generalize dependent C.
  induction T; intro C; intro; subst; eauto.
  (* - Case "Top".
    exists c. apply cv_top.
  - Case "bvar".
    admit.
  - Case "fvar".
    admit.
  - exists c. apply cv_typ_arrow.
  - exists c. apply cv_typ_all.   *)
Admitted.

Lemma correlate_union_cv : forall E C1 C2 D1 D2,
  subcapt E C1 C2 ->
  subcapt E D1 D2 ->
  subcapt E (cset_union C1 D1) (cset_union C2 D2).
Proof.
  (* Somehow by transitivity. *)
Admitted.

Lemma cv_through_subst_tt : forall X P Q T E G C D,
  wf_env (G ++ [(X, bind_sub Q)] ++ E) ->
  wf_typ (G ++ [(X, bind_sub Q)] ++ E) T ->
  cv (G ++ [(X, bind_sub Q)] ++ E) T C ->
  cv (map (subst_tb X P) G ++ E) (subst_tt X P T) D ->
  sub E P Q ->
  subcapt (map (subst_tb X P) G ++ E) D C.
Proof.
  (* intros *. intros Hwf_env Hwf_typ Hcv_wide Hcv_narrow Hsub.
  generalize dependent C.
  generalize dependent D.
  induction T; intros D Hcv_narrow C Hcv_wide.
  - inversion Hcv_wide; subst.
    inversion Hcv_narrow; subst.
    admit.
    (* apply subcapt_split.
    apply cset_subset_reflexivity. *)
  - Case "bvar".
    (* What's going on here, why do I get a bvar? Doesn't this mean that T would be simply ill-formed? *)
    admit.
  - Case "fvar".
    admit.
  - inversion Hcv_narrow; subst.
    inversion Hcv_wide; subst.
    admit.
    (* apply subcapt_split. *)
    (* apply cset_subset_reflexivity. *)
  - inversion Hcv_narrow; subst.
    inversion Hcv_wide; subst.
    admit.
    (* apply subcapt_split.
    apply cset_subset_reflexivity. *)
  (* - inversion Hwf_typ; subst.
    inversion Hcv_narrow; subst.
    inversion Hcv_wide; subst.
    specialize (IHT H2 C2 H5 C0 H6).
    apply correlate_union_cv; trivial.
    apply subcapt_reflexivity.
    apply wf_env_subst_tb with (Q := Q); auto. *) *)
Admitted.

(* Type substitution preserves subcapturing *)

Lemma captures_through_subst_tt : forall Q E F Z P C x,
  wf_typ E P ->
  captures (F ++ [(Z, bind_sub Q)] ++ E) C x ->
  captures (map (subst_tb Z P) F ++ E) C x.
Proof with eauto using wf_env_subst_tb, wf_cset_subst_tb.
  intros Q E F Z P C x Tp H.
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
  subst.
  constructor...
  unfold AtomSet.F.For_all in *. intros.
  specialize (H1 x H2)...
Qed.


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
    lapply (H X); [intros K | auto].
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
    lapply (H X); [intros K | auto].
    rewrite <- concat_assoc.
    apply (H0 X)...
Admitted.


(************************************************************************ *)
(** ** Narrowing for typing (7) *)

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
    pick fresh y and apply typing_abs.
    rewrite <- concat_assoc.
    apply H0...
  - Case "typing_app".
    admit.
  - Case "typing_tabs".
    pick fresh Y and apply typing_tabs.
    rewrite <- concat_assoc.
    apply H0...
Admitted.

(************************************************************************ *)
(** ** Substitution preserves typing (8) *)

Lemma self_subst_idempotent : forall F E x T D,
  wf_env (F ++ [(x, bind_typ T)] ++ E) ->
  subst_ct x D T = T.
Proof.
  (* Plan: *)
  (*   - fv(T) subset E *)
  (*   - therefore x not in fv(t) *)
  (*   - therefore subst idempotent *)
  admit.
Admitted.

Lemma wf_env_subst_cb : forall Q C x E F,
  wf_env (F ++ [(x, bind_typ Q)] ++ E) ->
  wf_cset E C ->
  wf_env (map (subst_cb x C) F ++ E).
Proof
  (* with eauto 6 using wf_typ_subst_tb *)
  .
  admit.
  (* induction F; intros Wf_env WP; simpl_env; *)
  (*   inversion Wf_env; simpl_env in *; simpl subst_tb... *)
Admitted.

(* Alex: on a second look, this is just a mangled version of cv regularity *)
(* cv regularity is fine as well, potentially also necessary when doing recursion on cv *)
Lemma wf_cset_from_cv : forall E T C,
  wf_env E ->
  cv E T C ->
  wf_cset E C.
Proof.
Admitted.

Hint Extern 1 (wf_cset ?E ?C) =>
  match goal with
  | H1: cv ?E _ ?C, H2 : wf_env ?E |- _ => apply (wf_cset_from_cv _ _ _ H2 H1)
  end : core.

Lemma wf_env_strengthening : forall F E,
    wf_env (F ++ E) ->
    wf_env E.
Proof.
  (* induction on F? *)
  admit.
Admitted.

Lemma cset_subst_self : forall C x,
    subst_cset x C (cset_fvar x) = C.
Proof.
  trivial.
  admit.
Admitted.

Lemma sub_through_subst_ct : forall E F x U C S T,
  sub (F ++ [(x, bind_typ U)] ++ E) S T ->
  cv E U C ->
  sub (map (subst_cb x C) F ++ E) (subst_ct x C S) (subst_ct x C T).
Proof.
  trivial.
  admit.
Admitted.

Lemma subst_ct_open_ct_var : forall (x y:atom) c t,
  y <> x ->
  (* doesn't seem necessary by analogy to subst_ct_open_tt_var *)
  (* type t -> *)
  capt c ->
  (open_ct (subst_ct x c t) (cset_fvar y)) = (subst_ct x c (open_ct t (cset_fvar y))).
Proof with auto*.
  admit.
Admitted.

Lemma subst_ct_open_ct : forall x c1 t c2,
  capt c1 ->
  subst_ct x c1 (open_ct t c2) = (open_ct (subst_ct x c1 t) (subst_cset x c1 c2)).
Proof with auto*.
  intros.
  admit.
Admitted.

Lemma cv_through_subst_c : forall F x U E C T D,
    cv (F ++ [(x, bind_typ U)] ++ E) T C ->
    cv E U D ->
    cv (map (subst_cb x D) F ++ E) (subst_ct x D T) (subst_cset x D C).
Proof.
  admit.
Admitted.

Lemma subcapt_through_subst_cset : forall F x U E C1 C2 D,
    subcapt (F ++ [(x, bind_typ U)] ++ E) C1 C2 ->
    cv E U D ->
    subcapt (map (subst_cb x D) F ++ E) (subst_cset x D C1) (subst_cset x D C2).
Proof.
  admit.
Admitted.

Lemma subst_ct_open_tt : forall x c t1 t2,
  capt c ->
  subst_ct x c (open_tt t1 t2) = (open_tt (subst_ct x c t1) (subst_ct x c t2)).
Proof with auto*.
  intros.
  admit.
Admitted.

Lemma cset_union_empty_idempotent : forall C,
    cset_union C {}C = C.
Proof.
  admit.
Admitted.

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
  induction Htyp.
  all: intros C0 Hcv.
  all: try solve [ inversion Hv ].
  - inversion Hcv...
    apply subcapt_reflexivity...
  - inversion Hcv.
    apply subcapt_reflexivity...
  - epose proof (cv_exists E S P1 _ ) as [D HcvS].
    pose proof (sub_implies_subcapt _ _ _ _ _ H HcvS Hcv).
    epose proof (IHHtyp Hv _ _ _ D HcvS)...
    apply subcapt_transitivity with (C2 := D)...
    Unshelve.
    all: auto.
Qed.

Lemma typing_through_subst_ee : forall U E F x T C e u,
  typing (F ++ [(x, bind_typ U)] ++ E) e T ->
  typing E u U ->
  cv E U C ->
  typing (map (subst_cb x C) F ++ E) (subst_ee x u C e) (subst_ct x C T).

(** We provide detailed comments for the following proof, mainly to
    point out several useful tactics and proof techniques.

    Starting a proof with "Proof with <some tactic>" allows us to
    specify a default tactic that should be used to solve goals.  To
    invoke this default tactic at the end of a proof step, we signal
    the end of the step with three periods instead of a single one,
    e.g., "apply typing_weakening...". *)

Proof with simpl_env;
           eauto 4.

  (** The proof proceeds by induction on the given typing derivation
      for e.  We use the remember tactic, along with generalize
      dependent, to ensure that the goal is properly strengthened
      before we use induction. *)

  intros *.
  intros HtypT HcvU HtypU.
  assert (wf_env E) as HwfE. {
    apply wf_env_strengthening with (F := (F ++ [(x, bind_typ U)]))...
  }
  (* assert (wf_env (F ++ [(x, bind_typ U)] ++ E)) as HwfFxE by auto. *)
  (* assert (wf_env (map (subst_cb x C) F ++ E)) as HwfsubstFE. { *)
  (*   (* rewrite_env (map (subst_cb x C) F ++ E). *) *)
  (*   eapply wf_env_subst_cb... *)
  (* } *)
  remember (F ++ [(x, bind_typ U)] ++ E).
  generalize dependent F.
  induction HtypT; intros F EQ; subst; simpl subst_ee...
  (* induction HtypT; intros F EQ HwfsubstFE; subst; simpl subst_ee... *)

  (** The typing_var case involves a case analysis on whether the
      variable is the same as the one being substituted for. *)

  - Case "typing_var_tvar".
    destruct (x0 == x); subst.
    + binds_get H0.
      inversion H2; subst.
      rewrite_env (empty ++ map (subst_cb x C) F ++ E).
      apply typing_weakening...
      eapply wf_env_subst_cb...
    + simpl.
      binds_cases H0...
      * rewrite_env (empty ++ map (subst_cb x C) F ++ E).
        apply typing_weakening...
        eapply wf_env_subst_cb...
      * apply typing_var_tvar...
        eapply wf_env_subst_cb...
        apply binds_head.
        replace (bind_typ X) with (subst_cb x C (bind_typ X))...
  - Case "typing_var".
    destruct (x0 == x); subst.
    + SCase "x0 = x".
      binds_get H0.
      inversion H2; subst.
      rewrite_env (empty ++ map (subst_cb x C) F ++ E).
      apply typing_weakening...
      * inversion HtypU; subst.
        simpl.
        rewrite cset_subst_self.
        pose proof (self_subst_idempotent _ _ _ _ C H) as Heq.
        injection Heq.
        intros HeqP _.
        rewrite HeqP.
        trivial.
      * eapply wf_env_subst_cb...
    + SCase "x0 <> x".
      binds_cases H0.
      * assert ((typ_capt x0 P) = (subst_ct x C (typ_capt x0 P))) as Heq. {
          apply subst_ct_fresh.
          (* somehow by larger env being wf *)
          admit.
        }
        rewrite <- Heq.
        rewrite_env (empty ++ map (subst_cb x C) F ++ E).
        apply typing_weakening...
        eapply wf_env_subst_cb...
      * simpl.
        rewrite <- (subst_cset_fresh x).
        2: notin_solve.
        eapply typing_var.
        eapply wf_env_subst_cb...
        (* heavy environment wrangling ahead... *)
        assert (binds x0 (bind_typ (subst_ct x C (typ_capt C0 P))) (map (subst_cb x C) F)). {
          (* unsimpl (subst_cb x C (bind_typ (typ_capt C0 P))). *)
          assert
            ((subst_cb x C (bind_typ (typ_capt C0 P))) = (bind_typ (subst_ct x C (typ_capt C0 P))))
            as H_y_u_no_unsimpl_coq by (simpl; reflexivity).
          rewrite <- H_y_u_no_unsimpl_coq.
          apply binds_map.
          trivial.
        }
        rewrite <- concat_nil.
        rewrite -> concat_assoc.
        apply binds_weaken.
        ** rewrite -> concat_nil...
        ** rewrite -> concat_nil...
           assert (wf_env (map (subst_cb x C) F ++ E))... {
             eapply wf_env_subst_cb...
           }

  (** Informally, the typing_abs case is a straightforward application
      of the induction hypothesis, which is called H0 here. *)

  - Case "typing_abs".

    (** We use the "pick fresh and apply" tactic to apply the rule
        typing_abs without having to calculate the appropriate finite
        set of atoms. *)

    simpl subst_ct.
    destruct (AtomSet.F.mem x (cset_fvars (free_for_cv e1))) eqn:EqMem.
    + SCase "x in fv e1".
      eenough (typing (map (subst_cb x C) F ++ E)
                      _
                      (typ_capt
                         (free_for_cv (subst_ee x u C e1))
                         (typ_arrow (subst_ct x C V) (subst_ct x C T1)))).
      * Set Nested Proofs Allowed.
        Local Lemma foo : forall x C e,
            AtomSet.F.In x (cset_fvars (free_for_cv e)) ->
            subst_cset x C (free_for_cv e) = cset_union C (cset_remove_fvar x (free_for_cv e)).
        Proof.
        Admitted.
        rewrite foo.
        Local Lemma bar : forall x C e u,
            AtomSet.F.In x (cset_fvars (free_for_cv e)) ->
            free_for_cv (subst_ee x u C e) = cset_union (free_for_cv u) (cset_remove_fvar x (free_for_cv e)).
        Proof.
        Admitted.
        rewrite bar in H1.
        Local Lemma baz : forall E C1 C2 D,
            wf_cset E D ->
            subcapt E C1 C2 ->
            subcapt E (cset_union C1 D) (cset_union C2 D).
        Proof.
        Admitted.
        eapply typing_sub.
        2: {
          eapply sub_capt.
          apply baz with (C1 := (free_for_cv u)).
          - (* wf_cset *) admit.
          - rewrite_env (empty ++ (map (subst_cb x C) F ++ E)).
            eapply value_therefore_fv_subcapt_cv.
            + admit.
            + eapply typing_weakening...
              eapply wf_env_subst_cb...
              (* how did I lose the environment ??? *)
              admit.
            + eapply cv_weakening...
              eapply wf_env_subst_cb...
              (* how did I lose the environment ??? *)
              admit.
          - apply sub_pre_reflexivity.
            + admit.
            + admit.
        }
        apply H1.
        1,2: admit.
      * pick fresh y and apply typing_abs.
        rewrite subst_ee_open_ee_var...
        rewrite subst_ct_open_ct_var...
        rewrite_env (map (subst_cb x C) ([(y, bind_typ V)] ++ F) ++ E).
        apply H0...
      Unshelve.
      all: auto.
    + SCase "x not in fv e1".
      assert ((subst_cset x C (free_for_cv e1)) = (free_for_cv (subst_ee x u C e1))) as Heq. {
        (* true b/c of subcase assumption, though probably will need to be shown in multiple steps. *)
        admit.
      }
      rewrite Heq.
      pick fresh y and apply typing_abs.
      rewrite subst_ee_open_ee_var...
      rewrite subst_ct_open_ct_var...
      rewrite_env (map (subst_cb x C) ([(y, (bind_typ V))] ++ F) ++ E).
      apply H0...
  - Case "typing_app".
    rewrite subst_ct_open_ct...
    eapply typing_app.
    + simpl subst_ct in IHHtypT1.
      apply IHHtypT1...
    + apply IHHtypT2...
    + eapply sub_through_subst_ct...
    + eapply cv_through_subst_c...
    + eapply cv_through_subst_c...
    + eapply subcapt_through_subst_cset...
    + eapply subcapt_through_subst_cset...
  - Case "typing_tabs".
    simpl subst_ct.
    destruct (AtomSet.F.mem x (cset_fvars (free_for_cv e1))) eqn:EqMem.
    + SCase "x in fv e1".
      admit.
    + SCase "x not in fv e1".
      assert ((subst_cset x C (free_for_cv e1)) = (free_for_cv (subst_ee x u C e1))) as Heq. {
        (* see above. *)
        admit.
      }
      rewrite Heq.
      pick fresh y and apply typing_tabs.
      rewrite subst_ee_open_te_var...
      rewrite subst_ct_open_tt_var...
      rewrite_env (map (subst_cb x C) ([(y, (bind_sub V))] ++ F) ++ E).
      apply H0...
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

(************************************************************************ *)
(** ** Type substitution preserves typing (11) *)

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
  - Case "typing_var".
    apply typing_var...
      rewrite (map_subst_tb_id E Z P);
        [ | auto | eapply fresh_mid_tail; eauto ].
      binds_cases H0...
  - Case "typing_abs".
    admit.
    (* pick fresh y and apply typing_abs. *)
    (* rewrite subst_te_open_ee_var... *)
    (* rewrite_env (map (subst_tb Z P) ([(y, bind_typ V)] ++ F) ++ E). *)
    (* apply H0... *)
  Case "typing_tabs".
    pick fresh Y and apply typing_tabs.
    rewrite subst_te_open_te_var...
    rewrite subst_tt_open_tt_var...
    rewrite_env (map (subst_tb Z P) ([(Y, bind_sub V)] ++ F) ++ E).
    apply H0...
  Case "typing_tapp".
    rewrite subst_tt_open_tt...
Qed.


(* ********************************************************************** *)
(** * #<a name="preservation"></a># Preservation *)


(* ********************************************************************** *)
(** ** Inversion of typing (13) *)

Lemma typing_inv_abs : forall E S1 e1 T,
  typing E (exp_abs S1 e1) T ->
  forall U1 U2, sub E T (typ_arrow U1 U2) ->
     sub E U1 S1
  /\ exists S2, exists L, forall x, x `notin` L ->
     typing ([(x, bind_typ S1)] ++ E) (open_ee e1 x) S2 /\ sub E S2 U2.
Proof with auto.
  intros E S1 e1 T Typ.
  remember (exp_abs S1 e1).
  generalize dependent e1.
  generalize dependent S1.
  induction Typ; intros S1 b1 EQ U1 U2 Sub; inversion EQ; subst.
  Case "typing_abs".
    inversion Sub; subst.
    split...
    exists T1. exists L...
  Case "typing_sub".
    auto using (sub_transitivity T).
Qed.

Lemma typing_inv_tabs : forall E S1 e1 T,
  typing E (exp_tabs S1 e1) T ->
  forall U1 U2, sub E T (typ_all U1 U2) ->
     sub E U1 S1
  /\ exists S2, exists L, forall X, X `notin` L ->
     typing ([(X, bind_sub U1)] ++ E) (open_te e1 X) (open_tt S2 X)
     /\ sub ([(X, bind_sub U1)] ++ E) (open_tt S2 X) (open_tt U2 X).
Proof with simpl_env; auto.
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



(* ********************************************************************** *)
(** ** Preservation (20) *)

Lemma preservation : forall E e e' T,
  typing E e T ->
  red e e' ->
  typing E e' T.
Proof with simpl_env; eauto.
  intros E e e' T Typ. generalize dependent e'.
  induction Typ; intros e' Red; try solve [ inversion Red; subst; eauto ].
  Case "typing_app".
    inversion Red; subst...
    SCase "red_abs".
      destruct (typing_inv_abs _ _ _ _ Typ1 T1 T2) as [P1 [S2 [L P2]]].
        apply sub_reflexivity...
      pick fresh x.
      destruct (P2 x) as [? ?]...
      rewrite (subst_ee_intro x)...
      rewrite_env (empty ++ E).
      apply (typing_through_subst_ee T).
        apply (typing_sub S2)...
          rewrite_env (empty ++ [(x, bind_typ T)] ++ E).
          apply sub_weakening...
        eauto.
  Case "typing_tapp".
    inversion Red; subst...
    SCase "red_tabs".
      destruct (typing_inv_tabs _ _ _ _ Typ T1 T2) as [P1 [S2 [L P2]]].
        apply sub_reflexivity...
      pick fresh X.
      destruct (P2 X) as [? ?]...
      rewrite (subst_te_intro X)...
      rewrite (subst_tt_intro X)...
      rewrite_env (map (subst_tb X T) empty ++ E).
      apply (typing_through_subst_te T1)...
Qed.


(* ********************************************************************** *)
(** * #<a name="progress"></a># Progress *)


(* ********************************************************************** *)
(** ** Canonical forms (14) *)

Lemma canonical_form_abs : forall e U1 U2,
  value e ->
  typing empty e (typ_arrow U1 U2) ->
  exists V, exists e1, e = exp_abs V e1.
Proof.
  intros e U1 U2 Val Typ.
  remember empty.
  remember (typ_arrow U1 U2).
  revert U1 U2 Heqt Heql.
  induction Typ; intros U1 U2 EQT EQE; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
  Case "typing_sub".
    inversion H; subst; eauto.
    inversion H0.
Qed.

Lemma canonical_form_tabs : forall e U1 U2,
  value e ->
  typing empty e (typ_all U1 U2) ->
  exists V, exists e1, e = exp_tabs V e1.
Proof.
  intros e U1 U2 Val Typ.
  remember empty.
  remember (typ_all U1 U2).
  revert U1 U2 Heqt Heql.
  induction Typ; intros U1 U2 EQT EQE; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
  Case "typing_sub".
    inversion H; subst; eauto.
    inversion H0.
Qed.



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
    right.
    destruct IHTyp1 as [Val1 | [e1' Rede1']]...
    SCase "Val1".
      destruct IHTyp2 as [Val2 | [e2' Rede2']]...
      SSCase "Val2".
        destruct (canonical_form_abs _ _ _ Val1 Typ1) as [S [e3 EQ]].
        subst.
        exists (open_ee e3 e2)...
  Case "typing_tapp".
    right.
    destruct IHTyp as [Val1 | [e1' Rede1']]...
    SCase "Val1".
      destruct (canonical_form_tabs _ _ _ Val1 Typ) as [S [e3 EQ]].
      subst.
      exists (open_te e3 T)...
Qed.
