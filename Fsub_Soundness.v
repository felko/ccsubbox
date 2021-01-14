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
  sub (G ++ F ++ E) S T.
Proof with simpl_env; auto using wf_typ_weakening, cv_weakening, subcapt_weakening.
  intros E F G S T Sub Ok.
  remember (G ++ E).
  generalize dependent G.
  induction Sub; intros G Ok EQ; subst...
  - Case "sub_trans_tvar".
    apply (sub_trans_tvar U)...
  - Case "sub_arrow".
    pick fresh Y and apply sub_arrow...
    rewrite <- concat_assoc.
    apply H0...
  - Case "sub_all".
    pick fresh Y and apply sub_all...
    rewrite <- concat_assoc.
    apply H0...
  - admit.
Admitted.

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

(* Probably not used? *)
Lemma cv_unique : forall T E C1 C2,
  cv E T C1 ->
  cv E T C2 ->
  C1 = C2.
Proof.
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
  empty_cset_bvars C3 -> 
  subcapt E C1 C2 ->
  subcapt E C2 C3 ->
  subcapt E C1 C3.
Proof with auto.
  intros E C1 C2 C3 Ok Closed H12 H23.
  remember C1.
  remember C2.
  inversion H12.
  - Case "subcapt_universal".
    destruct C3... exfalso. subst. inversion H23.
  - Case "subcapt_set".
    subst.
    remember C3.
    destruct C3. subst...
    assert (t0 = {}N) as cl. { subst. unfold empty_cset_bvars in Closed. csetdec. }
    subst.
    inversion H23; subst.
    eapply subcapt_set...    
    unfold AtomSet.F.For_all. intros.     
    apply captures_transitivity with (ys := ys)...
Qed.

Lemma sub_reflexivity : forall E T,
  wf_env E ->
  wf_typ E T ->
  sub E T T.
Proof with auto using subcapt_reflexivity.
  intros E T Ok Wf.
  induction Wf...
  (* eauto and econstructor is still broken... hence we need to proof this manually *)
  - apply sub_refl_tvar... 
    eapply wf_typ_var.
    apply H.
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
Admitted.

(* ********************************************************************** *)
(** ** Narrowing and transitivity (3) *)

Lemma cv_narrowing : forall S G Z Q E P C1 C2,
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
  induction HSub; intros; subst...
  - (* C1 = {}, trivial *)
    admit.
  - (* C1 = C2, trivial. *)
    admit.
  - 
    (* Given a valid capture set derivation, we can construct another
        one when we weaken the environment.
        
        Probably should be a lemma.*)  
    assert (exists C3, cv (G ++ [(Z, bind_sub U)] ++ E) S C3). {
      admit.
    }
    inversion H0 as [C3 H1].
    (* Needs subcapt-transitivity -- C1 <: C3 <: C2 *)
    admit.
  - (*by definition. *)  
    admit.
  - (*by defininition. *)
    admit.
  - (* inductively use T1 <: T2 *)
    admit.
  - 
    (** Now we need show that there is a C3 such that
       cv (G ++ [(Z, bind_sub T2)] ++ E) S C3 *)
    assert (exists C3, cv (G ++ [(Z, bind_sub T2)] ++ E) S C3). {
      admit.
    }
    inversion H0 as [C3 H1].
    (* inductively, use subtyping judgement. *) 
    specialize (IHHSub G C3 H1 C1 HCv1).
    (* now we need to show that C3 <: C2 and apply subcapt_transitivity,
      as cv (type_capt C T2) = C \cup cv T2 *)
    admit.
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
  wf_env (F ++ [(X, bind_typ P)] ++ E) ->
  sub E P Q ->
  captures (F ++ [(X, bind_typ Q)] ++ E) xs x ->
  captures (F ++ [(X, bind_typ P)] ++ E) xs x.
Proof with eauto using wf_cset_narrowing_typ, wf_env_narrowing_typ, cv_narrowing_typ.
  intros F X P Q E xs x Ok Sub H.
  remember (F ++ [(X, bind_typ Q)] ++ E). generalize dependent F.
  induction H; intros; subst.
  - apply captures_in...
  - assert (cv (F ++ [(X, bind_typ P)] ++ E) T (cset_set ys {}N))...
    eapply captures_var with (T := T).
    { destruct (x == X).
      + (* x == X *)
        binds_cases H.
        * apply binds_tail.
          apply binds_tail...
          trivial.
        * inversion H4; subst.
          apply binds_tail.
          (* ohoh, and now? *)
          admit.
          trivial.
        * apply binds_head...
      + (* x <> X *)
        binds_cases H.
        * apply binds_tail.
          apply binds_tail...
          trivial.
        * apply binds_head...
    }
    apply H3.
    unfold AtomSet.F.For_all in *. intros.
    apply H2...
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
  wf_env (F ++ [(x, bind_typ P)] ++ E) ->
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
    eapply captures_narrowing_typ...
Qed.

Definition transitivity_on Q := forall E S T,
  sub E S Q -> sub E Q T -> sub E S T.

Lemma sub_narrowing_aux : forall Q F E Z P S T,
  transitivity_on Q ->
  sub (F ++ [(Z, bind_sub Q)] ++ E) S T ->
  sub E P Q ->
  sub (F ++ [(Z, bind_sub P)] ++ E) S T.
Proof with simpl_env; eauto using wf_typ_narrowing, wf_env_narrowing.
  intros Q F E Z P S T TransQ SsubT PsubQ.
  remember (F ++ [(Z, bind_sub Q)] ++ E). generalize dependent F.
  induction SsubT; intros F EQ; subst...
  Case "sub_top".
    apply sub_top...
    (* Alex: here we have a CV in the old env, not in the new one. Really seems
    like we need to existentially quantify the result of the lemma, no? *)
    (* apply cv_narrowing with (Q := Q)... *)
    admit.
  Case "sub_refl_tvar".
    apply sub_refl_tvar...
  Case "sub_trans_tvar".
    destruct (X == Z); subst.
    SCase "X = Z".
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
    SCase "X <> Z".
      apply (sub_trans_tvar U)...
      binds_cases H...
  Case "sub_arrow".
    pick fresh Y and apply sub_arrow...
    rewrite <- concat_assoc.
    apply H0...
  Case "sub_all".
    pick fresh Y and apply sub_all...
    rewrite <- concat_assoc.
    apply H0...
  Case "sub_capt".
    constructor...
    apply subcapt_narrowing with (Q := Q)...
  admit. (* new subtyping case *)
Admitted.

Lemma empty_cset_implies_no_captures : forall E xs,
  wf_cset E (cset_set xs {}N) ->
  AtomSet.F.For_all (captures E {}) xs ->
  xs = {}.
Proof.
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
  - assert (C1 = {}C). { 
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
  - admit.
Admitted.

Lemma sub_narrowing_typ_aux : forall Q F E x P S T,
  transitivity_on Q ->
  sub (F ++ [(x, bind_typ Q)] ++ E) S T ->
  sub E P Q ->
  sub (F ++ [(x, bind_typ P)] ++ E) S T.
Proof with simpl_env; eauto using wf_typ_narrowing_typ, wf_env_narrowing_typ.
  intros Q F E x P S T TransQ SsubT PsubQ.
  remember (F ++ [(x, bind_typ Q)] ++ E). generalize dependent F.
  induction SsubT; intros F EQ; subst...
  - apply sub_top...
    apply cv_narrowing_typ with (Q := Q)...
  - apply sub_refl_tvar...
  - apply sub_trans_tvar with (U := U)...
    binds_cases H.
    + apply binds_tail. apply binds_tail... auto.
    + apply binds_head...
  - pick fresh Y and apply sub_arrow...
    rewrite <- concat_assoc.
    apply H0...
  - pick fresh Y and apply sub_all...
    rewrite <- concat_assoc.
    apply H0...
  - constructor...
    apply subcapt_narrowing_typ with (Q := Q)...
  - admit.
Admitted.

(* S <: Q    ->    Q <: T    ->    S <: T*)
Lemma sub_transitivity : forall Q,
  transitivity_on Q.
Proof with simpl_env; auto.
  unfold transitivity_on.
  intros Q E S T SsubQ QsubT.
  assert (W : type Q) by auto.
  
  generalize dependent T.
  generalize dependent S. 
  generalize dependent E.
  remember Q as Q' in |-.  
  generalize dependent Q'.
  
  induction W; intros Q'' EQ E' S' SsubQ.
  
  Ltac inductionThenInversion Rel1 Rel2 := 
      induction Rel1; try discriminate; inversion EQ; subst; intros T' Rel2; inversion Rel2; subst.

  (* type_top *)
  - inductionThenInversion SsubQ QsubT; eauto.
    econstructor...
    (*  HERE `sub E S T2` is now missing! *)
    admit.

  (* type_var *)
  - inductionThenInversion SsubQ QsubT; eauto.
  (* type_arrow *)
  - inductionThenInversion SsubQ QsubT.
    + eauto using sub_trans_tvar.
    + eauto.
    + econstructor... trivial.
    + apply sub_top...
      (* wf_typ typ_arrow *)
      pick fresh X and apply wf_typ_arrow...
      assert (X `notin` L0)...
      specialize (H1 X H6).
      (* by regularity *)
      assert (wf_typ ([(X, bind_typ T1)] ++ E) (open_ct S2 X))...
      rewrite_env (empty ++ [(X, bind_typ S1)] ++ E).
      eapply wf_typ_narrowing_typ with (C1 := T1).
      trivial.
      assert (wf_env (empty ++ [(X, bind_typ T1)] ++ E)). { auto. }
      pose proof (ok_from_wf_env _ H8).
      inversion H9.
      simpl_env.
      econstructor...
    + pick fresh Y and apply sub_arrow.
      SCase "bounds".
        eauto.
      SCase "bodies".
        lapply (H0 Y); [ intros K | auto ].
        apply (K (open_ct T2 Y))...
        rewrite_env (empty ++ [(Y, bind_typ T0)] ++ E).
        apply sub_narrowing_typ_aux with (Q := T1)...
        unfold transitivity_on.
        auto using (IHW T1).
    + apply sub_anycapt...
      admit. (* Now also broken... *) 
  (* type_all. *)
  - inductionThenInversion SsubQ QsubT.
    + eauto.
    + eauto.
    + eauto.
    + assert (sub E (typ_all S1 S2) (typ_all T1 T2)). {
        pick fresh y and apply sub_all...
      }
      auto.
    + pick fresh Y and apply sub_all.
      SCase "bounds".
        eauto.
      SCase "bodies".
        lapply (H0 Y); [ intros K | auto ].
        apply (K (open_tt T2 Y))...
        rewrite_env (empty ++ [(Y, bind_sub T0)] ++ E).
        apply (sub_narrowing_aux T1)...
        unfold transitivity_on.
        auto using (IHW T1).
    + admit. (* broken *)
  (* type_capt *)
  - inductionThenInversion SsubQ QsubT.
    + eauto.
    + eauto.
    + eauto.
    (* typ_capt <: typ_top *)
    + apply sub_top...
      assert (wf_typ E T1)...
      pose proof (subcapt_regular _ _ _ H0) as [WfCset H5].
      assert (wf_cset E C1)...
      (* from H3 we know: cv T = {}, C = {} *)
      inversion H3; subst.
      destruct (empty_cset_union _ _ H11).
      subst.

      (* We have to show that C1 is {} *)
      assert (C1 = {}C). { apply (empty_subcapt_implies_empty_cset E)... }
      subst.

      (* And that cv T1 = {} *)
      assert (cv E T1 {}C). { apply (subtyping_preserves_empty_cv E T1 T)... }      
      eapply cv_typ_capt...
    (* typ_capt <: typ_capt *)
    + apply sub_capt.
      apply (IHW T)...
      eapply subcapt_transitivity with (C2 := C)...
      pose proof (subcapt_regular _ _ _ H6) as [_ Wf].
      inversion Wf.
      (* What? cset_universal cannot have free bvars! *)
      admit.
      simpl.
      fnsetdec.
Admitted.

Lemma sub_narrowing : forall Q E F Z P S T,
  sub E P Q ->
  sub (F ++ [(Z, bind_sub Q)] ++ E) S T ->
  sub (F ++ [(Z, bind_sub P)] ++ E) S T.
Proof.
  intros.
  eapply sub_narrowing_aux; eauto.
  apply sub_transitivity.
Qed.

Lemma sub_narrowing_typ : forall E F x P Q S T,
  sub (F ++ [(x, bind_typ Q)] ++ E) S T ->
  sub E P Q ->
  sub (F ++ [(x, bind_typ P)] ++ E) S T.
Proof with eauto using wf_typ_narrowing_typ.
  intros.
  eapply sub_narrowing_typ_aux; eauto.
  apply sub_transitivity.
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
  - Case "bvar".
    admit.
  - Case "fvar".
    admit.
  - exists {}C. apply cv_typ_arrow.
  - exists {}C. apply cv_typ_all.
  - inversion H; subst.
    inversion Hwf_typ; subst.
    specialize (IHT H3 C2 H4).
    destruct IHT as [ C0 IHT ].
    exists (cset_union c C0).
    apply cv_typ_capt.
    apply IHT.
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
  intros *. intros Hwf_env Hwf_typ Hcv_wide Hcv_narrow Hsub.
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
  - inversion Hwf_typ; subst.
    inversion Hcv_narrow; subst.
    inversion Hcv_wide; subst.
    specialize (IHT H2 C2 H5 C0 H6).
    apply correlate_union_cv; trivial.
    apply subcapt_reflexivity.
    apply wf_env_subst_tb with (Q := Q); auto.
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
      * subst. admit.
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
  - Case "sub_top".
    apply sub_top...
    apply cv_subst_empty with (Q := Q)...
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
    apply subcapt_through_subst_tt with (Q := Q)...
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
  - Case "typing_abs".
    pick fresh y and apply typing_abs.
    rewrite <- concat_assoc.    
    admit.
    (* destruct (H y)... *)
    (* split... *)
    (* eapply wf_typ_narrowing with Q... *)
    (* admit. *)
    (* trivial. *)
  - Case "typing_app".
    admit.
  - Case "typing_tabs".
    pick fresh Y and apply typing_tabs.
    rewrite <- concat_assoc.
    apply H0...
Admitted.

(************************************************************************ *)
(** ** Substitution preserves typing (8) *)


Lemma wf_env_disallows_self_ref : forall F E x T C,
  wf_env (F ++ [(x, bind_typ T)] ++ E) ->
  eq (subst_ct x C T) T.
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

Lemma wf_cset_from_cv : forall E T C,
  wf_env E ->
  cv E T C ->
  wf_cset E C.
Proof.
Admitted.

(* Not tested to work. *)
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
    subst_cset x C x = C.
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
  remember (F ++ [(x, bind_typ U)] ++ E).
  generalize dependent F.
  induction HtypT; intros F EQ; subst; simpl subst_ee...

  (** The typing_var case involves a case analysis on whether the
      variable is the same as the one being substituted for. *)

  - Case "typing_var".
    destruct (x0 == x); subst.

    (** In the case where x0=x, we first observe that hypothesis H0
        implies that T=U, since x can only be bound once in the
        environment.  The conclusion then follows from hypothesis TypU
        and weakening.  We can use the binds_get tactic, described in
        the Environment library, with H0 to obtain the fact that
        T=U. *)

    + SCase "x0 = x".
      binds_get H0.
      inversion H2; subst.

      (** In order to apply typing_weakening, we need to rewrite the
            environment so that it has the right shape.  (We could
            also prove a corollary of typing_weakening.)  The
            rewrite_env tactic, described in the Environment library,
            is one way to perform this rewriting. *)


      rewrite_env (empty ++ map (subst_cb x C) F ++ E).
      apply typing_weakening...
      * simpl.
        assert (subst_cset x C x = C) as HeqCset by apply cset_subst_self.
        rewrite HeqCset...
        assert (eq (subst_ct x C U) U) as Heq. {
          eapply wf_env_disallows_self_ref.
          apply H.
        }
        rewrite Heq...
        apply typing_sub with (S := U)...
        apply sub_anycapt...
        apply sub_reflexivity...
      * eapply wf_env_subst_cb...
    (** In the case where x0<>x, the result follows by an exhaustive
        case analysis on exactly where x0 is bound in the environment.
        We perform this case analysis by using the binds_cases tactic,
        described in the Environment library. *)

    + SCase "x0 <> x".

      binds_cases H0.
      * assert ((typ_capt x0 T) = (subst_ct x C (typ_capt x0 T))) as Heq. {
          apply subst_ct_fresh.
          (* somehow by larger env being wf *)
          admit.
        }
        rewrite <- Heq.
        rewrite_env (empty ++ map (subst_cb x C) F ++ E).
        apply typing_weakening...
        eapply wf_env_subst_cb...
      * simpl.
        assert ((x0 : captureset) = subst_cset x C x0) as Heq. {
          apply subst_cset_fresh.
          (* somehow by x0 <> x *)
          admit.
        }
        rewrite <- Heq.
        apply typing_var.
        eapply wf_env_subst_cb...
        assert (binds x0 (bind_typ (subst_ct x C T)) (map (subst_cb x C) F)). {
          unsimpl (subst_cb x C (bind_typ T)).
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

    (* seems like for some reason the substitution isn't properly propagated? *)
    admit.
(*     pick fresh y and apply typing_abs. *)

(*     (** We cannot apply H0 directly here.  The first problem is that *)
(*         the induction hypothesis has (subst_ee open_ee), whereas in *)
(*         the goal we have (open_ee subst_ee).  The lemma *)
(*         subst_ee_open_ee_var lets us swap the order of these two *)
(*         operations. *) *)

(*     rewrite subst_ee_open_ee_var... *)

(*     (** The second problem is how the concatenations are associated in *)
(*         the environments.  In the goal, we currently have *)

(* <<       ([(y, bind_typ V)] ++ F ++ E), *)
(* >> *)
(*         where concatenation associates to the right.  In order to *)
(*         apply the induction hypothesis, we need *)

(* <<        (([(y, bind_typ V)] ++ F) ++ E). *)
(* >> *)
(*         We can use the rewrite_env tactic to perform this rewriting, *)
(*         or we can rewrite directly with an appropriate lemma from the *)
(*         Environment library. *) *)

(*     rewrite <- concat_assoc. *)

(*     (** Now we can apply the induction hypothesis. *) *)

(*     apply H0... *)

  (** The remaining cases in this proof are straightforward, given
      everything that we have pointed out above. *)

  - Case "typing_app".
    admit.
  - Case "typing_tabs".
    admit.
    (* pick fresh Y and apply typing_tabs. *)
    (* rewrite subst_ee_open_te_var... *)
    (* rewrite <- concat_assoc. *)
    (* apply H0... *)
  - Case "typing_tapp".
    admit.
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
