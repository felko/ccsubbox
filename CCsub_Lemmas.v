Require Import Coq.Program.Equality.

Require Export CCsub_Infrastructure.
Require Export CCsub_Wellformedness.
Require Import Atom.

Require Import LibTactics.

(* ********************************************************************** *)
(** * #<a name="notin"></a># Lemmas about free variables and "notin" *)


(** Uniqueness of bindings **)

Lemma binds_unique : forall b1 b2 x (E : env),
  binds x b1 E ->
  binds x b2 E ->
  b1 = b2.
Proof.
  intros* Hb1 Hb2.
  congruence.
Qed.

Lemma binds_sub_unique : forall T1 T2 X E,
  binds X (bind_sub T1) E ->
  binds X (bind_sub T2) E ->
  T1 = T2.
Proof.
  intros* Hb1 Hb2.
  congruence.
Qed.

Lemma binds_typ_unique : forall T1 T2 X E,
  binds X (bind_typ T1) E ->
  binds X (bind_typ T2) E ->
  T1 = T2.
Proof.
  intros* Hb1 Hb2.
  congruence.
Qed.

(** These proofs are all the same, but Coq isn't smart enough unfortunately... *)

Lemma notin_fv_tt_open_tt_rec : forall k (X : atom) U T,
  X ∉ fv_tt (open_tt_rec k U T) ->
  X ∉ fv_tt T.
Proof.
  intros k X U T. unfold open_tt.
  generalize k.
  induction T; simpl; intros k0 Fr; notin_simpl; try apply notin_union; eauto.
  unfold open_vt in Fr; destruct v; simpl in Fr; fsetdec.
Qed.

Lemma notin_fv_tt_open_tt : forall (X : atom) U T,
  X ∉ fv_tt (open_tt T U) ->
  X ∉ fv_tt T.
Proof with eauto.
  intros. apply notin_fv_tt_open_tt_rec with (k := 0) (U := U)...
Qed.

Lemma notin_cset_fvars_open_cset : forall X k C c,
  X ∉ `cset_fvars` (open_cset k C c) ->
  X ∉ `cset_fvars` c.
Proof.
  intros.
  destruct c.
  intros XIn.
  cbv in H.
  csetdec.
Qed.

Lemma notin_fv_tt_open_ct_rec : forall k (X : atom) C T,
  X ∉ fv_tt (open_ct_rec k C T) ->
  X ∉ fv_tt T.
Proof with eauto using notin_cset_fvars_open_cset.
  intros k Y C T. unfold open_tt.
  generalize k.
  induction T; simpl; intros k0 Fr; notin_simpl; try apply notin_union; eauto.
Qed.

Lemma notin_fv_tt_open_ct : forall (X : atom) C T,
  X ∉ fv_tt (open_ct T C) ->
  X ∉ fv_tt T.
Proof with eauto.
  intros. apply notin_fv_tt_open_ct_rec with (k := 0) (C := C)...
Qed.

Lemma notin_fv_ct_open_tt_rec : forall k (X : atom) U T,
  X ∉ fv_ct (open_tt_rec k U T) ->
  X ∉ fv_ct T.
Proof with eauto using notin_cset_fvars_open_cset.
  intros k X U T. unfold open_tt.
  generalize k.
  induction T; simpl; intros k0 Fr; notin_simpl; try apply notin_union...
Qed.

Lemma notin_fv_ct_open_tt : forall (X : atom) U T,
  X ∉ fv_ct (open_tt T U) ->
  X ∉ fv_ct T.
Proof with eauto*.
  intros. apply notin_fv_ct_open_tt_rec with (k := 0) (U := U)...
Qed.

Lemma notin_fv_tt_open : forall (X : atom) U T,
  X ∉ fv_tt (open_tt T U) ->
  X ∉ fv_ct (open_tt T U) ->
  X ∉ (fv_tt T `u`A fv_ct T).
Proof with auto.
 intros. apply notin_union.
 - apply notin_fv_tt_open_tt with (U := U)...
 - apply notin_fv_ct_open_tt with (U := U)...
Qed.

Lemma notin_fv_ct_open_ct_rec : forall (X : atom) T C k,
  X ∉ fv_ct (open_ct_rec k C T) ->
  X ∉ fv_ct T.
Proof with auto.
  intros X T C.
  induction T ; simpl ; intros k Fr ; try apply notin_union; eauto.
  - apply IHT1 with (k := k)...
  - apply IHT2 with (k := S k)...
  - apply IHT1 with (k := k)...
  - apply IHT2 with (k := S k)... 
  - apply notin_cset_fvars_open_cset with (k := k) (C := C)...
  - apply IHT with (k := k)...
Qed.

Lemma notin_fv_ct_open_ct : forall (X : atom) T C,
  X ∉ fv_ct (open_ct T C) ->
  X ∉ fv_ct T.
Proof with auto.
  intros. apply notin_fv_ct_open_ct_rec with (k := 0) (C := C)...
Qed.

(* Lemma notin_fv_ct_open_ct_rec : forall (Y X : atom) T k, *)
(*   X `notin` fv_ct (open_ct_rec k Y T) -> *)
(*   X <> Y -> *)
(*   X `notin` fv_ct T *)
(* with notin_fv_ct_open_cpt_rec : forall (Y X : atom) T k, *)
(*   X `notin` fv_cpt (open_cpt_rec k Y T) -> *)
(*   X <> Y -> *)
(*   X `notin` fv_cpt T. *)
(* Proof with eauto*. *)
(* ------ *)
(*   intros Y X T. *)
(*   induction T ; simpl ; intros k H Fr ; try apply notin_union; eauto. *)
(*   - apply notin_cset_fvars_open_cset with (k := k) (C := Y)... *)
(*     discriminate. *)
(*   - apply notin_fv_ct_open_cpt_rec with (k := k) (Y := Y)... *)
(* ------ *)
(*   intros Y X T. *)
(*   induction T ; simpl ; intros k H Fr ; try apply notin_union; eauto. *)
(*   - apply notin_fv_ct_open_ct_rec with (Y := Y) (k := k)... *)
(*   - apply notin_fv_ct_open_ct_rec with (Y := Y) (k := S k)... *)
(*   - apply notin_fv_ct_open_ct_rec with (Y := Y) (k := k)... *)
(*   - apply notin_fv_ct_open_ct_rec with (Y := Y) (k := S k)... *)
(* Qed. *)

(* Lemma notin_fv_ct_open_ct : forall (Y X : atom) T, *)
(*   X `notin` fv_ct (open_ct T Y) -> *)
(*   X <> Y -> *)
(*   X `notin` fv_ct T *)
(* with notin_fv_ct_open_cpt : forall (Y X : atom) T, *)
(*   X `notin` fv_cpt (open_cpt T Y) -> *)
(*   X <> Y -> *)
(*   X `notin` fv_cpt T. *)
(* Proof with eauto*. *)
(*   intros. apply notin_fv_ct_open_ct_rec with (k := 0) (Y := Y)... *)
(*   intros. apply notin_fv_ct_open_cpt_rec with (k := 0) (Y := Y)... *)
(* Qed. *)


Lemma notin_fv_ct_open : forall (X : atom) T C,
  X ∉ fv_ct (open_ct T C) ->
  X ∉ fv_tt (open_ct T C) ->
  X ∉ (fv_tt T `u`A fv_ct T).
Proof with auto.
  intros. apply notin_union...
  - apply notin_fv_tt_open_ct with (C := C)...
  - apply notin_fv_ct_open_ct with (C := C)...
Qed.

Lemma notin_fv_wf_cset : forall Γ (x : atom) C,
  Γ ⊢ₛ C wf ->
  x ∉ dom Γ ->
  x ∉ `cset_fvars` C.
Proof with eauto*.
  intros * WfC NotIn.
  destruct WfC as [fvars univ AllBound].
  contradict AllBound; rename AllBound into In; intros AllBound.
  destruct (AllBound x In) as [C [R Binds]].
  apply NotIn.
  eapply binds_In, Binds.
Qed.

Lemma notin_fv_wf_typ : forall Γ (X : atom) T,
  Γ ⊢ T wf ->
  X ∉ dom Γ ->
  X ∉ (fv_tt T `u`A fv_ct T).
Proof with eauto using notin_fv_wf_cset.
  intros * WfT.
  induction WfT; intros NotIn; simpl.
  - Case "wf_typ_var".
    rename select (binds _ _ _) into Binds.
    enough (X <> X0) by fsetdec.
    enough (X0 ∈ dom Γ) by fsetdec.
    applys binds_In Binds.
  - Case "⊤".
    fsetdec.
  - Case "∀ (S) T".
    rename select (forall x : atom, x ∉ L -> X ∉ dom _ -> _) into IH.
    pick fresh y and specialize IH.
    rewrite dom_concat in IH; simpl in IH.
    specialize (IH ltac:(notin_solve)).
    destruct (AtomSetNotin.elim_notin_union IH) as [NotInFvTT NotInFvCT].
    apply notin_fv_tt_open_ct in NotInFvTT.
    apply notin_fv_ct_open_ct in NotInFvCT.
    specialize (IHWfT ltac:(notin_solve)).
    simpl in IHWfT.
    clear - NotInFvTT NotInFvCT IHWfT.
    fsetdec.
  - Case "∀ [R] T".
    rename select (forall x : atom, x ∉ L -> X ∉ dom _ -> _) into IH.
    pick fresh Y and specialize IH.
    rewrite dom_concat in IH; simpl in IH.
    specialize (IH ltac:(notin_solve)).
    destruct (AtomSetNotin.elim_notin_union IH) as [NotInFvTT NotInFvCT].
    apply notin_fv_tt_open_tt in NotInFvTT.
    apply notin_fv_ct_open_tt in NotInFvCT.
    specialize (IHWfT ltac:(notin_solve)).
    clear - NotInFvTT NotInFvCT IHWfT.
    fsetdec.
  - Case "□ T".
    auto.
  - Case "C # R".
    specialize (IHWfT NotIn).
    rename select (Γ ⊢ₛ C wf) into WfC.
    assert (X ∉ `cset_fvars` C) by (eapply notin_fv_wf_cset; eauto).
    fsetdec.
Qed.

Local Lemma notin_fv_vv_open_vv : forall k u x v,
  x ∉ fv_vv (open_vv k u v) ->
  x ∉ fv_vv v.
Proof with eauto.
  intros.
  unfold fv_vv, open_vv in *.
  destruct v...
Qed.

Local Lemma notin_fv_ve_open_ve_rec : forall k u (y x : atom) t,
  x ∉ fv_ve (open_ve_rec k u (`cset_fvar` y) t) ->
  x <> y ->
  x ∉ fv_ve t.
Proof with eauto using notin_fv_vv_open_vv.
  intros. generalize dependent k.
  induction t; simpl in *; intros k H; try (trivial || notin_solve)...
  all: destruct (AtomSetNotin.elim_notin_union H)...
  destruct v; simpl in *; enough (x ∉ `cset_fvars` c) by fsetdec; eapply notin_cset_fvars_open_cset...
Qed.

Lemma notin_fv_ve_open_ve : forall u (y x : atom) t,
  x ∉ fv_ve (open_ve t u (`cset_fvar` y)) ->
  x <> y ->
  x ∉ fv_ve t.
Proof with eauto.
  intros. unfold open_ve in *.
  apply (notin_fv_ve_open_ve_rec 0 u y)...
Qed.

(* Lemma notin_fv_ct_open_tt_rec : forall k (Y X : atom) T, *)
(*   X `notin` fv_ct (open_tt_rec k Y T) -> *)
(*   X `notin` fv_ct T *)
(* with notin_fv_cpt_open_tpt_rec : forall k (Y X : atom) T, *)
(*   X `notin` fv_cpt (open_tpt_rec k Y T) -> *)
(*   X `notin` fv_cpt T. *)
(* Proof. *)
(* ------ *)
(*   intros k Y X T. unfold open_tt. *)
(*   generalize k. *)
(*   induction T; simpl; intros k0 Fr; notin_simpl; try apply notin_union; eauto. *)
(* ------ *)
(*   intros k Y X T. unfold open_tt. *)
(*   generalize k. *)
(*   induction T; simpl; intros k0 Fr; notin_simpl; try apply notin_union; eauto. *)
(* Qed. *)

Local Lemma notin_fv_ve_open_te_rec : forall k (y x : atom) t,
  x ∉ fv_ve (open_te_rec k y t) ->
  x <> y ->
  x ∉ fv_ve t.
Proof with eauto.
  intros. generalize dependent k.
  induction t; simpl in *; intros k H; try (trivial || notin_solve)...
  all: destruct (AtomSetNotin.elim_notin_union H)...
Qed.

Lemma notin_fv_ve_open_te : forall (y x : atom) t,
  x ∉ fv_ve (open_te t y) ->
  x <> y ->
  x ∉ fv_ve t.
Proof with eauto.
  intros. unfold open_ve in *.
  apply (notin_fv_ve_open_te_rec 0 y)...
Qed.

Lemma map_subst_tb_id : forall G Z P,
  wf_env G ->
  Z ∉ dom G ->
  G = map (subst_tb Z P) G.
Proof with auto.
  intros G Z P H.
  induction H; intros Fr; simpl_env...
  - rewrite <- IHwf_env...
    simpl.
    rewrite <- subst_tt_fresh...
    eapply notin_fv_wf_typ; eauto.
  - rewrite <- IHwf_env...
    cbn [subst_tb].
    rewrite <- subst_tt_fresh...
    eapply notin_fv_wf_typ; eauto.
Qed.

(* ********************************************************************** *)
(** * #<a name="cvfree"></a># Lemmas about free variables -- in particular properties of [free_for_cv] *)
(** TODO Maybe have a separate file for free_for_cv lemmas **)

(* REVIEW: none of these are true anymore, since exp_cv could be universal.

Lemma exp_cv_open_ve_rec_same_uvar : forall k x C e,
  `cset_uvar` (exp_cv (open_ve_rec k x C e)) = `cset_uvar` (exp_cv e).
Proof with eauto*.
  intros.
  revert k.
  induction e; intros k; simpl.
  - destruct v; simpl in *...
    destruct (k === n)...
  - apply IHe.
  - destruct v; simpl.
    + destruct v0; simpl.
      * reflexivity.
      * destruct (k === n); simpl...
    + destruct v0; simpl.
      * destruct (k === n); simpl...
      * destruct (k === n); destruct (k === n0); simpl...
  - f_equal.
    + apply IHe1.
    + apply IHe2.
  - apply IHe.
  - destruct v; simpl.
    + reflexivity.
    + destruct (k === n); simpl...
  - reflexivity.
  - f_equal.
    + unfold open_cset.
      destruct_set_mem k c.
    + destruct v; simpl.
      * reflexivity.
      * destruct (k === n); simpl...
Qed.

Lemma typ_cv_never_universal : forall o

Lemma exp_cv_open_te_rec_same_uvar : forall k T e,
  type T ->
  `cset_uvar` (exp_cv (open_te_rec k T e)) = `cset_uvar` (exp_cv e).
Proof with eauto*.
  intros.
  revert k.
  induction e; intros k; simpl...
  - f_equal.
    + apply IHe1.
    + apply IHe2.
  - f_equal.
    destruct v; simpl.
    + unfold open_cset.
      destruct_set_mem k c.
    destruct v; simpl;
      repeat rewrite orb_false_r;
      unfold open_cset;
      destruct_set_mem k c;
      destruct c eqn:Hc;
      simpl...
    + unfold typ_cv.
      destruct T eqn:HeqT...
      * destruct v...
      * exfalso.
        inversion H; inversion H0.
        destruct c0.
  - destruct v; simpl in *...
    destruct (k === n)...
  - apply IHe.
  - destruct v; simpl.
    + destruct v0; simpl.
      * reflexivity.
      * destruct (k === n); simpl...
    + destruct v0; simpl.
      * destruct (k === n); simpl...
      * destruct (k === n); destruct (k === n0); simpl...
  - f_equal.
    + apply IHe1.
    + apply IHe2.
  - apply IHe.
  - destruct v; simpl.
    + reflexivity.
    + destruct (k === n); simpl...
  - reflexivity.
  - f_equal.
    + unfold open_cset.
      destruct_set_mem k c.
    + destruct v; simpl.
      * reflexivity.
      * destruct (k === n); simpl...
Qed.

TODO: Γ ⊢ e : T -> * ∉ cv e
adjust subcapt_univ_through_subst_cb

Lemma exp_cv_never_universal : forall e,
  expr e ->
  ~ `* in` (exp_cv e).
Proof with eauto*.
  intros.
  induction H; simpl...
  - pick fresh x and specialize H1.
    erewrite <- exp_cv_open_ve_rec_same_uvar.
    apply H1.
  - pick fresh x and specialize H1.
    intro.
    destruct (`cset_uvar` (exp_cv e1)) eqn:He1...
    destruct (`cset_uvar` (exp_cv e2)) eqn:He2...
    erewrite <- exp_cv_open_ve_rec_same_uvar with (k := 0) (x := x) (C := `cset_fvar` x) in He2.
    apply (H1 He2).
  - pick fresh X and specialize H1.
    erewrite <- exp_cv_open_te_rec_same_uvar.
    apply H1.
    appl 
    destruct (exp_cv (open_ve_rec 0 x (`cset_fvar` x) e2)) eqn:Hu.
    inversion Hu; subst.
    assert (`cset_uvar` (exp_cv (open_ve_rec 0 x (`cset_fvar` x) e2)) = `cset_uvar` (cset_set t t0 true)).
    { Unset Printing Notations. f_equal.

    }
    replace ( * ∈ exp_cv (open_ve_rec 0 x (`cset_fvar` x) e2)) with (`cset_uvar` (exp_cv (open_ve e2 x (`cset_fvar` x)))).
    Unset Printing Notations.
    
    erewrite <- exp_cv_open_ve_rec_same_uvar.
    enough (`cset_uvar` (exp_cv e2) = false).
  induction H;
    repeat match goal with
    | [v : var |- _] =>
        destruct v;
        simpl;
        eauto*
    end;
    try discriminate...
  simpl.
  - destruct (exp_cv e1) eqn:Hfc1;
    destruct (exp_cv e2) eqn:Hfc2...
    csetdec.
  -  
Qed.

Lemma cv_free_has_universal_false : forall e,
  `* mem` (free_for_cv e) = false.
Proof.
  intros.
  destruct (`* mem` (free_for_cv e)) eqn:EQ; trivial.
  pose proof (cv_free_never_universal e).
  intuition.
Qed.

Lemma cv_free_var_is_bvar_free : forall v,
  NatSet.F.Empty (`cset_bvars` (free_for_cv_var v)).
Proof with eauto.
  intros.
  destruct v; simpl; fnsetdec.
Qed.

Lemma cv_free_is_bvar_free : forall e,
  NatSet.F.Empty (`cset_bvars` (free_for_cv e)).
Proof with eauto using cv_free_var_is_bvar_free.
  induction e; simpl...
  - intros x. apply NatSetNotin.notin_union; apply cv_free_var_is_bvar_free.
  - intros x. apply NatSetNotin.notin_union; [ apply IHe1 | apply IHe2 ].
Qed.
*)

Lemma var_cv_open : forall v k (y : atom),
  cset_subset_prop (var_cv v) (var_cv (open_vv k y v)).
Proof with eauto*.
  intros.
  destruct v; simpl...
  destruct (k === n); subst; simpl...
  unfold cset_subset_prop.
  repeat split...
  fsetdec.
Qed.

Lemma exp_cv_open_ve_rec : forall e k (y : atom) C,
  cset_subset_prop (exp_cv e) (exp_cv (open_ve_rec k y C e)).
Proof with eauto using var_cv_open, subset_union.
  intros e.
  induction e; intros; simpl...
  destruct v; csetsimpl; destruct c.
  - repeat split; unfold open_cset.
    + destruct_set_mem k t0; simpl; fsetdec.
    + fsetdec.
    + destruct_set_mem k t0; simpl; fsetdec.
  - repeat split; unfold open_cset; csetsimpl.
    + destruct_set_mem k t0; simpl; fsetdec.
    + destruct (k === n); simpl; fsetdec.
    + destruct_set_mem k t0; destruct (k === n); subst; unfold leb; destruct b; simpl...
Qed.

Lemma exp_cv_open_te_rec : forall e k (y : atom),
  cset_subset_prop (exp_cv e) (exp_cv (open_te_rec k y e)).
Proof with eauto*.
  induction e; intros; simpl...
  specialize (IHe1 k y).
  specialize (IHe2 (`succ` k) y).
  apply subset_union...
Qed.

Lemma var_cv_binds : forall Γ v (x : atom),
  Γ ⊢ wf ->
  Γ ⊢ₛ (var_cv v) wf ->
  x ∈ `cset_fvars` (var_cv v) ->
  exists C R, binds x (bind_typ (C # R)) Γ.
Proof with eauto.
  intros * WfEnv WfV xIn.
  destruct v; simpl in *.
  - inversion WfV; subst.
    assert (x = a) by fsetdec; subst...
  - fsetdec.
Qed.

Lemma exp_cv_binds : forall Γ e (x : atom),
  Γ ⊢ wf ->
  Γ ⊢ₛ (exp_cv e) wf ->
  x ∈ `cset_fvars` (exp_cv e) ->
  exists C R, binds x (bind_typ (C # R)) Γ.
Proof with eauto using var_cv_binds.
  intros * WfEnv WfCV xIn.
  induction e; intros; simpl in *; try fsetdec...
  - destruct (proj1 (wf_cset_over_union _ _ _) WfCV) as [WfC WfD].
    destruct (AtomSet.F.union_1 xIn)...
  - destruct (proj1 (wf_cset_over_union _ _ _) WfCV) as [WfC WfD].
    destruct (AtomSet.F.union_1 xIn)...
  - destruct (proj1 (wf_cset_over_union _ _ _) WfCV) as [WfC WfD].
    destruct (AtomSet.F.union_1 xIn)...
    destruct (cset_references_fvar_over_union _ _ _ xIn) as [xInC1 | xInC2]...
    inversion WfC; subst...
Qed.

Lemma var_cv_subset_fv_vv : forall v,
  `cset_fvars` (var_cv v) `c`A fv_vv v.
Proof with eauto.
  intros v.
  destruct v; simpl; fsetdec.
Qed.

Lemma var_cv_closed : forall v,
  `cset_bvars` (var_cv v) = {}N.
Proof with eauto*.
  destruct v...
Qed.

Lemma exp_cv_subset_fv_ve : forall e,
  `cset_fvars` (exp_cv e) `c`A fv_ve e.
Proof with eauto using var_cv_subset_fv_vv, atomset_subset_union; eauto*.
  induction e; simpl...
  - fsetdec.
  - apply atomset_subset_union...
Qed.

Lemma exp_cv_closed : forall e,
  `cset_bvars` (exp_cv e) = {}N.
Proof with eauto using var_cv_closed.
  induction e; simpl...
  - rewrite (var_cv_closed v), (var_cv_closed v0); csetdec.
  - rewrite IHe1, IHe2; csetdec.
  - rewrite (var_cv_closed v); csetdec.
Qed.

(* REVIEW: hard to prove
Lemma wf_env_bound_to_var_implies_var_bind_sub : forall Γ x (X : atom),
  Γ ⊢ wf ->
  bound x X Γ -> (* binds x (bind_sub X) Γ *)
  exists S, binds X (bind_sub S) Γ.
Proof with eauto*.
  intros.
  generalize dependent X.
  generalize dependent x.
  induction H; intros.
  - inversion H0; inversion H.
  - inversion H3; subst.
    + inversion H4; subst.
      destruct (x == X); subst.
      * inversion H6; subst.
      * destruct (IHwf_env x X0 (bound_typ x X0 Γ H6)) as [S ?].
        exists S.
        assert (X0 <> X).
        { pose proof (binds_In _ _ _ _ H5).
          fsetdec.
        }
        apply binds_tail; simpl...
    + inversion H4; subst.
      destruct (x == X); subst.
      * inversion H6; inversion H7; subst.
        destruct (X == X0); subst...
        admit.
      * admit.
Admitted. *)

Lemma subcapt_empty : forall Γ C,
  Γ ⊢ₛ C wf ->
  Γ ⊢ₛ {} <: C.
Proof with eauto*.
  intros.
  apply subcapt_set...
  intros x xIn.
  exfalso.
  fsetdec.
Qed.

(* TODO: idk
Lemma typing_var_bind_typ : forall Γ (x : atom) T,
  Γ ⊢ x : (C # P) ->
  exists D Q, Γ ⊢ Q <: P
     /\ binds x (bind_typ (D # Q)) Γ
     /\ Γ ⊢ₛ (`cset_fvar` x) <: C
     /\ (Γ ⊢ₛ D <: C \/ x ∈ `cset_fvars` C).
Proof with eauto*.
  intros.
  dependent induction H.
  - Case "typing_var".
    exists (C # R).
    split...

      * unfold wf_cset.
        intros y x0In.
        destruct (y == x); try (contradict n; fsetdec); subst.
        exists X.
        apply bound_typ, H0.
      * enough (x ∈ dom Γ) by fsetdec.
        eapply binds_In, H0.
    + destruct (wf_env_bound_to_var_implies_var_bind_sub Γ x X H (bound_typ x X Γ H0)) as [S ?].
      apply wf_typ_var with (T := S), H1.
  - Case "typing_var".
    exists (C # R).
    split...
    apply sub_capt.
    + admit. (* REVIEW: unprovable *)
    + admit. (* REVIEW: need reflexivity here which has not yet been proven *)
  - Case "typing_sub".
    admit.
Admitted.*)

(*
Γ ⊢ e : T ->
x ∈ fv_ve e ->
exists S, binds x (bind_typ S) Γ.
*)

(** This should be easily true: free variables
    are all bound if a term has a type.... *)
Lemma typing_cv : forall Γ e C R,
  Γ ⊢ e : (C # R) ->
  Γ ⊢ₛ (exp_cv e) wf.
Proof with eauto using wf_cset_over_union; eauto*.
  intros * Htyp.
  induction Htyp; simpl...
  - Case "typing_var".
    rename select (binds _ _ _) into Binds.
    forwards: binds_In Binds.
    simpl. constructor...
    intros y ?.
    assert (x = y) by fsetdec.
    subst.
    exists C0, R0...
  - Case "typing_abs".
    pick fresh y.
    assert (y ∉ L) by fsetdec.
    assert (y ∉ `cset_fvars` (exp_cv e1)).
    { pose proof (exp_cv_subset_fv_ve e1) as P... }
    forwards SpH0: H1 y...
    pose proof (exp_cv_open_ve_rec e1 0 y (`cset_fvar` y))...
    pose proof (exp_cv_closed e1).
    destruct (exp_cv e1) eqn:Ecv1; subst.
    inversion SpH0; subst.
    unfold open_ve in H5.
    rewrite <- H5 in H4.
    destruct H4 as [t_sub_fvars [_ b_le_univ]].
    econstructor.
    + intros x xIn.
      assert (x ∈ fvars) by (clear - xIn t_sub_fvars; fsetdec).
      destruct (H6 x H4) as [D [Q B]].
      assert (x <> y) by (clear - xIn H3; fsetdec).
      inversion B; destruct (x == y); subst...
  - Case "typing_app".
    apply wf_cset_union...
  - Case "typing_let".
    apply wf_cset_over_union; split...
    pick fresh y.
    assert (y ∉ L) by fsetdec.
    assert (y ∉ `cset_fvars` (exp_cv k)).
    { pose proof (exp_cv_subset_fv_ve k) as P... }
    forwards SpH0: H0 y...
    pose proof (exp_cv_open_ve_rec k 0 y (`cset_fvar` y))...
    pose proof (exp_cv_closed k).
    destruct (exp_cv k) eqn:Hfcv1; subst...
    unfold open_ve in *.
    inversion SpH0; subst...
    rename select (_ = _) into EQ.
    rename select (cset_subset_prop _ _) into HH.
    destruct HH as (HA1 & HA2 & HA3).
    rewrite <- EQ in *.
    simpl in *.
    constructor.
    intros x ?.
    destruct (x == y). {
      csetdec.
    }
    forwards (D & Q & B): H5 x. {
      fsetdec.
    }
    simpl_env in *.
    exists D, Q. binds_cases B...
  - Case "typing_tapp".
    pick fresh y.
    assert (y ∉ L) by fsetdec.
    assert (y ∉ `cset_fvars` (exp_cv e1)).
    { pose proof (exp_cv_subset_fv_ve e1) as P... }
    forwards SpH0: H2 y...
    pose proof (exp_cv_open_te_rec e1 0 y)...
    pose proof (exp_cv_closed e1).
    destruct (exp_cv e1) eqn:Hfcv1; subst...
    unfold open_te in *.
    inversion SpH0; subst...
    rename select (_ = _) into EQ.
    rewrite <- EQ in *.
    rename select (cset_subset_prop _ _) into HH.
    destruct HH as (HA1 & HA2 & HA3).
    simpl in *.
    constructor.
    intros x ?.
    destruct (x == y). {
      csetdec.
    }
    forwards (D & Q & B): H7 x. {
      fsetdec.
    }
    simpl_env in *.
    exists D, Q. binds_cases B...
  - Case "typing_box".
    apply wf_cset_union...
    inversion H; subst.
    apply wf_concrete_cset...
Qed. 

Lemma subst_cset_fresh_for_cv_var : forall z v C,
  z `notin` fv_vv v ->
  subst_cset z C (var_cv v) = var_cv v.
Proof with eauto*.
  intros.
  destruct v; unfold subst_cset; simpl in *...
  - replace (AtomSet.F.mem z (singleton a)) with false by fset_mem_dec.
    reflexivity.
  - replace (AtomSet.F.mem z {}A) with false by fset_mem_dec.
    reflexivity.
Qed.

Lemma subst_cset_fresh_for_cv : forall z t C,
  z ∉ fv_ve t ->
  subst_cset z C (exp_cv t) = exp_cv t.
Proof with eauto using subst_cset_fresh_for_cv_var; eauto*.
  intros.
  induction t; simpl in H |- *...
  - rewrite subst_cset_distributive_across_union.
    repeat rewrite subst_cset_fresh_for_cv_var...
  - rewrite subst_cset_distributive_across_union.
    rewrite IHt1 by notin_solve.
    rewrite IHt2 by notin_solve.
    reflexivity.
  - unfold subst_cset.
    destruct_set_mem z {}A...
    exfalso; clear - zIn; fsetdec.
  - destruct c.
    unfold subst_cset; simpl.
    destruct_set_mem z (t `u`A `cset_fvars` (var_cv v))...
    destruct (AtomSetNotin.elim_notin_union H).
    destruct (AtomSet.F.union_1 zIn).
    + exfalso; apply (H0 H2).
    + rewrite cset_fvars_var_cv_is_fv_vv in H2.
      exfalso; apply (H1 H2).
Qed.

(*
Lemma subst_commutes_with_free_for_cv : forall x u C e,
  x `notin` (`cset_fvars` (free_for_cv e)) ->
  (subst_cset x C (free_for_cv e)) = (free_for_cv (subst_ve x u C e)).
Proof with eauto.
  intros *.
  intro Fr.
  induction e.
  - simpl.
    unfold subst_cset.
    find_and_destroy_set_mem.
    + notin_solve.
    + easy.
  - simpl in *.
    assert (a <> x) by fsetdec.
    destruct (a == x); try easy.
    cbv.
    destruct_if.
    + rewrite <- AtomSetFacts.mem_iff in Heqb. exfalso. fsetdec.
    + reflexivity.
  - apply IHe...
  - simpl in *.
    pose proof (cv_free_never_universal e1).
    pose proof (cv_free_never_universal e2).
    destruct (free_for_cv e1); try easy.
    destruct (free_for_cv e2); try easy.
    rewrite <- IHe1...
    rewrite <- IHe2...
    rewrite subst_cset_distributive_across_union.
    reflexivity.
  - apply IHe...
  - apply IHe...
  - apply IHe...
  - simpl in *.
    pose proof (cv_free_never_universal e1).
    pose proof (cv_free_never_universal e2).
    destruct (free_for_cv e1); try easy.
    destruct (free_for_cv e2); try easy.
    rewrite <- IHe1...
    rewrite <- IHe2...
    rewrite subst_cset_distributive_across_union.
    reflexivity.
  - simpl in *.
    cbv.
    replace (AtomSet.F.mem x {}A) with false by fset_mem_dec.
    reflexivity.
Qed.

Lemma free_for_cv_subst_ee_cset_irrelevancy: forall x u C D t,
  free_for_cv (subst_ee x u C t) =
  free_for_cv (subst_ee x u D t).
Proof with eauto.
  induction t; simpl; eauto.
  - rewrite IHt1.
    rewrite IHt2...
  - rewrite IHt1.
    rewrite IHt2...
Qed.
*)

Lemma bind_typ_notin_fv_tt : forall x S Γ T,
  binds x (bind_typ S) Γ ->
  Γ ⊢ T wf ->
  x ∉ fv_tt T.
Proof with auto.
  intros * Hbnd WfT.
  dependent induction WfT; simpl...
  - apply AtomSetNotin.notin_union...
    pick fresh y and specialize H0.
    eapply notin_fv_tt_open_ct with (C := `cset_fvar` y).
    apply H0.
    apply binds_tail...
  - apply AtomSetNotin.notin_union...
    pick fresh Y and specialize H1.
    eapply notin_fv_tt_open_tt.
    apply H1.
    apply binds_tail...
Qed.

Lemma wf_cset_notin_fvars : forall x Γ C,
  Γ ⊢ₛ C wf ->
  x ∉ dom Γ ->
  x ∉ (`cset_fvars` C).
Proof with eauto*.
  intros * WfC NotIn.
  induction WfC.
  enough (fvars `c`A dom Γ) by fsetdec.
  intros y yIn.
  destruct (H y ltac:(fsetdec)) as [C [R B]]; eapply binds_In...
Qed.

Lemma wf_typ_notin_fv_ct : forall x Γ T,
  Γ ⊢ T wf ->
  x ∉ dom Γ ->
  x ∉ fv_ct T.
Proof with eauto*.
  intros * WfT NotIn.
  induction WfT; simpl.
  - fsetdec.
  - fsetdec.
  - apply AtomSetNotin.notin_union...
    pick fresh y and specialize H0.
    apply notin_fv_ct_open_ct with (C := `cset_fvar` y)...
  - apply AtomSetNotin.notin_union...
    pick fresh Y and specialize H1.
    apply notin_fv_ct_open_tt with (U := Y)...
  - apply (IHWfT NotIn).
  - apply AtomSetNotin.notin_union...
    eapply wf_cset_notin_fvars...
Qed.

(* ********************************************************************** *)
(** * #<a name="regularity"></a># Regularity of relations *)

Lemma subcapt_regular : forall Γ C D,
  Γ ⊢ₛ C <: D ->
  Γ ⊢ₛ C wf /\ Γ ⊢ₛ D wf.
Proof with eauto*.
  intros * SubCapt.
  dependent induction SubCapt; subst...
  - split...
    constructor.
    intros y yInX.
    rewrite AtomSetFacts.singleton_iff in yInX; subst...
  - split...
    constructor.
    + intros y yIn.
      forwards (WfX & _): H1 y yIn.
      inversion WfX; subst.
      rename select (allbound _ _) into HABnd.
      applys HABnd y.
      fsetdec.
Qed.

Lemma sub_regular : forall Γ S T,
  Γ ⊢ S <: T ->
  Γ ⊢ wf /\ Γ ⊢ S wf /\ Γ ⊢ T wf.
Proof with simpl_env; eauto*.
  intros * Sub.
  induction Sub...
  - Case "sub_capt".
    rename select (_ ⊢ₛ _ <: _) into SubCapt.
    destruct (subcapt_regular _ _ _ SubCapt).
    repeat split...
  - Case "sub_arr".
    repeat split...
    + pick fresh x and apply wf_typ_arr...
      * apply wf_typ_capt...
        rename select (_ ⊢ₛ _ <: _) into SubCapt.
        applys subcapt_regular SubCapt.
      * rename select (forall x : atom, x ∉ L -> ([(x, bind_typ (C2 # R2))] ++ Γ) ⊢ wf /\ _ /\ _) into IHSsubT.
        rewrite_nil_concat.
        eapply wf_typ_ignores_typ_bindings.
        apply IHSsubT.
        fsetdec.
    + pick fresh x and apply wf_typ_arr...
      * apply wf_typ_capt...
        rename select (_ ⊢ₛ _ <: _) into SubCapt.
        applys subcapt_regular SubCapt.
      * rewrite_env (∅ ++ [(x, bind_typ (C2 # R2))] ++ Γ).
        eapply wf_typ_ignores_typ_bindings.
        rename select (forall x, _ -> _ /\ _ /\ _) into IHSubT.
        apply IHSubT.
        fsetdec.
  - Case "sub_all".
    repeat split...
    + pick fresh X and apply wf_typ_all...
      rename select (forall x, _ -> _ /\ _ /\ _) into IHSsubT.
      rewrite_nil_concat.
      eapply wf_typ_ignores_sub_bindings.
      apply IHSsubT.
      fsetdec.
    + pick fresh X and apply wf_typ_all...
      rewrite_env (∅ ++ [(X, bind_sub R2)] ++ Γ).
      eapply wf_typ_ignores_sub_bindings.
      rename select (forall x, _ -> _ /\ _ /\ _) into IHSubT.
      apply IHSubT.
      fsetdec.
Qed.

Lemma typing_var_implies_binds : forall Γ (x : atom) T,
  Γ ⊢ x : T ->
  exists C R, binds x (bind_typ (C # R)) Γ.
Proof with eauto*.
  intros * Typ.
  dependent induction Typ...
Qed.

(* REVIEW: not provable???????? *)
(*
Lemma sub_tvar : forall Γ X U,
  Γ ⊢ wf ->
  binds X (bind_sub U) Γ ->
  Γ ⊢ X <: U.
Proof with eauto*.
  intros * Wf.
  generalize dependent U.
  generalize dependent X.
  induction Wf; intros Y U Binds.
  - inversion Binds.
  - binds_cases Binds; simpl_env in *.
    + assert (Neq : X <> Y) by fsetdec. 
      clear Fr.
      rewrite_env (∅ ++ [(X, bind_sub T)] ++ Γ).
      apply sub_weakening...
      apply wf_env_sub...
    + rename select (bind_sub _ = bind_sub _) into Eq.
      injection Eq as Eq; subst.
Admitted.
*)

Lemma sub_pure_type : forall Γ S T,
  Γ ⊢ S <: T ->
  pure_type S <-> pure_type T.
Proof with eauto*.
  intros * Sub.
  split.
  - intros PureS.
    induction Sub; inversion PureS; subst...
    + apply IHSub.
      forwards (WfEnv & _ & _): sub_regular Sub.
      applys wf_typ_env_bind_sub...
    + Case "type_arr".
      pick fresh x and apply type_arr.
      * apply type_capt...
        eapply capt_from_wf_cset.
        rename select (_ ⊢ₛ _ <: _) into SubCapt.
        applys subcapt_regular SubCapt.
      * rename select (forall x : atom, x ∉ L -> _ ⊢ _ <: _) into IHSubCodomain.
        specialize (IHSubCodomain x ltac:(fsetdec)).
        eapply type_from_wf_typ.
        rename select (_ ⊢ _ <: _) into SubT.
        applys sub_regular SubT.
    + Case "type_all".
      pick fresh X and apply type_all...
      rename select (forall X, _ -> _ ⊢ _ <: _) into SubT.
      specialize (SubT X ltac:(fsetdec)).
      eapply type_from_wf_typ.
      rename select (_ ⊢ _ <: _) into Sub'.
      applys sub_regular Sub'.
    + Case "type_box".
      apply type_box.
      eapply type_from_wf_typ.
      rename select (_ ⊢ _ <: _) into Sub'.
      applys sub_regular Sub'.
  - intros PureT.
    induction Sub; inversion PureT; subst...
    + Case "sub_arr".
      pick fresh x and apply type_arr.
      * apply type_capt...
        eapply capt_from_wf_cset.
        rename select (_ ⊢ₛ _ <: _) into SubCapt.
        applys subcapt_regular SubCapt.
      * rename select (forall x, _ -> _ ⊢ _ <: _) into SubT.
        specialize (SubT x ltac:(fsetdec)).
        eapply type_from_wf_typ.
        applys sub_regular SubT.
    + Case "type_all".
      pick fresh X and apply type_all...
      rename select (forall x, _ -> _ ⊢ _ <: _) into SubT.
      specialize (SubT X ltac:(fsetdec)).
      eapply type_from_wf_typ.
      rename select (_ ⊢ _ <: _) into Sub'.
      applys sub_regular Sub'.
    + Case "type_box".
      apply type_box.
      eapply type_from_wf_typ.
      rename select (_ ⊢ _ <: _) into Sub'.
      applys sub_regular Sub'.
Qed.

Lemma sub_capt_type : forall Γ S T,
  Γ ⊢ S <: T ->
  (exists C R, S = C # R) <-> (exists C R, T = C # R).
Proof with eauto*.
  intros * Sub.
  induction Sub; split; intros [C [R EQ]]; try inversion EQ; subst...
  - assert (WfEnv : Γ ⊢ wf) by (applys sub_regular Sub).
    assert (PureU : pure_type U) by (applys wf_typ_env_bind_sub WfEnv H).
    assert (PureCapt : pure_type (C # R)) by (apply (proj1 (sub_pure_type _ _ _ Sub) PureU)).
    inversion PureCapt.
  - inversion select (pure_type (_ # _)). 
Qed.

Lemma typing_regular : forall Γ e T,
  Γ ⊢ e : T ->
  Γ ⊢ wf /\ expr e /\ Γ ⊢ T wf.
Proof with simpl_env; auto*.
  intros * Typ.
  induction Typ.
  - Case "typing_var".
    repeat split...
    rename select (Γ ⊢ wf) into WfEnv.
    rename select (binds _ _ _) into Binds.
    destruct (wf_typ_env_bind_typ _ _ _ WfEnv Binds) as [D [Q [Eq WfCR]]]; symmetry in Eq; inversion Eq; subst; clear Eq.
    inversion WfCR; subst...
    constructor...
    constructor.
    intros y yIn; destruct (y == x); try (contradict n; fsetdec); subst; clear yIn.
    exists C, R...
  - Case "typing_abs".
    pick fresh y; assert (y ∉ L) by fsetdec...
    rename select (forall x, _ -> _ /\ _ /\ _) into IH.
    unshelve epose proof (IH y _) as IHy...
    inversion IHy as [Henv [Hexpr Hwf]]...
    repeat split...
    + inversion Henv...
    + pick fresh x and apply expr_abs.
      * eapply type_from_wf_typ.
        eapply wf_typ_from_wf_env_typ.
        apply Henv.
      * destruct (IH x)...
    + constructor...
      eapply typing_cv with (e := (λ (C # R) e1)) (C := exp_cv e1) (R := ∀ (C # R) T1)...
      * apply typing_abs with (L := L)...
      * eapply wf_typ_arr...
        apply IH.
      * apply type_from_wf_typ in H.
        pick fresh x and apply type_arr...
        eapply type_from_wf_typ with (Γ := [(x, bind_typ (C # R))] ++ Γ).
        apply IH.
        fsetdec.
  - Case "typing_app".
    destruct IHTyp1 as [_ [_ Hwf]].
    inversion Hwf; rename select (_ ⊢ _ wf) into HwfR; subst.
    repeat split...
    apply wf_typ_open_capt with (S := D # Q)...
    destruct (typing_var_implies_binds _ _ _ Typ2) as [C1' [R1' xBinds]].
    constructor.
    intros z zIn; assert (z = x) by (clear - zIn; fsetdec); subst; clear zIn.
    eauto.
  - Case "typing_let".
    repeat split...
    + pick fresh x and apply expr_let...
      assert (x ∉ L) by fsetdec...
      rename select (forall x, _ -> _ ⊢ _ : _) into Typ2.
      rename select (forall x, _ -> _ /\ _ /\ _) into IH.
      unshelve epose proof (Typ2 x _) as Typ2x...
      apply IH...
    + pick fresh x.
      rename select (forall x, _ -> _ /\ _ /\ _) into IH.
      destruct (IH x ltac:(fsetdec)) as [_ [_ WfT2]].
      assert (Γ ⊢ T2 wf).
      { rewrite_env (∅ ++ Γ).
        eapply wf_typ_strengthen with (x := x) (U := C1 # T1)...
      }
      assumption.
  - Case "typing_tabs".
    pick fresh Y; assert (Y ∉ L) by fsetdec...
    rename select (forall x, _ -> _ /\ _ /\ _) into IH.
    unshelve epose proof (IH Y _) as IHY...
    inversion IHY as [Henv [Hexpr Hwf]]...
    repeat split...
    + inversion Henv...
    + pick fresh X and apply expr_tabs...
      destruct (IH X)...
    + constructor...
      eapply typing_cv with (e := (exp_tabs V e1)) (C := exp_cv e1) (R := ∀ [V] T1)...
      * apply typing_tabs with (L := L)...
      * eapply wf_typ_all; trivial.
        apply IH.
      * apply type_from_wf_typ in H.
        pick fresh X and apply type_all...
        eapply type_from_wf_typ with (Γ := [(X, bind_sub V)] ++ Γ).
        apply IH.
        fsetdec.
  - Case "typing_tapp".
    destruct IHTyp as [HwfΓ [Hexpr Hwf]]...
    rename select (_ ⊢ _ <: _) into Sub.
    forwards (R1 & R2 & R3): sub_regular Sub...
    assert (PureQ : pure_type Q).
    { enough (PureQT : pure_type (∀ [Q] T)) by (inversion PureQT; assumption).
      enough (TypeCQT : type (C # ∀ [Q] T)) by (inversion TypeCQT; subst; [ inversion H | assumption ]).
      eapply type_from_wf_typ, Hwf.
    }
    assert (PureP : pure_type P) by (apply (proj2 (sub_pure_type _ _ _ Sub) PureQ)).
    repeat split...
    apply wf_typ_open_type with (R := Q); inversion Hwf; subst...
  - Case "typing_box".
    repeat split...
    apply wf_typ_capt...
    apply type_box.
    eapply type_from_wf_typ.
    applys IHTyp.
  - Case "typing_unbox".
    destruct IHTyp as [HwfΓ [Hex Hwf]].
    inversion Hwf; rename select (_ ⊢ (_ # _) wf) into WfEbCR;
    inversion WfEbCR; rename select (_ ⊢ (□ C # R) wf) into WfbCR;
    inversion WfbCR; subst.
    repeat split...
    apply expr_unbox.
    eapply capt_from_wf_cset...
    eassumption.
  - Case "typing_sub".
    destruct IHTyp as [HwfΓ [Hex Hwf]].
    repeat split...
    eapply sub_regular; eassumption.
Qed.

Lemma value_regular : forall e,
  value e ->
  expr e.
Proof.
  intros e H. induction H; auto.
Qed.

Lemma eval_typing_regular : forall Γ K T U,
  Γ ⊢ K : T ⇒ U ->
  Γ ⊢ wf /\ Γ ⊢ T wf /\ Γ ⊢ U wf.
Proof with eauto*.
  intros * EvalTyp.
  induction EvalTyp.
  - rename select (_ ⊢ _ <: _) into Sub.
    destructs sub_regular Sub.
    repeat split...
  - pick fresh x and specialize H.
    destructs typing_regular H as [wf_xTE _].
    inversion wf_xTE; subst...
Qed.

Lemma exp_cv_binds_typ : forall Γ e (x : atom) S,
  Γ ⊢ e : S ->
  x ∈ `cset_fvars` (exp_cv e) ->
  exists C R, binds x (bind_typ (C # R)) Γ.
Proof with eauto using wf_cset_over_union.
  intros * Typ xIn.
  induction Typ; simpl in *...
  - assert (x = x0) by fsetdec; subst...
  - pick fresh y.
    forwards HA: H1 y.
    + notin_solve.
    + forwards (? & ? & ?): exp_cv_open_ve_rec e1 0 y.
      unfold open_ve.
      clear Fr;fsetdec.
    + destruct HA as (D & Q & HA)...
      inversion HA.
      assert (x <> y) by notin_solve.
      destruct (x == y)...
      easy.
  - destruct_union_mem xIn...
  - pick fresh y.
    destruct (cset_references_fvar_over_union _ _ _ xIn).
    + apply IHTyp...
    + forwards HA: H0 y.
      * notin_solve.
      * assert (cset_subset_prop (exp_cv e) (exp_cv (open_ve e y (`cset_fvar` y)))) by apply (exp_cv_open_ve_rec e 0 y).
        assert (cset_subset_prop (exp_cv k) (exp_cv (open_ve k y (`cset_fvar` y)))) by apply (exp_cv_open_ve_rec k 0 y).
        clear - xIn H1 H2 H3 IHTyp.
        rewrite <- fvars_union_1 in xIn.
        apply subset_in with (A := exp_cv k)...
      * destruct HA as (D & Q & HA)...
        inversion HA.
        assert (x <> y) by notin_solve.
        destruct (x == y)...
        easy.
  - pick fresh y.
    forwards HA: H2 y.
    + notin_solve.
    + forwards (? & ? & ?): exp_cv_open_te_rec e1 0 y.
      clear Fr; fsetdec.
    + destruct HA as (D & Q & HA)...
      inversion HA.
      assert (x <> y) by notin_solve.
      destruct (x == y)...
      easy.
  - exfalso; clear - xIn; fsetdec.
  - destruct (AtomSet.F.union_1 xIn)...
    clear IHTyp xIn.
    rename select (_ ⊢ₛ _ wf) into WfC.
    rename select (x ∈ _) into xIn.
    destruct WfC as [fvars univ AllBound].
    destruct (AllBound x xIn) as [D [Q B]].
    exists D, Q...
Qed.

(* *********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

(** The lemma [ok_from_wf_env] was already added above as a hint since it
    helps blur the distinction between [wf_env] and [ok] in proofs.

    As currently stated, the regularity lemmas are ill-suited to be
    used with [auto] and [eauto] since they end in conjunctions.  Even
    if we were, for example, to split [sub_regularity] into three
    separate lemmas, the resulting lemmas would be usable only by
    [eauto] and there is no guarantee that [eauto] would be able to
    find proofs effectively.  Thus, the hints below apply the
    regularity lemmas and [type_from_wf_typ] to discharge goals about
    local closure and well-formedness, but in such a way as to
    minimize proof search.

    The first hint introduces an [wf_env] fact into the context.  It
    works well when combined with the lemmas relating [wf_env] and
    [wf_typ].  We choose to use those lemmas explicitly via [(auto
    using ...)] tactics rather than add them as hints.  When used this
    way, the explicitness makes the proof more informative rather than
    more cluttered (with useless details).

    The other three hints try outright to solve their respective
    goals. *)

Hint Extern 1 (wf_cset ?E ?C) =>
  match goal with
  | H: subcapt _ C _ |- _ => apply (proj1 (subcapt_regular _ _ _ H))
  | H: subcapt _ _ C |- _ => apply (proj2 (subcapt_regular _ _ _ H))
  end
: core.

Hint Extern 1 (wf_env ?E) =>
  match goal with
  | H: sub _ _ _ |- _ => apply (proj1 (sub_regular _ _ _ H))
  | H: typing _ _ _ _ |- _ => apply (proj1 (typing_regular _ _ _ _ H))
  end
: core.

Hint Extern 1 (wf_typ ?E ?T) =>
  match goal with
  | H: typing E _ _ T |- _ => apply (proj2 (proj2 (typing_regular _ _ _ _ H)))
  | H: sub E T _ |- _ => apply (proj1 (proj2 (sub_regular _ _ _ H)))
  | H: sub E _ T |- _ => apply (proj2 (proj2 (sub_regular _ _ _ H)))
  end
: core.

Hint Extern 1 (type ?T) =>
  let go E := eapply (type_from_wf_typ E); eauto in
  match goal with
  | H: typing ?E _ _ T |- _ => go E
  | H: sub ?E T _ |- _ => go E
  | H: sub ?E _ T |- _ => go E
  | H: wf_typ ?E _ _ T |- _ => go E
  end
: core.

Hint Extern 1 (capt ?C) =>
  let go E := eapply (capt_from_wf_cset E); eauto in
  match goal with
  | H: subcapt ?E C _ |- _ => go E
  | H: subcapt ?E _ C |- _ => go E
  | H: exp_cv ?E _ C |- _ => go E
  end
: core.

Hint Extern 1 (expr ?e) =>
  match goal with
  | H: typing _ _ ?e _ |- _ => apply (proj1 (proj2 (typing_regular _ _ _ _ H)))
  (* | H: red ?e _ |- _ => apply (proj1 (red_regular _ _ H)) *)
  (* | H: red _ ?e |- _ => apply (proj2 (red_regular _ _ H)) *)
  end
: core.

(** * #<a name="auto"></a># Automation Tests *)

Local Lemma test_subcapt_regular : forall Γ C1 C2,
  Γ ⊢ₛ C1 <: C2 ->
  Γ ⊢ₛ C1 wf /\ Γ ⊢ₛ C2 wf.
Proof with eauto*.
  intros.
  repeat split.
  all: auto.
Qed.