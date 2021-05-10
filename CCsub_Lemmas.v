Require Import Coq.Program.Equality.

Require Export CCsub_Infrastructure.
Require Import Atom.

(* ********************************************************************** *)
(** * #<a name="wft"></a># Utils *)

Lemma ok_tail : forall (F E : env),
  ok (F ++ E) ->
  ok E.
Proof.
  intros.
  rewrite_env (empty ++ F ++ E) in H.
  rewrite_env (empty ++ E).
  eapply ok_remove_mid; eauto.
Qed.

Hint Extern 1 (ok ?E) =>
match goal with
  | H : ok (?F ++ E) |- _ =>
    apply (ok_tail F E)
end : core.

Ltac clear_frees :=
  repeat match goal with
         | H : _ `notin` _ |- _ =>
           clear H
         end.

Ltac prepare_for_fsetdec :=
  clear_frees; simpl_env in *.

Hint Extern 10 (AtomSet.F.Subset _ _) =>
(* idtac "go fsetdec go" ; *)
(* NOTE: "free" hypothesis are unlikely to help with subsets and they can cause fsetdec to hang *)
try solve [prepare_for_fsetdec; fsetdec]
: core.

(* ********************************************************************** *)
(** * #<a name="wft"></a># Properties of [wf_typ] *)

(** If a type is well-formed in an environment, then it is locally
    closed. *)

Lemma capt_from_wf_cset : forall E A C,
  wf_cset E A C -> capt C.
Proof with auto.
  intros.
  inversion H...
Qed.

Lemma type_from_wf_typ : forall E Ap Am T,
  wf_typ E Ap Am T -> type T
with pretype_from_wf_pretyp : forall E Ap Am T,
  wf_pretyp E Ap Am T -> pretype T.
Proof with eauto using capt_from_wf_cset.
------
  intros *. intros H.
  induction H.
  econstructor.
  econstructor...
------
  intros *. intros H.
  induction H.
  - trivial.
  - pick fresh X and apply type_arrow...
  - pick fresh X and apply type_all...
Qed.

(** This is a useful helper tactic for clearing away
    capture set wellformedness. *)

Ltac wf_cset_simpl instantiate_ext :=
  match goal with
  | H : _ |- (wf_cset _ _ cset_universal) =>
    constructor
  | H : (wf_cset _ _ ?C) |- (wf_cset _ _ ?C) =>
    let Hdestruct := fresh "Hdestruct" in
    let x  := fresh "x" in
    let Hx := fresh "Hxin" in
    let Hexists := fresh "Hexists" in
    let T := fresh "T" in
    let Hbound := fresh "Hbound" in
    let E := fresh "E" in
    let A := fresh "A" in
    let fvars := fresh "fvars" in
    let Hclosed := fresh "Hclosed" in
    inversion H as [E A fvars univ Hbound Hclosed]; subst; [
      constructor; [
        unfold allbound_typ in Hbound;
        intros x Hx;
        destruct (Hbound x Hx) as [T Hexists];
        lazymatch instantiate_ext with
        | True => exists T
        | False => idtac
        end |
        fsetdec
      ]
    ]
  end.

Lemma wf_cset_weakening : forall E A A' F G C,
    wf_cset (G ++ E) A C ->
    ok (G ++ F ++ E) ->
    AtomSet.F.Subset A A' ->
    wf_cset (G ++ F ++ E) A' C.
Proof with auto*.
  intros *.
  intros Hcset Henv Hpres.
  wf_cset_simpl True...
Qed.

Lemma wf_cset_set_weakening : forall E A A' C,
  wf_cset E A C ->
  AtomSet.F.Subset A A' ->
  wf_cset E A' C.
Proof with eauto*.
  intros.
  inversion H; constructor...
Qed.

Lemma wf_cset_weaken_head : forall C E A F,
  wf_cset E A C ->
  ok (F ++ E) ->
  wf_cset (F ++ E) A C.
Proof.
  intros.
  rewrite_env (empty ++ F++ E).
  apply wf_cset_weakening with (A := A); auto.
Qed.

Local Lemma atomset_union_right : forall A B C,
  AtomSet.F.Subset A B ->
  AtomSet.F.Subset (A `union` C) (B `union` C).
Proof.
  intros.
  fsetdec.
Qed.

Lemma wf_typ_weakening : forall T E Ap Am Ap' Am' F G,
  wf_typ (G ++ E) Ap Am T ->
  ok (G ++ F ++ E) ->
  AtomSet.F.Subset Ap Ap' ->
  AtomSet.F.Subset Am Am' ->
  wf_typ (G ++ F ++ E) Ap' Am' T
with wf_pretyp_weakening : forall T E Ap Am Ap' Am' F G,
  wf_pretyp (G ++ E) Ap Am T ->
  ok (G ++ F ++ E) ->
  AtomSet.F.Subset Ap Ap' ->
  AtomSet.F.Subset Am Am' ->
  wf_pretyp (G ++ F ++ E) Ap' Am' T.
Proof with simpl_env; eauto using wf_cset_weakening.
------
  intros.
  remember (G ++ E).
  generalize dependent G.
  induction H; intros G Hok Heq; subst.
  - apply wf_typ_var with (U := U)...
  - apply wf_typ_capt...
------
  intros.
  remember (G ++ E).
  generalize dependent G.
  induction H; intros G Hok Heq; subst.
  - apply wf_typ_top.
  (* typ_arrow case *)
  - pick fresh Y and apply wf_typ_arrow.
    eapply wf_typ_weakening...
    rewrite <- concat_assoc.
    eapply wf_typ_weakening...
  (* typ_all case *)
  - pick fresh Y and apply wf_typ_all.
    eapply wf_typ_weakening...
    rewrite <- concat_assoc.
    eapply wf_typ_weakening...
Qed.

Lemma wf_typ_weaken_head : forall T E Ap Am Ap' Am' F,
  wf_typ E Ap Am T ->
  ok (F ++ E) ->
  AtomSet.F.Subset Ap Ap' ->
  AtomSet.F.Subset Am Am' ->
  wf_typ (F ++ E) Ap' Am' T.
Proof.
  intros.
  rewrite_env (empty ++ F ++ E).
  apply wf_typ_weakening with (Ap := Ap) (Am := Am); eauto || fsetdec.
Qed.

Lemma wf_typ_set_weakening : forall E Ap Am Ap' Am' T,
  wf_typ E Ap Am T ->
  ok E ->
  AtomSet.F.Subset Ap Ap' ->
  AtomSet.F.Subset Am Am' ->
  wf_typ E Ap' Am' T
with wf_pretyp_set_weakening : forall E Ap Am Ap' Am' T,
  wf_pretyp E Ap Am T ->
  ok E ->
  AtomSet.F.Subset Ap Ap' ->
  AtomSet.F.Subset Am Am' ->
  wf_pretyp E Ap' Am' T.
Proof.
------
  intros.
  rewrite_env (empty ++ empty ++ E).
  rewrite_env (empty ++ E) in H.
  eapply wf_typ_weakening; eauto.
------
  intros.
  rewrite_env (empty ++ empty ++ E).
  rewrite_env (empty ++ E) in H.
  eapply wf_pretyp_weakening; eauto.
Qed.

(* Type bindings don't matter at all! *)
Lemma wf_cset_narrowing_base : forall V U C E A F X,
  wf_cset (F ++ [(X, bind_sub V)] ++ E) A C ->
  ok (F ++ [(X, bind_sub U)] ++ E) ->
  wf_cset (F ++ [(X, bind_sub U)] ++ E) A C.
Proof with simpl_env; eauto.
  intros *.
  intros Hwf Hok.
  wf_cset_simpl True...
  binds_cases Hexists...
Qed.

Lemma wf_typ_narrowing_base : forall V U T E Ap Am F X,
  wf_typ (F ++ [(X, bind_sub V)] ++ E) Ap Am T ->
  ok (F ++ [(X, bind_sub U)] ++ E) ->
  wf_typ (F ++ [(X, bind_sub U)] ++ E) Ap Am T
with wf_pretyp_narrowing_base : forall V U T E Ap Am F X,
  wf_pretyp (F ++ [(X, bind_sub V)] ++ E) Ap Am T ->
  ok (F ++ [(X, bind_sub U)] ++ E) ->
  wf_pretyp (F ++ [(X, bind_sub U)] ++ E) Ap Am T.
Proof with simpl_env; eauto using wf_cset_narrowing_base.
------
  intros.
  remember (F ++ [(X, bind_sub V)] ++ E).
  generalize dependent F.
  induction H; intros F Hok Heq; subst.
  (* typ_var *)
  - binds_cases H.
    + apply wf_typ_var with (U := U0)...
    + apply wf_typ_var with (U := U)...
    + apply wf_typ_var with (U := U0)...
  - apply wf_typ_capt...
------
  intros.
  remember (F ++ [(X, bind_sub V)] ++ E).
  generalize dependent F.
  induction H; intros F Hok Heq; subst; try solve [econstructor].
  (* typ_arrow *)
  - pick fresh Y and apply wf_typ_arrow...
    rewrite <- concat_assoc.
    eapply wf_typ_narrowing_base...
  (* typ_all *)
  - pick fresh Y and apply wf_typ_all...
    rewrite <- concat_assoc.
    eapply wf_typ_narrowing_base...
Qed.

Lemma wf_cset_narrowing_typ_base : forall C1 C2 C E A F X,
  wf_cset (F ++ [(X, bind_typ C1)] ++ E) A C ->
  ok (F ++ [(X, bind_typ C2)] ++ E) ->
  wf_cset (F ++ [(X, bind_typ C2)] ++ E) A C.
Proof with simpl_env; eauto.
  intros *. intros Hwf Hok.
  wf_cset_simpl False.
  binds_cases Hexists...
Qed.

Lemma wf_typ_narrowing_typ_base : forall V U T E Ap Am F X,
  wf_typ (F ++ [(X, bind_typ V)] ++ E) Ap Am T ->
  ok (F ++ [(X, bind_typ U)] ++ E) ->
  wf_typ (F ++ [(X, bind_typ U)] ++ E) Ap Am T
with wf_pretyp_narrowing_typ_base : forall V U T E Ap Am F X,
  wf_pretyp (F ++ [(X, bind_typ V)] ++ E) Ap Am T ->
  ok (F ++ [(X, bind_typ U)] ++ E) ->
  wf_pretyp (F ++ [(X, bind_typ U)] ++ E) Ap Am T.
Proof with simpl_env; eauto using wf_cset_narrowing_typ_base.
------
  intros *. intros Hwf_typ Hok.
  remember (F ++ [(X, bind_typ V)] ++ E).
  generalize dependent F.
  induction Hwf_typ; intros F Hok Heq; subst.
  - binds_cases H...
  - econstructor...
------
  intros *. intros Hwf_typ Hok.
  remember (F ++ [(X, bind_typ V)] ++ E).
  generalize dependent F.
  induction Hwf_typ; intros F Hok Heq; subst.
  - constructor.
  - Case "typ_arrow".
    pick fresh Y and apply wf_typ_arrow...
    rewrite <- concat_assoc.
    eapply wf_typ_narrowing_typ_base...
  - Case "typ_all".
    pick fresh Y and apply wf_typ_all...
    rewrite <- concat_assoc.
    eapply wf_typ_narrowing_typ_base...
Qed.

Hint Extern 5 (wf_typ ?E _ _ ?T) =>
match goal with
| H : (wf_typ E ?Ap0 ?Am0 T) |- _ =>
  apply wf_typ_set_weakening with (Ap := Ap0) (Am := Am0)
| H : (wf_typ_in E T) |- _ =>
  unfold wf_typ_in in H; apply wf_typ_set_weakening with (Ap := (dom E)) (Am := (dom E))
end : core.


(** Substitution lemmas *)
Lemma wf_cset_subst_tb : forall F Q E Ap Am Z P C,
  wf_cset (F ++ [(Z, bind_sub Q)] ++ E) Ap C ->
  wf_typ E Ap Am P ->
  ok (map (subst_tb Z P) F ++ E) ->
  wf_cset (map (subst_tb Z P) F ++ E) Ap C.
Proof with simpl_env; eauto*.
  intros *. intros HwfC HwfP Hok.
  wf_cset_simpl False...
  binds_cases Hexists...
  * exists (subst_tt Z P T)...
Qed.

Lemma wf_typ_subst_tb : forall F Q E Ap Am Z P T,
  wf_typ (F ++ [(Z, bind_sub Q)] ++ E) Ap Am T ->
  (** NOTE here that P needs to be well formed in both the + and - environments, *)
(*       as we're substituting in both places. *)
  wf_typ E Ap Am P ->
  wf_typ E Am Ap P ->
  ok (map (subst_tb Z P) F ++ E) ->
  wf_typ (map (subst_tb Z P) F ++ E) Ap Am (subst_tt Z P T)
with wf_pretyp_subst_tb : forall F Q E Ap Am Z P T,
  wf_pretyp (F ++ [(Z, bind_sub Q)] ++ E) Ap Am T ->
  wf_typ E Ap Am P ->
  wf_typ E Am Ap P ->
  ok (map (subst_tb Z P) F ++ E) ->
  wf_pretyp (map (subst_tb Z P) F ++ E) Ap Am (subst_tpt Z P T).
Proof with simpl_env; eauto using wf_typ_weaken_head, type_from_wf_typ, wf_cset_subst_tb.
------
  intros *. intros HwfT HwfPp HwfPm Hok.
  remember (F ++ [(Z, bind_sub Q)] ++ E).
  generalize dependent F.
  induction HwfT; intros F EQF Hok; subst; simpl subst_tt.
  - Case "wf_typ_var".
    destruct (X == Z); subst...
    + SCase "X <> Z".
      unfold wf_typ_in in *.
      binds_cases H...
      apply (wf_typ_var (subst_tt Z P U))...
  - unfold wf_typ_in in *.
    econstructor...
------
  intros *. intros HwfT HwfPp HwfPm Hok.
  remember (F ++ [(Z, bind_sub Q)] ++ E).
  generalize dependent F.
  induction HwfT; intros F EQF Hok; subst; simpl subst_tt.
  - constructor.
  - Case "wf_typ_arrow".
    pick fresh Y and apply wf_typ_arrow...
    + SCase "T2".
      unfold open_ct in *...
      rewrite <- subst_tt_open_ct_rec...
      rewrite_env (map (subst_tb Z P) ([(Y, bind_typ T1)] ++ F) ++ E).
      eapply wf_typ_subst_tb...
      * apply wf_typ_set_weakening with (Ap := Ap) (Am := Am)...
  - Case "wf_typ_all".
    pick fresh Y and apply wf_typ_all...
    + SCase "T2".
      unfold open_ct in *...
      rewrite subst_tt_open_tt_var...
      rewrite_env (map (subst_tb Z P) ([(Y, bind_sub T1)] ++ F) ++ E).
      eapply wf_typ_subst_tb...
Qed.

Lemma wf_cset_over_subst : forall F Q E A Z C C',
  ok (map (subst_cb Z C) F ++ E) ->
  wf_cset E A C ->
  wf_cset (F ++ [(Z, bind_typ Q)] ++ E) A C' ->
  ok (F ++ [(Z, bind_typ Q)] ++ E) ->
  wf_cset (map (subst_cb Z C) F ++ E) (A `remove` Z) (subst_cset Z C C').
Proof with eauto*.
    intros F Q E A Z C C'.
    intros HokFE HwfC HwfC' Hok.
    inversion HwfC; inversion HwfC'; subst...
    (** Case analysis : this should maybe go through better, hopefully? *)
    + unfold subst_cset; try constructor...
    find_and_destroy_if.
      destruct_set_mem Z (cset_set fvars0 {}N univ0)...
      {
        csetdecplus.
        constructor...
        intros x Hfvx.
        specialize (H2 _ Hfvx).
        rewrite cset_not_references_fvar_eq in H_destruct...
        csethyp.
        assert (x <> Z) by fsetdec.
        inversion H2 as [T H0]...
        binds_cases H0...
        exists (subst_ct Z cset_universal T)...
      }
      {
        rewrite cset_not_references_fvar_eq in H_destruct...
        csethyp.
        fsetdec.
      }
    +
      assert (fvars `subset` dom E). {
        unfold allbound_typ in *. intros fv Hfv.
        specialize (H fv Hfv) as [T Hbinds].
        apply binds_In in Hbinds. assumption.
      }
      assert (Z `notin` dom E). {
        apply fresh_mid_tail in Hok.
        assumption.  
      }
      unfold subst_cset...
      cset_split; inversion HwfC; inversion HwfC';
      try rewrite cset_not_references_fvar_eq in H_destruct;
      try rewrite cset_references_fvar_eq in H_destruct;
      assert (NatSet.F.union {}N {}N = {}N) as Hunion by (fnsetdec; eauto*); subst;
      try rewrite Hunion in *; constructor; unfold allbound_typ in *; intros...
      {
        assert (x `in` (fvars `union` fvars0)) as Hfv by fsetdec.
        assert (x <> Z) by fsetdec.
        rewrite AtomSetFacts.union_iff in Hfv...
        inversion Hfv...
        + specialize (H _ H8).
          inversion H as [T H10].
          exists T...
        + specialize (H4 _ H8).
          destruct H4 as [T Hbinds].
          binds_cases Hbinds; subst...
          eexists (subst_ct Z _ T).
          apply binds_head...
      }
      {
        assert ((fvars `union` fvars0) `subset` A) by fsetdec.
        assert (((fvars `union` fvars0) `remove` Z) `subset` (A `remove` Z)) by fsetdec.
        (** Z is not in fvars as Z is not in dom(E) *)
        fsetdec.
      }
      {
        specialize (H11 _ H3)...
        inversion H11 as [T H10].
        binds_cases H10; subst...
        {
          csethyp.
          fsetdec.
        }
        {
          exists (subst_ct Z (cset_set fvars {}N) T)...
        }
      }
      {
        csethyp.
        fsetdec.
      }
Qed.
Lemma wf_typ_subst_cb : forall F Q E Ap Am Z C T,
  wf_typ (F ++ [(Z, bind_typ Q)] ++ E) Ap Am T ->
  wf_cset E Ap C ->
  wf_cset E Am C ->
  ok (map (subst_cb Z C) F ++ E) ->
  ok (F ++ [(Z, bind_typ Q)] ++ E) ->
  wf_typ (map (subst_cb Z C) F ++ E)
         (Ap `remove` Z) (Am `remove` Z)
         (subst_ct Z C T)
with wf_pretyp_subst_cb : forall F Q E Ap Am Z C T,
  wf_pretyp (F ++ [(Z, bind_typ Q)] ++ E) Ap Am T ->
  wf_cset E Ap C ->
  wf_cset E Am C ->
  ok (map (subst_cb Z C) F ++ E) ->
  ok (F ++ [(Z, bind_typ Q)] ++ E) ->
  wf_pretyp (map (subst_cb Z C) F ++ E)
            (Ap `remove` Z) (Am `remove` Z)
            (subst_cpt Z C T).
Proof with simpl_env; eauto using wf_typ_weaken_head, type_from_wf_typ, wf_cset_subst_tb,
    capt_from_wf_cset.
------
  intros *. intros HwfT HwfCp HwfCm Hok HokZ.
  remember (F ++ [(Z, bind_typ Q)] ++ E).
  generalize dependent F.
  induction HwfT; intros F ? Hok; subst; simpl subst_ct...
  - Case "wf_typ_var".
    binds_cases H...
    apply (wf_typ_var (subst_ct Z C U))...
  - Case "wf_typ_capt".
    constructor...
    apply wf_cset_over_subst with (Q := Q)...
------
  intros *. intros HwfT HwfCp HwfCm Hok HokZ.
  remember (F ++ [(Z, bind_typ Q)] ++ E).
  generalize dependent F.
  induction HwfT; intros F ? Hok; subst; simpl subst_ct.
  - constructor.
  - Case "wf_typ_arrow".
    pick fresh Y and apply wf_typ_arrow.
    all : fold subst_ct...
    + SCase "T2".
      unfold open_ct in *...
      rewrite <- subst_ct_open_ct_rec...
      rewrite_env (map (subst_cb Z C) ([(Y, bind_typ T1)] ++ F) ++ E).
      replace (Ap `remove` Z `union` singleton Y)
        with ((Ap `union` singleton Y) `remove` Z).
      2: {
        assert (Y `notin` singleton Z) by notin_solve.
        clear Fr.
        fsetdec.
      }
      apply wf_typ_subst_cb with (Q := Q)...
      * apply wf_cset_set_weakening with (A := Ap)...
      * econstructor...
      * unfold cset_references_fvar, cset_all_fvars.
        simpl.
        notin_solve.
  - Case "wf_typ_all".
    pick fresh Y and apply wf_typ_all; fold subst_ct...
    + SCase "T2".
      unfold open_ct in *...
      rewrite subst_ct_open_tt_var...
      rewrite_env (map (subst_cb Z C) ([(Y, bind_sub T1)] ++ F) ++ E).
      eapply wf_typ_subst_cb...
Qed.

Lemma wf_typ_subst_cb' : forall F Q E Z T C,
  wf_typ_in (F ++ [(Z, bind_typ Q)] ++ E) T ->
  wf_cset_in E C ->
  ok (F ++ [(Z, bind_typ Q)] ++ E) ->
  ok (map (subst_cb Z C) F ++ E) ->
  wf_typ_in (map (subst_cb Z C) F ++ E) (subst_ct Z C T).
Proof with eauto.
  intros.
  unfold wf_typ_in.
  simpl_env.
  replace (dom F `union` dom E)
    with ((dom F `union` singleton Z `union` dom E) `remove` Z).
  2: {
    (* Z is not in dom F nor in dom E. *)
    assert (Z `notin` dom F). {
      apply fresh_mid_head in H1.
      assumption.
    }
    assert (Z `notin` dom E). {
      apply fresh_mid_tail in H1.
      assumption.
    }
    fsetdec.
  }
  apply wf_typ_subst_cb with (Q := Q)...
  eapply wf_cset_set_weakening...
  eapply wf_cset_set_weakening...
Qed.

Lemma wf_typ_open_capt : forall E C T1 T2,
  ok E ->
  wf_pretyp_in E (typ_arrow T1 T2) ->
  wf_cset_in E C ->
  wf_typ_in E (open_ct T2 C).
Proof with simpl_env; eauto.
  intros E C T1 T2 Hok HwfA HwfC.
  inversion HwfA; subst...
  pick fresh X.
  rewrite (subst_ct_intro X)...
  rewrite_env (map (subst_cb X C) empty ++ E).
  (** another lemma needed *)
  eapply wf_typ_subst_cb' with (Q := T1)...
  assert (X `notin` L) by fsetdec.
  specialize (H5 X H).
  unfold wf_typ_in...
Qed.


Lemma wf_cset_narrowing : forall F E x Q P C,
  wf_cset_in (F ++ [(x, bind_sub Q)] ++ E) C ->
  ok (F ++ [(x, bind_sub P)] ++ E) ->
  wf_cset_in (F ++ [(x, bind_sub P)] ++ E) C.
Proof with eauto using wf_cset_narrowing_base.
  intros.
  unfold wf_cset_in in *.
  simpl_env in *...
Qed.

Lemma wf_cset_narrowing_typ : forall F E x Q P C,
  wf_cset_in (F ++ [(x, bind_typ Q)] ++ E) C ->
  ok (F ++ [(x, bind_typ P)] ++ E) ->
  wf_cset_in (F ++ [(x, bind_typ P)] ++ E) C.
Proof with eauto using wf_cset_narrowing_typ_base.
  intros.
  unfold wf_cset_in in *.
  simpl_env in *...
Qed.

Lemma wf_typ_narrowing : forall F E Z Q P T,
  wf_typ_in (F ++ [(Z, bind_sub Q)] ++ E) T ->
  ok (F ++ [(Z, bind_sub P)] ++ E) ->
  wf_typ_in (F ++ [(Z, bind_sub P)] ++ E) T.
Proof with eauto using wf_typ_narrowing_base.
  intros.
  unfold wf_typ_in in *.
  simpl_env in *...
Qed.

Lemma wf_typ_narrowing_typ : forall F E Z Q P T,
  wf_typ_in (F ++ [(Z, bind_typ Q)] ++ E) T ->
  ok (F ++ [(Z, bind_typ P)] ++ E) ->
  wf_typ_in (F ++ [(Z, bind_typ P)] ++ E) T.
Proof with eauto using wf_typ_narrowing_typ_base.
  intros *.
  unfold wf_typ_in in *.
  simpl_env in *...
Qed.

Lemma wf_pretyp_narrowing : forall F E Z Q P T,
  wf_pretyp_in (F ++ [(Z, bind_sub Q)] ++ E) T ->
  ok (F ++ [(Z, bind_sub P)] ++ E) ->
  wf_pretyp_in (F ++ [(Z, bind_sub P)] ++ E) T.
Proof with eauto using wf_pretyp_narrowing_base.
  intros.
  unfold wf_pretyp_in in *.
  simpl_env in *...
Qed.

Lemma wf_pretyp_narrowing_typ : forall F E Z Q P T,
  wf_pretyp_in (F ++ [(Z, bind_typ Q)] ++ E) T ->
  ok (F ++ [(Z, bind_typ P)] ++ E) ->
  wf_pretyp_in (F ++ [(Z, bind_typ P)] ++ E) T.
Proof with eauto using wf_pretyp_narrowing_typ_base.
  intros *.
  unfold wf_pretyp_in in *.
  simpl_env in *...
Qed.


Lemma wf_cset_ignores_typ_bindings : forall E F x T1 T2 Ap C,
  wf_cset (F ++ [(x, bind_typ T1)] ++ E) Ap C ->
  wf_cset (F ++ [(x, bind_typ T2)] ++ E) Ap C.
Proof with eauto.
  intros*.
  intros H.
  remember (F ++ [(x, bind_typ T1)] ++ E).
  generalize dependent F.
  induction H; intros F Eq; subst...
  econstructor... unfold allbound_typ in *.
  intros.
  destruct (H x0 H1) as [T Hb].
  binds_cases Hb...
Qed.

Lemma wf_cset_ignores_sub_bindings : forall E F x T1 T2 Ap C,
  wf_cset (F ++ [(x, bind_sub T1)] ++ E) Ap C ->
  wf_cset (F ++ [(x, bind_sub T2)] ++ E) Ap C.
Proof with eauto.
  intros*.
  intros H.
  remember (F ++ [(x, bind_sub T1)] ++ E).
  generalize dependent F.
  induction H; intros F Eq; subst...
  econstructor... unfold allbound_typ in *.
  intros.
  destruct (H x0 H1) as [T Hb].
  binds_cases Hb...
Qed.

Lemma wf_typ_ignores_typ_bindings : forall E F x T1 T2 Ap Am T,
  wf_typ (F ++ [(x, bind_typ T1)] ++ E) Ap Am T ->
  wf_typ (F ++ [(x, bind_typ T2)] ++ E) Ap Am T
with wf_pretyp_ignores_typ_bindings : forall E F x T1 T2 Ap Am T,
  wf_pretyp (F ++ [(x, bind_typ T1)] ++ E) Ap Am T ->
  wf_pretyp (F ++ [(x, bind_typ T2)] ++ E) Ap Am T.
Proof with eauto.
------
  intros*.
  intros H.
  remember (F ++ [(x, bind_typ T1)] ++ E).
  generalize dependent F.
  induction H; intros F Eq; subst.
  - apply wf_typ_var with (U := U)...
    binds_cases H...
  (* requires wf_cset_ignores_bindings *)
  - econstructor... eapply wf_cset_ignores_typ_bindings...
------
  intros*.
  intros H.
  remember (F ++ [(x, bind_typ T1)] ++ E).
  generalize dependent F.
  induction H; intros F Eq; subst.
  - econstructor.
  - pick fresh X and apply wf_typ_arrow.
    + eapply wf_typ_ignores_typ_bindings...
    + rewrite_parenthesise_binding.
      eapply wf_typ_ignores_typ_bindings with (T1 := T1)...
      eapply H0...
  - pick fresh X and apply wf_typ_all.
    + eapply wf_typ_ignores_typ_bindings...
    + rewrite_parenthesise_binding.
      eapply wf_typ_ignores_typ_bindings with (T1 := T1)...
      eapply H0...
Qed.

Lemma wf_typ_ignores_sub_bindings : forall E F x T1 T2 Ap Am T,
  ok (F ++ [(x, bind_sub T1)] ++ E) ->
  wf_typ (F ++ [(x, bind_sub T1)] ++ E) Ap Am T ->
  wf_typ (F ++ [(x, bind_sub T2)] ++ E) Ap Am T
with wf_pretyp_ignores_sub_bindings : forall E F x T1 T2 Ap Am T,
  ok (F ++ [(x, bind_sub T1)] ++ E) ->
  wf_pretyp (F ++ [(x, bind_sub T1)] ++ E) Ap Am T ->
  wf_pretyp (F ++ [(x, bind_sub T2)] ++ E) Ap Am T.
Proof with eauto.
------
  intros*.
  intros Hok H.
  remember (F ++ [(x, bind_sub T1)] ++ E).
  generalize dependent F.
  induction H; intros F Eq; subst.
  - destruct (X == x); subst; eapply wf_typ_var.
    + binds_cases H...
    + binds_cases H...
    (* requires wf_cset_ignores_bindings *)
  - econstructor... eapply wf_cset_ignores_sub_bindings...
------
  intros*.
  intros Hok H.
  remember (F ++ [(x, bind_sub T1)] ++ E).
  generalize dependent F.
  induction H; intros F Eq; subst.
  - econstructor.
  - pick fresh X and apply wf_typ_arrow.
    + eapply wf_typ_ignores_sub_bindings...
    + rewrite_parenthesise_binding.
      eapply wf_typ_ignores_sub_bindings with (T1 := T1)...
      simpl_env; constructor...
      eapply H0...
  - pick fresh X and apply wf_typ_all.
    + eapply wf_typ_ignores_sub_bindings...
    + rewrite_parenthesise_binding.
      eapply wf_typ_ignores_sub_bindings with (T1 := T1)...
      simpl_env; constructor...
      eapply H0...
Qed.


(* ********************************************************************** *)
(** * #<a name="oktwft"></a># Properties of [wf_env] and [wf_typ] *)

Lemma ok_from_wf_env : forall E,
  wf_env E ->
  ok E.
Proof.
  intros E H; induction H; auto.
Qed.

(** We add [ok_from_wf_env] as a hint here since it helps blur the
    distinction between [wf_env] and [ok] in proofs.  The lemmas in
    the [Environment] library use [ok], whereas here we naturally have
    (or can easily show) the stronger [wf_env].  Thus,
    [ok_from_wf_env] serves as a bridge that allows us to use the
    environments library. *)

Hint Resolve ok_from_wf_env : core.

Lemma wf_typ_from_binds_typ : forall x U E,
  wf_env E ->
  binds x (bind_typ U) E ->
  wf_typ_in E U.
Proof with eauto using wf_typ_weaken_head.
  intros x U E Hwf Hbinds.
  (* remember m; generalize dependent m. *)
  unfold wf_typ_in.
  induction Hwf; binds_cases Hbinds...
  inversion H3; subst...
Qed.

Lemma wf_typ_from_binds_sub : forall x U E,
  wf_env E ->
  binds x (bind_sub U) E ->
  wf_typ_in E U.
Proof with eauto using wf_typ_weaken_head.
  intros x U E Hwf Hbinds.
  (* remember m; generalize dependent m. *)
  unfold wf_typ_in.
  induction Hwf; binds_cases Hbinds...
  inversion H3; subst...
Qed.

Lemma wf_typ_from_wf_env_typ : forall x T E,
  wf_env ([(x, bind_typ T)] ++ E) ->
  wf_typ_in E T.
Proof.
  intros x T E H. inversion H; auto.
Qed.

Lemma wf_typ_from_wf_env_sub : forall x T E,
  wf_env ([(x, bind_sub T)] ++ E) ->
  wf_typ_in E T.
Proof.
  intros x T E H. inversion H; auto.
Qed.

(* ********************************************************************** *)
(** * #<a name="okt"></a># Properties of [wf_env] *)

(** These properties are analogous to the properties that we need to
    show for the subtyping and typing relations. *)

Lemma wf_env_narrowing : forall V E F U X,
  wf_env (F ++ [(X, bind_sub V)] ++ E) ->
  wf_typ_in E U ->
  wf_env (F ++ [(X, bind_sub U)] ++ E).
Proof with eauto 6 using wf_typ_narrowing_base.
  induction F; intros U X Wf_env Wf;
    inversion Wf_env; subst; simpl_env in *...
  + econstructor...
    apply wf_typ_narrowing_base with (V := V)...
  + econstructor...
    apply wf_typ_narrowing_base with (V := V)...
Qed.

Lemma wf_env_narrowing_typ : forall V E F U X,
  wf_env (F ++ [(X, bind_typ V)] ++ E) ->
  wf_typ_in E U ->
  wf_env (F ++ [(X, bind_typ U)] ++ E).
Proof with eauto 6 using wf_typ_narrowing_typ_base, wf_cset_narrowing_typ_base.
  induction F; intros U X Wf_env Wf;
    inversion Wf_env; subst; simpl_env in *...
  + econstructor...
    eapply wf_typ_narrowing_typ_base with (V := V)...
  + econstructor...
    apply wf_typ_narrowing_typ_base with (V := V)...
Qed.
Lemma wf_cset_set_strengthen : forall X S E A C,
  binds X (bind_sub S) E ->
  wf_cset E A C ->
  wf_cset E (A `remove` X) C.
Proof with eauto.
  intros* Hb WfCs.
  inversion WfCs.
  - eauto.
  - assert (fvars `subset` (A `remove` X)). {
      assert (X `notin` fvars). {
        intro.
        specialize (H X ltac:(trivial)) as [? ?].
        congruence.
      }
      fsetdec.
    }
    constructor...
Qed.

Lemma wf_cset_adapt : forall {A' E A C},
  wf_cset E A' C ->
  A' = A ->
  wf_cset E A C.
Proof.
  intros.
  congruence.
Qed.

Lemma wf_pretyp_adapt : forall {Ap' Am' E Ap Am T},
  wf_pretyp E Ap' Am' T ->
  Ap' = Ap ->
  Am' = Am ->
  wf_pretyp E Ap Am T.
Proof.
  intros.
  congruence.
Qed.

Lemma wf_typ_adapt : forall {Ap' Am' E Ap Am T},
  wf_typ E Ap' Am' T ->
  Ap' = Ap ->
  Am' = Am ->
  wf_typ E Ap Am T.
Proof.
  intros.
  congruence.
Qed.

Lemma wf_typ_set_strengthen : forall X S Ap Am E T,
  binds X (bind_sub S) E ->
  wf_typ E Ap Am T ->
  wf_typ E (Ap `remove` X) (Am `remove` X) T
with wf_pretyp_set_strengthen : forall X S Ap Am E P,
  binds X (bind_sub S) E ->
  wf_pretyp E Ap Am P ->
  wf_pretyp E (Ap `remove` X) (Am `remove` X) P.
Proof with eauto using wf_cset_set_strengthen.
{ intros * XinE WfT.
  induction WfT.
  - econstructor...
  - econstructor...
}
{ intros * XinE WfP.
  induction WfP.
  - econstructor...
  - pick fresh Y and apply wf_typ_arrow...
    specialize (H0 Y ltac:(notin_solve)).
    apply (wf_typ_set_strengthen X S) in H0...
    assert (Y `notin` (Ap `union` Am `union` singleton X)) by notin_solve.
    clear Fr.
    apply (wf_typ_adapt H0); fsetdec.
  - pick fresh Y and apply wf_typ_all...
}
Qed.


Lemma wf_cset_in_subst_tb : forall Q F E Z P C,
  ok (F ++ [(Z, bind_sub Q)] ++ E) ->
  wf_typ_in E P ->
  wf_cset_in (F ++ [(Z, bind_sub Q)] ++ E) C ->
  wf_cset_in (map (subst_tb Z P) F ++ E) C.
Proof with eauto.
  intros* Ok WfP WfC.
  apply (wf_cset_set_strengthen Z Q) in WfC...
  eapply wf_cset_subst_tb with (Q := Q) (Am := dom E).
  - apply (wf_cset_adapt WfC)...
    apply binding_uniq_from_ok in Ok.
    simpl_env.
    fsetdec.
  - rewrite_env (empty ++ empty ++ E).
    eapply wf_typ_weakening; simpl_env in *.
    + apply WfP.
    + eapply ok_tail...
    + fsetdec.
    + fsetdec.
  - trivial...
Qed.

Lemma wf_typ_in_subst_tb : forall Q F E Z P T,
  ok (F ++ [(Z, bind_sub Q)] ++ E) ->
  wf_typ_in E P ->
  wf_typ_in (F ++ [(Z, bind_sub Q)] ++ E) T ->
  wf_typ_in (map (subst_tb Z P) F ++ E) (subst_tt Z P T)
with wf_pretyp_in_subst_tb : forall Q F E Z P T,
  ok (F ++ [(Z, bind_sub Q)] ++ E) ->
  wf_typ_in E P ->
  wf_pretyp_in (F ++ [(Z, bind_sub Q)] ++ E) T ->
  wf_pretyp_in (map (subst_tb Z P) F ++ E) (subst_tpt Z P T).
Proof with eauto.
{ intros* Ok WfP WfT.
  apply (wf_typ_set_strengthen Z Q) in WfT.
  2: trivial...
  assert (Z `notin` (dom F `union` dom E)). {
    eapply binding_uniq_from_ok...
  }
  unshelve epose proof (wf_typ_subst_tb _ _ _ _ _ _ P _ WfT _ _ _) as HA.
  - eapply wf_typ_set_weakening.
    + apply WfP.
    + eapply ok_tail...
    + simpl_env; fsetdec.
    + simpl_env; fsetdec.
  - eapply wf_typ_set_weakening.
    + apply WfP.
    + eapply ok_tail...
    + simpl_env; fsetdec.
    + simpl_env; fsetdec.
  - eauto.
  - apply (wf_typ_adapt HA).
    + simpl_env; fsetdec.
    + simpl_env; fsetdec.
}
{ intros* Ok WfP WfT.
  apply (wf_pretyp_set_strengthen Z Q) in WfT.
  2: trivial...
  assert (Z `notin` (dom F `union` dom E)). {
    eapply binding_uniq_from_ok...
  }
  unshelve epose proof (wf_pretyp_subst_tb _ _ _ _ _ _ P _ WfT _ _ _) as HA.
  - eapply wf_typ_set_weakening; simpl_env.
    + apply WfP.
    + eapply ok_tail...
    + simpl_env; fsetdec.
    + simpl_env; fsetdec.
  - eapply wf_typ_set_weakening; simpl_env.
    + apply WfP.
    + eapply ok_tail...
    + simpl_env; fsetdec.
    + simpl_env; fsetdec.
  - eauto.
  - apply (wf_pretyp_adapt HA).
    + simpl_env; fsetdec.
    + simpl_env; fsetdec.
}
Qed.

Lemma wf_env_subst_tb : forall Q Z P E F,
  wf_env (F ++ [(Z, bind_sub Q)] ++ E) ->
  wf_typ_in E P ->
  wf_env (map (subst_tb Z P) F ++ E).
Proof with eauto 6 using wf_typ_subst_tb.
  induction F; intros Wf_env WP; simpl_env;
    inversion Wf_env; subst; simpl_env in *; simpl subst_tb...
  - econstructor...
    eapply wf_typ_in_subst_tb...
  - econstructor...
    eapply wf_typ_in_subst_tb...
Qed.

Lemma wf_env_inv : forall F Z b E,
  wf_env (F ++ [(Z, b)] ++ E) ->
  wf_env E /\ Z `notin` dom E.
Proof with eauto.
  induction F ; intros ; simpl_env in *.
  inversion H ; subst...
  inversion H ; subst...
Qed.

(* ********************************************************************** *)
(** * #<a name="subst"></a># Environment is unchanged by substitution for a fresh name *)

(** These proofs are all the same, but Coq isn't smart enough unfortunately... *)

Local Lemma notin_fv_tt_open_tt_rec : forall k (Y X : atom) T,
  X `notin` fv_tt (open_tt_rec k Y T) ->
  X `notin` fv_tt T
with notin_fv_tpt_open_tpt_rec : forall k (Y X : atom) T,
  X `notin` fv_tpt (open_tpt_rec k Y T) ->
  X `notin` fv_tpt T.
Proof.
------
  intros k Y X T. unfold open_tt.
  generalize k.
  induction T; simpl; intros k0 Fr; notin_simpl; try apply notin_union; eauto.
------
  intros k Y X T. unfold open_tt.
  generalize k.
  induction T; simpl; intros k0 Fr; notin_simpl; try apply notin_union; eauto.
Qed.


Local Lemma notin_fv_tt_open_tt : forall (Y X : atom) T,
  X `notin` fv_tt (open_tt T Y) ->
  X `notin` fv_tt T
with notin_fv_tpt_open_tpt : forall (Y X : atom) T,
  X `notin` fv_tpt (open_tpt T Y) ->
  X `notin` fv_tpt T.
Proof with eauto.
  intros. apply notin_fv_tt_open_tt_rec with (k := 0) (Y := Y)...
  intros. apply notin_fv_tpt_open_tpt_rec with (k := 0) (Y := Y)...
Qed.

Local Lemma notin_fv_tt_open_et_rec : forall (Y X : atom) T k,
  X `notin` fv_et (open_tt_rec k Y T) ->
  X `notin` fv_et T
with notin_fv_tt_open_ept_rec : forall (Y X : atom) T k,
  X `notin` fv_ept (open_tpt_rec k Y T) ->
  X `notin` fv_ept T.
Proof.
------
  intros Y X T. unfold open_tt_rec.
  induction T; simpl; intros k Fr; notin_simpl; try apply notin_union; eauto.
------
  intros Y X T. unfold open_tt_rec.
  induction T; simpl; intros k Fr; notin_simpl; try apply notin_union; eauto.
Qed.

Local Lemma notin_fv_tt_open_et : forall (Y X : atom) T,
  X `notin` fv_et (open_tt T Y) ->
  X `notin` fv_et T
with notin_fv_tt_open_ept : forall (Y X : atom) T,
  X `notin` fv_ept (open_tpt T Y) ->
  X `notin` fv_ept T.
Proof with eauto.
  intros. apply notin_fv_tt_open_et_rec with (k := 0) (Y := Y)...
  intros. apply notin_fv_tt_open_ept_rec with (k := 0) (Y := Y)...
Qed.

Local Lemma notin_fv_tt_open : forall (Y X : atom) T,
  X `notin` fv_tt (open_tt T Y) ->
  X `notin` fv_et (open_tt T Y) ->
  X `notin` (fv_tt T `union` fv_et T).
Proof with auto.
 intros. apply notin_union.
 - apply notin_fv_tt_open_tt with (Y := Y)...
 - apply notin_fv_tt_open_et with (Y := Y)...
Qed.

Local Lemma notin_fv_ct_open_tt_rec : forall (X : atom) T C k,
  X `notin` fv_tt (open_ct_rec k C T) ->
  X `notin` fv_tt T
with notin_fv_cpt_open_tpt_rec : forall (X : atom) T C k,
  X `notin` fv_tpt (open_cpt_rec k C T) ->
  X `notin` fv_tpt T.
Proof with auto.
------
  intros X T C. unfold open_ct.
  induction T ; simpl ; intros k Fr ; try apply notin_union; eauto.
------
  intros X T C. unfold open_ct.
  induction T ; simpl ; intros k Fr ; try apply notin_union; eauto.
  - apply notin_fv_ct_open_tt_rec with (C := C) (k := k)...
  - apply notin_fv_ct_open_tt_rec with (C := C) (k := S k)...
  - apply notin_fv_ct_open_tt_rec with (C := C) (k := k)...
  - apply notin_fv_ct_open_tt_rec with (C := C) (k := S k)...
Qed.

Local Lemma notin_fv_ct_open_tt : forall (X : atom) T C,
  X `notin` fv_tt (open_ct T C) ->
  X `notin` fv_tt T
with notin_fv_cpt_open_tpt : forall (X : atom) T C,
  X `notin` fv_tpt (open_cpt T C) ->
  X `notin` fv_tpt T.
Proof with eauto.
  intros. apply notin_fv_ct_open_tt_rec with (k := 0) (C := C)...
  intros. apply notin_fv_cpt_open_tpt_rec with (k := 0) (C := C)...
Qed.

Local Lemma notin_fv_open_cset : forall (X : atom) c C k,
  c <> cset_universal ->
  X `notin` (fv_cset (open_cset k c C)) ->
  X `notin` (fv_cset C).
Proof with auto.
  intros. revert H0.
  unfold fv_cset. unfold open_cset.
  cset_split; destruct C eqn:HC; destruct c eqn:Hc...
Qed.

Local Lemma notin_fv_ct_open_et_rec : forall (X : atom) T C k,
  C <> cset_universal ->
  X `notin` fv_et (open_ct_rec k C T) ->
  X `notin` fv_et T
with notin_fv_ct_open_ept_rec : forall (X : atom) T C k,
  C <> cset_universal ->
  X `notin` fv_ept (open_cpt_rec k C T) ->
  X `notin` fv_ept T.
Proof with auto.
------
  intros X T C.
  induction T ; simpl ; intros k H Fr ; try apply notin_union; eauto.
  - apply notin_fv_open_cset with (k := k) (c := C)...
  - apply notin_fv_ct_open_ept_rec with (C := C) (k := k)...
------
    intros X T C.
    induction T ; simpl ; intros k H Fr ; try apply notin_union; eauto.
    - apply notin_fv_ct_open_et_rec with (C := C) (k := k)...
    - apply notin_fv_ct_open_et_rec with (C := C) (k := S k)...
    - apply notin_fv_ct_open_et_rec with (C := C) (k := k)...
    - apply notin_fv_ct_open_et_rec with (C := C) (k := S k)...
Qed.

Local Lemma notin_fv_ct_open_et : forall (X : atom) T C,
  C <> cset_universal ->
  X `notin` fv_et (open_ct T C) ->
  X `notin` fv_et T
with notin_fv_ct_open_ept : forall (X : atom) T C,
  C <> cset_universal ->
  X `notin` fv_ept (open_cpt T C) ->
  X `notin` fv_ept T.
Proof with auto.
  intros. apply notin_fv_ct_open_et_rec with (k := 0) (C := C)...
  intros. apply notin_fv_ct_open_ept_rec with (k := 0) (C := C)...
Qed.

Local Lemma notin_fv_ct_open_ct_rec : forall (Y X : atom) T k,
  X `notin` fv_et (open_ct_rec k Y T) ->
  X <> Y ->
  X `notin` fv_et T
with notin_fv_ct_open_cpt_rec : forall (Y X : atom) T k,
  X `notin` fv_ept (open_cpt_rec k Y T) ->
  X <> Y ->
  X `notin` fv_ept T.
Proof with eauto*.
------
  intros Y X T.
  induction T ; simpl ; intros k H Fr ; try apply notin_union; eauto.
  - apply notin_fv_open_cset with (k := k) (c := Y)...
    discriminate.
  - apply notin_fv_ct_open_cpt_rec with (k := k) (Y := Y)...
------
  intros Y X T.
  induction T ; simpl ; intros k H Fr ; try apply notin_union; eauto.
  - apply notin_fv_ct_open_ct_rec with (Y := Y) (k := k)...
  - apply notin_fv_ct_open_ct_rec with (Y := Y) (k := S k)...
  - apply notin_fv_ct_open_ct_rec with (Y := Y) (k := k)...
  - apply notin_fv_ct_open_ct_rec with (Y := Y) (k := S k)...
Qed.

Local Lemma notin_fv_ct_open_ct : forall (Y X : atom) T,
  X `notin` fv_et (open_ct T Y) ->
  X <> Y ->
  X `notin` fv_et T
with notin_fv_ct_open_cpt : forall (Y X : atom) T,
  X `notin` fv_ept (open_cpt T Y) ->
  X <> Y ->
  X `notin` fv_ept T.
Proof with eauto*.
  intros. apply notin_fv_ct_open_ct_rec with (k := 0) (Y := Y)...
  intros. apply notin_fv_ct_open_cpt_rec with (k := 0) (Y := Y)...
Qed.


Lemma notin_fv_ct_open : forall (X : atom) T C,
  C <> cset_universal ->
  X `notin` fv_et (open_ct T C) ->
  X `notin` fv_tt (open_ct T C) ->
  X `notin` (fv_tt T `union` fv_et T).
Proof with auto.
  intros. apply notin_union...
  - apply notin_fv_ct_open_tt with (C := C)...
  - apply notin_fv_ct_open_et with (C := C)...
Qed.

Lemma notin_fv_wf_typ : forall E Ap Am (X : atom) T,
  wf_typ E Ap Am T ->
  X `notin` dom E ->
  X `notin` (fv_tt T `union` fv_et T)
with notin_fv_wf_pretyp : forall E Ap Am (X : atom) T,
  wf_pretyp E Ap Am T ->
  X `notin` dom E ->
  X `notin` (fv_tpt T `union` fv_ept T).
Proof with eauto.
-------
  intros * Wf_typ.
  induction Wf_typ; intros FrE; simpl...
  - assert (X0 `in` dom E) by (eapply binds_In; eauto)...
  - specialize (notin_fv_wf_pretyp _ _ _ _ _ H0 FrE) as Wf.
    inversion H; destruct C; subst; simpl in *; try notin_solve.
    assert (X `notin` fvars). {
      unfold allbound_typ in *; unfold cset_fvars in *.
      intro Hin; specialize (H1 X Hin) as [T Hbinds].
      apply binds_In in Hbinds. intuition.
    }
    notin_solve.
-------
  intros * Wf_pretyp.
  induction Wf_pretyp; intros FrE; simpl...
  - pick fresh Y.
    specialize (notin_fv_wf_typ _ _ _ X _ H ltac:(assumption)) as HT1.
    specialize (H0 Y ltac:(notin_solve)) as WfT2.
    specialize (notin_fv_wf_typ _ _ _ X _ WfT2) as HT2.
    simpl in *.
    specialize (HT2 ltac:(notin_solve)).
    assert (X `notin` fv_tt T2). {
      apply notin_fv_ct_open_tt with (C := Y).
      notin_solve.
    }
    assert (X `notin` fv_et T2). {
      apply notin_fv_ct_open_et with (C := Y); try discriminate.
      notin_solve.
    }
    notin_solve.
  - pick fresh Y.
    specialize (notin_fv_wf_typ _ _ _ X _ H ltac:(assumption)) as HT1.
    specialize (H0 Y ltac:(notin_solve)) as WfT2.
    specialize (notin_fv_wf_typ _ _ _ X _ WfT2) as HT2.
    simpl in *.
    specialize (HT2 ltac:(notin_solve)).
    assert (X `notin` fv_tt T2). {
      apply notin_fv_tt_open_tt with (Y := Y).
      notin_solve.
    }
    assert (X `notin` fv_et T2). {
      apply notin_fv_tt_open_et with (Y := Y); try discriminate.
      notin_solve.
    }
    notin_solve.
Qed.

Lemma notin_fv_wf : forall E (X : atom) T,
  wf_typ_in E T ->
  X `notin` dom E ->
  X `notin` fv_tt T.
Proof with eauto.
  intros E X T Wf_typ F.
  assert (X `notin` (fv_tt T `union` fv_et T)). {
    eapply notin_fv_wf_typ...
  }
  fsetdec.
Qed.

Local Lemma notin_fv_ee_open_ee_rec : forall k u (y x : atom) t,
  x `notin` fv_ee (open_ee_rec k u y t) ->
  x <> y ->
  x `notin` fv_ee t.
Proof with eauto.
  intros. generalize dependent k.
  induction t; simpl in *; intros k H; try (trivial || notin_solve).
  - apply notin_union...
    + apply notin_fv_ct_open_ct_rec with (Y := y) (k := k)...
    + apply (IHt (S k)). notin_solve.
  - apply notin_union...
    + apply (IHt1 k). notin_solve.
    + apply (IHt2 k). notin_solve.
  - apply notin_union.
    + apply notin_fv_ct_open_ct_rec with (Y := y) (k := k)...
    + eapply (IHt (S k)). notin_solve.
  - apply notin_union.
    + apply notin_fv_ct_open_ct_rec with (Y := y) (k := k)...
    + apply (IHt k). notin_solve.
Qed.

Lemma notin_fv_ee_open_ee : forall u (y x : atom) t,
  x `notin` fv_ee (open_ee t u y) ->
  x <> y ->
  x `notin` fv_ee t.
Proof with eauto.
  intros. unfold open_ee in *.
  apply (notin_fv_ee_open_ee_rec 0 u y)...
Qed.

Local Lemma notin_fv_et_open_tt_rec : forall k (Y X : atom) T,
  X `notin` fv_et (open_tt_rec k Y T) ->
  X `notin` fv_et T
with notin_fv_ept_open_tpt_rec : forall k (Y X : atom) T,
  X `notin` fv_ept (open_tpt_rec k Y T) ->
  X `notin` fv_ept T.
Proof.
------
  intros k Y X T. unfold open_tt.
  generalize k.
  induction T; simpl; intros k0 Fr; notin_simpl; try apply notin_union; eauto.
------
  intros k Y X T. unfold open_tt.
  generalize k.
  induction T; simpl; intros k0 Fr; notin_simpl; try apply notin_union; eauto.
Qed.

Local Lemma notin_fv_ee_open_te_rec : forall k (y x : atom) t,
  x `notin` fv_ee (open_te_rec k y t) ->
  x <> y ->
  x `notin` fv_ee t.
Proof with eauto.
  intros. generalize dependent k.
  induction t; simpl in *; intros k H; try (trivial || notin_solve).
  - apply notin_union...
    + apply (notin_fv_et_open_tt_rec k y)...
    + apply (IHt (S k)). notin_solve.
  - apply notin_union...
    + apply (IHt1 k). notin_solve.
    + apply (IHt2 k). notin_solve.
  - apply notin_union.
    + apply (notin_fv_et_open_tt_rec k y)...
    + apply (IHt (S k)). notin_solve.
  - apply notin_union.
    + apply (notin_fv_et_open_tt_rec k y)...
    + apply (IHt k). notin_solve.
Qed.

Lemma notin_fv_ee_open_te : forall (y x : atom) t,
  x `notin` fv_ee (open_te t y) ->
  x <> y ->
  x `notin` fv_ee t.
Proof with eauto.
  intros. unfold open_ee in *.
  apply (notin_fv_ee_open_te_rec 0 y)...
Qed.

Lemma map_subst_tb_id : forall G Z P,
  wf_env G ->
  Z `notin` dom G ->
  G = map (subst_tb Z P) G.
Proof with auto.
  intros G Z P H.
  induction H; simpl; intros Fr; simpl_env...
  rewrite <- IHwf_env...
    rewrite <- subst_tt_fresh... eapply notin_fv_wf; eauto.
  rewrite <- IHwf_env...
    rewrite <- subst_tt_fresh... eapply notin_fv_wf; eauto.
Qed.


(* ********************************************************************** *)
(** * #<a name="regularity"></a># Regularity of relations *)

Require Import TaktikZ.

Lemma subcapt_regular : forall E C D,
  subcapt E C D ->
  wf_cset_in E C /\ wf_cset_in E D.
Proof with eauto*.
  intros* H.
  induction H; subst...
  - split...
    constructor.
    2: {
      apply binds_In in H...
    }
    intros y yInX.
    rewrite AtomSetFacts.singleton_iff in yInX; subst...
  - split...
    constructor.
    + intros y yIn.
      forwards (WfX & _): H1 y yIn.
      inversion WfX; subst.
      rename select (allbound_typ _ _) into HABnd.
      applys HABnd y.
      fsetdec.
    + intros y yIn.
      forwards (WfX & _): H1 y yIn.
      inversion WfX; subst.
      fsetdec.
Qed.

Hint Unfold wf_typ_in : core.
Hint Unfold wf_pretyp_in : core.

Lemma sub_regular : forall E S T,
  sub E S T ->
  wf_env E /\ wf_typ_in E S /\ wf_typ_in E T
with sub_pre_regular : forall E S T,
  sub_pre E S T ->
  wf_env E /\ wf_pretyp_in E S /\ wf_pretyp_in E T.
Proof with simpl_env; auto*.
------
  intros E S T H.
  induction H.
  - repeat split...
  - Case "sub_trans_tvar".
    repeat split...
    apply wf_typ_var with (U := U)...
  - Case "sub_capt".
    assert (wf_cset_in E C1 /\ wf_cset_in E C2). { apply subcapt_regular... }
    assert (wf_env E /\ wf_pretyp_in E P1 /\ wf_pretyp_in E P2). { apply sub_pre_regular... }
    repeat split...
------
  intros E S T H.
  induction H.
  - repeat split...
  - Case  "sub_trans_arrow".
    pose proof (sub_regular E _ _ H).
    repeat split; [
      auto* |
      apply wf_typ_arrow with (L := L); auto* |
      apply wf_typ_arrow with (L := L); auto*
    ].
  - Case "sub_all".
    pose proof (sub_regular E _ _ H).
    repeat split; [
      auto* |
      apply wf_typ_all with (L := L); auto* |
      apply wf_typ_all with (L := L); auto*
    ].
Qed.

Lemma cv_free_never_universal : forall e,
  free_for_cv e <> cset_universal.
Proof with eauto*.
  intros. induction e; unfold free_for_cv; try discriminate...
  fold free_for_cv.
  unfold cset_union...
  destruct (free_for_cv e1) eqn:Hfc1;
    destruct (free_for_cv e2) eqn:Hfc2...
Qed.

Lemma cv_free_is_bvar_free : forall e,
  empty_cset_bvars (free_for_cv e).
Proof with eauto using cv_free_never_universal.
  intros. induction e...
  - simpl; fnsetdec...
  - simpl; fnsetdec...
  - unfold empty_cset_bvars in *.
    unfold cset_all_bvars in *.
    simpl in *.
    destruct (free_for_cv e1) eqn:Hc1;
    destruct (free_for_cv e2) eqn:Hc2...
    unfold cset_union.
    fnsetdec...
Qed.

Lemma cv_free_atom : forall (x : atom),
  free_for_cv x = x.
Proof with auto*.
  intros.
  unfold free_for_cv...
Qed.

Lemma singleton_set_eq : forall (x y : atom),
  singleton x = singleton y <-> x = y.
Proof.
  split; intros.
  * assert (y `in` singleton x).
    { rewrite H. fsetdec. }
    fsetdec.
  * fsetdec.
Qed.

Lemma free_for_cv_open : forall e k (y : atom),
  cset_subset_prop (free_for_cv e) (free_for_cv (open_ee_rec k y y e)).
Proof with eauto*.
  intros e.
  induction e; intros; simpl...
  - destruct (k === n); constructor; fsetdec...
  - constructor...
  - specialize (IHe1 k y).
    specialize (IHe2 k y).
    inversion IHe1; inversion IHe2; subst; constructor...
    fnsetdec.
Qed.

Lemma free_for_cv_open_type : forall e k (y : atom),
  cset_subset_prop (free_for_cv e) (free_for_cv (open_te_rec k y e)).
Proof with eauto*.
  intros e; induction e; intros; simpl...
  - constructor; fsetdec...
  - constructor; fsetdec...
  - specialize (IHe1 k y).
    specialize (IHe2 k y).
    inversion IHe1; inversion IHe2; subst; constructor...
    fnsetdec.
Qed.

Lemma empty_over_union : forall N1 N2,
  {}N = NatSet.F.union N1 N2 ->
  {}N = N1 /\ {}N = N2.
Proof.
  intros.
  assert (NatSet.F.Empty (NatSet.F.union N1 N2)) by (rewrite <- H; fnsetdec).
  split; fnsetdec.
Qed.

Lemma allbound_over_union : forall E T1 T2,
  allbound_typ E (AtomSet.F.union T1 T2) ->
  allbound_typ E T1 /\ allbound_typ E T2.
Proof with eauto*.
  intros.
  unfold allbound_typ in *.
  split; intros; assert (x `in` (T1 `union` T2)) by fsetdec...
Qed.

Lemma wf_cset_over_union : forall E A C1 C2,
  C1 <> cset_universal ->
  C2 <> cset_universal ->
  wf_cset E A (cset_union C1 C2) <->
  wf_cset E A C1 /\ wf_cset E A C2.
Proof with eauto*.
  intros; split; intros; destruct C1 eqn:HC1;
                         destruct C2 eqn:HC2;
                         unfold cset_union in *...
  + inversion H1; subst...
    apply empty_over_union in H3; inversion H3.
    apply allbound_over_union in H6; inversion H6.
    subst.
    split; constructor...
    all : fsetdec.
  + destruct H1 as [Hwf1 Hwf2].
    inversion Hwf1; inversion Hwf2; subst...
    (** this should really be a lemma... *)
    assert (NatSet.F.union {}N {}N = {}N) by fnsetdec; rewrite H1.
    constructor.
    unfold allbound_typ in *...
    intros.
    apply AtomSetFacts.union_iff in H2...
    fsetdec.
Qed.

Lemma cset_references_fvar_over_union : forall C1 C2 x,
  cset_references_fvar x (cset_union C1 C2) ->
  cset_references_fvar x C1 \/ cset_references_fvar x C2.
Proof with eauto*.
  intros C1 C2 x H.
  unfold cset_references_fvar in H.
  unfold cset_all_fvars in H.
  destruct (cset_union C1 C2) eqn:Hunion...
  unfold cset_union in *.
  destruct C1 eqn:HC1; destruct C2 eqn:HC2; subst...
  inversion Hunion...
  assert (x `in` (t1 `union` t3)) by (rewrite H1; eauto*)...
  apply AtomSetFacts.union_iff in H0; inversion H0; subst...
Qed.

Lemma free_for_cv_bound : forall E e (x : atom),
  wf_cset_in E (free_for_cv e) ->
  cset_references_fvar x (free_for_cv e) ->
  exists T, binds x (bind_typ T) E.
Proof with eauto using wf_cset_over_union, cv_free_never_universal.
  intros E e.
  induction e; intros; simpl in *; try fsetdec...
  - assert (x = a) by fsetdec; subst...
    inversion H; subst...
  - apply wf_cset_over_union in H...
    apply cset_references_fvar_over_union in H0...
    inversion H0.
    + apply IHe1... apply H.
    + apply IHe2... apply H.
Qed.

Lemma free_for_cv_is_free_ee : forall e,
  cset_subset_prop (free_for_cv e) (cset_set (fv_ee e) {}N).
Proof with eauto using cv_free_never_universal; eauto*.
  intros e.
  (** gah why doesn't eauto pick this up. *)
  pose proof (cv_free_never_universal).
  induction e; try destruct (free_for_cv e) eqn:Hcve;
    subst; simpl; try rewrite Hcve; try constructor; try inversion IHe;
    try fsetdec; try fnsetdec.
  - unfold cset_union in *;
    destruct (free_for_cv e1) eqn:Hcve1;
    destruct (free_for_cv e2) eqn:Hcve2...
    inversion IHe1; inversion IHe2; subst...
    constructor; try fsetdec; try fnsetdec...
Qed.

(** This should be easily true: free variables
    are all bound if a term has a type.... *)
Lemma typing_cv : forall E e T,
  typing E e T ->
  wf_cset_in E (free_for_cv e).
Proof with eauto using cv_free_never_universal, wf_cset_over_union; eauto*.
  intros E e T Htyp.
  induction Htyp; simpl...
  (** TODO: merge the abs/t-abs case somehow (maybe a match to decide what
      gets posed? )*)
  - pose proof (binds_In _ _ _ _ H0).
    simpl. constructor...
    unfold allbound_typ. intros.
    assert (x = x0) by fsetdec.
    subst. exists X...
  - pose proof (binds_In _ _ _ _ H0).
    simpl. constructor...
    unfold allbound_typ. intros.
    assert (x = x0) by fsetdec.
    subst. exists (typ_capt C P)...
  - pick fresh y.
    assert (y `notin` L) by fsetdec.
    assert (~ cset_references_fvar y (free_for_cv e1)).
    {
      pose proof (free_for_cv_is_free_ee e1) as P...
      inversion P; subst...
      simpl...
    }
    unshelve epose proof (H2 y _) as SpH0...
    pose proof (free_for_cv_open e1 0 y)...
    pose proof (cv_free_never_universal).
    pose proof (cv_free_is_bvar_free e1).
    csethyp.
    destruct (free_for_cv e1) eqn:Hfcv1; subst...
    unfold open_ee in *.
    inversion SpH0; subst...
    match goal with H : (cset_subset_prop _ _) |- _ =>
      inversion H; subst
    end...
    rewrite <- H8 in H13. inversion H13; subst...
    assert (t0 = {}N) by fnsetdec; subst...
    constructor...
    unfold allbound_typ in *.
    intros.
    destruct (x == y)...
    unshelve epose proof (H9 x _) as [T Hbinds]...
    exists T.
    binds_cases Hbinds...
  - simpl...
    apply wf_cset_over_union...
  (* typing_app_poly *)
  - pick fresh y.
    assert (y `notin` L) by fsetdec.
    assert (~ cset_references_fvar y (free_for_cv e1)).
    {
      pose proof (free_for_cv_is_free_ee e1) as P...
      inversion P; subst; simpl...
    }
    simpl.
    unshelve epose proof (H2 y _) as SpH0...
    pose proof (free_for_cv_open_type e1 0 y).
    pose proof (cv_free_never_universal).
    pose proof (cv_free_is_bvar_free e1).
    csethyp.
    destruct (free_for_cv e1) eqn:Hfcv1...
    unfold open_te in *.
    inversion SpH0; subst...
    match goal with H : (cset_subset_prop _ _) |- _ =>
      inversion H; subst
    end...
    rewrite <- H8 in H13. inversion H13; subst...
    assert (t0 = {}N) by fnsetdec; subst...
    constructor...
    unfold allbound_typ in *.
    intros.
    destruct (x == y)...
    unshelve epose proof (H9 x _) as [T Hbinds]...
    exists T.
    binds_cases Hbinds...
Qed.

Lemma wf_typ_open : forall E U T1 T2,
  ok E ->
  wf_pretyp_in E (typ_all T1 T2) ->
  wf_typ_in E U ->
  wf_typ_in E (open_tt T2 U).
Proof with simpl_env; eauto.
  intros E U T1 T2 Hok HwfA HwfU.
  inversion HwfA; subst...
  pick fresh X.
  rewrite (subst_tt_intro X)...
  rewrite_env (map (subst_tb X U) empty ++ E).
  assert (({} `union` dom E) = dom E) by fsetdec.
  rewrite_env (map (subst_tb X U) empty ++ E).
  apply wf_typ_subst_tb with (Q := T1)...
  all : rewrite H...
Qed.

(** The things that the cv relation returns are all well-formed,
    assuming the type is well formed... *)
Lemma cv_wf : forall E T C,
  cv E T C ->
  wf_cset_in E C.
Proof with simpl_env; eauto*.
  intros E T C HC.
  induction HC; intros; subst; try apply IHHC; try apply H1.
Qed.

Lemma typing_regular : forall E e T,
  typing E e T ->
  wf_env E /\ expr e /\ wf_typ_in E T.
Proof with simpl_env; auto*.
  intros E e T H.
  induction H...
  (* typing rule: x : X \in E --> E |- x : X *)
  - repeat split...
    apply wf_typ_from_binds_typ with (x := x)...
  (* typing rule : x : C P \in E --> E |- x : {x} P *)
  - repeat split...
    assert (wf_typ_in E (typ_capt C P)). {
      apply wf_typ_from_binds_typ with (x := x)...
    }
    inversion H1; subst...
    constructor...
    constructor...
    unfold allbound_typ; intros. assert (x0 = x) by fsetdec; subst; eauto.
    assert (x `in` dom E). eapply binds_In. apply H0. fsetdec.
  (* typing rule: (\x e) has type fv((\x e)) T1 -> T2 *)
  - pick fresh y; assert (y `notin` L) by fsetdec...
    unshelve epose proof (H2 y _) as H4...
    inversion H4 as [Henv [Hexpr Hwf]]...
    repeat split...
    + inversion Henv...
    + pick fresh x and apply expr_abs.
        * eapply type_from_wf_typ.
          eapply wf_typ_from_wf_env_typ.
          apply Henv.
        * destruct (H2 x)...
    + constructor...
      apply typing_cv with (e := (exp_abs V e1)) (T := (typ_capt (free_for_cv e1) (typ_arrow V T1)))...
      apply typing_abs with (L := L)...
      eapply wf_typ_arrow. assumption.
      apply H0.
  (* typing rule: application *)
  - repeat split...
    destruct IHtyping1 as [_ [_ Hwf]].
    inversion Hwf; subst...
    inversion H9; subst...
    apply wf_typ_set_weakening with (Ap := dom E) (Am := dom E)...
    (** needs substitution lemma here. *)
    apply wf_typ_open_capt with (T1 := T1)...
    apply cv_wf with (T := T1')...
  (* typing rule: type abstractions. *)
  - pick fresh y; assert (y `notin` L) by fsetdec...
    unshelve epose proof (H2 y _) as H4...
    inversion H4 as [Henv [Hexpr Hwf]]...
    repeat split...
    + inversion Henv...
    + pick fresh x and apply expr_tabs.
      * eapply type_from_wf_typ.
        eapply wf_typ_from_wf_env_sub.
        apply Henv.
      * destruct (H2 x)...
    + constructor...
      apply typing_cv with (e := (exp_tabs V e1)) (T := (typ_capt (free_for_cv e1) (typ_all V T1)))...
      apply typing_tabs with (L := L)...
      eapply wf_typ_all. assumption.
      apply H0.
  (* typing rule: type application *)
  - destruct IHtyping as [HwfE [Hexpr Hwf]]...
    repeat split...
    constructor...
    pose proof (sub_regular E T T1 H0) as [_ [HwfT HwfT1]].
    eapply type_from_wf_typ with (E := E); apply HwfT.
    inversion Hwf; subst...
    apply wf_typ_open with (T1 := T1)...
    destruct (sub_regular _ _ _ H0) as [R1 [R2 R3]]...
  - repeat split...
    pose proof (sub_regular E S T H0)...
Qed.


Lemma value_regular : forall e,
  value e ->
  expr e.
Proof.
  intros e H. induction H; auto.
Qed.

Lemma red_regular : forall e e',
  red e e' ->
  expr e /\ expr e'.
Proof with auto*.
  intros e e' H.
  induction H; assert (J := value_regular); split...
  - Case "red_abs".
    inversion H. pick fresh y.
    rewrite (subst_ee_intro y)...
    eapply subst_ee_expr...
    pose proof (cv_free_is_bvar_free v2).
    unfold empty_cset_bvars in H5. unfold cset_all_bvars in H5.
    destruct (free_for_cv v2); subst...
    assert (t0 = {}N) by fnsetdec; subst...
  - Case "red_tabs".
    inversion H. pick fresh Y. rewrite (subst_te_intro Y)...
Qed.

Lemma cv_regular : forall E T C,
  cv E T C ->
  wf_env E /\ wf_typ_in E T /\ wf_cset_in E C.
Proof with eauto*.
  intros. induction H...
Qed.

(** Moved from Soundness *)


(* *********************************************************************** *)
(** * Auxilliary lemmas for Soundness *)

Lemma subst_cset_distributive_across_union : forall z C D1 D2,
  subst_cset z C (cset_union D1 D2) =
  cset_union (subst_cset z C D1) (subst_cset z C D2).
Proof with eauto.
  intros.
  destruct D1; destruct D2.
  all :
    try solve [
          unfold cset_union, subst_cset, cset_references_fvar_dec;
          (try destruct_match);
          reflexivity].

  unfold cset_union, subst_cset, cset_references_fvar_dec.
  destruct (AtomSet.F.mem z t) eqn:EQ1.
  - rewrite <- AtomSetFacts.mem_iff in EQ1.
    assert (AtomSet.F.mem z (t `union` t1) = true) as HA by fset_mem_dec.
    rewrite HA.
    destruct C.
    + unfold cset_union.
      all : repeat destruct_match.
      all : easy.
    + unfold cset_union, cset_remove_fvar.
      destruct (AtomSet.F.mem z t1) eqn:EQ2.
      * rewrite <- AtomSetFacts.mem_iff in EQ2.
        cset_eq_dec.
      * rewrite <- AtomSetFacts.not_mem_iff in EQ2.
        cset_eq_dec.
  - rewrite <- AtomSetFacts.not_mem_iff in EQ1.
    destruct (AtomSet.F.mem z t1) eqn:EQ2.
    + rewrite <- AtomSetFacts.mem_iff in EQ2.
      assert (AtomSet.F.mem z (t `union` t1) = true) as HA by fset_mem_dec.
      rewrite HA.
      destruct C.
      * unfold cset_union.
        all : repeat destruct_match.
        all : easy.
      * unfold cset_remove_fvar, cset_union.
        cset_eq_dec.
    + rewrite <- AtomSetFacts.not_mem_iff in EQ2.
      assert (AtomSet.F.mem z (t `union` t1) = false) as HA by fset_mem_dec.
      rewrite HA.
      reflexivity.
Qed.

Lemma subst_cset_fresh_for_cv : forall z t C,
  z `notin` fv_ee t ->
  (subst_cset z C (free_for_cv t)) = (free_for_cv t).
Proof.
  intros.
  induction t; simpl in H |- *.
  - cbv.
    replace (AtomSet.F.mem z {}) with false by fset_mem_dec.
    cset_eq_dec.
  - cbv.
    replace (AtomSet.F.mem z (singleton a)) with false by fset_mem_dec.
    cset_eq_dec.
  - apply IHt. fsetdec.
  - rewrite subst_cset_distributive_across_union.
    rewrite IHt1 by notin_solve.
    rewrite IHt2 by notin_solve.
    reflexivity.
  - apply IHt. fsetdec.
  - apply IHt. fsetdec.
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

Hint Extern 1 (wf_cset ?E _ ?C) =>
  match goal with
  | H: subcapt _ C _ |- _ => apply (proj1 (subcapt_regular _ _ _ H))
  | H: subcapt _ _ C |- _ => apply (proj2 (subcapt_regular _ _ _ H))
  | H: cv E _ C |- _ => apply (proj2 (proj2 (cv_regular _ _ _ H)))
  end
: core.

Hint Extern 1 (wf_env ?E) =>
  match goal with
  | H: sub _ _ _ |- _ => apply (proj1 (sub_regular _ _ _ H))
  | H: sub_pre _ _ _ |- _ => apply (proj1 (sub_pre_regular _ _ _ H))
  | H: typing _ _ _ |- _ => apply (proj1 (typing_regular _ _ _ H))
  | H: cv E _ _ |- _ => apply (proj1 (cv_regular _ _ _ H))
  end
: core.

Hint Extern 1 (wf_typ ?E _ _ ?T) =>
  match goal with
  | H: typing E _ T |- _ => apply (proj2 (proj2 (typing_regular _ _ _ H)))
  | H: sub E T _ |- _ => apply (proj1 (proj2 (sub_regular _ _ _ H)))
  | H: sub E _ T |- _ => apply (proj2 (proj2 (sub_regular _ _ _ H)))
  | H: cv E T _ |- _ => apply (proj1 (proj2 (cv_regular _ _ _ H)))
  end
: core.

Hint Extern 1 (wf_pretyp ?E ?T) =>
  match goal with
  | H: sub_pre E T _ |- _ => apply (proj1 (proj2 (sub_pre_regular _ _ _ H)))
  | H: sub_pre E _ T |- _ => apply (proj2 (proj2 (sub_pre_regular _ _ _ H)))
  end
: core.

Hint Extern 1 (type ?T) =>
  let go E := eapply (type_from_wf_typ E); eauto in
  match goal with
  | H: typing ?E _ T |- _ => go E
  | H: sub ?E T _ |- _ => go E
  | H: sub ?E _ T |- _ => go E
  | H: wf_typ ?E _ _ T |- _ => go E
  end
: core.

Hint Extern 1 (pretype ?T) =>
  let go E := eapply (pretype_from_wf_pretyp E); eauto in
  match goal with
  | H: sub_pre ?E T _ |- _ => go E
  | H: sub_pre ?E _ T |- _ => go E
  | H: wf_pretyp ?E _ _ T |- _ => go E
  end
: core.

Hint Extern 1 (capt ?C) =>
  let go E := eapply (capt_from_wf_cset E); eauto in
  match goal with
  | H: subcapt ?E C _ |- _ => go E
  | H: subcapt ?E _ C |- _ => go E
  | H: cv ?E _ C |- _ => go E
  end
: core.

Hint Extern 1 (expr ?e) =>
  match goal with
  | H: typing _ ?e _ |- _ => apply (proj1 (proj2 (typing_regular _ _ _ H)))
  | H: red ?e _ |- _ => apply (proj1 (red_regular _ _ H))
  | H: red _ ?e |- _ => apply (proj2 (red_regular _ _ H))
  end
: core.

(** More automation *)
Lemma capt_from_cv : forall E T C,
    cv E T C -> capt C.
Proof with eauto.
  intros.
  assert (wf_cset_in E C) as HA by auto.
  eapply capt_from_wf_cset...
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

(** * #<a name="auto"></a># Automation Tests *)

Local Lemma test_cv_regular : forall E T C,
    cv E T C ->
    wf_env E /\ wf_typ_in E T /\ wf_cset_in E C.
Proof.
  intros.
  repeat split.
  all: auto.
Qed.

Local Lemma test_subcapt_regular : forall E C1 C2,
  subcapt E C1 C2 ->
  wf_cset E (dom E) C1 /\ wf_cset E (dom E) C2.
Proof with eauto*.
  intros.
  repeat split.
  all: auto.
Qed.
