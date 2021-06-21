Require Import Coq.Program.Equality.

Require Export CCsub_Infrastructure.
Require Export CCsub_Wellformedness.
Require Import Atom.

Require Import TaktikZ.


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

Lemma notin_fv_tt_open_tt_rec : forall k (Y X : atom) T,
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


Lemma notin_fv_tt_open_tt : forall (Y X : atom) T,
  X `notin` fv_tt (open_tt T Y) ->
  X `notin` fv_tt T
with notin_fv_tpt_open_tpt : forall (Y X : atom) T,
  X `notin` fv_tpt (open_tpt T Y) ->
  X `notin` fv_tpt T.
Proof with eauto.
  intros. apply notin_fv_tt_open_tt_rec with (k := 0) (Y := Y)...
  intros. apply notin_fv_tpt_open_tpt_rec with (k := 0) (Y := Y)...
Qed.

Lemma notin_cset_fvars_open_cset : forall X k C c,
  X `~in`A `cset_fvars` (open_cset k C c) ->
  X `~in`A `cset_fvars` c.
Proof.
  intros.
  destruct c.
  intros XIn.
  cbv in H.
  csetdec.
Qed.

Lemma notin_fv_tt_open_ct_rec : forall (Y X : atom) T k,
  X `notin` fv_ct (open_tt_rec k Y T) ->
  X `notin` fv_ct T
with notin_fv_tt_open_cpt_rec : forall (Y X : atom) T k,
  X `notin` fv_cpt (open_tpt_rec k Y T) ->
  X `notin` fv_cpt T.
Proof with eauto using notin_cset_fvars_open_cset.
------
  intros Y X T. unfold open_tt_rec.
  induction T; simpl; intros k Fr; notin_simpl; try apply notin_union...
------
  intros Y X T. unfold open_tt_rec.
  induction T; simpl; intros k Fr; notin_simpl; try apply notin_union...
Qed.

Lemma notin_fv_tt_open_ct : forall (Y X : atom) T,
  X `notin` fv_ct (open_tt T Y) ->
  X `notin` fv_ct T
with notin_fv_tt_open_cpt : forall (Y X : atom) T,
  X `notin` fv_cpt (open_tpt T Y) ->
  X `notin` fv_cpt T.
Proof with eauto.
  intros. apply notin_fv_tt_open_ct_rec with (k := 0) (Y := Y)...
  intros. apply notin_fv_tt_open_cpt_rec with (k := 0) (Y := Y)...
Qed.

Lemma notin_fv_tt_open : forall (Y X : atom) T,
  X `notin` fv_tt (open_tt T Y) ->
  X `notin` fv_ct (open_tt T Y) ->
  X `notin` (fv_tt T `union` fv_ct T).
Proof with auto.
 intros. apply notin_union.
 - apply notin_fv_tt_open_tt with (Y := Y)...
 - apply notin_fv_tt_open_ct with (Y := Y)...
Qed.

Lemma notin_fv_ct_open_tt_rec : forall (X : atom) T C k,
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

Lemma notin_fv_ct_open_tt : forall (X : atom) T C,
  X `notin` fv_tt (open_ct T C) ->
  X `notin` fv_tt T
with notin_fv_cpt_open_tpt : forall (X : atom) T C,
  X `notin` fv_tpt (open_cpt T C) ->
  X `notin` fv_tpt T.
Proof with eauto.
  intros. apply notin_fv_ct_open_tt_rec with (k := 0) (C := C)...
  intros. apply notin_fv_cpt_open_tpt_rec with (k := 0) (C := C)...
Qed.

Lemma notin_fv_ct_open_ct_rec : forall (X : atom) T C k,
  X `notin` fv_ct (open_ct_rec k C T) ->
  X `notin` fv_ct T
with notin_fv_ct_open_cpt_rec : forall (X : atom) T C k,
  X `notin` fv_cpt (open_cpt_rec k C T) ->
  X `notin` fv_cpt T.
Proof with auto.
------
  intros X T C.
  induction T ; simpl ; intros k Fr ; try apply notin_union; eauto.
  - apply notin_cset_fvars_open_cset with (k := k) (C := C)...
  - apply notin_fv_ct_open_cpt_rec with (C := C) (k := k)...
------
    intros X T C.
    induction T ; simpl ; intros k Fr ; try apply notin_union; eauto.
    - apply notin_fv_ct_open_ct_rec with (C := C) (k := k)...
    - apply notin_fv_ct_open_ct_rec with (C := C) (k := S k)...
    - apply notin_fv_ct_open_ct_rec with (C := C) (k := k)...
    - apply notin_fv_ct_open_ct_rec with (C := C) (k := S k)...
Qed.

Lemma notin_fv_ct_open_ct : forall (X : atom) T C,
  X `notin` fv_ct (open_ct T C) ->
  X `notin` fv_ct T
with notin_fv_ct_open_cpt : forall (X : atom) T C,
  X `notin` fv_cpt (open_cpt T C) ->
  X `notin` fv_cpt T.
Proof with auto.
  intros. apply notin_fv_ct_open_ct_rec with (k := 0) (C := C)...
  intros. apply notin_fv_ct_open_cpt_rec with (k := 0) (C := C)...
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
  X `notin` fv_ct (open_ct T C) ->
  X `notin` fv_tt (open_ct T C) ->
  X `notin` (fv_tt T `union` fv_ct T).
Proof with auto.
  intros. apply notin_union...
  - apply notin_fv_ct_open_tt with (C := C)...
  - apply notin_fv_ct_open_ct with (C := C)...
Qed.

Lemma notin_fv_wf_typ : forall E Ap Am (X : atom) T,
  wf_typ E Ap Am T ->
  X `notin` dom E ->
  X `notin` (fv_tt T `union` fv_ct T)
with notin_fv_wf_pretyp : forall E Ap Am (X : atom) T,
  wf_pretyp E Ap Am T ->
  X `notin` dom E ->
  X `notin` (fv_tpt T `union` fv_cpt T).
Proof with eauto.
-------
  intros * Wf_typ.
  induction Wf_typ; intros FrE; simpl...
  - assert (X0 `in` dom E) by (eapply binds_In; eauto)...
  - specialize (notin_fv_wf_pretyp _ _ _ _ _ H0 FrE) as Wf.
    inversion H; destruct C; subst; simpl in *; try notin_solve.
    assert (X `notin` fvars). {
      unfold allbound in *.
      intro Hin; specialize (H1 X Hin) as [T B].
      destruct B as [B|B]; apply binds_In in B; intuition.
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
      apply notin_fv_ct_open_tt with (C := (`cset_fvar` Y)).
      notin_solve.
    }
    assert (X `notin` fv_ct T2). {
      apply notin_fv_ct_open_ct with (C := (`cset_fvar` Y)); try discriminate.
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
    assert (X `notin` fv_ct T2). {
      apply notin_fv_tt_open_ct with (Y := Y); try discriminate.
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
  assert (X `notin` (fv_tt T `union` fv_ct T)). {
    eapply notin_fv_wf_typ...
  }
  fsetdec.
Qed.

Lemma notin_fv_ee_open_ee_rec : forall k u (y x : atom) t,
  x `notin` fv_ee (open_ee_rec k u (`cset_fvar` y) t) ->
  x <> y ->
  x `notin` fv_ee t.
Proof with eauto.
  intros. generalize dependent k.
  induction t; simpl in *; intros k H; try (trivial || notin_solve).
  - apply (IHt (S k)). notin_solve.
  - apply notin_union...
    + apply (IHt1 k). notin_solve.
    + apply (IHt2 k). notin_solve.
  - eapply (IHt (S k)). notin_solve.
  - apply (IHt k). notin_solve.
  - apply (IHt (S k)). notin_solve.
  - apply notin_union...
    + apply (IHt1 k). notin_solve.
    + apply (IHt2 k). notin_solve.
Qed.

Lemma notin_fv_ee_open_ee : forall u (y x : atom) t,
  x `notin` fv_ee (open_ee t u (`cset_fvar` y)) ->
  x <> y ->
  x `notin` fv_ee t.
Proof with eauto.
  intros. unfold open_ee in *.
  apply (notin_fv_ee_open_ee_rec 0 u y)...
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

Lemma notin_fv_ee_open_te_rec : forall k (y x : atom) t,
  x `notin` fv_ee (open_te_rec k y t) ->
  x <> y ->
  x `notin` fv_ee t.
Proof with eauto.
  intros. generalize dependent k.
  induction t; simpl in *; intros k H; try (trivial || notin_solve).
  - apply (IHt (S k)). notin_solve.
  - apply notin_union...
    + apply (IHt1 k). notin_solve.
    + apply (IHt2 k). notin_solve.
  - apply (IHt (S k)). notin_solve.
  - apply (IHt k). notin_solve.
  - apply (IHt (S k)). notin_solve.
  - apply notin_union...
    + apply (IHt1 k). notin_solve.
    + apply (IHt2 k). notin_solve.
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
    rewrite <- subst_tt_fresh... eapply notin_fv_wf_typ; eauto.
  rewrite <- IHwf_env...
    rewrite <- subst_tt_fresh... eapply notin_fv_wf_typ; eauto.
Qed.


(* ********************************************************************** *)
(** * #<a name="cvfree"></a># Lemmas about free variables -- in particular properties of [free_for_cv] *)
(** TODO Maybe have a separate file for free_for_cv lemmas **)


Lemma cv_free_never_universal : forall e,
  ~ `* in` (free_for_cv e).
Proof with eauto*.
  intros. induction e; unfold free_for_cv; try discriminate...
  - fold free_for_cv.
    unfold cset_union...
    destruct (free_for_cv e1) eqn:Hfc1;
      destruct (free_for_cv e2) eqn:Hfc2...
    csetdec.
  - fold free_for_cv.
    unfold cset_union...
    destruct (free_for_cv e1) eqn:Hfc1;
      destruct (free_for_cv e2) eqn:Hfc2...
    csetdec.
Qed.

Lemma cv_free_has_universal_false : forall e,
  `* mem` (free_for_cv e) = false.
Proof.
  intros.
  destruct (`* mem` (free_for_cv e)) eqn:EQ; trivial.
  pose proof (cv_free_never_universal e).
  intuition.
Qed.

Lemma cv_free_is_bvar_free : forall e,
  NatSet.F.Empty (`cset_bvars` (free_for_cv e)).
Proof with eauto.
  intros. induction e; fnsetdec...
Qed.

Lemma cv_free_atom : forall (x : atom),
  free_for_cv x = (`cset_fvar` x).
Proof with auto*.
  intros.
  unfold free_for_cv...
Qed.

Lemma free_for_cv_open : forall e k (y : atom),
  cset_subset_prop (free_for_cv e) (free_for_cv (open_ee_rec k y (`cset_fvar` y) e)).
Proof with eauto*.
  intros e.
  induction e; intros; simpl...
  - destruct (k === n); constructor; fsetdec...
  - specialize (IHe1 k y).
    specialize (IHe2 k y).
    csetdec.
    pose proof (cv_free_has_universal_false) as HA.
    repeat rewrite HA...
  - specialize (IHe1 k y).
    specialize (IHe2 k y).
    csetdec.
    pose proof (cv_free_has_universal_false) as HA.
    repeat rewrite HA...
Qed.

Lemma free_for_cv_open_type : forall e k (y : atom),
  cset_subset_prop (free_for_cv e) (free_for_cv (open_te_rec k y e)).
Proof with eauto*.
  intros e; induction e; intros; simpl...
  - specialize (IHe1 k y).
    specialize (IHe2 k y).
    csetdec.
    pose proof (cv_free_has_universal_false) as HA.
    repeat rewrite HA...
  - specialize (IHe1 k y).
    specialize (IHe2 k y).
    csetdec.
    pose proof (cv_free_has_universal_false) as HA.
    repeat rewrite HA...
Qed.

Lemma free_for_cv_bound : forall E e (x : atom),
  wf_cset_in E (free_for_cv e) ->
  x A`in` (free_for_cv e) ->
  exists T, bound x T E.
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
  - apply wf_cset_over_union in H...
    apply cset_references_fvar_over_union in H0...
    inversion H0.
    + apply IHe1... apply H.
    + apply IHe2... apply H.
  - assert (x = a) by fsetdec; subst...
    inversion H; subst...
Qed.

Lemma free_for_cv_is_free_ee : forall e,
  cset_subset_prop (free_for_cv e) (cset_set (fv_ee e) {}N false).
Proof with eauto using cv_free_never_universal; eauto*.
  intros e.
  (** gah why doesn't eauto pick this up. *)
  induction e; try destruct (free_for_cv e) eqn:Hcve;
    subst; simpl; try rewrite Hcve; try constructor; try inversion IHe;
      csetdec.
  - pose proof cv_free_has_universal_false as HA.
    repeat rewrite HA...
  - pose proof cv_free_has_universal_false as HA.
    repeat rewrite HA...
Qed.

Lemma free_for_cv_bound_typing : forall E e (x : atom) S,
  typing E e S ->
  x A`in` (free_for_cv e) ->
  exists T, binds x (bind_typ T) E.
Proof with eauto using wf_cset_over_union, cv_free_never_universal.
  intros * Htyp xIn.
  induction Htyp; simpl in *...
  - assert (x = x0) by fsetdec; subst...
  - assert (x = x0) by fsetdec; subst...
  - pick fresh y.
    forwards HA: H2 y.
    + notin_solve.
    + forwards (? & ? & ?): free_for_cv_open e1 0 y.
      unfold open_ee.
      clear Fr;fsetdec.
    + destruct HA as (T & HA)...
      inversion HA.
      assert (x <> y) by notin_solve.
      destruct (x == y)...
      easy.
  - destruct_union_mem xIn...
  - pick fresh y.
    forwards HA: H2 y.
    + notin_solve.
    + forwards (? & ? & ?): free_for_cv_open_type e1 0 y.
      clear Fr;fsetdec.
    + destruct HA as (T & HA)...
      inversion HA.
      assert (x <> y) by notin_solve.
      destruct (x == y)...
      easy.
  - pick fresh y.
    forwards HA: H0 y.
    + notin_solve.
    + forwards (? & ? & ?): free_for_cv_open e 0 y.
      clear Fr.
      fsetdec.
    + destruct HA as (T & HA)...
      inversion HA.
      assert (x <> y) by notin_solve.
      destruct (x == y)...
      easy.
  - destruct_union_mem xIn...
  - assert (x = x0) by fsetdec; subst...
Qed.

(** This should be easily true: free variables
    are all bound if a term has a type.... *)
Lemma typing_cv : forall E e T,
  typing E e T ->
  wf_cset_in E (free_for_cv e).
Proof with eauto using cv_free_never_universal, wf_cset_over_union; eauto*.
  intros * Htyp.
  induction Htyp; simpl...
  (** TODO: merge the abs/t-abs case somehow (maybe a match to decide what
      gets posed? )*)
  - forwards: binds_In H0.
    simpl. constructor...
    intros y ?.
    assert (x = y) by fsetdec.
    subst. exists X...
  - forwards: binds_In H0.
    simpl. constructor...
    intros y ?.
    assert (x = y) by fsetdec.
    subst. exists (typ_capt C P)...
  - pick fresh y.
    assert (y `notin` L) by fsetdec.
    assert (~ y A`in` (free_for_cv e1)). {
      pose proof (free_for_cv_is_free_ee e1) as P...
      inversion P; subst.
      simpl in *.
      csetdec.
    }
    forwards SpH0: H2 y...
    pose proof (free_for_cv_open e1 0 y)...
    pose proof (cv_free_never_universal).
    pose proof (cv_free_is_bvar_free e1).
    destruct (free_for_cv e1) eqn:Hfcv1; subst...
    unfold open_ee in *.
    inversion SpH0; subst...
    rename select (_ = _) into EQ.
    rename select (cset_subset_prop _ _) into HH.
    destruct HH as (HA1 & HA2 & HA3).
    rewrite <- EQ in *.
    simpl in *.
    assert (t0 = {}N) by fnsetdec; subst...
    constructor.
    2: clear Fr; fsetdec.
    intros x ?.
    destruct (x == y). {
      csetdec.
    }
    forwards (T & B): H9 x. {
      fsetdec.
    }
    simpl_env in *.
    exists T. destruct B as [B|B]; binds_cases B...
  - apply wf_cset_over_union...
  - (* typing_app_poly *)
    pick fresh y.
    assert (y `notin` L) by fsetdec.
    assert (~ y A`in` (free_for_cv e1)). {
      pose proof (free_for_cv_is_free_ee e1) as P...
      inversion P; subst.
      simpl in *.
      csetdec.
    }
    forwards SpH0: H2 y...
    pose proof (free_for_cv_open_type e1 0 y)...
    pose proof (cv_free_never_universal).
    pose proof (cv_free_is_bvar_free e1).
    destruct (free_for_cv e1) eqn:Hfcv1; subst...
    unfold open_te in *.
    inversion SpH0; subst...
    rename select (_ = _) into EQ.
    rewrite <- EQ in *.
    rename select (cset_subset_prop _ _) into HH.
    destruct HH as (HA1 & HA2 & HA3).
    simpl in *.
    assert (t0 = {}N) by fnsetdec; subst...
    constructor.
    2: clear Fr; fsetdec.
    intros x ?.
    destruct (x == y). {
      csetdec.
    }
    forwards (T & B): H9 x. {
      fsetdec.
    }
    simpl_env in *.
    exists T. destruct B as [B|B]; binds_cases B...
  - admit.
  - admit.
  - admit.
Admitted.


Lemma subst_cset_fresh_for_cv : forall z t C,
  z `notin` fv_ee t ->
  (subst_cset z C (free_for_cv t)) = (free_for_cv t).
Proof.
  intros.
  induction t; simpl in H |- *.
  - cbv.
    replace (AtomSet.F.mem z {}A) with false by fset_mem_dec.
    reflexivity.
  - cbv.
    replace (AtomSet.F.mem z (singleton a)) with false by fset_mem_dec.
    reflexivity.
  - apply IHt. fsetdec.
  - rewrite subst_cset_distributive_across_union.
    rewrite IHt1 by notin_solve.
    rewrite IHt2 by notin_solve.
    reflexivity.
  - apply IHt. fsetdec.
  - apply IHt. fsetdec.
  - apply IHt. fsetdec.
  - rewrite subst_cset_distributive_across_union.
    rewrite IHt1 by notin_solve.
    rewrite IHt2 by notin_solve.
    reflexivity.
  - cbv.
    replace (AtomSet.F.mem z (singleton a)) with false by fset_mem_dec.
    reflexivity.
Qed.


Lemma subst_commutes_with_free_for_cv : forall x u C e,
  x `notin` (`cset_fvars` (free_for_cv e)) ->
  (subst_cset x C (free_for_cv e)) = (free_for_cv (subst_ee x u C e)).
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
    assert (a <> x) by fsetdec.
    destruct (a == x); try easy.
    cbv.
    destruct_if.
    + rewrite <- AtomSetFacts.mem_iff in Heqb. exfalso. fsetdec.
    + reflexivity.
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

Lemma subst_te_idempotent_wrt_free_for_cv : forall e x C,
  free_for_cv (subst_te x C e) = free_for_cv e.
Proof with eauto.
  intros.
  induction e; simpl...
  - rewrite IHe1.
    rewrite IHe2...
  - rewrite IHe1.
    rewrite IHe2...
Qed.

Lemma bind_typ_notin_fv_tt : forall x S E Ap Am T,
  binds x (bind_typ S) E ->
  wf_typ E Ap Am T ->
  x `~in`A fv_tt T
with bind_typ_notin_fv_tpt : forall x S E Ap Am T,
  binds x (bind_typ S) E ->
  wf_pretyp E Ap Am T ->
  x `~in`A fv_tpt T.
Proof with auto.
{ intros * Hbnd WfT.
  dependent induction T;simpl...
  - inversion WfT; subst.
    eapply bind_typ_notin_fv_tpt; eauto.
  - inversion WfT; subst.
    destruct (x == a); [|fsetdec].
    subst.
    forwards: binds_unique a; eauto.
}
{ intros * Hbnd WfT.
  dependent induction T; simpl.
  - fsetdec.
  - inversion WfT; subst.
    rename H4 into Wf__t.
    rename H5 into Wf__t0.
    pick fresh y.
    specialize (Wf__t0 y ltac:(fsetdec)).
    forwards: bind_typ_notin_fv_tt Wf__t; [eauto|..].
    forwards HA: bind_typ_notin_fv_tt x Wf__t0; [eauto|..].
    forwards: notin_fv_ct_open_tt HA.
    notin_solve.
  - inversion WfT; subst.
    rename H4 into Wf__t.
    rename H5 into Wf__t0.
    pick fresh y.
    specialize (Wf__t0 y ltac:(fsetdec)).
    forwards: bind_typ_notin_fv_tt Wf__t; [eauto|..].
    forwards HA: bind_typ_notin_fv_tt x Wf__t0; [eauto|..].
    forwards: notin_fv_tt_open_tt HA.
    notin_solve.
  - inversion WfT; subst.
    eapply bind_typ_notin_fv_tt...
    admit.
}
Admitted.

(* ********************************************************************** *)
(** * #<a name="regularity"></a># Regularity of relations *)

Lemma subcapt_regular : forall E C D,
  subcapt E C D ->
  wf_cset_in E C /\ wf_cset_in E D.
Proof with eauto*.
  (* Useful when copying this lemma to definitions. *)
  Require Import Program.Equality.
  Require Import TaktikZ.
  intros* H.
  dependent induction H; subst...
  - split...
    constructor.
    2: {
      apply binds_In in H...
    }
    intros y yInX.
    rewrite AtomSetFacts.singleton_iff in yInX; subst...
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
      rename select (allbound _ _) into HABnd.
      applys HABnd y.
      fsetdec.
    + intros y yIn.
      forwards (WfX & _): H1 y yIn.
      inversion WfX; subst.
      fsetdec.
Qed.

(* TODO check whether we need those and otherwise drop *)
Hint Unfold wf_typ_in : core.
Hint Unfold wf_pretyp_in : core.

Lemma sub_regular : forall E S T,
  sub E S T ->
  wf_env E /\ wf_typ_in E S /\ wf_typ_in E T
with sub_pre_regular : forall E S T,
  sub_pre E S T ->
  wf_env E /\ wf_pretyp_in E S /\ wf_pretyp_in E T.
Proof with simpl_env; eauto*.
------
  intros E S T H.
  induction H.
  - repeat split...
  - Case "sub_trans_tvar".
    repeat split...
    apply wf_typ_var with (U := U)...
    eapply binds_In...
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
      apply wf_typ_arrow with (L := L); auto* ..
    ].
  - Case "sub_all".
    pose proof (sub_regular E _ _ H).
    repeat split.
    + auto*.
    + apply wf_typ_all with (L := L `u`A dom E)...
    + apply wf_typ_all with (L := L `u`A dom E)...
  - pose proof (sub_regular E _ _ H).
    repeat split...
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
    + intros y ?.
      assert (y = x) by fsetdec; subst; eauto.
    + assert (x `in` dom E).
      eapply binds_In.
      apply H0.
      fsetdec.
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
      eapply (wf_typ_all (L `u`A dom E))...
  (* typing rule: type application *)
  - destruct IHtyping as [HwfE [Hexpr Hwf]]...
    forwards (R1 & R2 & R3): sub_regular H0...
    repeat split...
    + constructor...
      eapply type_from_wf_typ with (E := E); apply R2.
    + apply wf_typ_open with (T1 := T1)...
      inversion Hwf; subst...
  - repeat split...
    forwards: sub_regular H0...
  - admit.
  - admit.
  - admit.
Admitted.

Lemma value_regular : forall e,
  value e ->
  expr e.
Proof.
  intros e H. induction H; auto.
Qed.

(* Lemma red_regular : forall e e', *)
(*   red e e' -> *)
(*   expr e /\ expr e'. *)
(* Proof with auto*. *)
(*   intros e e' H. *)
(*   induction H; assert (J := value_regular); split... *)
(*   - Case "red_abs". *)
(*     inversion H. pick fresh y. *)
(*     rewrite (subst_ee_intro y)... *)
(*     eapply subst_ee_expr... *)
(*     pose proof (cv_free_is_bvar_free v2). *)
(*     destruct (free_for_cv v2); subst... *)
(*   - Case "red_tabs". *)
(*     inversion H. pick fresh Y. rewrite (subst_te_intro Y)... *)
(* Qed. *)


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
  end
: core.

Hint Extern 1 (wf_env ?E) =>
  match goal with
  | H: sub _ _ _ |- _ => apply (proj1 (sub_regular _ _ _ H))
  | H: sub_pre _ _ _ |- _ => apply (proj1 (sub_pre_regular _ _ _ H))
  | H: typing _ _ _ |- _ => apply (proj1 (typing_regular _ _ _ H))
  end
: core.

Hint Extern 1 (wf_typ ?E _ _ ?T) =>
  match goal with
  | H: typing E _ T |- _ => apply (proj2 (proj2 (typing_regular _ _ _ H)))
  | H: sub E T _ |- _ => apply (proj1 (proj2 (sub_regular _ _ _ H)))
  | H: sub E _ T |- _ => apply (proj2 (proj2 (sub_regular _ _ _ H)))
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
  (* | H: red ?e _ |- _ => apply (proj1 (red_regular _ _ H)) *)
  (* | H: red _ ?e |- _ => apply (proj2 (red_regular _ _ H)) *)
  end
: core.

Hint Extern 1 (wf_pretyp ?E (dom ?E) (dom ?E) ?P) =>
match goal with
| H : typing E _ (typ_capt _ P) |- _ =>
  apply typing_regular in H;
  destruct H as [_ [_ H]];
  inversion H; subst; assumption
end : core.

Hint Extern 1 (wf_pretyp_in ?E ?P) =>
match goal with
| H : typing E _ (typ_capt _ P) |- _ =>
  apply typing_regular in H;
  destruct H as [_ [_ H]];
  inversion H; subst; assumption
end : core.

(** * #<a name="auto"></a># Automation Tests *)

Local Lemma test_subcapt_regular : forall E C1 C2,
  subcapt E C1 C2 ->
  wf_cset E (dom E) C1 /\ wf_cset E (dom E) C2.
Proof with eauto*.
  intros.
  repeat split.
  all: auto.
Qed.
