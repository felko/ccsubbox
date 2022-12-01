Require Import Coq.Program.Equality.

Require Export CCsub_Infrastructure.
Require Import Atom.

Require Import TaktikZ.

(* ********************************************************************** *)
(** * #<a name="utils"></a># Automation Utils -- mostly related to wellformedness of environments [ok], [wf_env], [dom], ...*)


Lemma capt_from_wf_cset : forall Γ C,
  Γ ⊢ₛ C wf -> capt C.
Proof with auto.
  intros.
  inversion H...
Qed.

Lemma capt_from_wf_cset_in : forall Γ C, Γ ⊢ₛ C wf -> capt C.
Proof. eauto using capt_from_wf_cset. Qed.

Hint Resolve capt_from_wf_cset_in : core.

Lemma allbound_over_union : forall Γ T1 T2,
  allbound Γ (T1 `u`A T2) ->
  allbound Γ T1 /\ allbound Γ T2.
Proof with eauto*.
  intros.
  split; intros ? ?; assert (x `in` (T1 `u`A T2)) by fsetdec...
Qed.

Lemma allbound_weaken : forall Γ T1 T2,
  T1 `c`A T2 ->
  allbound Γ T2 ->
  allbound Γ T1.
Proof with eauto*.
  intros * T1_subset_T2 T2_bound.
  intros x x_in_T1.
  apply (T2_bound x ltac:(fsetdec)).
Qed.

Lemma ok_from_wf_env : forall Γ,
  Γ ⊢ wf ->
  ok Γ.
Proof.
  intros Γ H; induction H; auto.
Qed.

(** We add [ok_from_wf_env] as a hint here since it helps blur the
    distinction between [wf_env] and [ok] in proofs.  The lemmas in
    the [Environment] library use [ok], whereas here we naturally have
    (or can easily show) the stronger [wf_env].  Thus,
    [ok_from_wf_env] serves as a bridge that allows us to use the
    environments library. *)

Hint Resolve ok_from_wf_env : core.

(* This lemma is needed by a couple of lemmas about wf_typ *)
Lemma wf_env_tail : forall Γ Δ,
  (Δ ++ Γ) ⊢ wf ->
  Γ ⊢ wf.
Proof with eauto.
  intros * Hwf.
  induction Δ; (trivial || inversion Hwf; subst)...
Qed.

Hint Resolve wf_env_tail : core.

Hint Extern 1 (ok (map ?f ?Δ ++ ?Γ)) =>
match goal with
| H : (Δ ++ ?b ++ Γ) ⊢ wf |- _ =>
  enough (ok (Δ ++ b ++ Γ))
end : core.

(* TODO WHERE TO PUT THIS? *)
Lemma dom_x_subst_away : forall x f b Γ Δ,
  (Δ ++ [(x, b)] ++ Γ) ⊢ wf ->
  dom (map f Δ ++ Γ) = dom (Δ ++ [(x, b)] ++ Γ) `remove` x.
Proof with eauto*.
  intros * Hwf.
  simpl_env in *.
  assert (x `notin` (dom Δ `u`A dom Γ)). {
    pose proof (binding_uniq_from_ok _ Δ Γ x _ ltac:(eauto)).
    fsetdec.
  }
  fsetdec.
Qed.

Lemma binding_uniq_from_wf_env : forall F E x b,
  (F ++ ([(x, b)]) ++ E) ⊢ wf ->
  x `~in`A (dom F `union` dom E).
Proof.
  intros.
  apply ok_from_wf_env in H.
  eapply binding_uniq_from_ok; eauto.
Qed.

Lemma distinct_binding_from_wf_env : forall F x b E y,
  (F ++ [(x, b)] ++ E) ⊢ wf ->
  y `in`A dom E ->
  y `~in`A dom F.
Proof.
  intros * H ?.
  induction F.
  - simpl_env; fsetdec.
  - inversion H; subst;
      specialize (IHF H3); simpl_env in *; fsetdec.
Qed.


(* ********************************************************************** *)
(** * #<a name="wfset"></a># Properties of [wf_cset] *)

Lemma empty_cset_wf : forall Γ, Γ ⊢ₛ {} wf.
Proof.
  intros.
  constructor.
  - intros ? ?. fsetdec.
  - fsetdec.
Qed.

Lemma univ_cset_wf : forall Γ, Γ ⊢ₛ {*} wf.
Proof.
  intros.
  constructor.
  - intros ? ?. fsetdec.
  - fsetdec.
Qed.

Hint Resolve empty_cset_wf univ_cset_wf : core.

Lemma wf_cset_union : forall Γ C D,
  Γ ⊢ₛ C wf ->
  Γ ⊢ₛ D wf ->
  Γ ⊢ₛ (C `u` D) wf.
Proof with eauto.
  intros *.
  intros H1 H2.
  inversion H1; inversion H2; subst; simpl...
  unfold cset_union; csetsimpl.
  constructor...
  unfold allbound in *...
  intros.
  rewrite AtomSetFacts.union_iff in *.
  auto*.
  fsetdec.
Qed.

Lemma wf_cset_remove_fvar : forall Γ C x,
  Γ ⊢ₛ C wf ->
  Γ ⊢ₛ (C A`\` x) wf.
Proof with eauto.
  intros.
  induction H; simpl...
  constructor...
  unfold allbound in *.
  intros.
  apply H.
  fsetdec.
  fsetdec.
Qed.

Lemma wf_cset_over_union : forall Γ C D,
  Γ ⊢ₛ (C `u` D) wf <->
  Γ ⊢ₛ C wf /\ Γ ⊢ₛ D wf.
Proof with eauto*.
  intros; split; intros; destruct C eqn:HC1;
                         destruct D eqn:HC2;
                         unfold cset_union in *...
  - inversion H; subst...
    apply empty_over_union in H1; inversion H1.
    apply allbound_over_union in H3; inversion H3.
    subst.
    split; constructor...
    fsetdec.
    fsetdec.
  - destruct H as [Hwf1 Hwf2].
    inversion Hwf1; inversion Hwf2; subst...
    csetsimpl.
    (** this should really be a lemma... *)
    (* assert (NatSet.F.union {}N {}N = {}N) by fnsetdec; rewrite H1. *)
    constructor.
    + intros ? ?.
      apply AtomSetFacts.union_iff in H...
    + fsetdec.
Qed.

(** The things that the cv relation returns are all well-formed,
    assuming the type is well formed... *)
Lemma cv_wf : forall Γ T,
  Γ ⊢ T wf ->
  Γ ⊢ₛ (typ_cv T) wf.
Proof with simpl_env; eauto using empty_cset_wf.
  intros * HC.
  inversion HC; simpl; subst...
  constructor.
  - intros y yIn.
    rewrite AtomSetFacts.singleton_iff in yIn; symmetry in yIn; subst...
  - enough (X `in`A dom Γ) by fsetdec.
    apply binds_In in H... 
Qed.


(** This is a useful helper tactic for clearing away
    capture set wellformedness. *)

Ltac wf_cset_simpl instantiate_ext :=
  match goal with
  | H : _ |- (_ ⊢ₛ {*} wf) =>
    constructor
  | H : (_ ⊢ₛ ?C wf) |- (_ ⊢ₛ ?C wf) =>
    let x  := fresh "x" in
    let Hx := fresh "In" x in
    let Hexists := fresh "Hexists" in
    let T := fresh "T" in
    let Hbound := fresh "Hbound" in
    inversion H;
    rename select (allbound _ _) into Hbound;
    subst; constructor;
    [ intros x Hx;
      destruct (Hbound x Hx) as [T Hexists];
      lazymatch instantiate_ext with
      | True => exists T; destruct Hexists; auto
      | False => idtac
      end
    | (* REVIEW: automation broke here, it seems that dom_concat is not automatically rewritten (see below) *)
      try fsetdec
    ]
  end.

Lemma wf_cset_weakening : forall Γ Θ Δ C,
  (Δ ++ Γ) ⊢ₛ C wf ->
  ok (Δ ++ Θ ++ Γ) ->
  (Δ ++ Θ ++ Γ) ⊢ₛ C wf.
Proof with auto*.
  intros * Hwf Hok.
  wf_cset_simpl True...
  rewrite dom_concat in H0.
  repeat rewrite dom_concat.
  fsetdec.
Qed.

Lemma wf_cset_weaken_head : forall C Γ Δ,
  Γ ⊢ₛ C wf ->
  ok (Δ ++ Γ) ->
  (Δ ++ Γ) ⊢ₛ C wf.
Proof.
  intros.
  rewrite_env (nil ++ Δ ++ Γ).
  apply wf_cset_weakening; auto.
Qed.

Ltac destruct_bound H :=
  destruct H as [H|H].

(* Type bindings don't matter at all! *)
Lemma wf_cset_narrowing : forall V U C Γ Δ X,
  (Δ ++ [(X, bind_sub V)] ++ Γ) ⊢ₛ C wf ->
  ok (Δ ++ [(X, bind_sub U)] ++ Γ) ->
  (Δ ++ [(X, bind_sub U)] ++ Γ) ⊢ₛ C wf.
Proof with simpl_env; eauto.
  intros *.
  intros Hwf Hok.
  wf_cset_simpl False...
  - rename Hexists into B;
    destruct_bound B; binds_cases B...
  - repeat rewrite dom_concat in H0; simpl in H0.
    fsetdec. 
Qed.

Lemma wf_cset_narrowing_typ : forall C1 C2 C Γ Δ X,
  (Δ ++ [(X, bind_typ C1)] ++ Γ) ⊢ₛ C wf ->
  ok (Δ ++ [(X, bind_typ C2)] ++ Γ) ->
  (Δ ++ [(X, bind_typ C2)] ++ Γ) ⊢ₛ C wf.
Proof with simpl_env; eauto.
  intros * Hwf Hok.
  wf_cset_simpl False.
  - rename Hexists into B;
    destruct_bound B; binds_cases B...
  - repeat rewrite dom_concat; simpl.
    repeat rewrite dom_concat in H0; simpl in H0.
    fsetdec. 
Qed.

Lemma wf_cset_ignores_typ_bindings : forall Γ Δ x T1 T2 C,
  (Δ ++ [(x, bind_typ T1)] ++ Γ) ⊢ₛ C wf ->
  (Δ ++ [(x, bind_typ T2)] ++ Γ) ⊢ₛ C wf.
Proof with eauto.
  intros*.
  intros H.
  remember (Δ ++ [(x, bind_typ T1)] ++ Γ).
  generalize dependent Δ.
  induction H; intros Δ Eq; subst...
  econstructor...
  - unfold allbound in *.
    intros.
    destruct (H x0 H1) as [T Hb].
    destruct_bound Hb; binds_cases Hb...
  - repeat rewrite dom_concat; simpl.
    repeat rewrite dom_concat in H0; simpl in H0.
    fsetdec. 
Qed.

Lemma wf_cset_ignores_sub_bindings : forall Γ Δ x T1 T2 C,
  (Δ ++ [(x, bind_sub T1)] ++ Γ) ⊢ₛ C wf ->
  (Δ ++ [(x, bind_sub T2)] ++ Γ) ⊢ₛ C wf.
Proof with eauto.
  intros * H.
  remember (Δ ++ [(x, bind_sub T1)] ++ Γ).
  generalize dependent Δ.
  induction H; intros Δ Eq; subst...
  econstructor...
  - unfold allbound in *.
    intros.
    destruct (H x0 H1) as [T Hb].
    destruct_bound Hb; binds_cases Hb...
  - repeat rewrite dom_concat; simpl.
    repeat rewrite dom_concat in H0; simpl in H0.
    fsetdec. 
Qed.

Create HintDb fsetdec.

Hint Extern 1 (_ `in` _) => fsetdec: fsetdec.

Lemma wf_cset_singleton_by_mem : forall xs b1 Γ x b2,
  Γ ⊢ₛ (cset_set xs {}N b1) wf ->
  x `in` xs ->
  Γ ⊢ₛ (cset_set {x}A {}N b2) wf.
Proof with eauto with fsetdec.
  intros * Wfxs xIn.
  inversion Wfxs; subst...
  constructor...
  - intros y yIn; assert (y = x) by (clear - yIn; fsetdec); subst; clear yIn.
    apply (H2 x ltac:(fsetdec)).
  - fsetdec.
Qed.

(* NOTE: wf_cset precondition in wf_cset_singleton_by_mem0 can be proven by
         constructor, which leaves an uninstantiated evar. This approach avoids the
         problem. *)
Hint Extern 1 (wf_cset ?Γ (cset_set {?x}A {}N _ _)) =>
match goal with
| H1 : x `in` ?xs , H2 : (wf_cset ?Γ (cset_set ?xs {}N ?b ?ls)) |- _ =>
  apply (wf_cset_singleton_by_mem xs b ls)
end : core.

Local Lemma __test_wf_cset_singleton2 : forall xs b1 Γ x b2,
  Γ ⊢ₛ (cset_set xs {}N b1) wf ->
  x `in` xs ->
  Γ ⊢ₛ (cset_set {x}A {}N b2) wf.
Proof with eauto*.
  intros.
  constructor.
  - intros x' x'_in_x.
    assert (x' = x) by fsetdec; subst.
    inversion H; subst...
  - enough (xs `c`A dom Γ) by fsetdec.
    inversion H; subst...
Qed.

Local Lemma __test_wf_cset_singleton1 : forall xs b1 Γ x b2,
  Γ ⊢ₛ (cset_set xs {}N b1) wf ->
  x `in` xs ->
  Γ ⊢ₛ (cset_set {x}A {}N b2) wf.
Proof.
  eauto using __test_wf_cset_singleton2.
Qed.

(* ********************************************************************** *)
(** * #<a name="wft"></a># Properties of [wf_typ] *)

Ltac wf_typ_inversion H :=
  inversion H;
  let t := type of H in
  let has_useful_wf_pretyp :=
      fun T =>
        match T with
        | (typ_arr _ _) => true
        | (typ_all _ _) => true
        | _ => false
        end
  in
  let invert_pure_typ :=
      fun Γ T =>
        match goal with
        | H : Γ ⊢ T wf |- _ =>
          inversion H
        end
  in
  match t with
  | ?Γ ⊢ (_ # ?T) wf =>
    match has_useful_wf_pretyp T with
    | true => invert_pure_typ Γ T
    | false => idtac
    end
  | _ => idtac
  end; subst.

Local Lemma test_wf_typ_inversion : forall Γ C S T,
  Γ ⊢ C # ∀ (S) T wf ->
  Γ ⊢ S wf.
Proof.
  intros * H1.
  wf_typ_inversion H1.
  assumption.
Qed.

(** If a type is well-formed in an environment, then it is locally
    closed. *)

Lemma type_from_wf_typ : forall Γ T,
  Γ ⊢ T wf ->
  type T.
Proof with eauto using capt_from_wf_cset.
  intros * H.
  induction H...
Qed.

Tactic Notation "solve_obvious" "with" ident(id) :=
  try solve [econstructor; eauto using id].

Lemma wf_cset_strengthen : forall x Γ Δ C U,
  x `~in`A (`cset_fvars` C) ->
  (Δ ++ [(x, bind_typ U)] ++ Γ) ⊢ₛ C wf ->
  (Δ ++ Γ) ⊢ₛ C wf.
Proof with eauto.
  intros * ? H.
  inversion H; subst.
  econstructor.
  - intros y ?.
    destruct (H1 y H3) as [V ?].
    exists V.
    inversion H4.
    + binds_cases H5...
      fsetdec.
    + binds_cases H5... 
  - rewrite dom_concat.
    repeat rewrite dom_concat in H2; simpl in H2.
    fsetdec.
Qed.

Lemma notin_open_cset_cv : forall k x U c,
  x `~in`A ((`cset_fvars` c) `u`A (`cset_fvars` (typ_cv U))) ->
  x `~in`A (`cset_fvars` (open_cset k (typ_cv U) c)).
Proof with eauto*.
  intros * NotIn.
  unfold open_cset.
  destruct (k N`mem` c)...
Qed.

Lemma notin_open_tt_rec_fv_ct : forall k x T U,
  x `~in`A (fv_ct T `u`A (`cset_fvars` (typ_cv U)) `u`A fv_ct U) ->
  x `~in`A fv_ct (open_tt_rec k U T).
Proof with eauto*.
  intros * NotIn.
  generalize dependent k.
  induction T; intros k; simpl in *...
  induction U; unfold open_vt; destruct v; simpl...
  all: destruct (k === n); simpl; simpl in NotIn...
Qed.

Lemma notin_open_cset : forall k x c d,
  x `~in`A ((`cset_fvars` c) `u`A (`cset_fvars` d)) ->
  x `~in`A (`cset_fvars` (open_cset k c d)).
Proof with eauto*.
  intros * NotIn.
  unfold open_cset.
  destruct (k N`mem` d)...
Qed.

Lemma notin_open_ct_rec_fv_ct : forall k x c T,
  x `~in`A (fv_ct T `u`A (`cset_fvars` c)) ->
  x `~in`A fv_ct (open_ct_rec k c T).
Proof with eauto using notin_open_cset.
  intros * NotIn.
  generalize dependent k.
  induction T; intros k; simpl in *...
Qed.

Lemma wf_typ_strengthen : forall x Γ Δ T U,
  x `~in`A (dom Δ `u`A fv_ct T) ->
  (Δ ++ [(x, bind_typ U)] ++ Γ) ⊢ T wf ->
  (Δ ++ Γ) ⊢ T wf.
Proof with eauto*.
  intros * NotIn WfT.
  eremember (Δ ++ [(x, bind_typ U)] ++ Γ) as Ctx.
  generalize dependent Δ.
  induction WfT; intros Ctx NotIn EQ; subst; simpl in *; notin_simpl; simpl_env in *.
  - binds_cases H; simpl in *; notin_simpl...
  - apply wf_typ_top.
  - pick fresh y and apply wf_typ_arr...
    rewrite_env (([(y, bind_typ (C # R))] ++ Ctx) ++ Γ).
    assert (x <> y) by (clear - Fr; fsetdec).
    apply H0.
    + fsetdec.
    + repeat rewrite dom_concat; simpl.
      repeat apply notin_union...
      apply notin_open_ct_rec_fv_ct...
    + auto.
  - pick fresh Y and apply wf_typ_all...
    rewrite_env (([(Y, bind_sub R)] ++ Ctx) ++ Γ).
    assert (x <> Y) by (clear - Fr; fsetdec).
    apply H1.
    + fsetdec.
    + repeat rewrite dom_concat; simpl.
      repeat apply notin_union...
      apply notin_open_tt_rec_fv_ct...
    + auto.
  - auto.
  - apply wf_typ_capt...
    eapply wf_cset_strengthen...
Qed.

Lemma wf_typ_weakening : forall T Γ Θ Δ,
  (Δ ++ Γ) ⊢ T wf ->
  ok (Δ ++ Θ ++ Γ) ->
  (Δ ++ Θ ++ Γ) ⊢ T wf.
Proof with eauto*.
  intros * Hwf Hok.
  eremember (Δ ++ Γ) as Ctx.
  generalize dependent Δ.
  induction Hwf; intros Δ EQ Hok; subst...
  - pick fresh x and apply wf_typ_arr...
    rewrite_env (([(x, bind_typ (C # R))] ++ Δ) ++ Θ ++ Γ).
    apply H0...
    apply ok_cons...
  - pick fresh X and apply wf_typ_all...
    rewrite_env (([(X, bind_sub R)] ++ Δ) ++ Θ ++ Γ).
    apply H1...
    apply ok_cons...
  - apply wf_typ_capt...
    apply wf_cset_weakening...
Qed.

Lemma wf_typ_weaken_head : forall T Γ Δ,
  Γ ⊢ T wf ->
  ok (Δ ++ Γ) ->
  (Δ ++ Γ) ⊢ T wf.
Proof.
  intros.
  rewrite_env (nil ++ Δ ++ Γ).
  apply wf_typ_weakening; eauto || fsetdec.
Qed.

Lemma wf_typ_ignores_sub_bindings : forall V U T Γ Δ X,
  (Δ ++ [(X, bind_sub V)] ++ Γ) ⊢ T wf ->
  (Δ ++ [(X, bind_sub U)] ++ Γ) ⊢ T wf.
Proof with simpl_env; eauto using wf_cset_ignores_sub_bindings.
  intros.
  remember (Δ ++ [(X, bind_sub V)] ++ Γ).
  generalize dependent Δ.
  induction H; intros Δ Heq; subst...
  - Case "X0".
    binds_cases H...
  - Case "∀ (S) T".
    pick fresh y and apply wf_typ_arr...
    rewrite_env (([(y, bind_typ (C # R))] ++ Δ) ++ [(X, bind_sub U)] ++ Γ).
    apply H1...
  - Case "∀ [R] T".
    pick fresh Y and apply wf_typ_all...
    rewrite_env (([(Y, bind_sub R)] ++ Δ) ++ [(X, bind_sub U)] ++ Γ).
    apply H2...
Qed.

Lemma wf_typ_ignores_typ_bindings : forall V U T Γ Δ x,
  (Δ ++ [(x, bind_typ V)] ++ Γ) ⊢ T wf ->
  (Δ ++ [(x, bind_typ U)] ++ Γ) ⊢ T wf.
Proof with simpl_env; eauto using wf_cset_ignores_typ_bindings.
  intros.
  remember (Δ ++ [(x, bind_typ V)] ++ Γ).
  generalize dependent Δ.
  induction H; intros Δ Heq; subst...
  - Case "X0".
    binds_cases H...
  - Case "∀ (S) T".
    pick fresh y and apply wf_typ_arr...
    rewrite_env (([(y, bind_typ (C # R))] ++ Δ) ++ [(x, bind_typ U)] ++ Γ).
    apply H1...
  - Case "∀ [R] T".
    pick fresh Y and apply wf_typ_all...
    rewrite_env (([(Y, bind_sub R)] ++ Δ) ++ [(x, bind_typ U)] ++ Γ).
    apply H2...
Qed.

Notation "x `mem`A E" := (AtomSet.F.mem x E) (at level 69) : metatheory_scope.

(* ********************************************************************** *)
(** * #<a name="wffrom"></a># Lemmas helping to extract wellformedness or closedness from other properties. *)


Lemma wf_typ_from_binds_typ : forall x U Γ,
  Γ ⊢ wf ->
  binds x (bind_typ U) Γ ->
  Γ ⊢ U wf.
Proof with eauto using wf_typ_weaken_head.
  intros * Hwf Hbinds.
  induction Hwf; binds_cases Hbinds...
  inversion H3; subst...
Qed.

Lemma wf_typ_from_binds_sub : forall x U Γ,
  Γ ⊢ wf ->
  binds x (bind_sub U) Γ ->
  Γ ⊢ U wf.
Proof with eauto using wf_typ_weaken_head.
  intros x U E Hwf Hbinds.
  induction Hwf; binds_cases Hbinds...
  rename select (_ = _) into EQ.
  inversion EQ; subst...
Qed.

Lemma wf_typ_from_wf_env_typ : forall x T Γ,
  ([(x, bind_typ T)] ++ Γ) ⊢ wf ->
  Γ ⊢ T wf.
Proof.
  intros * H; inversion H; auto.
Qed.

Lemma wf_typ_from_wf_env_sub : forall x T Γ,
  ([(x, bind_sub T)] ++ Γ) ⊢ wf ->
  Γ ⊢ T wf.
Proof.
  intros * H; inversion H; auto.
Qed.

Lemma wf_cset_from_binds : forall b x Γ,
  Γ ⊢ wf ->
  binds x (bind_typ b) Γ ->
  Γ ⊢ₛ (`cset_fvar` x) wf.
Proof.
  intros.
  econstructor.
  - intros x0 HIn.
    rewrite AtomSetFacts.singleton_iff in HIn.
    subst.
    eauto.
  - apply binds_In in H0.
    fsetdec.
Qed.

Lemma wf_cv_env_bind_typ : forall x U Γ Δ,
  (Δ ++ [(x, bind_typ U)] ++ Γ) ⊢ wf ->
  Γ ⊢ₛ (typ_cv U) wf.
Proof with eauto.
  intros * H.
  apply cv_wf.
  assert (wf_env ([(x, bind_typ U)] ++ Γ)) as HA by eauto.
  inversion HA...
Qed.

Lemma wf_typ_env_bind_typ : forall x U Γ Δ,
  (Δ ++ [(x, bind_typ U)] ++ Γ) ⊢ wf ->
  Γ ⊢ U wf.
Proof with eauto.
  intros * H.
  assert (([(x, bind_typ U)] ++ Γ) ⊢ wf) as HA by eauto.
  inversion HA...
Qed.

Lemma wf_typ_env_bind_sub : forall X U Γ Δ,
  (Δ ++ [(X, bind_sub U)] ++ Γ) ⊢ wf ->
  Γ ⊢ U wf.
Proof with eauto.
  intros * H.
  assert (([(X, bind_sub U)] ++ Γ) ⊢ wf) as HA by eauto.
  inversion HA...
Qed.

Hint Resolve wf_cv_env_bind_typ : core.
Hint Resolve wf_typ_env_bind_typ : core.
Hint Resolve wf_typ_env_bind_sub : core.

(* ********************************************************************** *)
(** * #<a name="wfsubst"></a># Lemmas connecting substitution and wellformedness of [wf_cset], [wf_typ], ... *)

Ltac destruct_union_mem H :=
  rewrite AtomSetFacts.union_iff in H; destruct H as [H|H].

Lemma wf_cset_subst_tb : forall Γ Δ Q Z P C,
  (Δ ++ [(Z, bind_sub Q)] ++ Γ) ⊢ₛ C wf ->
  Γ ⊢ P wf ->
  ok (Δ ++ [(Z, bind_sub Q)] ++ Γ) ->
  (map (subst_tb Z P) Δ ++ Γ) ⊢ₛ (subst_cset Z (typ_cv P) C) wf.
Proof with simpl_env; eauto*.
  intros * HwfC HwfP Hok.
  inversion HwfC; subst.
  unfold subst_cset.
  destruct_set_mem Z fvars.
  - Case "Z ∈ fvars".
    destruct HwfP; simpl.
    + SCase "X".
      repeat rewrite dom_concat in H0; simpl in H0.
      unfold cset_union; csetsimpl.
      constructor...
      2: apply binds_In in H1;
         apply fresh_mid_tail in Hok;
         fsetdec.
      intros y yIn.
      destruct_union_mem yIn. {
        rewrite AtomSetFacts.singleton_iff in yIn; symmetry in yIn; subst...
      }
      rename H into H'.
      forwards (S & H): H' y.
      1: fsetdec.
      assert (y <> Z) by fsetdec.
      simpl_env in H.
      destruct H; binds_cases H.
      rename select (binds y _ _) into HBnd.
      * exists S...
      * exists (subst_tt Z X S)...
      * exists S...
      * exists (subst_tt Z X S)...
    + SCase "⊤".
      repeat rewrite dom_concat in H0; simpl in H0.
      unfold cset_union; csetsimpl.
      constructor...
      2: fsetdec.
      intros y yIn.
      assert (y <> Z) by fsetdec.
      destruct (H y ltac:(fsetdec)) as [U Hbound].
      destruct_bound Hbound.
      * binds_cases Hbound...
        exists (subst_tt Z (⊤) U).
        apply bound_typ.
        apply binds_head.
        replace (bind_typ (subst_tt Z (⊤) U)) with (subst_tb Z (⊤) (bind_typ U)) by reflexivity.
        apply binds_map, H3.
      * binds_cases Hbound...
        exists (subst_tt Z (⊤) U).
        apply bound_sub.
        apply binds_head.
        replace (bind_sub (subst_tt Z (⊤) U)) with (subst_tb Z (⊤) (bind_sub U)) by reflexivity.
        apply binds_map, H3.
    + SCase "∀ (S) T".
      repeat rewrite dom_concat in H0; simpl in H0.
      unfold cset_union; csetsimpl.
      constructor...
      2: fsetdec.
      intros y yIn.
      assert (y <> Z) by fsetdec.
      destruct (H y ltac:(fsetdec)) as [U Hbound].
      destruct_bound Hbound.
      * binds_cases Hbound...
        exists (subst_tt Z (∀ (C # R) T) U).
        apply bound_typ.
        apply binds_head.
        replace (bind_typ (subst_tt Z (∀ (C # R) T) U)) with (subst_tb Z (∀ (C # R) T) (bind_typ U)) by reflexivity.
        apply binds_map, H4.
      * binds_cases Hbound...
        exists (subst_tt Z (∀ (C # R) T) U).
        apply bound_sub.
        apply binds_head.
        replace (bind_sub (subst_tt Z (∀ (C # R                                   ) T) U)) with (subst_tb Z (∀ (C # R) T) (bind_sub U)) by reflexivity.
        apply binds_map, H4.
    + SCase "∀ [R] T".
      repeat rewrite dom_concat in H0; simpl in H0.
      unfold cset_union; csetsimpl.
      constructor...
      2: fsetdec.
      intros y yIn.
      assert (y <> Z) by fsetdec.
      destruct (H y ltac:(fsetdec)) as [U Hbound].
      destruct_bound Hbound.
      * binds_cases Hbound...
        exists (subst_tt Z (∀ [R] T) U).
        apply bound_typ.
        apply binds_head.
        replace (bind_typ (subst_tt Z (∀ [R] T) U)) with (subst_tb Z (∀ [R] T) (bind_typ U)) by reflexivity.
        apply binds_map, H5.
      * binds_cases Hbound...
        exists (subst_tt Z (∀ [R] T) U).
        apply bound_sub.
        apply binds_head.
        replace (bind_sub (subst_tt Z (∀ [R] T) U)) with (subst_tb Z (∀ [R] T) (bind_sub U)) by reflexivity.
        apply binds_map, H5.
    + SCase "□ T".
      repeat rewrite dom_concat in H0; simpl in H0.
      unfold cset_union; csetsimpl.
      constructor...
      2: fsetdec.
      intros y yIn.
      assert (y <> Z) by fsetdec.
      destruct (H y ltac:(fsetdec)) as [U Hbound].
      destruct_bound Hbound.
      * binds_cases Hbound...
        exists (subst_tt Z (□ T) U).
        apply bound_typ.
        apply binds_head.
        replace (bind_typ (subst_tt Z (□ T) U)) with (subst_tb Z (□ T) (bind_typ U)) by reflexivity.
        apply binds_map, H3.
      * binds_cases Hbound...
        exists (subst_tt Z (□ T) U).
        apply bound_sub.
        apply binds_head.
        replace (bind_sub (subst_tt Z (□ T) U)) with (subst_tb Z (□ T) (bind_sub U)) by reflexivity.
        apply binds_map, H3.
    + SCase "C # R".
      repeat rewrite dom_concat in H0; simpl in H0.
      destruct H1.
      rename fvars0 into cs.
      unfold cset_union; csetsimpl.
      constructor.
      2: {
        assert (Z `~in`A cs). {
          apply fresh_mid_tail in Hok.
          intros ZIn'.
          specialize (H1 Z ZIn') as [? H1].
          destruct H1; apply binds_In in H1; fsetdec.
        }
        rewrite dom_concat, dom_map.
        fsetdec.
      }
      intros y yIn.
      destruct_union_mem yIn.
      * specialize (H1 y ltac:(fsetdec)).
        destruct H1 as [S H1].
        destruct H1; binds_cases H1...
      * inversion HwfC; subst.
        match goal with
        | H : allbound _ fvars |- _ =>
          specialize (H y ltac:(fsetdec));
            destruct H as [S H];
            destruct H; binds_cases H
        end...
        -- exists (subst_tt Z (typ_capt (cset_set cs {}N univ0) R) S)...
        -- exfalso; fsetdec.
        -- exists (subst_tt Z (typ_capt (cset_set cs {}N univ0) R) S)...
  - Case "Z ∉ fvars".
    repeat rewrite dom_concat in H0; simpl in H0.
    inversion HwfC; rename select (allbound _ _) into HAllBound; subst; constructor. {
      intros x xIn.
      destruct (HAllBound x xIn) as [T HBnd].
      destruct_bound HBnd; binds_cases HBnd...
      + exists (subst_tt Z P T)...
      + exists (subst_tt Z P T)...
    }
    destruct HwfP; simpl...
    all: fsetdec.               (* automation gets a bit lost here, why? *)
Qed.

Lemma wf_cset_over_subst : forall Γ Δ Q Z C C',
  ok (map (subst_cb Z C) Δ ++ Γ) ->
  Γ ⊢ₛ C wf ->
  (Δ ++ [(Z, bind_typ Q)] ++ Γ) ⊢ₛ C' wf ->
  ok (Δ ++ [(Z, bind_typ Q)] ++ Γ) ->
  (map (subst_cb Z C) Δ ++ Γ) ⊢ₛ (subst_cset Z C C') wf.
Proof with eauto*.
  intros Γ Δ Q Z C C'.
  intros HokFE HwfC HwfC' Hok.
  inversion HwfC; inversion HwfC'; subst...
  (** Case analysis : this should maybe go through better, hopefully? *)
  + unfold subst_cset; try constructor...
    repeat rewrite dom_concat in H4; simpl in H4.
    find_and_destroy_set_mem. {
      csetdec.
      constructor...
      2: {
        assert (Z `~in`A (dom Γ)) as HA by (eapply fresh_mid_tail; eauto* ).
        assert (Z `~in`A fvars) by (destruct_set_mem Z fvars; eauto* ).
        rewrite dom_concat, dom_map.
        fsetdec.
      }
      intros x Hfvx.

      destruct_union_mem Hfvx. {
        specialize (H x Hfvx) as [T H]...
        destruct H...
      }

      rename H3 into H3'.
      forwards [T H3]: (H3' x)...
      1: fsetdec.
      simpl_env in H3.
      destruct_bound H3; binds_cases H3...
      - exfalso; fsetdec.
      - exists (subst_ct Z (cset_set fvars {}N univ) T)...
      - exists (subst_ct Z (cset_set fvars {}N univ) T)...
    }
    {
      constructor.
      2: rewrite dom_concat, dom_map; fsetdec.
      intros y yIn.
      assert (y <> Z) by fsetdec.
      rename H3 into H3'.
      forwards [T H3]: (H3' y)...
      simpl_env in H3.
      destruct_bound H3; binds_cases H3...
      - exists (subst_ct Z (cset_set fvars {}N univ) T)...
      - exists (subst_ct Z (cset_set fvars {}N univ) T)...
    }
Qed.

Lemma wf_typ_subst_cb : forall Γ Δ Q Z C T,
  (Δ ++ [(Z, bind_typ Q)] ++ Γ) ⊢ T wf ->
  Γ ⊢ₛ C wf ->
  ok (map (subst_cb Z C) Δ ++ Γ) ->
  ok (Δ ++ [(Z, bind_typ Q)] ++ Γ) ->
  (map (subst_cb Z C) Δ ++ Γ) ⊢ (subst_ct Z C T) wf.
Proof with simpl_env;
           eauto using wf_typ_weaken_head,
                       wf_cset_subst_tb,
                       type_from_wf_typ,
                       capt_from_wf_cset.
  intros *.
  intros HwfT HwfC Hok HokZ.
  remember (Δ ++ [(Z, bind_typ Q)] ++ Γ).
  generalize dependent Δ.
  induction HwfT; intros Δ ? Hok; subst; simpl subst_ct...
  - Case "X".
    assert (X <> Z). {
      binds_cases H...
      - simpl_env in *.
        notin_solve.
      - assert (binds X (bind_sub T) (Δ ++ [(Z, bind_typ Q)] ++ Γ)) by auto.
        forwards: fresh_mid_head HokZ.
        forwards: binds_In H1.
        fsetdec.
    }
    binds_cases H...
    apply (wf_typ_var _ X (subst_ct Z C T))...
  - Case "∀ (S) T".
    pick fresh y and apply wf_typ_arr.
    + fold subst_ct...
    + unfold open_ct in *...
      rewrite <- subst_ct_open_ct_rec.
      2-4: eauto.
      rewrite_env (map (subst_cb Z C) ([(y, bind_typ (C0 # R))] ++ Δ) ++ Γ).
      apply H0...
  - Case "∀ [R] T".
    pick fresh Y and apply wf_typ_all.
    + fold subst_ct...
    + apply subst_ct_pure_type...
    + rewrite subst_ct_open_tt_var.
      2-3: eauto.
      rewrite_env (map (subst_cb Z C) ([(Y, bind_sub R)] ++ Δ) ++ Γ).
      apply H1...
  - Case "C # R".
    apply wf_typ_capt.
    + apply wf_cset_over_subst with (Q := Q)...
    + apply IHHwfT...
    + apply subst_ct_pure_type...
Qed. 

Lemma wf_cset_subst_cb : forall Γ Δ Q x C D,
  (Δ ++ [(x, bind_typ Q)] ++ Γ) ⊢ₛ C wf ->
  (Δ ++ [(x, bind_typ Q)] ++ Γ) ⊢ wf ->
  Γ ⊢ₛ D wf ->
  ok (map (subst_cb x D) Δ ++ Γ) ->
  (map (subst_cb x D) Δ ++ Γ) ⊢ₛ (subst_cset x D C) wf.
Proof with simpl_env; eauto*.
  intros * HwfC HwfEnv HwfD Hok.
  destruct C.
  unfold subst_cset.
  forwards: binding_uniq_from_wf_env HwfEnv.
  destruct_set_mem x t...
  - apply wf_cset_union.
    + rewrite_nil_concat.
      apply wf_cset_weakening; simpl_env...
    + inversion HwfC; subst.
      constructor...
      unfold allbound in *.
      intros y yIn.
      2: {
        repeat rewrite dom_concat in H5; simpl in H5.
        fsetdec.
      }
      destruct (y == x).
      * exfalso; fsetdec.
      * forwards (T & B): H3 y.
        ** fsetdec.
        ** simpl_env in B.
           destruct_bound B; binds_cases B; eauto; exists (subst_ct x D T)...
  - inversion HwfC; subst.
    constructor...
    unfold allbound in *.
    intros y yIn.
    forwards (T & B): H3 y.
    { fsetdec. }
    simpl_env in B.
    destruct_bound B; binds_cases B; eauto*; exists (subst_ct x D T)...
    repeat rewrite dom_concat in H5; simpl in H5.
    fsetdec.
Qed.

(*
  opening capture sets in types preserves well-formedness. *)
Lemma open_ct_wf_typ : forall Γ T C,
  Γ ⊢ T wf ->
  Γ ⊢ (open_ct T C) wf.
Proof with eauto using type_from_wf_typ.
  intros *.
  intros H.
  closed_type...
Qed.

Lemma wf_typ_open_capt : forall Γ C S T,
  ok Γ ->
  Γ ⊢ (∀ (S) T) wf ->
  Γ ⊢ₛ C wf ->
  Γ ⊢ (open_ct T C) wf.
Proof with simpl_env; eauto.
  intros * Hok HwfA HwfC.
  inversion HwfA; subst...
  pick fresh x.
  rewrite (subst_ct_intro x)...
  rewrite_env (map (subst_cb x C) nil ++ Γ).
  eapply wf_typ_subst_cb with (Q := C0 # R)...
Qed.

Lemma wf_typ_subst_tb : forall Γ Δ Q Z P T,
  (Δ ++ [(Z, bind_sub Q)] ++ Γ) ⊢ T wf ->
  (** NOTE here that P needs to be well formed in both the + and - environments, *)
(*       as we're substituting in both places. *)
  Γ ⊢ P wf ->
  pure_type P ->
  ok (Δ ++ [(Z, bind_sub Q)] ++ Γ) ->
  (map (subst_tb Z P) Δ ++ Γ) ⊢ (subst_tt Z P T) wf.
Proof with simpl_env; eauto using wf_typ_weaken_head, type_from_wf_typ, wf_cset_subst_tb.
  intros * HwfT HwfP HpureP Hok.
  (* remember (F ++ [(Z, bind_sub Q)] ++ E). *)
  (* generalize dependent F. *)
  (* induction HwfT; intros F EQF Hok; subst; simpl subst_tt. *)
  dependent induction HwfT; simpl...
  - Case "X".
    destruct (X == Z); subst.
    + SCase "X == Z".
      eapply wf_typ_weaken_head...
    + SCase "X <> Z".
      forwards: fresh_mid_tail Hok.
      binds_cases H.
      * applys wf_typ_var T...
      * applys wf_typ_var (subst_tt Z P T)...
  - Case "∀ (S) T".
    pick fresh y and apply wf_typ_arr...
    unfold open_ct in *...
    rewrite <- subst_tt_open_ct_rec...
    rewrite_env (map (subst_tb Z P) ([(y, bind_typ (C # R))] ++ Δ) ++ Γ).
    eapply H0...
  - Case "∀ [R] T".
    pick fresh Y and apply wf_typ_all...
    unfold open_ct in *...
    1: apply subst_tt_pure_type...
    rewrite subst_tt_open_tt_var...
    rewrite_env (map (subst_tb Z P) ([(Y, bind_sub R)] ++ Δ) ++ Γ).
    eapply H1...
  - Case "C # R".
    apply wf_typ_capt...
    apply subst_tt_pure_type...
Qed.

Lemma wf_typ_open_type : forall Γ U R T,
  ok Γ ->
  Γ ⊢ (∀ [R] T) wf->
  Γ ⊢ U wf ->
  pure_type U ->
  Γ ⊢ (open_tt T U) wf.
Proof with simpl_env; eauto.
  intros * Hok HwfA HwfU HpureU.
  inversion HwfA; subst...
  pick fresh X.
  rewrite (subst_tt_intro X)...
  assert (X `~in`A dom Γ) by notin_solve.
  rewrite_env (map (subst_tb X U) nil ++ Γ).
  apply wf_typ_subst_tb with (Q := R)...
Qed.

Lemma wf_env_subst_tb : forall Γ Δ Q Z P,
  (Δ ++ [(Z, bind_sub Q)] ++ Γ) ⊢ wf ->
  Γ ⊢ P wf ->
  pure_type P ->
  (map (subst_tb Z P) Δ ++ Γ) ⊢ wf.
Proof with eauto 6 using wf_typ_subst_tb.
  induction Δ; intros * WfEnv WfP HpureP; simpl...
  inversion WfEnv; subst; simpl subst_tb; simpl_env in *.
  - apply wf_env_sub.
    + eapply IHΔ...
    + eapply wf_typ_subst_tb...
    + apply subst_tt_pure_type... 
    + rewrite dom_concat, dom_map...
  - apply wf_env_typ.
    + eapply IHΔ... 
    + replace (subst_cset Z (typ_cv P) C # subst_tt Z P R) with (subst_tt Z P (C # R)) by reflexivity.
      eapply wf_typ_subst_tb...
    + rewrite dom_concat, dom_map...
Qed.

Lemma wf_env_subst_cb : forall Γ Δ Q C x,
  (Δ ++ [(x, bind_typ Q)] ++ Γ) ⊢ wf ->
  Γ ⊢ₛ C wf ->
  (map (subst_cb x C) Δ ++ Γ) ⊢ wf.
Proof with eauto using wf_typ_subst_cb.
  intros *.
  induction Δ; intros Hwf HwfC...
  simpl.
  inversion Hwf; subst; simpl subst_cb; simpl_env in *.
  - apply wf_env_sub.
    + eapply IHΔ...
    + eapply wf_typ_subst_cb...
    + apply subst_ct_pure_type...
    + rewrite dom_concat, dom_map...
  - apply wf_env_typ.
    + eapply IHΔ...
    + replace (subst_cset x C C0 # subst_ct x C R) with (subst_ct x C (C0 # R)) by reflexivity.
      eapply wf_typ_subst_cb...
    + rewrite dom_concat, dom_map...
Qed.

Lemma wf_typ_preserved_by_subst_wf_cset : forall Γ x C T,
  Γ ⊢ wf ->
  x ∉ dom Γ ->
  Γ ⊢ₛ C wf ->
  Γ ⊢ T wf ->
  Γ ⊢ (subst_ct x C T) wf.
Proof with eauto.
  intros * WfΓ NotIn WfC WfT.
  induction WfT; simpl...
  - Case "∀ (S) T".
    pick fresh y and apply wf_typ_arr...
    rewrite subst_ct_open_ct_var; [| notin_solve | eapply capt_from_wf_cset]...
    rewrite_nil_concat.
    apply wf_typ_ignores_typ_bindings with (V := C0 # R); simpl.
    apply H0.
    + fsetdec.
    + apply wf_env_typ...
    + rewrite dom_concat...
    + apply wf_cset_weaken_head...
  - Case "∀ [R] T".
    pick fresh Y and apply wf_typ_all...
    1: apply subst_ct_pure_type...
    rewrite_nil_concat.
    apply wf_typ_ignores_sub_bindings with (V := R); simpl.
    rewrite subst_ct_open_tt_var; [| notin_solve | eapply capt_from_wf_cset]...
    apply H1.
    + fsetdec.
    + apply wf_env_sub...
    + rewrite dom_concat...
    + apply wf_cset_weaken_head...
  - Case "C # R".
    apply wf_typ_capt.
    + unfold subst_cset.
      destruct_if; eauto using wf_cset_union, wf_cset_remove_fvar.
    + apply IHWfT...
    + apply subst_ct_pure_type...
Qed.

(* ********************************************************************** *)
(** * #<a name="okt"></a># Properties of [wf_env] *)

Lemma wf_env_strengthening : forall Γ Δ,
  (Δ ++ Γ) ⊢ wf ->
  Γ ⊢ wf.
Proof with eauto.
  induction Δ...
Qed.

Lemma wf_env_strengthening_typ : forall Γ Δ x T,
  x `~in`A fv_cctx Δ ->
  (Δ ++ [(x, bind_typ T)] ++ Γ) ⊢ wf ->
  (Δ ++ Γ) ⊢ wf.
Proof with eauto using wf_cset_strengthen.
  intros * NotIn WfEnv.
  eremember (Δ ++ [(x, bind_typ T)] ++ Γ) as Ctx.
  generalize dependent Δ.
  induction WfEnv; intros Δ NotIn EQ.
  - induction Δ; inversion EQ.
  - induction Δ; simpl_env in *.
    + inversion EQ.
    + destruct a as [y [U | U]]; simpl in *; simpl_env in *.
      * inversion EQ; subst.
        assert (Ok : ok (Δ ++ [(x, bind_typ T)] ++ Γ)) by apply ok_from_wf_env, WfEnv.
        assert (NotIn' : x ∉ dom Δ `u`A dom Γ)
            by (apply notin_union; [ eapply fresh_mid_head | eapply fresh_mid_tail ]; apply Ok).
        apply wf_env_sub.
        -- apply IHWfEnv...
        -- apply wf_typ_strengthen in H; [ apply H | ].
           clear - NotIn NotIn'.
           fsetdec.
        -- assumption. 
        -- repeat rewrite dom_concat.
           rename select (y ∉ _) into yNotIn.
           repeat rewrite dom_concat in yNotIn; simpl in yNotIn.
           clear - yNotIn; fsetdec.
      * inversion EQ; subst.
  - induction Δ; simpl_env in *.
    + inversion EQ; subst...
    + destruct a as [y [U | U]]; simpl in *; simpl_env in *.
      * inversion EQ; subst.
      * inversion EQ; subst.
        assert (Ok : ok (Δ ++ [(x, bind_typ T)] ++ Γ)) by apply ok_from_wf_env, WfEnv.
        assert (NotIn' : x ∉ dom Δ `u`A dom Γ)
            by (apply notin_union; [ eapply fresh_mid_head | eapply fresh_mid_tail ]; apply Ok).
        apply wf_env_typ.
        -- apply IHWfEnv...
        -- apply wf_typ_strengthen in H; [ apply H | ].
           clear - NotIn NotIn'.
           fsetdec.
        -- repeat rewrite dom_concat.
           rename select (y ∉ _) into yNotIn.
           repeat rewrite dom_concat in yNotIn; simpl in yNotIn.
           clear - yNotIn; fsetdec.
Qed.

Lemma wf_env_narrowing : forall Γ Δ V U X,
  (Δ ++ [(X, bind_sub V)] ++ Γ) ⊢ wf ->
  pure_type U ->
  Γ ⊢ U wf ->
  (Δ ++ [(X, bind_sub U)] ++ Γ) ⊢ wf.
Proof with eauto using wf_typ_ignores_sub_bindings, wf_typ_ignores_typ_bindings.
  induction Δ; intros * WfEnv Wf;
    inversion WfEnv; subst; simpl_env in *...
Qed.

Lemma wf_env_narrowing_typ : forall Γ Δ V C R X,
  (Δ ++ [(X, bind_typ V)] ++ Γ) ⊢ wf ->
  Γ ⊢ (C # R) wf ->
  (Δ ++ [(X, bind_typ (C # R))] ++ Γ) ⊢ wf.
Proof with eauto using wf_typ_ignores_sub_bindings, wf_typ_ignores_typ_bindings.
  induction Δ; intros * WfEnv Wf;
    inversion WfEnv; subst; simpl_env in *...
Qed.

Lemma wf_env_inv : forall Γ Δ Z b,
  (Δ ++ [(Z, b)] ++ Γ) ⊢ wf ->
  Γ ⊢ wf /\ Z ∉ dom Γ.
Proof with eauto.
  induction Δ ; intros ; simpl_env in *.
  inversion H ; subst...
  inversion H ; subst...
Qed.
