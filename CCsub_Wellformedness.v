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

Lemma binding_uniq_from_wf_env : forall F E x b,
  (F ++ ([(x, b)]) ++ E) ⊢ wf ->
  x ∉ (dom F `union` dom E).
Proof.
  intros.
  apply ok_from_wf_env in H.
  eapply binding_uniq_from_ok; eauto.
Qed.

(* ********************************************************************** *)
(** * #<a name="wfset"></a># Properties of [wf_cset] *)

Lemma empty_cset_wf : forall Γ, Γ ⊢ₛ {} wf.
Proof.
  intros.
  constructor.
  intros ? ?.
  fsetdec.
Qed.

Lemma univ_cset_wf : forall Γ, Γ ⊢ₛ {*} wf.
Proof.
  intros.
  constructor.
  intros ? ?.
  fsetdec.
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
Qed.

Lemma wf_cset_over_union : forall Γ C D,
  Γ ⊢ₛ (C `u` D) wf <->
  Γ ⊢ₛ C wf /\ Γ ⊢ₛ D wf.
Proof with eauto*.
  intros; split; intros H; destruct C eqn:HC1;
                           destruct D eqn:HC2;
                           unfold cset_union in *.
  - inversion H; subst...
    rename select (allbound _ (_ `u`A _)) into AllBoundCD.
    rename select ({}N = _ `u`N _) into EmptyBVarsCD.
    apply empty_over_union in EmptyBVarsCD.
    destruct EmptyBVarsCD as [EmptyBVarsC EmptyBVarsD].
    apply allbound_over_union in AllBoundCD.
    destruct AllBoundCD as [AllBoundC AllBoundD].
    subst.
    split; constructor...
  - destruct H as [Hwf1 Hwf2].
    inversion Hwf1; inversion Hwf2; subst...
    csetsimpl.
    (** this should really be a lemma... *)
    (* assert (NatSet.F.union {}N {}N = {}N) by fnsetdec; rewrite H1. *)
    constructor.
    intros ? ?.
    apply AtomSetFacts.union_iff in H...
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
    intros x Hx;
    destruct (Hbound x Hx) as [C [R Hexists]];
    lazymatch instantiate_ext with
    | True => exists T; destruct Hexists; auto
    | False => idtac
    end
  end.

Lemma wf_cset_weakening : forall Γ Θ Δ C,
  (Δ ++ Γ) ⊢ₛ C wf ->
  ok (Δ ++ Θ ++ Γ) ->
  (Δ ++ Θ ++ Γ) ⊢ₛ C wf.
Proof with auto*.
  intros * Hwf Hok.
  inversion Hwf.
  constructor.
  intros x xIn.
  destruct (H x xIn) as [D [Q Bound]].
  exists D, Q.
  binds_cases Bound...
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
  exists C, R.
  binds_cases Hexists...
Qed.

Lemma wf_cset_narrowing_typ : forall C1 R1 C2 R2 C Γ Δ X,
  (Δ ++ [(X, bind_typ (C1 # R1))] ++ Γ) ⊢ₛ C wf ->
  ok (Δ ++ [(X, bind_typ (C2 # R2))] ++ Γ) ->
  (Δ ++ [(X, bind_typ (C2 # R2))] ++ Γ) ⊢ₛ C wf.
Proof with simpl_env; eauto.
  intros * Hwf Hok.
  wf_cset_simpl False.
  rename Hexists into B.
  binds_cases B...
Qed.

Lemma wf_cset_ignores_typ_bindings : forall Γ Δ x C1 R1 C2 R2 C,
  (Δ ++ [(x, bind_typ (C1 # R1))] ++ Γ) ⊢ₛ C wf ->
  (Δ ++ [(x, bind_typ (C2 # R2))] ++ Γ) ⊢ₛ C wf.
Proof with eauto.
  intros*.
  intros H.
  remember (Δ ++ [(x, bind_typ (C1 # R1))] ++ Γ).
  generalize dependent Δ.
  induction H; intros Δ Eq; subst...
  econstructor...
  unfold allbound in *.
  intros y yIn.
  destruct (H y yIn) as [C [R Hb]].
  binds_cases Hb...
Qed.

Lemma wf_cset_ignores_sub_bindings : forall Γ Δ x R1 R2 C,
  (Δ ++ [(x, bind_sub R1)] ++ Γ) ⊢ₛ C wf ->
  (Δ ++ [(x, bind_sub R2)] ++ Γ) ⊢ₛ C wf.
Proof with eauto.
  intros * H.
  remember (Δ ++ [(x, bind_sub R1)] ++ Γ).
  generalize dependent Δ.
  induction H; intros Δ Eq; subst...
  econstructor...
  unfold allbound in *.
  intros y yIn.
  destruct (H y yIn) as [C [R Hb]].
  binds_cases Hb...
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
  intros y yIn; assert (y = x) by (clear - yIn; fsetdec); subst; clear yIn.
  rename select (allbound _ _) into Hb.
  apply (Hb x ltac:(fsetdec)).
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
  intros x' x'_in_x.
  assert (x' = x) by fsetdec; subst.
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
  x ∉ (`cset_fvars` C) ->
  (Δ ++ [(x, bind_typ U)] ++ Γ) ⊢ₛ C wf ->
  (Δ ++ Γ) ⊢ₛ C wf.
Proof with eauto.
  intros * ? H.
  inversion H; subst.
  rename select (allbound _ _) into Hb.
  econstructor.
  intros y yIn.
  destruct (Hb y yIn) as [C [R B]].
  exists C, R.
  binds_cases B...
  contradict yIn.
  assumption.
Qed.

Lemma notin_open_tt_rec_fv_ct : forall k x T U,
  x ∉ (fv_ct T `u`A fv_ct U) ->
  x ∉ fv_ct (open_tt_rec k U T).
Proof with eauto*.
  intros * NotIn.
  generalize dependent k.
  induction T; intros k; simpl in *...
  induction U; unfold open_vt; destruct v; simpl...
  all: destruct (k === n); simpl; simpl in NotIn...
Qed.

Lemma notin_open_cset : forall k x c d,
  x ∉ ((`cset_fvars` c) `u`A (`cset_fvars` d)) ->
  x ∉ (`cset_fvars` (open_cset k c d)).
Proof with eauto*.
  intros * NotIn.
  unfold open_cset.
  destruct (k N`mem` d)...
Qed.

Lemma notin_open_ct_rec_fv_ct : forall k x c T,
  x ∉ (fv_ct T `u`A (`cset_fvars` c)) ->
  x ∉ fv_ct (open_ct_rec k c T).
Proof with eauto using notin_open_cset.
  intros * NotIn.
  generalize dependent k.
  induction T; intros k; simpl in *...
Qed.

Lemma wf_typ_strengthen : forall x Γ Δ T U,
  x ∉ (dom Δ `u`A fv_ct T) ->
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

Lemma wf_typ_ignores_typ_bindings : forall C1 R1 C2 R2 T Γ Δ x,
  (Δ ++ [(x, bind_typ (C1 # R1))] ++ Γ) ⊢ T wf ->
  (Δ ++ [(x, bind_typ (C2 # R2))] ++ Γ) ⊢ T wf.
Proof with simpl_env; eauto using wf_cset_ignores_typ_bindings.
  intros.
  remember (Δ ++ [(x, bind_typ (C1 # R1))] ++ Γ).
  generalize dependent Δ.
  induction H; intros Δ Heq; subst...
  - Case "X0".
    binds_cases H...
  - Case "∀ (S) T".
    pick fresh y and apply wf_typ_arr...
    rewrite_env (([(y, bind_typ (C # R))] ++ Δ) ++ [(x, bind_typ (C2 # R2))] ++ Γ).
    apply H1...
  - Case "∀ [R] T".
    pick fresh Y and apply wf_typ_all...
    rewrite_env (([(Y, bind_sub R)] ++ Δ) ++ [(x, bind_typ (C2 # R2))] ++ Γ).
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

Lemma wf_cset_from_binds : forall C R x Γ,
  Γ ⊢ wf ->
  binds x (bind_typ (C # R)) Γ ->
  Γ ⊢ₛ (`cset_fvar` x) wf.
Proof.
  intros.
  econstructor.
  intros x0 HIn.
  rewrite AtomSetFacts.singleton_iff in HIn.
  subst.
  eauto.
Qed.

Lemma wf_typ_env_bind_typ : forall x U Γ,
  Γ ⊢ wf ->
  binds x (bind_typ U) Γ ->
  exists C R, U = C # R /\ Γ ⊢ (C # R) wf.
Proof with eauto using wf_typ_weaken_head.
  intros * WfEnv Binds.
  induction WfEnv.
  - inversion Binds.
  - binds_cases Binds.
    rename select (binds x _ _) into Binds.
    destruct (IHWfEnv Binds) as [C [R [EQ WfCR]]].
    exists C, R.
    split...
  - binds_cases Binds.
    + rename select (binds x _ _) into Binds.
      destruct (IHWfEnv Binds) as [D [Q [EQ WfCR]]].
      exists D, Q.
      split...
    + exists C, R.
      inversion select (bind_typ _ = bind_typ _).
      split...
Qed.

Lemma wf_typ_env_bind_sub : forall X U Γ,
  Γ ⊢ wf ->
  binds X (bind_sub U) Γ ->
  pure_type U /\ Γ ⊢ U wf.
Proof with eauto using wf_typ_weaken_head. 
  intros * WfEnv Binds.
  induction WfEnv.
  - inversion Binds.
  - binds_cases Binds.
    + rename select (binds X _ _) into Binds.
      destruct (IHWfEnv Binds) as [PureU WfU].
      split...
    + inversion select (bind_sub _ = bind_sub _).
      split... 
  - binds_cases Binds.
    rename select (binds X _ _) into Binds.
    destruct (IHWfEnv Binds) as [PureU WfU].
    split...
Qed.

(* Hint Resolve wf_cv_env_bind_typ : core. *)
Hint Resolve wf_typ_env_bind_typ : core.
Hint Resolve wf_typ_env_bind_sub : core.

(* ********************************************************************** *)
(** * #<a name="wfsubst"></a># Lemmas connecting substitution and wellformedness of [wf_cset], [wf_typ], ... *)

Ltac destruct_union_mem H :=
  rewrite AtomSetFacts.union_iff in H; destruct H as [H|H].

(* REVIEW: there is something weird with subst_tb:
  - subst_tb X (C # P) (bind_sub X) = bind_sub (C # P)
  - subst_tb X P (bind_typ X) = bind_typ P
  breaks the invariant that P in bind_sub P is a pure type
  and T in bind_typ T is not a captured type.
  Possible solution: make bind_typ take a captured type like
  bind_typ C P instead of bind_typ (C # P), and force the second
  argument of subst_tb to be a pure type.
 *)
Lemma wf_cset_subst_tb : forall Γ Δ Q Z P C,
  (Δ ++ [(Z, bind_sub Q)] ++ Γ) ⊢ₛ C wf ->
  Γ ⊢ P wf ->
  pure_type P ->
  ok (Δ ++ [(Z, bind_sub Q)] ++ Γ) ->
  (map (subst_tb Z P) Δ ++ Γ) ⊢ₛ C wf.
Proof with simpl_env; eauto*.
  intros * HwfC HwfP PureP Hok.
  destruct HwfC as [fvars univ Hb].
  unfold subst_cset.
  repeat rewrite dom_concat in Hb; simpl in Hb.
  destruct_set_mem Z fvars.
  - Case "Z ∈ fvars".
    unfold cset_union; csetsimpl.
    constructor...
    intros y yIn.
    destruct (Hb y yIn) as [C [R Binds]].
    binds_cases Binds.
    + exists C, R.
      apply binds_tail...
      inversion select (binds y _ _).
      destruct (y == Z)...
    + exists C, (subst_tt Z P R).
      replace (bind_typ (C # subst_tt Z P R))
         with (subst_tb Z P (bind_typ (C # R)))
           by reflexivity.
        apply binds_head, binds_map.
        assumption.
  - Case "Z ∉ fvars".
    constructor.
    intros y yIn.
    destruct (Hb y yIn) as [C [R Binds]].
    binds_cases Binds.
    + exists C, R.
      apply binds_tail...
      inversion H...
      destruct (y == Z); try (subst; clear - ZIn yIn; exfalso; apply (ZIn yIn)).
      assumption.
    + exists C, (subst_tt Z P R).
      replace (bind_typ (C # subst_tt Z P R))
         with (subst_tb Z P (bind_typ (C # R)))
          by reflexivity.
      apply binds_head, binds_map.
      assumption.
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
  destruct HwfC as [fvars univ Hb].
  destruct HwfC' as [fvars' univ' Hb'].
  (** Case analysis : this should maybe go through better, hopefully? *)
  - unfold subst_cset; try constructor...
    repeat rewrite dom_concat in Hb'; simpl in Hb'.
    find_and_destroy_set_mem.
    + csetdec.
      constructor...
      intros x xIn.
      destruct_union_mem xIn.
      * destruct (Hb x xIn) as [C [R B]]...
      * destruct (Hb' x ltac:(clear - xIn; fsetdec)) as [C [R B]].
        binds_cases B.
        -- exists C, R.
           apply binds_tail...
           inversion H.
           destruct (x == Z); try (subst; clear - ZIn xIn; exfalso; fsetdec).
           assumption.
        -- exists (subst_cset Z (cset_set fvars {}N univ) C), (subst_ct Z (cset_set fvars {}N univ) R).
           replace (bind_typ (subst_cset Z (cset_set fvars {}N univ) C # subst_ct Z (cset_set fvars {}N univ) R))
              with (subst_cb Z (cset_set fvars {}N univ) (bind_typ (C # R)))
                by reflexivity.
           apply binds_head, binds_map.
           assumption.
    + constructor...
      intros x xIn.
      destruct (Hb' x xIn) as [C [R B]].
      binds_cases B.
      * exists C, R.
        apply binds_tail...
        inversion H...
        destruct (x == Z); try (subst; clear - ZIn xIn; exfalso; apply (ZIn xIn)).
        assumption.
      * exists (subst_cset Z (cset_set fvars {}N univ) C), (subst_ct Z (cset_set fvars {}N univ) R).
        replace (bind_typ (subst_cset Z (cset_set fvars {}N univ) C # subst_ct Z (cset_set fvars {}N univ) R))
           with (subst_cb Z (cset_set fvars {}N univ) (bind_typ (C # R)))
            by reflexivity.
        apply binds_head, binds_map.
        assumption.
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
      destruct (y == x).
      * exfalso; fsetdec.
      * forwards (C & R & B): H1 y.
        1: fsetdec.
        simpl_env in B.
        binds_cases B; eauto; exists (subst_cset x D C), (subst_ct x D R)...
        replace (bind_typ (subst_cset x D C # subst_ct x D R))
           with (subst_cb x D (bind_typ (C # R)))
             by reflexivity...
  - inversion HwfC; subst.
    constructor...
    unfold allbound in *.
    intros y yIn.
    forwards (C & R & B): H1 y.
    1: fsetdec.
    simpl_env in B.
    binds_cases B; eauto*; exists (subst_cset x D C), (subst_ct x D R)...
    replace (bind_typ (subst_cset x D C # subst_ct x D R))
       with (subst_cb x D (bind_typ (C # R)))
         by reflexivity...
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
    simpl.
    apply wf_typ_capt...
    assert ((map (subst_tb Z P) Δ ++ Γ) ⊢ subst_tt Z P R wf) by (eapply IHHwfT; eauto* ).
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
  assert (X ∉ dom Γ) by notin_solve.
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
    + replace (C # subst_tt Z P R) with (subst_tt Z P (C # R)) by reflexivity.
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

(* ********************************************************************** *)
(** * #<a name="okt"></a># Properties of [wf_env] *)

Lemma wf_env_narrowing : forall Γ Δ V U X,
  (Δ ++ [(X, bind_sub V)] ++ Γ) ⊢ wf ->
  pure_type U ->
  Γ ⊢ U wf ->
  (Δ ++ [(X, bind_sub U)] ++ Γ) ⊢ wf.
Proof with eauto using wf_typ_ignores_sub_bindings, wf_typ_ignores_typ_bindings.
  induction Δ; intros * WfEnv Wf;
    inversion WfEnv; subst; simpl_env in *...
Qed.

Lemma wf_env_narrowing_typ : forall Γ Δ C1 R1 C2 R2 X,
  (Δ ++ [(X, bind_typ (C1 # R1))] ++ Γ) ⊢ wf ->
  Γ ⊢ (C2 # R2) wf ->
  (Δ ++ [(X, bind_typ (C2 # R2))] ++ Γ) ⊢ wf.
Proof with eauto using wf_typ_ignores_sub_bindings, wf_typ_ignores_typ_bindings.
  induction Δ; intros * WfEnv Wf;
    inversion WfEnv; subst; simpl_env in *...
Qed.
