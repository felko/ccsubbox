Require Import Coq.Program.Equality.

Require Export CCsub_Infrastructure.
Require Import Atom.

Require Import TaktikZ.

(* ********************************************************************** *)
(** * #<a name="utils"></a># Automation Utils -- mostly related to wellformedness of environments [ok], [wf_env], [dom], ...*)


Lemma capt_from_wf_cset : forall E A C,
  wf_cset E A C -> capt C.
Proof with auto.
  intros.
  inversion H...
Qed.

Lemma capt_from_wf_cset_in : forall E C, wf_cset_in E C -> capt C.
Proof. eauto using capt_from_wf_cset. Qed.

Hint Resolve capt_from_wf_cset_in : core.

Lemma allbound_over_union : forall E T1 T2,
  allbound E (AtomSet.F.union T1 T2) ->
  allbound E T1 /\ allbound E T2.
Proof with eauto*.
  intros.
  split; intros ? ?; assert (x `in` (T1 `union` T2)) by fsetdec...
Qed.

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

(* This lemma is needed by a couple of lemmas about wf_typ *)
Lemma wf_env_tail : forall F E,
  wf_env (F ++ E) ->
  wf_env E.
Proof with eauto.
  intros * Hwf.
  induction F; (trivial || inversion Hwf; subst)...
Qed.

Hint Resolve wf_env_tail : core.

Hint Extern 1 (ok (map ?f ?F ++ ?E)) =>
match goal with
| H : wf_env (F ++ ?b ++ E) |- _ =>
  enough (ok (F ++ b ++ E))
end : core.

(* TODO WHERE TO PUT THIS? *)
Lemma dom_x_subst_away : forall x f b F E,
  wf_env (F ++ [(x, b)] ++ E) ->
  dom (map f F ++ E) = dom (F ++ [(x, b)] ++ E) `remove` x.
Proof with eauto*.
  intros * Hwf.
  simpl_env in *.
  assert (x `notin` (dom F `union` dom E)). {
    pose proof (binding_uniq_from_ok _ F E x _ ltac:(eauto)).
    fsetdec.
  }
  fsetdec.
Qed.

Lemma binding_uniq_from_wf_env : forall F E x b,
  wf_env (F ++ ([(x, b)]) ++ E) ->
  x `notin` (dom F `union` dom E).
Proof.
  intros.
  apply ok_from_wf_env in H.
  eapply binding_uniq_from_ok; eauto.
Qed.

Lemma distinct_binding_from_wf_env : forall F x b E y,
  wf_env (F ++ [(x, b)] ++ E) ->
  y `in` dom E ->
  y `notin` dom F.
Proof.
  intros * H ?.
  induction F.
  - simpl_env; fsetdec.
  - inversion H; subst;
      specialize (IHF H3); simpl_env in *; fsetdec.
Qed.


(* ********************************************************************** *)
(** * #<a name="wfset"></a># Properties of [wf_cset] *)

Lemma empty_cset_wf : forall E A, wf_cset E A {*}.
Proof.
  intros.
  constructor.
  - intros ? ?. fsetdec.
  - fsetdec.
Qed.

Hint Resolve empty_cset_wf : core.

Lemma wf_cset_adapt : forall {A' E A C},
  wf_cset E A' C ->
  A' = A ->
  wf_cset E A C.
Proof.
  intros.
  congruence.
Qed.

Lemma wf_cset_extra : forall S2 E C,
  wf_cset_in E C ->
  dom E `subset` S2 ->
  wf_cset E S2 C.
Proof with eauto*.
  intros * HwfC.
  induction HwfC...
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
  unfold cset_union; csetsimpl.
  constructor...
  unfold allbound in *...
  intros.
  rewrite AtomSetFacts.union_iff in *.
  auto*.
Qed.

Lemma wf_cset_remove_fvar : forall A E C x, wf_cset E A C -> wf_cset E A (C A`\` x).
Proof with eauto.
  intros.
  unfold wf_cset_in in *.
  induction H; simpl...
  constructor...
  unfold allbound in *.
  intros.
  apply H.
  fsetdec.
Qed.

Lemma wf_cset_over_union : forall E A C1 C2,
  wf_cset E A (cset_union C1 C2) <->
  wf_cset E A C1 /\ wf_cset E A C2.
Proof with eauto*.
  intros; split; intros; destruct C1 eqn:HC1;
                         destruct C2 eqn:HC2;
                         unfold cset_union in *...
  - inversion H; subst...
    apply empty_over_union in H1; inversion H1.
    apply allbound_over_union in H4; inversion H4.
    subst.
    split; constructor...
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
    Lemma cv_wf : forall E T,
    wf_typ_in E T ->
    wf_cset_in E (cv T).
  Proof with simpl_env; eauto*.
    intros * HC.
    inversion HC; subst...
    constructor.
    2: fsetdec.
    intros y yIn.
    rewrite AtomSetFacts.singleton_iff in yIn; symmetry in yIn; subst...
  Qed.


(** This is a useful helper tactic for clearing away
    capture set wellformedness. *)

Ltac wf_cset_simpl instantiate_ext :=
  match goal with
  | H : _ |- (wf_cset _ _ {*}) =>
    constructor
  | H : (wf_cset _ _ ?C) |- (wf_cset _ _ ?C) =>
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
      | True => exists T; destruct Hexists
      | False => idtac
      end
    | fsetdec
    ]
  end.

Lemma wf_cset_weakening : forall E A A' F G C,
  wf_cset (G ++ E) A C ->
  ok (G ++ F ++ E) ->
  A `c`A A' ->
  wf_cset (G ++ F ++ E) A' C.
Proof with auto*.
  intros * Hcset Henv Hpres.
  wf_cset_simpl True...
Qed.

Lemma wf_cset_in_weakening : forall E F G C,
  wf_cset_in (G ++ E) C ->
  ok (G ++ F ++ E) ->
  wf_cset_in (G ++ F ++ E) C.
Proof with eauto.
  intros * Hwf Hok.
  eapply wf_cset_weakening...
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

Ltac destruct_bound H :=
  destruct H as [H|H].

Lemma wf_cset_strengthen : forall x E Ap C,
  x `~in`A (dom E) ->
  wf_cset E Ap C ->
  wf_cset E (Ap `\`A x) C.
Proof with eauto.
  intros * ? H.
  inversion H; subst.
  econstructor...
  enough (xs `c`A (dom E)) by fsetdec.
  intros y yIn.
  forwards (? & B): H1 y yIn.
  destruct_bound B; forwards: binds_In B; fsetdec.
Qed.

(* Type bindings don't matter at all! *)
Lemma wf_cset_narrowing_base : forall V U C E A F X,
  wf_cset (F ++ [(X, bind_sub V)] ++ E) A C ->
  ok (F ++ [(X, bind_sub U)] ++ E) ->
  wf_cset (F ++ [(X, bind_sub U)] ++ E) A C.
Proof with simpl_env; eauto.
  intros *.
  intros Hwf Hok.
  wf_cset_simpl False...
  rename Hexists into B;
  destruct_bound B; binds_cases B...
Qed.

Lemma wf_cset_narrowing_typ_base : forall C1 C2 C E A F X,
  wf_cset (F ++ [(X, bind_typ C1)] ++ E) A C ->
  ok (F ++ [(X, bind_typ C2)] ++ E) ->
  wf_cset (F ++ [(X, bind_typ C2)] ++ E) A C.
Proof with simpl_env; eauto.
  intros *. intros Hwf Hok.
  wf_cset_simpl False.
  rename Hexists into B;
  destruct_bound B; binds_cases B...
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

Lemma wf_cset_ignores_typ_bindings : forall E F x T1 T2 Ap C,
  wf_cset (F ++ [(x, bind_typ T1)] ++ E) Ap C ->
  wf_cset (F ++ [(x, bind_typ T2)] ++ E) Ap C.
Proof with eauto.
  intros*.
  intros H.
  remember (F ++ [(x, bind_typ T1)] ++ E).
  generalize dependent F.
  induction H; intros F Eq; subst...
  econstructor... unfold allbound in *.
  intros.
  destruct (H x0 H1) as [T Hb].
  destruct_bound Hb; binds_cases Hb...
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
  econstructor... unfold allbound in *.
  intros.
  destruct (H x0 H1) as [T Hb].
  destruct_bound Hb; binds_cases Hb...
Qed.


Create HintDb fsetdec.

Hint Extern 1 (_ `in` _) => fsetdec: fsetdec.

Lemma wf_cset_singleton_by_mem : forall xs b1 l1 E A x b2 l2,
  wf_cset E A (cset_set xs {}N b1 l1) ->
  x `in` xs ->
  wf_cset E A (cset_set {x}A {}N b2 l2).
Proof with eauto with fsetdec.
  intros * Wfxs xIn.
  inversion Wfxs; subst...
Qed.

(* NOTE: wf_cset precondition in wf_cset_singleton_by_mem0 can be proven by
         constructor, which leaves an uninstantiated evar. This approach avoids the
         problem. *)
Hint Extern 1 (wf_cset_in ?E (cset_set {?x}A {}N _ _)) =>
match goal with
| H1 : x `in` ?xs , H2 : (wf_cset_in ?E (cset_set ?xs {}N ?b ?ls)) |- _ =>
  apply (wf_cset_singleton_by_mem xs b ls)
end : core.

Hint Extern 1 (wf_cset ?E ?A (cset_set {?x}A {}N _ _)) =>
match goal with
| H1 : x `in` ?xs , H2 : (wf_cset ?E A (cset_set ?xs {}N ?b ?ls)) |- _ =>
  apply (wf_cset_singleton_by_mem xs b ls)
end : core.

Local Lemma __test_wf_cset_singleton1 : forall xs b1 l1 E x b2 l2,
  wf_cset_in E (cset_set xs {}N b1 l1) ->
  x `in` xs ->
  wf_cset_in E (cset_set {x}A {}N b2 l2).
Proof. eauto. Qed.

Local Lemma __test_wf_cset_singleton2 : forall xs b1 l1 E A x b2 l2,
  wf_cset E A (cset_set xs {}N b1 l1) ->
  x `in` xs ->
  wf_cset E A (cset_set {x}A {}N b2 l2).
Proof. eauto. Qed.



(* ********************************************************************** *)
(** * #<a name="wft"></a># Properties of [wf_typ] *)

Ltac wf_typ_inversion H :=
  inversion H;
  let t := type of H in
  let has_useful_wf_pretyp :=
      fun T =>
        match T with
        | (typ_arrow _ _) => true
        | (typ_all _ _) => true
        | _ => false
        end
  in
  let invert_pretyp :=
      fun E T =>
        match goal with
        | H : wf_pretyp E _ _ T |- _ =>
          inversion H
        end
  in
  match t with
  | wf_typ_in ?E (typ_capt _ ?T) =>
    match has_useful_wf_pretyp T with
    | true => invert_pretyp E T
    | false => idtac
    end
  | wf_typ ?E _ _ (typ_capt _ ?T) =>
    match has_useful_wf_pretyp T with
    | true => invert_pretyp E T
    | false => idtac
    end
  | _ => idtac
  end; subst.

Local Lemma test_wf_typ_inversion : forall E Ap Am C S T U D P,
  wf_typ_in E (typ_capt C (typ_arrow S T)) ->
  wf_typ E Ap Am (typ_capt C (typ_arrow S T)) ->
  wf_typ_in E (typ_capt D P) ->
  wf_typ_in E U ->
  wf_typ_in E S /\ wf_typ E Am Ap S.
Proof.
  intros* H1 H2 H3 H4.
  let t := match goal with |- ?g => g end in idtac t.
  wf_typ_inversion H1.
  wf_typ_inversion H2.
  wf_typ_inversion H3.          (* shouldn't invert pretyp *)
  wf_typ_inversion H4.          (* shouldn't break, has to duplicate goal *)
  1,2 : split; assumption.
Qed.

(** If a type is well-formed in an environment, then it is locally
    closed. *)

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
  induction H; solve_obvious.
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

Tactic Notation "solve_obvious" "with" ident(id) :=
  try solve [econstructor; eauto using id].

Lemma wf_typ_strengthen : forall x E Ap Am P,
  x `~in`A (dom E) ->
  wf_typ E Ap Am P ->
  wf_typ E (Ap `\`A x) (Am `\`A x) P
with wf_pretyp_strengthen : forall x E Ap Am P,
  x `~in`A (dom E) ->
  wf_pretyp E Ap Am P ->
  wf_pretyp E (Ap `\`A x) (Am `\`A x) P.
Proof with eauto using wf_cset_strengthen.
{ intros * ? WfP.
  dependent induction WfP; solve_obvious with wf_cset_strengthen.
  - econstructor...
    apply binds_In in H0.
    fsetdec.
  - econstructor...
}
{ intros * ? WfP.
  dependent induction WfP; solve_obvious.
  - pick fresh y and apply wf_typ_arrow...
    specialize (H1 y ltac:(notin_solve)).
    eapply (wf_typ_strengthen x) in H1...
    assert (y <> x) by notin_solve.
    apply (wf_typ_adapt H1); clear Fr; fsetdec.
  - pick fresh y and apply wf_typ_all...
    specialize (H1 y ltac:(notin_solve)).
    eapply (wf_typ_strengthen x) in H1...
    assert (y <> x) by notin_solve.
    apply (wf_typ_adapt H1); clear Fr; fsetdec.
}
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
  induction H; intros G Hok Heq; subst; solve_obvious.
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

Lemma wf_typ_in_weakening : forall T E F G,
  wf_typ_in (G ++ E) T ->
  ok (G ++ F ++ E) ->
  wf_typ_in (G ++ F ++ E) T.
Proof with eauto.
  intros * Hwf Hok.
  eapply wf_typ_weakening...
Qed.

Lemma wf_pretyp_in_weakening : forall T E F G,
  wf_pretyp_in (G ++ E) T ->
  ok (G ++ F ++ E) ->
  wf_pretyp_in (G ++ F ++ E) T.
Proof with eauto.
  intros * Hwf Hok.
  eapply wf_pretyp_weakening...
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
  induction H; intros F Hok Heq; subst; solve_obvious.
  (* typ_arrow *)
  - pick fresh Y and apply wf_typ_arrow...
    rewrite <- concat_assoc.
    eapply wf_typ_narrowing_base...
  (* typ_all *)
  - pick fresh Y and apply wf_typ_all...
    rewrite <- concat_assoc.
    eapply wf_typ_narrowing_base...
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
  - binds_cases H; econstructor...
  - econstructor...
------
  intros *. intros Hwf_typ Hok.
  remember (F ++ [(X, bind_typ V)] ++ E).
  generalize dependent F.
  induction Hwf_typ; intros F Hok Heq; subst; solve_obvious.
  - Case "typ_arrow".
    pick fresh Y and apply wf_typ_arrow...
    rewrite <- concat_assoc.
    eapply wf_typ_narrowing_typ_base...
  - Case "typ_all".
    pick fresh Y and apply wf_typ_all...
    rewrite <- concat_assoc.
    eapply wf_typ_narrowing_typ_base...
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

Lemma wf_typ_ignores_typ_bindings : forall E F x T1 T2 Ap Am T,
  wf_typ (F ++ [(x, bind_typ T1)] ++ E) Ap Am T ->
  wf_typ (F ++ [(x, bind_typ T2)] ++ E) Ap Am T
with wf_pretyp_ignores_typ_bindings : forall E F x T1 T2 Ap Am T,
  wf_pretyp (F ++ [(x, bind_typ T1)] ++ E) Ap Am T ->
  wf_pretyp (F ++ [(x, bind_typ T2)] ++ E) Ap Am T.
Proof with eauto.
------
  intros* H.
  remember (F ++ [(x, bind_typ T1)] ++ E).
  generalize dependent F.
  induction H; intros F Eq; subst.
  - apply wf_typ_var with (U := U)...
    binds_cases H...
  - econstructor... eapply wf_cset_ignores_typ_bindings...
------
  intros* H.
  remember (F ++ [(x, bind_typ T1)] ++ E).
  generalize dependent F.
  induction H; intros F Eq; subst; solve_obvious.
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
  - destruct (X == x); subst; eapply wf_typ_var...
  - econstructor... eapply wf_cset_ignores_sub_bindings...
------
  intros*.
  intros Hok H.
  remember (F ++ [(x, bind_sub T1)] ++ E).
  generalize dependent F.
  induction H; intros F Eq; subst; solve_obvious.
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

Hint Extern 5 (wf_typ ?E _ _ ?T) =>
match goal with
| H : (wf_typ E ?Ap0 ?Am0 T) |- _ =>
  apply wf_typ_set_weakening with (Ap := Ap0) (Am := Am0)
| H : (wf_typ_in E T) |- _ =>
  unfold wf_typ_in in H; apply wf_typ_set_weakening with (Ap := (dom E)) (Am := (dom E))
end : core.

Notation "x `mem`A E" := (AtomSet.F.mem x E) (at level 69) : metatheory_scope.



(* ********************************************************************** *)
(** * #<a name="wffrom"></a># Lemmas helping to extract wellformedness or closedness from other properties. *)


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

Lemma wf_typ_from_binds_sig : forall x U Q,
  wf_sig Q ->
  Signatures.binds x (bind_sig U) Q ->
  wf_typ_in empty U.
Proof with eauto using wf_typ_weaken_head.
  intros * Hwf Hbinds.
  unfold wf_typ_in.
  induction Hwf; Signatures.binds_cases Hbinds...
  inversion select (_ = _); subst...
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

Lemma wf_cset_from_binds : forall b x E,
  wf_env E ->
  binds x (bind_typ b) E ->
  wf_cset_in E (`cset_fvar` x).
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

Lemma wf_cv_env_bind_typ : forall F x U E,
  wf_env (F ++ [(x, bind_typ U)] ++ E) ->
  wf_cset_in E (cv U).
Proof with eauto.
  intros * H.
  apply cv_wf.
  assert (wf_env ([(x, bind_typ U)] ++ E)) as HA by eauto.
  inversion HA...
Qed.

Lemma wf_typ_env_bind_typ : forall F x U E,
  wf_env (F ++ [(x, bind_typ U)] ++ E) ->
  wf_typ_in E U.
Proof with eauto.
  intros * H.
  assert (wf_env ([(x, bind_typ U)] ++ E)) as HA by eauto.
  inversion HA...
Qed.

Lemma wf_typ_env_bind_sub : forall F x U E,
  wf_env (F ++ [(x, bind_sub U)] ++ E) ->
  wf_typ_in E U.
Proof with eauto.
  intros * H.
  assert (wf_env ([(x, bind_sub U)] ++ E)) as HA by eauto.
  inversion HA...
Qed.

Hint Resolve wf_cv_env_bind_typ : core.
Hint Resolve wf_typ_env_bind_typ : core.
Hint Resolve wf_typ_env_bind_sub : core.



(* ********************************************************************** *)
(** * #<a name="wfsubst"></a># Lemmas connecting substitution and wellformedness of [wf_cset], [wf_typ], ... *)

Ltac destruct_union_mem H :=
  rewrite AtomSetFacts.union_iff in H; destruct H as [H|H].

Lemma wf_cset_subst_tb : forall F Q E Ap Am Z P C,
  wf_cset (F ++ [(Z, bind_sub Q)] ++ E) Ap C ->
  wf_typ E Ap Am P ->
  ok (F ++ [(Z, bind_sub Q)] ++ E) ->
  wf_cset (map (subst_tb Z P) F ++ E) (Ap `\`A Z ) (subst_cset Z (cv P) C).
Proof with simpl_env; eauto*.
  intros * HwfC HwfP Hok.
  inversion HwfC; subst.
  unfold subst_cset.
  destruct_set_mem Z xs.
  - destruct HwfP; simpl.
    + unfold cset_union; csetsimpl.
      destruct_set_mem Z Ap; [|exfalso; fsetdec].
      constructor.
      2: apply binds_In in H1;
        apply fresh_mid_tail in Hok;
        fsetdec.

      intros y yIn.
      destruct_union_mem yIn. {
        rewrite AtomSetFacts.singleton_iff in yIn; symmetry in yIn; subst...
      }
      rename H into H'.
      forwards (S & H): H' y.
      1: { fsetdec. }
      assert (y <> Z) by fsetdec.
      {
        simpl_env in H.
        destruct H; binds_cases H.
        rename select (binds y _ _) into HBnd.
        - exists S...
        - exists (subst_tt Z X S)...
        - exists S...
        - exists (subst_tt Z X S)...
      }
    + destruct H1.
      rename xs0 into cs.
      destruct_set_mem Z A; [|exfalso; fsetdec].
      unfold cset_union; csetsimpl.
      constructor.
      2: {
        assert (Z `~in`A cs). {
          apply fresh_mid_tail in Hok.
          intros ZIn'.
          specialize (H1 Z ZIn') as [? H1].
          destruct H1; apply binds_In in H1; fsetdec.
        }
        fsetdec.
      }
      intros y yIn.
      destruct_union_mem yIn.
      * specialize (H1 y ltac:(fsetdec)).
        destruct H1 as [S H1].
        destruct H1; binds_cases H1...
      * inversion HwfC; subst.
        match goal with
        | H : allbound _ xs |- _ =>
          specialize (H y ltac:(fsetdec));
            destruct H as [S H];
            destruct H; binds_cases H
        end...
        -- exists (subst_tt Z (typ_capt (cset_set cs {}N b0 ls0) P) S)...
        -- exfalso; fsetdec.
        -- exists (subst_tt Z (typ_capt (cset_set cs {}N b0 ls0) P) S)...
  - inversion HwfC; rename select (allbound _ _) into HAllBound; subst; constructor. {
      intros x xIn.
      destruct (HAllBound x xIn) as [T HBnd].
      destruct_bound HBnd; binds_cases HBnd...
      + exists (subst_tt Z P T)...
      + exists (subst_tt Z P T)...
    }
    destruct HwfP; simpl; destruct_set_mem Z Ap.
    all: fsetdec.               (* automation gets a bit lost here, why? *)
Qed.

Lemma wf_typ_subst_tb : forall F Q E Ap Am Z P T,
  wf_typ (F ++ [(Z, bind_sub Q)] ++ E) Ap Am T ->
  (** NOTE here that P needs to be well formed in both the + and - environments, *)
(*       as we're substituting in both places. *)
  wf_typ E Ap Am P ->
  wf_typ E Am Ap P ->
  ok (F ++ [(Z, bind_sub Q)] ++ E) ->
  wf_typ (map (subst_tb Z P) F ++ E) (Ap `\`A Z) (Am `\`A Z) (subst_tt Z P T)
with wf_pretyp_subst_tb : forall F Q E Ap Am Z P T,
  wf_pretyp (F ++ [(Z, bind_sub Q)] ++ E) Ap Am T ->
  wf_typ E Ap Am P ->
  wf_typ E Am Ap P ->
  ok (F ++ [(Z, bind_sub Q)] ++ E) ->
  wf_pretyp (map (subst_tb Z P) F ++ E) (Ap `\`A Z) (Am `\`A Z) (subst_tpt Z P T).
Proof with simpl_env; eauto using wf_typ_weaken_head, type_from_wf_typ, wf_cset_subst_tb.
------
  intros *. intros HwfT HwfPp HwfPm Hok.
  (* remember (F ++ [(Z, bind_sub Q)] ++ E). *)
  (* generalize dependent F. *)
  (* induction HwfT; intros F EQF Hok; subst; simpl subst_tt. *)
  dependent induction HwfT; simpl.
  - Case "wf_typ_var".
    destruct (X == Z); subst.
    + eapply wf_typ_weaken_head with (Ap := (Ap `\`A Z)) (Am := (Am `\`A Z))...
      forwards: fresh_mid_tail Hok.
      eapply wf_typ_strengthen...
    + SCase "X <> Z".
      unfold wf_typ_in in *.
      forwards: fresh_mid_tail Hok.
      binds_cases H.
      * apply (wf_typ_var U)...
        fsetdec.
      * apply (wf_typ_var (subst_tt Z P U))...
        fsetdec.
  - unfold wf_typ_in in *.
    simpl subst_tt.
    econstructor...
------
  intros * HwfT HwfPp HwfPm Hok.
  dependent induction HwfT; simpl; solve_obvious.
  - Case "wf_typ_arrow".
    pick fresh Y and apply wf_typ_arrow...
    + SCase "T2".
      unfold open_ct in *...
      rewrite <- subst_tt_open_ct_rec...
      rewrite_env (map (subst_tb Z P) ([(Y, bind_typ T1)] ++ F) ++ E).
      replace ((Ap `\`A Z) `u`A {Y}A) with ((Ap `u`A {Y}A) `\`A Z).
      2: {
        assert (Y <> Z) by notin_solve.
        clear Fr; fsetdec.
      }
      eapply wf_typ_subst_tb...
      * apply wf_typ_set_weakening with (Ap := Ap) (Am := Am)...
        apply ok_tail, ok_tail in Hok...
      * apply wf_typ_set_weakening with (Ap := Am) (Am := Ap)...
        apply ok_tail, ok_tail in Hok...
  - Case "wf_typ_all".
    pick fresh Y and apply wf_typ_all...
    + SCase "T2".
      unfold open_ct in *...
      rewrite subst_tt_open_tt_var...
      rewrite_env (map (subst_tb Z P) ([(Y, bind_sub T1)] ++ F) ++ E).
      replace ((Ap `\`A Z) `u`A {Y}A) with ((Ap `u`A {Y}A) `\`A Z).
      replace ((Am `\`A Z) `u`A {Y}A) with ((Am `u`A {Y}A) `\`A Z).
      2,3: assert (Y <> Z) by notin_solve; clear Fr; fsetdec.
      eapply wf_typ_subst_tb...
      * apply wf_typ_set_weakening with (Ap := Ap) (Am := Am)...
        apply ok_tail, ok_tail in Hok...
      * apply wf_typ_set_weakening with (Ap := Am) (Am := Ap)...
        apply ok_tail, ok_tail in Hok...
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
  intros * HwfC HwfEnv HwfD Hsset HApRsnbl Hok.
  destruct C.
  unfold subst_cset.
  forwards: binding_uniq_from_wf_env HwfEnv.
  destruct_set_mem x t...
  - apply wf_cset_union.
    + rewrite_nil_concat.
      apply wf_cset_weakening with (A := Ap'); simpl_env...
    + inversion HwfC; subst.
      constructor...
      unfold allbound in *.
      intros y yIn.
      destruct (y == x).
      * exfalso; fsetdec.
      * forwards (T & B): H4 y.
        ** fsetdec.
        ** simpl_env in B.
           destruct_bound B; binds_cases B; eauto; exists (subst_ct x D T)...
  - inversion HwfC; subst.
    constructor...
    unfold allbound in *.
    intros y yIn.
    forwards (T & B): H4 y.
    { fsetdec. }
    simpl_env in B.
    destruct_bound B; binds_cases B; eauto*; exists (subst_ct x D T)...
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
    forwards: binding_uniq_from_wf_env (bind_typ Q)...
  }
  unfold wf_cset_in in *.
  replace (dom (map (subst_cb x D) F ++ E))
    with ((dom (F ++ [(x, bind_typ Q)] ++ E)) `remove` x) by (simpl_env; fsetdec).
  apply (wf_cset_subst_cb Q (dom E))...
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
    find_and_destroy_set_mem. {
      csetdec.
      constructor...
      2: {
        assert (Z `~in`A (dom E)) as HA. {
          eapply fresh_mid_tail...
        }
        assert (Z `~in`A xs). {
          destruct_set_mem Z xs...
          specialize (H Z ZIn0) as [T H].
          destruct H; apply binds_In in H; exfalso...
        }
        fsetdec.
      }
      intros x Hfvx.

      destruct_union_mem Hfvx. {
        specialize (H x Hfvx) as [T H]...
        destruct H...
      }

      rename H4 into H4'.
      forwards [T H4]: (H4' x)...
      1: { fsetdec. }
      simpl_env in H4.
      destruct_bound H4; binds_cases H4...
      - exfalso; fsetdec.
      - exists (subst_ct Z (cset_set xs {}N b ls) T)...
      - exists (subst_ct Z (cset_set xs {}N b ls) T)...
    }
    {
      constructor.
      2: fsetdec.
      intros y yIn.
      assert (y <> Z) by fsetdec.
      rename H4 into H4'.
      forwards [T H4]: (H4' y)...
      simpl_env in H4.
      destruct_bound H4; binds_cases H4...
      - exists (subst_ct Z (cset_set xs {}N b ls) T)...
      - exists (subst_ct Z (cset_set xs {}N b ls) T)...
    }
Qed.

Lemma wf_cset_in_subst_tb : forall Q F E Z P C,
  ok (F ++ [(Z, bind_sub Q)] ++ E) ->
  wf_typ_in E P ->
  wf_cset_in (F ++ [(Z, bind_sub Q)] ++ E) C ->
  wf_cset_in (map (subst_tb Z P) F ++ E) (subst_cset Z (cv P) C).
Proof with eauto.
  intros * Ok WfP WfC.
  unfold wf_cset_in; simpl_env.
  replace (dom F `u`A dom E) with (dom (F ++ [(Z, bind_sub Q)] ++ E) `\`A Z).
  2: {
    forwards: fresh_mid_head Ok.
    forwards: fresh_mid_tail Ok.
    simpl_env; fsetdec.
  }
  eapply wf_cset_subst_tb with (Q := Q) (Am := dom E).
  - apply (wf_cset_adapt WfC)...
  - rewrite_env (empty ++ empty ++ E).
    eapply wf_typ_weakening; simpl_env in *.
    + apply WfP.
    + eapply ok_tail...
    + fsetdec.
    + fsetdec.
  - trivial...
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
    assert (X <> Z). {
      binds_cases H...
      - simpl_env in *.
        notin_solve.
      - assert (binds X (bind_sub U) (F ++ [(Z, bind_typ Q)] ++ E)) by auto.
        forwards: fresh_mid_head HokZ.
        forwards: binds_In H2.
        fsetdec.
    }
    binds_cases H...
    + apply (wf_typ_var U)...
      fsetdec.
    + apply (wf_typ_var (subst_ct Z C U))...
      fsetdec.
  - Case "wf_typ_capt".
    constructor...
    apply wf_cset_over_subst with (Q := Q)...
------
  intros * HwfT HwfCp HwfCm Hok HokZ.
  remember (F ++ [(Z, bind_typ Q)] ++ E).
  generalize dependent F.
  induction HwfT; intros F ? Hok; subst; simpl subst_ct; solve_obvious.
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
  - Case "wf_typ_all".
    pick fresh Y and apply wf_typ_all; fold subst_ct...
    + SCase "T2".
      unfold open_ct in *...
      rewrite subst_ct_open_tt_var...
      rewrite_env (map (subst_cb Z C) ([(Y, bind_sub T1)] ++ F) ++ E).
      replace ((Ap `\`A Z) `u`A {Y}A) with ((Ap `u`A {Y}A) `\`A Z).
      replace ((Am `\`A Z) `u`A {Y}A) with ((Am `u`A {Y}A) `\`A Z).
      2,3: assert (Y `notin` singleton Z) by notin_solve; clear Fr; fsetdec.
      apply wf_typ_subst_cb with (Q := Q)...
      * apply wf_cset_set_weakening with (A := Ap)...
      * apply wf_cset_set_weakening with (A := Am)...
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

Lemma wf_typ_in_subst_cset : forall x U C F E T,
  wf_env (F ++ [(x, bind_typ U)] ++ E) ->
  wf_typ_in (F ++ [(x, bind_typ U)] ++ E) T ->
  wf_cset_in E C ->
  wf_typ_in (map (subst_cb x C) F ++ E) (subst_ct x C T).
Proof with eauto*.
  intros * Hwf HwfT HwfC.
  unfold wf_typ_in.
  erewrite dom_x_subst_away...
  eapply wf_typ_subst_cb...
  1, 2: simpl_env in *; apply wf_cset_extra...
Qed.

Lemma wf_pretyp_in_subst_cset : forall x U C F E T,
  wf_env (F ++ [(x, bind_typ U)] ++ E) ->
  wf_pretyp_in (F ++ [(x, bind_typ U)] ++ E) T ->
  wf_cset_in E C ->
  wf_pretyp_in (map (subst_cb x C) F ++ E) (subst_cpt x C T).
Proof with eauto*.
  intros * Hwf HwfT HwfC.
  unfold wf_pretyp_in.
  erewrite dom_x_subst_away...
  eapply wf_pretyp_subst_cb...
  1, 2: simpl_env in *; apply wf_cset_extra...
Qed.

(*
  opening capture sets in types preserves well-formedness. *)
Lemma open_ct_wf_typ : forall E Ap Am T C,
  wf_typ E Ap Am T ->
  wf_typ E Ap Am (open_ct T C).
Proof with eauto using type_from_wf_typ.
  intros *.
  intros H.
  closed_type...
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
  eapply wf_typ_subst_cb' with (Q := T1)...
  assert (X `notin` L) by fsetdec.
  specialize (H5 X H).
  unfold wf_typ_in...
Qed.

Lemma wf_typ_open_type : forall E U T1 T2,
  ok E ->
  wf_pretyp_in E (typ_all T1 T2) ->
  wf_typ_in E U ->
  wf_typ_in E (open_tt T2 U).
Proof with simpl_env; eauto.
  intros * Hok HwfA HwfU.
  inversion HwfA; subst...
  pick fresh X.
  rewrite (subst_tt_intro X)...
  assert (X `~in`A dom E) by notin_solve.
  unfold wf_typ_in.
  replace (dom E) with ((dom E `u`A {X}A) `\`A X) by (clear Fr;fsetdec).
  rewrite_env (map (subst_tb X U) empty ++ E).
  apply wf_typ_subst_tb with (Q := T1)...
  csetsimpl...
Qed.

Lemma wf_typ_in_subst_cb_cv : forall U F E x T,
  wf_env (F ++ [(x, bind_typ U)] ++ E) ->
  wf_typ_in (F ++ [(x, bind_typ U)] ++ E) T ->
  wf_typ_in (map (subst_cb x (cv U)) F ++ E) (subst_ct x (cv U) T).
Proof with eauto*.
  intros * Hwf HwfT.
  unfold wf_typ_in.
  erewrite dom_x_subst_away...
  eapply wf_typ_subst_cb...
  1, 2: simpl_env in *; apply wf_cset_extra...
Qed.

Lemma wf_pretyp_in_subst_cb_cv : forall U F E x T,
  wf_env (F ++ [(x, bind_typ U)] ++ E) ->
  wf_pretyp_in (F ++ [(x, bind_typ U)] ++ E) T ->
  wf_pretyp_in (map (subst_cb x (cv U)) F ++ E) (subst_cpt x (cv U) T).
Proof with eauto*.
  intros * Hwf HwfT.
  unfold wf_pretyp_in.
  erewrite dom_x_subst_away...
  eapply wf_pretyp_subst_cb...
  1, 2: simpl_env in *; apply wf_cset_extra...
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
{ intros * Ok WfP WfT.
  unfold wf_typ_in; simpl_env.
  replace (dom F `u`A dom E) with (dom (F ++ [(Z, bind_sub Q)] ++ E) `\`A Z).
  2: {
    forwards: fresh_mid_head Ok.
    forwards: fresh_mid_tail Ok.
    simpl_env; fsetdec.
  }

  assert (Z `notin` (dom F `union` dom E)). {
    eapply binding_uniq_from_ok...
  }
  forwards HA: wf_typ_subst_tb Q P WfT.
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
  unfold wf_pretyp_in; simpl_env.
  replace (dom F `u`A dom E) with (dom (F ++ [(Z, bind_sub Q)] ++ E) `\`A Z).
  2: {
    forwards: fresh_mid_head Ok.
    forwards: fresh_mid_tail Ok.
    simpl_env; fsetdec.
  }
  assert (Z `notin` (dom F `union` dom E)). {
    eapply binding_uniq_from_ok...
  }

  forwards HA: wf_pretyp_subst_tb Q P WfT.
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
    inversion Wf_env; subst; simpl_env in *; simpl subst_tb;
      try solve [econstructor; eauto; eapply wf_typ_in_subst_tb; eauto]...
Qed.


Lemma wf_env_subst_cb : forall Q C x E F,
wf_env (F ++ [(x, bind_typ Q)] ++ E) ->
wf_cset_in E C ->
wf_env (map (subst_cb x C) F ++ E).
Proof with eauto using wf_typ_subst_cb, wf_cset_extra.
  intros *.
  induction F; intros Hwf HwfC; simpl_env in *;
    inversion Hwf; simpl_env in *; simpl subst_tb...
  + constructor...
    unfold wf_typ_in.
    erewrite dom_x_subst_away...
    eapply wf_typ_subst_cb...
    all : simpl_env in *; apply wf_cset_extra...
  + constructor...
    unfold wf_typ_in.
    erewrite dom_x_subst_away...
    eapply wf_typ_subst_cb...
    all : simpl_env in *; apply wf_cset_extra...
Qed.

Lemma wf_typ_subst_cb_cv : forall U G F E x T Ap Am,
  wf_env (G ++ F ++ [(x, bind_typ U)] ++ E) ->
  wf_typ (G ++ F ++ [(x, bind_typ U)] ++ E) Ap Am T ->
  (dom E `union` dom F) `subset` Ap ->
  (dom E `union` dom F) `subset` Am ->
  wf_typ (map (subst_cb x (cv U)) (G ++ F) ++ E) (Ap `remove` x) (Am `remove` x) (subst_ct x (cv U) T).
Proof with eauto*.
  intros * Hwf HwfT Hp Hm.
  eapply wf_typ_subst_cb; simpl_env...
  1, 2: simpl_env in *; apply wf_cset_extra...
  rewrite_env (map (subst_cb x (cv U)) (G ++ F) ++ E)...
  apply ok_from_wf_env...
  eapply wf_env_subst_cb...
  simpl_env in *...
Qed.

Lemma wf_pretyp_subst_cb_cv : forall U G F E x T Ap Am,
  wf_env (G ++ F ++ [(x, bind_typ U)] ++ E) ->
  wf_pretyp (G ++ F ++ [(x, bind_typ U)] ++ E) Ap Am T ->
  (dom E `union` dom F) `subset` Ap ->
  (dom E `union` dom F) `subset` Am ->
  wf_pretyp (map (subst_cb x (cv U)) (G ++ F) ++ E)
            (Ap `remove` x)
            (Am `remove` x)
            (subst_cpt x (cv U) T).
Proof with eauto*.
  intros * Hwf HwfT Hp Hm.
  eapply wf_pretyp_subst_cb; simpl_env...
  1, 2: simpl_env in *; apply wf_cset_extra...
  rewrite_env (map (subst_cb x (cv U)) (G ++ F) ++ E)...
  apply ok_from_wf_env...
  eapply wf_env_subst_cb...
  simpl_env in *...
Qed.

Lemma wf_typ_preserved_by_subst_wf_cset : forall x C E Ap Am T,
  wf_env E ->
  Ap `c`A dom E ->
  Am `c`A dom E ->
  wf_typ E Ap Am T ->
  (x `notin` Am -> wf_cset E Ap C -> wf_typ E Ap Am (subst_ct x C T)) /\
  (x `notin` Ap -> wf_cset E Am C -> wf_typ E Ap Am (subst_ct x C T))
with wf_pretyp_preserved_by_subst_wf_cset : forall x C E Ap Am T,
  wf_env E ->
  Ap `c`A dom E ->
  Am `c`A dom E ->
  wf_pretyp E Ap Am T ->
  (x `notin` Am -> wf_cset E Ap C -> wf_pretyp E Ap Am (subst_cpt x C T)) /\
  (x `notin` Ap -> wf_cset E Am C -> wf_pretyp E Ap Am (subst_cpt x C T)).
Proof with eauto.
{ intros * ? ? ? WfT.
  generalize dependent Ap.
  generalize dependent Am.
  induction T; intros ? ? ? ? WfT.
  - simpl.
    split; intros ? WfC.
    + constructor.
      * unfold subst_cset.
        inversion WfT.
        destruct_if; eauto using wf_cset_union, wf_cset_remove_fvar.
      * inversion WfT; subst.
        unshelve epose proof (wf_pretyp_preserved_by_subst_wf_cset x C E Ap Am p _ _ _ _) as IH...
        apply (proj1 IH)...
    + constructor.
      * unfold subst_cset.
        inversion WfT; subst.
        destruct_if...
        inversion select (wf_cset _ _ c); subst.
        rewrite_set_facts_in Heqb.
        exfalso;fsetdec.
      * inversion WfT; subst.
        unshelve epose proof (wf_pretyp_preserved_by_subst_wf_cset x C E Ap Am p _ _ _ _) as IH...
        apply (proj2 IH)...
  - inversion WfT.
  - simpl...
}
{ intros * ? ? ? WfT.
  generalize dependent Ap.
  generalize dependent Am.
  induction T; intros ? ? ? ? WfT; solve_obvious.
  - wf_typ_inversion WfT.
    split; intros ? WfC.
    + pick fresh y and apply wf_typ_arrow; fold subst_ct...
      1: {
        unshelve epose proof (wf_typ_preserved_by_subst_wf_cset x C E Am Ap t _ _ _ _) as IH...
        apply (proj2 IH)...
      }
      specialize (H8 y ltac:(notin_solve)).
      apply (wf_typ_preserved_by_subst_wf_cset x C) in H8...
      rewrite subst_ct_open_ct_var ; [| notin_solve | eapply capt_from_wf_cset]...
      rewrite_nil_concat.
      eapply wf_typ_ignores_typ_bindings; simpl...
      apply (proj1 H8)...
      rewrite_nil_concat.
      eapply wf_cset_weakening; [ apply WfC | simpl_env; auto .. ].
    + pick fresh y and apply wf_typ_arrow; fold subst_ct...
      1: {
        unshelve epose proof (wf_typ_preserved_by_subst_wf_cset x C E Am Ap t _ _ _ _) as IH...
        apply (proj1 IH)...
      }
      specialize (H8 y ltac:(notin_solve)).
      apply (wf_typ_preserved_by_subst_wf_cset x C) in H8...
      rewrite subst_ct_open_ct_var ; [| notin_solve | eapply capt_from_wf_cset]...
      rewrite_nil_concat.
      eapply wf_typ_ignores_typ_bindings; simpl...
      apply (proj2 H8)...
      rewrite_nil_concat.
      eapply wf_cset_weakening; [ apply WfC | simpl_env; auto .. ].
  - wf_typ_inversion WfT.
    split; intros ? WfC.
    + pick fresh y and apply wf_typ_all; fold subst_ct...
      1: {
        unshelve epose proof (wf_typ_preserved_by_subst_wf_cset x C E Am Ap t _ _ _ _) as IH...
        apply (proj2 IH)...
      }
      specialize (H8 y ltac:(notin_solve)).
      apply (wf_typ_preserved_by_subst_wf_cset x C) in H8...
      rewrite subst_ct_open_tt_var ; [| notin_solve | eapply capt_from_wf_cset]...
      rewrite_nil_concat.
      eapply wf_typ_ignores_sub_bindings; simpl...
      apply (proj1 H8)...
      rewrite_nil_concat.
      eapply wf_cset_weakening; [ apply WfC | simpl_env; auto .. ].
    + pick fresh y and apply wf_typ_all; fold subst_ct...
      1: {
        unshelve epose proof (wf_typ_preserved_by_subst_wf_cset x C E Am Ap t _ _ _ _) as IH...
        apply (proj1 IH)...
      }
      specialize (H8 y ltac:(notin_solve)).
      apply (wf_typ_preserved_by_subst_wf_cset x C) in H8...
      rewrite subst_ct_open_tt_var ; [| notin_solve | eapply capt_from_wf_cset]...
      rewrite_nil_concat.
      eapply wf_typ_ignores_sub_bindings; simpl...
      apply (proj2 H8)...
      rewrite_nil_concat.
      eapply wf_cset_weakening; [ apply WfC | simpl_env; auto .. ].
  - wf_typ_inversion WfT.
    split; intros NotIn WfC.
    + apply wf_typ_ret; fold subst_ct.
      unshelve epose proof (wf_typ_preserved_by_subst_wf_cset x C E Am Ap t _ _ _ _) as [ IH1 IH2 ]...
    + apply wf_typ_ret; fold subst_ct.
      unshelve epose proof (wf_typ_preserved_by_subst_wf_cset x C E Am Ap t _ _ _ _) as [ IH1 IH2 ]...
}
Qed.


(* ********************************************************************** *)
(** * #<a name="okt"></a># Properties of [wf_env] *)


Lemma wf_env_strengthening : forall F E, wf_env (F ++ E) -> wf_env E.
Proof with eauto.
  induction F...
Qed.

Lemma wf_env_weaken_head : forall E F,
  wf_env (F ++ E) ->
  wf_env E.
Proof with eauto*.
  intros E F Hwf.
  induction F...
Qed.

Lemma wf_env_narrowing : forall V E F U X,
  wf_env (F ++ [(X, bind_sub V)] ++ E) ->
  wf_typ_in E U ->
  wf_env (F ++ [(X, bind_sub U)] ++ E).
Ltac hint ::=
  eauto using wf_typ_narrowing_base.
Proof with hint.
  induction F; intros U X Wf_env Wf;
    inversion Wf_env; subst; simpl_env in *.
  - constructor...
  - constructor.
    + eapply IHF...
    + apply wf_typ_narrowing_base with (V := V)...
    + simpl_env; fsetdec.
  - constructor.
    + eapply IHF...
    + apply wf_typ_narrowing_base with (V := V)...
    + simpl_env; fsetdec.
Qed.

Lemma wf_env_narrowing_typ : forall V E F U X,
  wf_env (F ++ [(X, bind_typ V)] ++ E) ->
  wf_typ_in E U ->
  wf_env (F ++ [(X, bind_typ U)] ++ E).
Proof with eauto using wf_typ_narrowing_typ_base, wf_cset_narrowing_typ_base.
  induction F; intros U X Wf_env Wf;
    inversion Wf_env; subst; simpl_env in *.
  - constructor...
  - constructor.
    + eapply IHF...
    + apply wf_typ_narrowing_typ_base with (V := V)...
    + simpl_env; fsetdec.
  - constructor.
    + eapply IHF...
    + apply wf_typ_narrowing_typ_base with (V := V)...
    + simpl_env; fsetdec.
Qed.

Lemma wf_env_inv : forall F Z b E,
  wf_env (F ++ [(Z, b)] ++ E) ->
  wf_env E /\ Z `notin` dom E.
Proof with eauto.
  induction F ; intros ; simpl_env in *.
  inversion H ; subst...
  inversion H ; subst...
Qed.
