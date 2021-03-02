Require Import Coq.Program.Equality.
Require Import Fsub_Soundness.
Require Import Fsub_CVfacts.

Inductive subcapt' : env -> captureset -> captureset -> Prop :=
  | subcapt__universal : forall E C,
      wf_cset_in E C ->
      subcapt' E C cset_universal
  | subcapt__in : forall E x xs,
      wf_cset_in E (cset_set (singleton x) {}N) ->
      wf_cset_in E (cset_set xs {}N) ->
      x `in` xs ->
      subcapt' E (cset_set (singleton x) {}N) (cset_set xs {}N)
  | subcapt__var : forall E x T C D,
      binds x (bind_typ T) E ->
      cv E T C ->
      subcapt' E C D ->
      subcapt' E (cset_set (singleton x) {}N) D
  | subcapt__set : forall E xs D,
      wf_cset_in E (cset_set xs {}N) ->
      wf_cset_in E D ->
      AtomSet.F.For_all (fun x => subcapt' E (cset_set (singleton x) {}N) D) xs ->
      subcapt' E (cset_set xs {}N) D
.

Lemma subcapt__regular : forall E C D,
  subcapt' E C D ->
  wf_cset_in E C /\ wf_cset_in E D.
Proof with eauto*.
  intros* H.
  induction H; subst...
  split...
  constructor.
  2: {
    apply binds_In in H...
  }
  intros y yInX.
  rewrite AtomSetFacts.singleton_iff in yInX; subst...
Qed.

Lemma subcapt_equivalence : forall E C D,
  subcapt' E C D <-> subcapt E C D.
Proof with eauto.
  intros.
  split.
  { intro Hsc.
    destruct C eqn:EQ__C. {
      inversion Hsc; subst.
      constructor.
      constructor.
    }
    destruct D eqn:EQ__D. {
      constructor.
      apply subcapt__regular in Hsc; eauto*.
    }
    apply subcapt__regular in Hsc as P.
    destruct P as (Reg1 & Reg2).
    inversion Reg1; subst.
    inversion Reg2; subst.
    constructor...
    unfold AtomSet.F.For_all.
    dependent induction Hsc.
    - intros y yInX.
      rewrite AtomSetFacts.singleton_iff in yInX; subst...
    - intros y yInX.
      rewrite AtomSetFacts.singleton_iff in yInX; symmetry in yInX; subst.
      destruct C. {
        inversion Hsc.
      }
      apply cv_regular in H0 as P.
      destruct P as (_ & _ & Reg3).
      inversion Reg3; subst.
      eapply captures_var.
      + apply H.
      + apply H0.
      + unfold AtomSet.F.For_all.
        apply IHHsc...
    - intros x xIn.
      eapply H2 with (x := x) (t := (singleton x))...
      3: fsetdec.
      2: {
        unfold allbound_typ in *...
        intros x0 x0InX.
        rewrite AtomSetFacts.singleton_iff in x0InX; symmetry in x0InX; subst...
      }
      {
        constructor. {
          unfold allbound_typ in *...
          intros x0 x0InX.
          rewrite AtomSetFacts.singleton_iff in x0InX; symmetry in x0InX; subst...
        }
        fsetdec.
      }
  }
  { intro Hsc.
    destruct C eqn:EQ__C. {
      inversion Hsc; subst.
      constructor.
      constructor.
    }
    destruct D eqn:EQ__D. {
      constructor.
      apply subcapt_regular in Hsc; eauto*.
    }
    apply subcapt_regular in Hsc as P.
    destruct P as (Reg1 & Reg2).
    inversion Reg1; subst.
    inversion Reg2; subst.
    inversion Hsc; subst.
    apply subcapt__set...
    unfold AtomSet.F.For_all in *.
    intros x xIn.
    specialize (H8 x xIn).
    clear xIn.
    dependent induction H8. {
      apply subcapt__in...
      constructor.
      2: fsetdec.
      intros y yInX.
      rewrite AtomSetFacts.singleton_iff in yInX; subst...
    }
    eapply subcapt__var...
    constructor...
    unfold AtomSet.F.For_all in *.
    intros y yIn.
    apply H8...
  }
Qed.

Check (exp_abs (typ_capt cset_universal typ_top) 0).
Check (typ_arrow (typ_capt cset_universal typ_top)
                 (typ_capt (cset_set {} (NatSet.F.singleton 0)) typ_top)).

Ltac hint := trivial.
Ltac hint ::=
  eauto.
Ltac fnset_mem_dec :=
  symmetry; rewrite <- NatSetFacts.mem_iff; fsetdec.

Set Nested Proofs Allowed.
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

Ltac cset_eq_dec :=
  apply cset_eq_injectivity; [try fsetdec | try fnsetdec].

Ltac replace_if_cond_with0 val :=
  match goal with
  | _ :_ |- context[if ?c then _ else _] =>
    replace c with val
  end.

Ltac replace_if_cond_with_by val tac :=
  match goal with
  | _ :_ |- context[if ?c then _ else _] =>
    replace c with val by tac
  end.

Tactic Notation "replace_if_cond_with" constr(tm) :=
  replace_if_cond_with0 tm.

Tactic Notation "replace_if_cond_with" constr(tm) "by" tactic(tac) :=
  replace_if_cond_with_by tm tac.

Ltac replace_if_cond_with_left :=
  let e := fresh "e" in
  let Eq := fresh "Eq" in
  let P := fresh "P" in
  match goal with
  |- context[if ?c then _ else _] =>
  assert (exists v, c = left v) as Eq; [
    destruct c as [P | P];
    (contradiction ||
     inversion P;
     eexists;
     reflexivity) |
    destruct Eq as [e Eq];
    rewrite Eq;
    clear Eq;
    clear e
  ]
  end.

Ltac simpl_hammer :=
  repeat (unfold open_tt, open_tpt, open_te, open_ee, open_ct, open_cpt, open_cset,
          binds
          ; simpl).

(* Ltac clear_frees := *)
(*   repeat match goal with *)
(*          | H : _ `notin` _ |- _ => *)
(*            clear H *)
(*          end. *)

(* Hint Extern 10 (AtomSet.F.Subset _ _) => *)
(* idtac "go fsetdec go" ; *)
(* (* NOTE: "free" hypothesis are unlikely to help with subsets and they can cause fsetdec to hang *) *)
(* try solve [clear_frees; simpl_env in *; fsetdec] *)
(* : core. *)

Fixpoint dom_typ (E : list (atom * binding)) : atoms :=
  match E with
  | nil => AtomSet.F.empty
  | (x, bind_typ _) :: E' => AtomSet.F.union (singleton x) (dom_typ E')
  | (x, bind_sub _) :: E' => (dom_typ E')
  end.

Ltac prepare_for_fsetdec ::=
  clear_frees; simpl_env in *; simpl dom_typ in *.

Lemma dom_typ_subsets_dom : forall E,
  AtomSet.F.Subset (dom_typ E) (dom E).
Proof.
  induction E.
  - simpl_hammer; fsetdec.
  - simpl_hammer.
    destruct a as [a b].
    destruct b; fsetdec.
Qed.

Lemma allbound_typ_if : forall E A,
  ok E ->
  AtomSet.F.Subset A (dom_typ E) ->
  allbound_typ E A.
Proof.
  intros.
  unfold allbound_typ.
  generalize dependent A.
  induction E; intros.
  - simpl dom_typ in *.
    assert (x `in` {}) by fsetdec.
    rewrite AtomSetFacts.empty_iff in H2.
    contradiction.
  - simpl dom_typ in *.
    destruct a.
    destruct b.
    + simpl_hammer.
      destruct (x == a).
      * exfalso.
        inversion H; subst.
        pose proof (dom_typ_subsets_dom E).
        assert (a `in` dom E) as P by fsetdec.
        apply (H6 P).
      * inversion H; subst.
        apply IHE with (A := A); trivial.
    + simpl_hammer.
      destruct (x == a).
      * eauto.
      * inversion H; subst.
        assert (x `in` dom_typ E) by fsetdec.
        apply IHE with (A := dom_typ E); eauto.
Qed.

Lemma mono_id_types : forall E,
  wf_env E ->
  typing E
         (exp_abs (typ_capt cset_universal typ_top) 0)
         (typ_capt {}C
                   (typ_arrow (typ_capt cset_universal typ_top)
                              (typ_capt (cset_set {} (NatSet.F.singleton 0)) typ_top)))
.
Proof with eauto.
  intros.
  pick fresh x and apply typing_abs...
  - simpl_hammer.
    (* Also works, but does too much: *)
    (* compute. *)
    replace_if_cond_with true by fnset_mem_dec.
    set (c := (cset_set _ _)).
    replace c with (cset_fvar x) by cset_eq_dec.
    apply wf_typ_capt...
    eapply wf_concrete_cset...
    apply allbound_typ_if...
  - simpl_hammer.
    replace_if_cond_with true by fnset_mem_dec.
    replace (cset_set (singleton x `union` {})
                      (NatSet.F.union {}N (NatSet.F.remove 0 (NatSet.F.singleton 0))))
      with (cset_fvar x)
      by cset_eq_dec.
    apply typing_var with (C := cset_universal).
    + econstructor...
    + simpl_hammer.
      replace_if_cond_with_left...
Qed.

Lemma id_types : forall E,
  wf_env E ->
  typing E
         (exp_tabs (typ_capt cset_universal typ_top)
                   (exp_abs (typ_capt cset_universal typ_top)
                            0))
         (typ_capt {}C
                   (typ_all (typ_capt cset_universal typ_top)
                            (typ_capt {}C
                                      (typ_arrow (typ_capt cset_universal typ_top)
                                                 (typ_capt (cset_set {} (NatSet.F.singleton 0))
                                                           typ_top)))))
.
Proof with eauto.
  intros.
  pick fresh X and apply typing_tabs...
  - simpl_hammer.
    apply wf_typ_capt... {
      eapply wf_concrete_cset...
      apply allbound_typ_if...
    }
    (* just copied from above... *)
    pick fresh x and apply wf_typ_arrow...
    simpl_hammer.
    replace_if_cond_with true by fnset_mem_dec.
    replace (cset_set (singleton x `union` {})
                      (NatSet.F.union {}N (NatSet.F.remove 0 (NatSet.F.singleton 0))))
      with (cset_fvar x)
      by cset_eq_dec.
    apply wf_typ_capt...
    eapply wf_concrete_cset...
    apply allbound_typ_if...
  - simpl_hammer.
    apply mono_id_types.
    econstructor...
Qed.

Lemma id_app_types : forall x,
  typing [(x, (bind_typ (typ_capt {}C typ_top)))]
         (exp_app (exp_tapp (exp_tabs (typ_capt cset_universal typ_top)
                             (exp_abs (typ_capt cset_universal typ_top)
                                      0))
                            (typ_capt {}C typ_top))
                  x)
         (typ_capt x typ_top)
.
Proof with eauto using allbound_typ_if.
  intros.
  assert (wf_env [(x, (bind_typ (typ_capt {}C typ_top)))]). {
    constructor...
    constructor...
    constructor...
  }
  epose (T1 := (open_ct _ _)).
  replace (typ_capt x typ_top) with T1.
  unfold T1.
  eapply typing_app.
  - epose (T2 := (open_tt _ _)).
    replace (typ_capt _ (typ_arrow _ _)) with T2; unfold T2.
    eapply typing_tapp.
    + apply id_types...
    + econstructor...
      constructor...
      autounfold.
      constructor...
    + reflexivity.
  - apply typing_var with (C := {}C)...
  - simpl_hammer.
    constructor...
    constructor...
    autounfold.
    constructor...
  - constructor...
    autounfold; constructor...
  - cbn in T1.
    subst T1.
    f_equal.
    cbv [open_cset cset_references_bvar_dec].
    replace_if_cond_with true.
    2: {
      match goal with
      | |- true = _ => symmetry
      | |- false = _ => symmetry
      | |- _ => idtac
      end.
      match goal with
      | |- NatSet.F.mem _ _ = true => rewrite <- NatSetFacts.mem_iff; fnsetdec
      | |- NatSet.F.mem _ _ = false => rewrite <- NatSetFacts.not_mem_iff; fnset_mem_dec
      end.
    }
    cbn.
    cset_eq_dec.
Qed.

Definition CC_List (c : captureset) (t : typ) :=
  (typ_capt
     c
     (typ_all
        (typ_capt cset_universal typ_top)
        (typ_capt
           c
           (typ_arrow
              (typ_capt
                 {}C
                 (typ_arrow
                    t
                    (typ_capt
                       {}C
                       (typ_arrow 0 0))))
              (typ_capt
                 {}C
                 (typ_arrow 0 0))))))
.

Definition CC_empty :=
  (exp_tabs
     (typ_capt cset_universal typ_top)
     (exp_tabs
      (typ_capt cset_universal typ_top)
      (exp_abs
         (typ_capt
            {}C
            (typ_arrow
               1
               (typ_capt
                  {}C
                  (typ_arrow 0 0))))
         (exp_abs 0 0)))).

Definition CC_cons :=
  (** forall T <: {*} Top,*)
  (exp_tabs
     (typ_capt cset_universal typ_top)
     (exp_abs
        (** lst : {*} List [T] *)
        (CC_List cset_universal
                 (typ_bvar 1)) (* NOTE: List itself has a type binder, so we put 0+1 *)
        (exp_abs
          (* e : T *)
          (typ_bvar 0)
          (** body of List *)
          (exp_tabs
            (** forall A*)
            (typ_capt cset_universal typ_top)
            (exp_abs
              (* f : T, A -> A *)
              (typ_capt
                  {}C
                  (typ_arrow
                    1
                    (typ_capt
                        {}C
                        (typ_arrow (typ_bvar 0)
                                   (typ_bvar 0)))))
              (exp_abs
                (* start : A*)
                (typ_bvar 0)
                (* (f e (lst f start)) *)
                (exp_app
                  (* (f e) *)
                  (exp_app (exp_bvar 1) (exp_bvar 2))
                  (exp_app
                    (* (lst f) *)
                     (exp_app
                        (exp_tapp (exp_bvar 3) (typ_bvar 0))
                        (exp_bvar 1))
                    (exp_bvar 0))))))))).

Definition CC_map :=
  (exp_tabs
    (typ_capt cset_universal typ_top) (** forall T <: {*} Top*)
    (exp_tabs
      (typ_capt cset_universal typ_top) (** forall A <: {*} Top, *)
      (exp_abs
        (CC_List cset_universal 1) (** lst : {*} List [T] *)
        (exp_abs
          (typ_capt {}C (typ_arrow (typ_bvar 1) (typ_bvar 0))) (** f : {}C T -> A *)
          (exp_app
            (exp_app (exp_bvar 1)
              (** \e \a -> (cons (f elem) accum) *)
              (exp_abs 1
                (exp_abs (typ_bvar 0)
                  (exp_app
                    (exp_app (exp_tapp CC_cons 1) (exp_app (exp_bvar 2) (exp_bvar 1)))
                    (exp_bvar 0)))))
            (exp_tapp CC_empty 1)))))).

(* ---------------------------------------------------------------------- *)
(** ** Position Markers *)

(** [ltac_Mark] and [ltac_mark] are dummy definitions used as sentinel
    by tactics, to mark a certain position in the context or in the goal. *)

Inductive ltac_Mark : Type :=
  | ltac_mark : ltac_Mark.

(** [gen_until_mark] repeats [generalize] on hypotheses from the
    context, starting from the bottom and stopping as soon as reaching
    an hypothesis of type [Mark]. If fails if [Mark] does not
    appear in the context. *)

Ltac gen_until_mark :=
  match goal with H: ?T |- _ =>
  match T with
  | ltac_Mark => clear H
  | _ => generalize H; clear H; gen_until_mark
  end end.

(* ---------------------------------------------------------------------- *)
(** ** Rewriting lemmas *)

Lemma wf_typ_closed_tt_rec : forall k x E T,
  wf_typ_in E T ->
  (open_tt_rec k x T) = T.
Proof.
  intros.
  erewrite <- open_tt_rec_type; eauto using type_from_wf_typ.
Qed.

Lemma wf_typ_closed_ct_rec : forall k D E T,
  wf_typ_in E T ->
  (open_ct_rec k D T) = T.
Proof.
  intros.
  erewrite <- open_ct_rec_type; eauto using type_from_wf_typ.
Qed.

Lemma wf_cset_closed_cset : forall k D E C,
  wf_cset_in E C ->
  (open_cset k D C) = C.
Proof.
  intros.
  erewrite <- open_cset_capt; eauto using capt_from_wf_cset.
Qed.

Lemma empty_closed_cset : forall k D,
  (open_cset k D {}C) = {}C.
Proof.
  intros.
  erewrite <- open_cset_capt.
  reflexivity.
  constructor.
Qed.

Lemma if_blatantly_true : forall A k (t s : A),
  (if k === k then t else s) = t.
Proof.
  intros.
  destruct_if; easy.
Qed.

Lemma if_blatantly_false : forall A k j (t s : A),
  k <> j ->
  (if k === j then t else s) = s.
Proof.
  intros.
  destruct_if; easy.
Qed.

Lemma empty_union_idempotent : forall C,
  {} `union` C = C.
Proof.
  intros.
  fsetdec.
Qed.

Lemma idempotent_union_empty : forall C,
  C `union` {} = C.
Proof.
  intros.
  fsetdec.
Qed.

Create HintDb typ.

Hint Rewrite if_blatantly_true : typ.
Hint Rewrite if_blatantly_false using congruence : typ.

Hint Rewrite empty_closed_cset : typ.
Hint Rewrite empty_union_idempotent : typ.
Hint Rewrite idempotent_union_empty : typ.

Ltac cbn_for_open :=
      cbn [
          open_ee open_te open_ct open_tt
                  open_ct_rec open_cpt_rec open_ee_rec open_te_rec open_tt_rec open_tpt_rec
        ].

Ltac cleanup :=
    cbn_for_open;
    cbn [free_for_cv] in *;
    simpl_env in *;
    cbn [fv_tt fv_et fv_tpt fv_ept fv_cset empty_cset] in *.

Ltac arw :=
  try (erewrite wf_typ_closed_tt_rec; [|progress eauto]);
  try (erewrite wf_typ_closed_ct_rec; [|progress eauto]);
  autorewrite with typ in *.

Ltac full_cleanup :=
  repeat progress (arw ; cleanup).

(* ---------------------------------------------------------------------- *)
(** ** Well-formedness trivia *)

Lemma UniTop_wf : forall E Ap Am,
  wf_typ E Ap Am (typ_capt cset_universal typ_top).
Proof.
  intros.
  constructor.
  - constructor.
  - constructor.
Qed.

Lemma pretyp_capturing_empty_wf_if : forall E Ap Am T,
  wf_pretyp E Ap Am T ->
  wf_typ E Ap Am (typ_capt {}C T).
Proof.
  intros.
  constructor.
  - constructor.
    + unfold allbound_typ.
      intros. exfalso; fsetdec.
    + fsetdec.
  - easy.
Qed.

Lemma empty_cset_wf : forall E Ap,
    wf_cset E Ap {}C.
Proof.
  intros.
  constructor.
  2: fsetdec.
  intros ? ?.
  exfalso; fsetdec.
Qed.

(* ---------------------------------------------------------------------- *)
(** ** Other trivia *)

Lemma empty_subcapts_all : forall E C,
  wf_cset_in E C ->
  subcapt E {}C C.
Proof with eauto.
  intros.
  { destruct C.
    - constructor...
      constructor.
      2: fsetdec.
      unfold allbound_typ; intros; exfalso; fsetdec.
    - inversion H; subst.
      constructor...
      constructor...
      unfold allbound_typ; intros; exfalso; fsetdec.
      intros ? ?; exfalso; fsetdec.
  }
Qed.

(* ---------------------------------------------------------------------- *)
(** ** Glorious taktiks *)

Ltac goal_env :=
  let pass_if_env := fun E => match type of E with env => E end in
  match goal with
  | |- _ ?E => pass_if_env E
  | |- _ ?E _ => pass_if_env E
  | |- _ ?E _ _ => pass_if_env E
  | |- _ ?E _ _ _ => pass_if_env E
  end.

Ltac assert_wf_env :=
  let E := goal_env in assert (wf_env E).

Ltac replace_type_with tp :=
  match goal with
  | |- typing _ _ ?T =>
    replace T with tp
  end;
  unfold tp.

Ltac assert_typing_with tp :=
  match goal with
  | |- typing ?E ?t _ =>
    assert (typing E t tp); [unfold tp|]
  end.

Ltac promise_wf_typ H T1 :=
  match goal with
  | |- typing ?E _ _ =>
    enough (wf_typ_in E T1) as H; [try unfold T1 in H|try unfold T1]
  | |- sub ?E _ _ =>
    enough (wf_typ_in E T1) as H; [try unfold T1 in H|try unfold T1]
  end.

Ltac extract_binding_uniqueness_rec x E :=
  lazymatch E with
  | [(?y, _)] =>
    assert (x <> y) by notin_solve
  | [(?y, _)] ++ ?G =>
    assert (x <> y) by notin_solve; extract_binding_uniqueness_rec x G
  end.

Ltac extract_binding_uniqueness :=
  lazymatch goal_env with
  | empty => idtac "Nothing to extract, env empty"
  | [(?x, _)] => idtac "Nothing to extract, single binding"
  | [(?x, _)] ++ ?E =>
    extract_binding_uniqueness_rec x E
  | [(?x, _)] ++ ?E =>
    extract_binding_uniqueness_rec x E
  end.

Ltac binds_dec :=
  cbv [binds get]; simpl;
    repeat first [ reflexivity | destruct_if; try congruence].

Ltac wf_typ_inversion_intros H :=
  match goal with
  | |- _ -> _ =>
    (let H' := fresh H in intro H'); wf_typ_inversion_intros H
  | |- _ => idtac
  end.

Ltac wf_typ_inversion' H :=
  pose (ltac_mark); wf_typ_inversion H; gen_until_mark; wf_typ_inversion_intros H.

Ltac wf_cleanup :=
  try apply pretyp_capturing_empty_wf_if;
  try apply UniTop_wf.

Tactic Notation "wf_step" ident(id) "with" constr(H) :=
  wf_cleanup;
  pick fresh id and apply H; simpl_env; [|extract_binding_uniqueness];
  wf_cleanup.

Hint Resolve allbound_typ_if : core.

(* ---------------------------------------------------------------------- *)
(** ** Clean notation *)

Notation "C |> T" := (typ_capt C T) (at level 80).
Notation "'UniTop'" := (typ_capt cset_universal typ_top).

Lemma nil_types : forall C,
  wf_cset_in empty C ->
  typing empty CC_empty (typ_capt {}C (typ_all (typ_capt cset_universal typ_top)
                                               (CC_List C 1))).
Proof with eauto.
  intros.
  unfold CC_empty, CC_List.

  epose (T0 := (typ_capt ?[T0__C] (typ_all ?[T0__A] ?[T0__R]))).
  promise_wf_typ T0__Wf T0.
  assert_typing_with T0. {
    wf_typ_inversion' T0__Wf.
    pick fresh Y and apply typing_tabs; simpl_env...
    assert_wf_env. {
      constructor...
    }
    full_cleanup.

    epose (T1 := (typ_capt ?[T1__C] (typ_all ?[T1__A] ?[T1__R]))).
    promise_wf_typ T1__Wf T1.
    assert_typing_with T1. {
      wf_typ_inversion' T1__Wf.
      pick fresh X and apply typing_tabs...
      { assert_wf_env. {
          constructor...
        }

        full_cleanup.

        epose (T2 := (typ_capt ?[T2__C] (typ_arrow ?[T2__A] ?[T2__R]))).
        promise_wf_typ T2__Wf T2.
        assert_typing_with T2. {
          wf_typ_inversion' T2__Wf.
          pick fresh y and apply typing_abs...
          { assert_wf_env. {
              constructor...
            }
            full_cleanup.

            epose (T3 := (typ_capt ?[T3__C] (typ_arrow ?[T3__A] ?[T3__R]))).
            promise_wf_typ T3__Wf T3.
            assert_typing_with T3. {
              wf_typ_inversion' T3__Wf.
              pick fresh z and apply typing_abs...
              { full_cleanup.
                assert_wf_env. {
                  constructor...
                }
                extract_binding_uniqueness.

                epose (T4 := _).
                replace_type_with T4. {
                  apply typing_var_tvar with (X := X). trivial.
                  binds_dec.
                }
                [T3__R] : exact X.
                reflexivity.
              }
            }
            { full_cleanup.
              replace_type_with T3. easy.
              [T2__R] : exact (typ_capt {}C (typ_arrow X X)).
              now full_cleanup.
            }
            { full_cleanup.
              constructor.
              - constructor; simpl_env...
              - assert (y <> X) by notin_solve.
                pick fresh y' and apply wf_typ_arrow...
                + extract_binding_uniqueness; cleanup;
                  econstructor; binds_dec.
            }
          }
        }
        { [T1__R] : exact (
                      typ_capt {}C
                              (typ_arrow (typ_capt {}C (typ_arrow Y (typ_capt {}C (typ_arrow 0 0))))
                                          (typ_capt {}C (typ_arrow 0 0)))
                    ).
          replace_type_with T2. easy.
          full_cleanup.
          reflexivity.
        }
        { wf_step y' with wf_typ_arrow.
          + wf_step y'' with wf_typ_arrow. {
              econstructor; binds_dec.
            }
            full_cleanup.
            wf_step y''' with wf_typ_arrow;
              cleanup; econstructor; binds_dec.
          + full_cleanup.
            wf_step y'' with wf_typ_arrow;
              cleanup; econstructor; binds_dec.
        }
      }
    }
    { [T0__R] :
        exact (
            {}C |> typ_all UniTop
              ({}C |> typ_arrow ({}C |> typ_arrow 1 ({}C |> typ_arrow 0 0)) ({}C |> typ_arrow 0 0))
          ).
      replace_type_with T1. easy.
      full_cleanup.
      reflexivity.
    }
    { full_cleanup.
      wf_step X with wf_typ_all...
      full_cleanup.
      wf_step y with wf_typ_arrow.
      + wf_step y' with wf_typ_arrow. {
          econstructor; binds_dec.
        }
        full_cleanup.
        wf_step y'' with wf_typ_arrow;
          cleanup; econstructor; binds_dec.
      + full_cleanup.
        wf_step y'' with wf_typ_arrow;
          cleanup; econstructor; binds_dec.
    }
  }
  2: {
    full_cleanup.
    wf_step Y with wf_typ_all.
    full_cleanup.
    wf_step X with wf_typ_all...
    full_cleanup.
    wf_step y with wf_typ_arrow.
    + wf_step y' with wf_typ_arrow. {
        econstructor; binds_dec.
      }
      full_cleanup.
      wf_step y'' with wf_typ_arrow;
        cleanup; econstructor; binds_dec.
    + full_cleanup.
      wf_step y'' with wf_typ_arrow;
        cleanup; econstructor; binds_dec.
  }
  full_cleanup.
  eapply typing_sub.
  apply H0.
  unfold T0.

  lazymatch goal with
  | |- sub ?E ?S ?U =>
    promise_wf_typ S2__Wf S; [
      promise_wf_typ T2__Wf U
    | ]
  end.

  apply sub_capt.
  1: apply empty_subcapts_all; apply empty_cset_wf.

  wf_typ_inversion' S2__Wf.
  wf_typ_inversion' T2__Wf.
  pick fresh Y and apply sub_all; simpl_env... {
    apply sub_capt...
  }
  { full_cleanup.
    apply sub_capt. {
      apply empty_subcapts_all.
      match goal with
      | |- wf_cset_in ?E _ =>
        change E with (empty ++ E ++ empty)
      end.
      eapply wf_cset_weakening; simpl_env...
    }
    Ltac cbn_for_open_in_star :=
      cbn [
          open_ee open_te open_ct open_tt
                  open_ct_rec open_cpt_rec open_ee_rec open_te_rec open_tt_rec open_tpt_rec
        ] in *.
    specialize (T2__Wf4 Y ltac:(notin_solve)).

    cbn_for_open_in_star.
    full_cleanup.
    wf_typ_inversion' T2__Wf4.
    pick fresh X and apply sub_all. {
      apply sub_capt...
      repeat constructor.
      simpl_env; fsetdec.
    }
    5: {
      full_cleanup.
      apply sub_capt. {
        apply empty_subcapts_all.
        match goal with
        | |- wf_cset_in ?E _ =>
          change E with (empty ++ E ++ empty)
        end.
        eapply wf_cset_weakening; simpl_env...
      }
      let e := goal_env in
      apply sub_pre_reflexivity with (Ap := dom e) (Am := dom e); simpl_env...
      { constructor...
        constructor...
      }

      specialize (T2__Wf9 X ltac:(notin_solve)).
      cbn_for_open_in_star; full_cleanup.
      wf_typ_inversion' T2__Wf9.
      set (foo := (typ_arrow ({}C |> typ_arrow Y ({}C |> typ_arrow X X)) ({}C |> typ_arrow X X))) in *.
      do 2 rewrite_nil_concat.
      eapply wf_pretyp_weakening; simpl_env.
      apply T2__Wf11.
      all : eauto.
    }
    1,2: repeat constructor.
    1,2: full_cleanup.
    - constructor.
      { match goal with
        | |- wf_cset ?E _ _ =>
          change E with (empty ++ E ++ empty)
        end.
        eapply wf_cset_weakening; simpl_env.
        all : eauto.
      }
      wf_step y' with wf_typ_arrow.
      + wf_step y'' with wf_typ_arrow. {
          econstructor; binds_dec.
        }
        full_cleanup.
        wf_step y''' with wf_typ_arrow;
          cleanup; econstructor; binds_dec.
      + full_cleanup.
        wf_step y'' with wf_typ_arrow;
          cleanup; econstructor; binds_dec.
    - wf_step y' with wf_typ_arrow.
      + wf_step y'' with wf_typ_arrow. {
          econstructor; binds_dec.
        }
        full_cleanup.
        wf_step y''' with wf_typ_arrow;
          cleanup; econstructor; binds_dec.
      + full_cleanup.
        wf_step y'' with wf_typ_arrow. {
          econstructor; binds_dec.
        }
        full_cleanup.
        econstructor; binds_dec.
  }
  { wf_cleanup.
    wf_step Y with wf_typ_all.
    full_cleanup.
    constructor. {
      match goal with
      | |- wf_cset ?E _ _ =>
        change E with (empty ++ E ++ empty)
      end.
      eapply wf_cset_weakening; simpl_env.
      all : eauto.
    }
    wf_step X with wf_typ_all.
    full_cleanup.
    constructor. {
      match goal with
      | |- wf_cset ?E _ _ =>
        change E with (empty ++ E ++ empty)
      end.
      eapply wf_cset_weakening; simpl_env.
      all : eauto.
    }
    wf_step y' with wf_typ_arrow.
    - wf_step y'' with wf_typ_arrow. {
        econstructor; binds_dec.
      }
      full_cleanup.
      wf_step y''' with wf_typ_arrow;
        cleanup; econstructor; binds_dec.
    - full_cleanup.
      wf_step y'' with wf_typ_arrow;
        cleanup; econstructor; binds_dec.
  }
  { wf_cleanup.
    wf_step Y with wf_typ_all.
    full_cleanup.
    wf_step X with wf_typ_all.
    full_cleanup.
    wf_step y' with wf_typ_arrow.
    - wf_step y'' with wf_typ_arrow. {
        econstructor; binds_dec.
      }
      full_cleanup.
      wf_step y''' with wf_typ_arrow;
        cleanup; econstructor; binds_dec.
    - full_cleanup.
      wf_step y'' with wf_typ_arrow;
        cleanup; econstructor; binds_dec.
  }
Qed.

Lemma empty_cset_union_idempotent : forall C,
    cset_union {}C C = C.
Proof.
  intros.
  unfold cset_union.
  destruct C; simpl.
  - reflexivity.
  - cset_eq_dec.
Qed.

Lemma cset_union_empty_idempotent : forall C,
    cset_union C {}C = C.
Proof.
  intros.
  unfold cset_union.
  destruct C; simpl.
  - reflexivity.
  - cset_eq_dec.
Qed.

Notation "{*}" := cset_universal.

Lemma universal_closed_cset : forall k D,
  (open_cset k D {*}) = {*}.
Proof.
  intros.
  erewrite <- open_cset_capt.
  reflexivity.
  constructor.
Qed.

Hint Rewrite empty_cset_union_idempotent : typ.
Hint Rewrite cset_union_empty_idempotent : typ.
Hint Rewrite universal_closed_cset : typ.

Ltac assert_typ_eq T id :=
match goal with
| |- typing _ _ ?T' =>
  assert (T = T') as id
end.

Lemma wf_pretyp_from_binds_typ : forall x E C V,
  wf_env E ->
  binds x (bind_typ (C |> V)) E ->
  wf_pretyp_in E V.
Proof with auto.
  intros.
  apply wf_typ_from_binds_typ in H0...
  wf_typ_inversion H0...
Qed.

Lemma binds_in_dom_typ : forall x T E,
  binds x (bind_typ T) E ->
  x `in` dom_typ E.
Proof.
  intros.
  induction E.
  - inversion H.
  - destruct a as (y & b).
    cbv [binds get] in H.
    destruct (x == y) eqn:EQ.
    + inversion H. subst.
      unfold dom_typ.
      fsetdec.
    + enough (x `in` dom_typ E) by (unfold dom_typ; destruct b; fsetdec).
      apply IHE.
      auto.
Qed.

Lemma wf_cset_from_binds_typ : forall T x E,
  wf_env E ->
  binds x (bind_typ T) E ->
  wf_cset_in E x.
Proof with auto.
  intros.
  apply binds_in_dom_typ in H0 as ?.
  pose proof (dom_typ_subsets_dom E).
  constructor...
Qed.

Ltac wf_cleanup ::=
  try apply pretyp_capturing_empty_wf_if;
  try apply wf_universal_cset;
  try apply wf_typ_all;
  try apply UniTop_wf.

Ltac clear_until_mark :=
  match goal with H: ?T |- _ =>
  match T with
  | ltac_Mark => clear H
  | _ => clear H; clear_until_mark
  end end.

Ltac extract_binding_uniqueness_rec x E ::=
  lazymatch E with
  | [(?y, _)] =>
    assert (x <> y) by assumption
  | [(?y, _)] ++ ?G =>
    assert (x <> y) by assumption; extract_binding_uniqueness_rec x G
  end.

Ltac extract_binding_uniqueness_intros :=
  match goal with
  | |- _ -> _ =>
    let F := fresh "F" in intro F;
    extract_binding_uniqueness_intros
  | _ => idtac
  end.

Ltac extract_binding_uniqueness ::=
  pose (ltac_mark);
  notin_simpl;
  pose (ltac_mark);
  lazymatch goal_env with
  | empty => idtac "Nothing to extract, env empty"
  | [(?x, _)] => idtac "Nothing to extract, single binding"
  | [(?x, _)] ++ ?E =>
    extract_binding_uniqueness_rec x E
  | [(?x, _)] ++ ?E =>
    extract_binding_uniqueness_rec x E
  end;
  gen_until_mark;
  clear_until_mark;
  extract_binding_uniqueness_intros.

Notation "[$ a ]" := (singleton a).
Notation "[. n ]" := (NatSet.F.singleton n).

Lemma union_empty_idempotent : forall xs,
    xs `union` {} = xs.
Proof. intros. fsetdec. Qed.

Lemma funion_empty_idempotent : forall xs,
    NatSet.F.union xs {}N = xs.
Proof. intros. fnsetdec. Qed.

Lemma empty_funion_idempotent : forall xs,
    NatSet.F.union {}N xs = xs.
Proof. intros. fnsetdec. Qed.

Lemma cset_locally_closed : forall k ys xs,
    (open_cset k ys (cset_set xs {}N)) = (cset_set xs {}N).
Proof.
  intros.
  unfold open_cset.
  destruct_if.
  - unfold cset_references_bvar_dec in Heqb.
    rewrite_set_facts_in Heqb.
    exfalso; fnsetdec.
  - reflexivity.
Qed.

Lemma NatSet_mem_singleton : forall A k (t s : A),
  (if NatSet.F.mem k [.k] then t else s) = t.
Proof.
  intros.
  destruct_if.
  - reflexivity.
  - rewrite_set_facts_in Heqb.
    exfalso. fnsetdec.
Qed.

Lemma NatSet_remove_singleton : forall k,
    NatSet.F.remove k [.k] = {}N.
Proof.
  intros.
  fnsetdec.
Qed.

Hint Rewrite cset_locally_closed : typ.

Hint Rewrite union_empty_idempotent : typ.
Hint Rewrite funion_empty_idempotent : typ.
Hint Rewrite empty_funion_idempotent : typ.

Hint Rewrite NatSet_mem_singleton : typ.
Hint Rewrite NatSet_remove_singleton : typ.

Lemma wf_cset_from_binds_typ' : forall E Ap x T,
    binds x (bind_typ T) E ->
    x `in` Ap ->
    wf_cset E Ap x.
Proof.
  intros.
  constructor.
  2: fsetdec.
  unfold allbound_typ.
  intros y In.
  rewrite AtomSetFacts.singleton_iff in In.
  subst.
  eauto.
Qed.

Ltac epose_open_ct :=
  let T := fresh "T1" in
  let Tt := fresh T "__T" in
  let Tc := fresh T "__C" in
  let Twf := fresh T "__Wf" in
  epose (T := (open_ct ?[Tt] ?[Tc]));
  promise_wf_typ Twf T.

Ltac goal_cleanup :=
  repeat progress (cbn_for_open; autorewrite with typ).

Ltac by_asserted_typing :=
lazymatch goal with
| H : typing _ ?t ?S |- typing _ ?t ?T =>
  let EQ := fresh "TMP" "EQ" in
  assert_typ_eq S EQ; [
    unfold S;
    goal_cleanup;
    reflexivity
  | rewrite EQ in H;
    assumption
  ]
end.

Hint Extern 1 (binds _ _ _ _) => binds_dec : core.

Ltac cset_prep :=
  cbv [cset_union open_cset];
  simpl;
  goal_cleanup.

Lemma cons_types: exists T,
  typing empty CC_cons T.
Proof with eauto.
  eexists ?[T0].

  unfold CC_cons.

  epose (T1 := ?[T1__C] |> typ_all ?[T1__A] ?[T1__R]).
  promise_wf_typ T1__Wf T1.
  assert_typing_with T1. {
    wf_typ_inversion' T1__Wf.
    pick fresh X and apply typing_tabs; simpl_env...
    assert_wf_env. {
      constructor...
    }
    clear_frees; full_cleanup.
    change (open_tt_rec 0 X (CC_List cset_universal 1))
      with (CC_List cset_universal X).

    clear_frees. full_cleanup.
    epose (T3 := ?[T3__C] |> typ_arrow ?[T3__A] ?[T3__R]).
    promise_wf_typ T3__Wf T3.
    assert_typing_with T3. {
      wf_typ_inversion' T3__Wf.
      pick fresh y and apply typing_abs...
      assert_wf_env. {
        constructor...
      }
      extract_binding_uniqueness.
      full_cleanup.

      epose (T4 := ?[T4__C] |> typ_arrow ?[T4__A] ?[T4__R]).
      promise_wf_typ T4__Wf T4.
      assert_typing_with T4. {
        wf_typ_inversion' T4__Wf.
        pick fresh z and apply typing_abs...
        assert_wf_env. {
          constructor...
        }
        extract_binding_uniqueness.
        full_cleanup.

        epose (T5 := ?[T5__C] |> typ_all ?[T5__A] ?[T5__R]).
        promise_wf_typ T5__Wf T5.
        assert_typing_with T5. {
          wf_typ_inversion' T5__Wf.
          pick fresh X' and apply typing_tabs...
          assert_wf_env. {
            constructor...
          }
          extract_binding_uniqueness.
          full_cleanup.

          epose (T6 := ?[T6__C] |> typ_arrow ?[T6__A] ?[T6__R]).
          promise_wf_typ T6__Wf T6.
          assert_typing_with T6. {
            wf_typ_inversion' T6__Wf.
            pick fresh y' and apply typing_abs...
            extract_binding_uniqueness.
            full_cleanup.
            assert_wf_env. {
              constructor; autounfold; simpl_env; [trivial .. | notin_solve].
            }

            epose (T7 := ?[T7__C] |> typ_arrow ?[T7__A] ?[T7__R]).
            promise_wf_typ T7__Wf T7.
            assert_typing_with T7. {
              wf_typ_inversion' T7__Wf.
              pick fresh z' and apply typing_abs...
              extract_binding_uniqueness.
              full_cleanup.
              assert_wf_env. {
                constructor; autounfold; simpl_env; [trivial .. | notin_solve].
              }

              epose_open_ct.
              assert_typing_with T0. {
                eapply typing_app.
                2: {
                  eapply typing_app.
                  2: {
                    eapply typing_var_tvar...
                  }
                  3: {
                    eapply cv_typ_var; [ binds_dec | trivial |]...
                  }
                  { epose (T8 := (open_ct ?[T8__T] ?[T8__C])).
                    promise_wf_typ T8__Wf T8.
                    assert_typing_with T8. {
                      eapply typing_app.
                      2: {
                        eapply typing_var; [trivial|binds_dec].
                      }
                      3: {
                        apply cv_typ_capt. trivial.

                        eapply (wf_pretyp_from_binds_typ y');
                          [ trivial | binds_dec ].

                        eapply wf_cset_from_binds_typ;
                          [ trivial | binds_dec ].
                      }
                      { epose (T9 := (open_tt ?[T9__T] ?[T9__C])).
                        promise_wf_typ T9__Wf T9.
                        assert_typing_with T9. {
                          eapply typing_tapp. {
                            eapply typing_var;
                              [ trivial | binds_dec ].
                          } {
                            eapply sub_trans_tvar.
                            binds_dec.
                            apply sub_capt.
                            constructor.
                            constructor.
                            constructor.
                            trivial.
                            constructor.
                          }
                        }
                        by_asserted_typing.
                        { goal_cleanup.

                          constructor.
                          1: wf_cleanup.
                          simpl_env.
                          wf_step y'' with wf_typ_arrow.
                          - wf_step y'' with wf_typ_arrow.
                            + econstructor. binds_dec.
                            + goal_cleanup.
                              wf_step z'' with wf_typ_arrow.
                              2: goal_cleanup.
                              1,2: econstructor; binds_dec.
                          - goal_cleanup.
                            clear_frees.
                            wf_step z'' with wf_typ_arrow.
                            2: goal_cleanup.
                            1,2: econstructor; binds_dec.
                        }
                      }
                      apply sub_capt.
                      eapply captures_from_binds...
                      let G := goal_env in
                      apply sub_pre_reflexivity with (Ap := dom G) (Am := dom G).
                      trivial.
                      wf_step y'' with wf_typ_arrow.
                      - econstructor. binds_dec.
                      - goal_cleanup.
                        wf_step z'' with wf_typ_arrow.
                        2: goal_cleanup.
                        1,2: econstructor; binds_dec.
                      - simpl_env; fsetdec.
                      - simpl_env; fsetdec.
                    }
                    by_asserted_typing.
                    goal_cleanup.
                    wf_step z'' with wf_typ_arrow.
                    2: goal_cleanup.
                    1,2: econstructor; binds_dec.
                  }
                  apply sub_refl_tvar;
                    [trivial | econstructor; binds_dec].
                }
                3: {
                  goal_cleanup.
                  eapply cv_typ_var; [binds_dec | assumption |].
                  apply cv_typ_capt.
                  assumption.
                  constructor.
                  constructor.
                }
                { epose_open_ct.
                  assert_typing_with T2.
                  eapply typing_app.
                  eapply typing_var ; [assumption | binds_dec].
                  eapply typing_var_tvar ; [assumption | binds_dec].
                  apply sub_refl_tvar; [assumption | econstructor; binds_dec].
                  {
                    eapply cv_typ_var; [binds_dec | assumption |].
                    apply cv_typ_capt.
                    assumption.
                    constructor.
                    constructor.
                  }
                  by_asserted_typing.
                  { goal_cleanup.
                    wf_step z'' with wf_typ_arrow.
                    2: goal_cleanup.
                    1,2: econstructor; binds_dec.
                  }
                }
                { goal_cleanup.
                  apply sub_refl_tvar;
                    [trivial | econstructor; binds_dec].
                }
              }
              { [T7__R]: exact X'.
                by_asserted_typing.
              }
              { goal_cleanup.
                econstructor; binds_dec.
              }
            }
            { assert (T7 = (open_ct ?T6__R y')) as HA. {
                unfold T7.

                [T6__R] :
                  exact (
                      (cset_union z (cset_union y 0))
                        |> typ_arrow X' X').

                goal_cleanup.
                cbv [cset_union open_cset cset_references_bvar_dec cset_remove_bvar].
                simpl.
                goal_cleanup.
                f_equal.
                cset_eq_dec.
              }
              rewrite <- HA.
              assumption.
            }
            { goal_cleanup.
              cbv [free_for_cv].
              constructor.
              - repeat apply wf_cset_union.

                5: apply empty_cset_wf.
                all : eapply wf_cset_from_binds_typ; [assumption | binds_dec].
              - goal_cleanup.
                wf_step z'' with wf_typ_arrow.
                2: goal_cleanup.
                1,2: econstructor; binds_dec.
            }
          }
          { assert (T6 = (open_tt ?T5__R X')) as HA. {
              unfold T6.
              cbv [free_for_cv].
              goal_cleanup.
              [T5__R]:
                exact
                  (cset_union
                     z y
                     |> typ_arrow ({}C |> typ_arrow X ({}C |> typ_arrow 0 0))
                     (cset_union z (cset_union y 0) |> typ_arrow 0 0)).
              goal_cleanup.
              reflexivity.
            }
            rewrite <- HA.
            assumption.
          }
          { cbv [free_for_cv].
            goal_cleanup.
            constructor.
            - apply wf_cset_union.
              all : eapply wf_cset_from_binds_typ; [assumption | binds_dec].
            - wf_step y' with wf_typ_arrow.
              + wf_step z' with wf_typ_arrow.
                * econstructor; binds_dec.
                * goal_cleanup.
                  wf_step z'' with wf_typ_arrow.
                  2: goal_cleanup.
                  1,2: econstructor; binds_dec.
              + goal_cleanup.
                replace (open_cset 0 y' (cset_union z (cset_union y 0)))
                  with (cset_union z (cset_union y y')).
                2: {
                  cbv [cset_union open_cset].
                  simpl.
                  goal_cleanup.
                  cset_eq_dec.
                }
                constructor.
                * repeat apply wf_cset_union.
                  all : eapply wf_cset_from_binds_typ'; [ binds_dec | fsetdec].
                * wf_step z'' with wf_typ_arrow.
                  2: goal_cleanup.
                  1,2: econstructor; binds_dec.
          }
        }
        { assert (T5 = (open_ct ?T4__R z)). {
            unfold T5.
            goal_cleanup.
            cbv [free_for_cv].
            goal_cleanup.
            [T4__R]:
              exact
                (cset_union
                   0 y
                   |> typ_all UniTop
                   (cset_union
                      0 y |>
                      typ_arrow ({}C |> typ_arrow X ({}C |> typ_arrow 0 0))
                      (cset_union 1 (cset_union y 0) |> typ_arrow 0 0))).
            goal_cleanup.
            replace (open_cset 0 z (cset_union 0 y))
              with (cset_union z y).
            2: {
              cbv [cset_union open_cset].
              simpl.
              goal_cleanup.
              cset_eq_dec.
            }
            replace (open_cset 1 z (cset_union 1 (cset_union y 0)))
              with (cset_union z (cset_union y 0)).
            2: {
              cbv [cset_union open_cset].
              simpl.
              goal_cleanup.
              destruct_if.
              - assert (~ NatSet.F.In 1 [.0]) by fnsetdec.
                cset_eq_dec.
              - rewrite_set_facts_in Heqb.
                exfalso; fnsetdec.
            }
            reflexivity.
          }
          rewrite <- H3.
          assumption.
        }
        { cbv [free_for_cv].
          goal_cleanup.
          autounfold.
          simpl_env.
          constructor. {
            apply wf_cset_union.
            all : eapply wf_cset_from_binds_typ'; [ binds_dec | fsetdec].
          }
          wf_step X' with wf_typ_all.
          goal_cleanup.
          constructor. {
            simpl_env.
            apply wf_cset_union.
            all : eapply wf_cset_from_binds_typ'; [ binds_dec | fsetdec].
          }
          wf_step y' with wf_typ_arrow.
          - wf_step y' with wf_typ_arrow.
            + econstructor; binds_dec.
            + goal_cleanup.
              wf_step z'' with wf_typ_arrow.
              2: goal_cleanup.
              1,2: econstructor; binds_dec.
          - goal_cleanup.
            replace (open_cset 0 y' (cset_union z (cset_union y 0)))
              with (cset_union z (cset_union y y')).
            2: {
              cbv [cset_union open_cset].
              simpl.
              goal_cleanup.
              cset_eq_dec.
            }
            constructor. {
              repeat apply wf_cset_union.
              all : eapply wf_cset_from_binds_typ'; [ binds_dec | fsetdec].
            }
            wf_step z'' with wf_typ_arrow.
            2: goal_cleanup.
            1,2: econstructor; binds_dec.
        }
      }
      {
        assert (T4 = (open_ct ?T3__R y)). {
          unfold T4.
          goal_cleanup.
          cbv [free_for_cv].
          goal_cleanup.
          [T3__R]:
            exact
              (0 |>
                 typ_arrow X
                 (cset_union 0 1
                             |> typ_all UniTop
                             (cset_union 0 1
                                         |> typ_arrow ({}C |> typ_arrow X ({}C |> typ_arrow 0 0))
                                         (cset_union 1 (cset_union 2 0) |> typ_arrow 0 0)))).
          goal_cleanup.
          replace (open_cset 0 y 0) with (cset_fvar y).
          2: {
            cbv [cset_union open_cset].
            simpl.
            goal_cleanup.
            cset_eq_dec.
          }
          replace (open_cset 1 y (cset_union 0 1)) with (cset_union 0 y).
          2: {
            cbv [cset_union open_cset].
            simpl.
            goal_cleanup.
            destruct_if.
            - assert (~ NatSet.F.In 1 [.0]) by fnsetdec.
              cset_eq_dec.
            - rewrite_set_facts_in Heqb.
              exfalso; fnsetdec.
          }
          replace (open_cset 2 y (cset_union 1 (cset_union 2 0)))
            with (cset_union 1 (cset_union y 0)).
          2: {
            cbv [cset_union open_cset].
            simpl.
            goal_cleanup.
            destruct_if.
            - assert (~ NatSet.F.In 2 [.1]) as HA by fnsetdec.
              assert (~ NatSet.F.In 2 [.0]). {
                intro bogus.
                rewrite NatSetFacts.singleton_iff in bogus.
                congruence.
              }
              cset_eq_dec.
            - rewrite_set_facts_in Heqb.
              exfalso; fnsetdec.
          }
          reflexivity.
        }
        rewrite <- H2.
        assumption.
      }
      { autounfold.
        full_cleanup.
        constructor. {
          eapply wf_cset_from_binds_typ'; [ binds_dec | fsetdec].
        }
        wf_step y'' with wf_typ_arrow. {
          econstructor; binds_dec.
        }
        goal_cleanup.
        replace (open_cset 0 y'' (cset_union 0 y)) with (cset_union y'' y).
        2: cset_prep; cset_eq_dec.
        replace (open_cset 1 y'' (cset_union 1 (cset_union y 0)))
          with (cset_union y'' (cset_union y 0)).
        2: {
          cset_prep.
          destruct_if.
          - assert (~ NatSet.F.In 1 [.0]) as HA by fnsetdec.
            cset_eq_dec.
          - rewrite_set_facts_in Heqb.
            exfalso; fnsetdec.
        }
        constructor. {
          simpl_env.
          apply wf_cset_union.
          all : eapply wf_cset_from_binds_typ'; [ binds_dec | fsetdec].
        }
        wf_step X' with wf_typ_all.
        goal_cleanup.
        constructor. {
          simpl_env.
          apply wf_cset_union.
          all : eapply wf_cset_from_binds_typ'; [ binds_dec | fsetdec].
        }
        wf_step y' with wf_typ_arrow.
        - wf_step y' with wf_typ_arrow.
          + econstructor; binds_dec.
          + goal_cleanup.
            wf_step z'' with wf_typ_arrow.
            2: goal_cleanup.
            1,2: econstructor; binds_dec.
        - goal_cleanup.
          replace (open_cset 0 y' (cset_union y'' (cset_union y 0)))
            with (cset_union y'' (cset_union y y')).
          2: {
            cset_prep; cset_eq_dec.
          }
          constructor. {
            repeat apply wf_cset_union.
            all : eapply wf_cset_from_binds_typ'; [ binds_dec | fsetdec].
          }
          wf_step z'' with wf_typ_arrow.
          2: goal_cleanup.
          1,2: econstructor; binds_dec.
      }
    }
    { assert (T3 = (open_tt ?T1__R X)). {
        unfold T3.
        full_cleanup.
        [T1__R]:
          exact (
              ({}C
                 |>
                 typ_arrow (CC_List {*} 1)
                 (0
                    |> typ_arrow 0
                    (cset_union 0 1
                                |> typ_all UniTop
                                (cset_union 0 1
                                            |> typ_arrow ({}C |> typ_arrow 1 ({}C |> typ_arrow 0 0))
                                            (cset_union 1 (cset_union 2 0) |> typ_arrow 0 0)))))).
        full_cleanup.
        reflexivity.
      }
      rewrite <- H1.
      assumption.
    }
    { full_cleanup.
      wf_step y with wf_typ_arrow. {
        unfold CC_List.
        constructor; wf_cleanup.
        wf_step X' with wf_typ_all.
        full_cleanup.
        constructor; wf_cleanup.
        wf_step y' with wf_typ_arrow.
        * wf_step y' with wf_typ_arrow.
          { econstructor; binds_dec.
          }
          full_cleanup.
          wf_step y'' with wf_typ_arrow;
            cleanup; econstructor; binds_dec.
        * full_cleanup.
          wf_step y'' with wf_typ_arrow;
            cleanup; econstructor; binds_dec.
      }
      goal_cleanup.
      replace (open_cset 0 y 0) with (cset_fvar y).
      2: cset_prep; cset_eq_dec.
      replace (open_cset 1 y (cset_union 0 1)) with (cset_union 0 y).
      2: {
        cset_prep.
        Ltac fnset_contradiction_in H :=
          rewrite_set_facts_in H; exfalso; fnsetdec.
        destruct_if; [|fnset_contradiction_in Heqb].
        assert (~ NatSet.F.In 1 [.0]) by fnsetdec.
        cset_eq_dec.
      }
      replace (open_cset 2 y (cset_union 1 (cset_union 2 0)))
        with (cset_union 1 (cset_union y 0)).
      2: {
        cset_prep.
        destruct_if.
        - assert (~ NatSet.F.In 2 [.1]) as HA by fnsetdec.
          assert (~ NatSet.F.In 2 [.0]). {
            intro bogus.
            rewrite NatSetFacts.singleton_iff in bogus.
            congruence.
          }
          cset_eq_dec.
        - rewrite_set_facts_in Heqb.
          exfalso; fnsetdec.
      }
      constructor. {
        eapply wf_cset_from_binds_typ'; [ binds_dec | fsetdec].
      }
      wf_step y'' with wf_typ_arrow. {
        econstructor; binds_dec.
      }
      goal_cleanup.
      replace (open_cset 0 y'' (cset_union 0 y)) with (cset_union y'' y).
      2: cset_prep; cset_eq_dec.
      replace (open_cset 1 y'' (cset_union 1 (cset_union y 0)))
        with (cset_union y'' (cset_union y 0)).
      2: {
        cset_prep.
        destruct_if.
        - assert (~ NatSet.F.In 1 [.0]) as HA by fnsetdec.
          cset_eq_dec.
        - rewrite_set_facts_in Heqb.
          exfalso; fnsetdec.
      }
      constructor. {
        apply wf_cset_union.
        all : eapply wf_cset_from_binds_typ'; [ binds_dec | fsetdec].
      }
      wf_step X' with wf_typ_all.
      goal_cleanup.
      constructor. {
        apply wf_cset_union.
        all : eapply wf_cset_from_binds_typ'; [ binds_dec | fsetdec].
      }
      wf_step y' with wf_typ_arrow.
      - wf_step y' with wf_typ_arrow.
        + econstructor; binds_dec.
        + goal_cleanup.
          wf_step z'' with wf_typ_arrow.
          2: goal_cleanup.
          1,2: econstructor; binds_dec.
      - goal_cleanup.
        replace (open_cset 0 y' (cset_union y'' (cset_union y 0)))
          with (cset_union y'' (cset_union y y')).
        2: {
          cset_prep; cset_eq_dec.
        }
        constructor. {
          repeat apply wf_cset_union.
          all : eapply wf_cset_from_binds_typ'; [ binds_dec | fsetdec].
        }
        wf_step z'' with wf_typ_arrow.
        2: goal_cleanup.
        1,2: econstructor; binds_dec.
    }
  }
  by_asserted_typing.
  full_cleanup.
  wf_step X with wf_typ_all.
  arw.
  fold open_tt_rec.
  change (open_tt_rec 0 X (CC_List cset_universal 1))
    with (CC_List cset_universal X).
  wf_step y with wf_typ_arrow. {
    unfold CC_List.
    constructor; wf_cleanup.
    wf_step X' with wf_typ_all.
    full_cleanup.
    constructor; wf_cleanup.
    wf_step y' with wf_typ_arrow.
    * wf_step y' with wf_typ_arrow.
      { econstructor; binds_dec.
      }
      full_cleanup.
      wf_step y'' with wf_typ_arrow;
        cleanup; econstructor; binds_dec.
    * full_cleanup.
      wf_step y'' with wf_typ_arrow;
        cleanup; econstructor; binds_dec.
  }
  goal_cleanup.
  replace (open_cset 0 y 0) with (cset_fvar y).
  2: cset_prep; cset_eq_dec.
  replace (open_cset 1 y (cset_union 0 1)) with (cset_union 0 y).
  2: {
    cset_prep.
    destruct_if.
    - assert (~ NatSet.F.In 1 [.0]) by fnsetdec.
      cset_eq_dec.
    - rewrite_set_facts_in Heqb.
      exfalso; fnsetdec.
  }
  replace (open_cset 2 y (cset_union 1 (cset_union 2 0)))
    with (cset_union 1 (cset_union y 0)).
  2: {
    cset_prep.
    destruct_if.
    - assert (~ NatSet.F.In 2 [.1]) as HA by fnsetdec.
      assert (~ NatSet.F.In 2 [.0]). {
        intro bogus.
        rewrite NatSetFacts.singleton_iff in bogus.
        congruence.
      }
      cset_eq_dec.
    - rewrite_set_facts_in Heqb.
      exfalso; fnsetdec.
  }
  constructor. {
    eapply wf_cset_from_binds_typ'; [ binds_dec | fsetdec].
  }
  wf_step y'' with wf_typ_arrow. {
    econstructor; binds_dec.
  }
  goal_cleanup.
  replace (open_cset 0 y'' (cset_union 0 y)) with (cset_union y'' y).
  2: cset_prep; cset_eq_dec.
  replace (open_cset 1 y'' (cset_union 1 (cset_union y 0)))
    with (cset_union y'' (cset_union y 0)).
  2: {
    cset_prep.
    destruct_if; [| fnset_contradiction_in Heqb].
    assert (~ NatSet.F.In 1 [.0]) by fnsetdec.
    cset_eq_dec.
  }
  constructor. {
    apply wf_cset_union.
    all : eapply wf_cset_from_binds_typ'; [ binds_dec | fsetdec].
  }
  wf_step X' with wf_typ_all.
  goal_cleanup.
  constructor. {
    apply wf_cset_union.
    all : eapply wf_cset_from_binds_typ'; [ binds_dec | fsetdec].
  }
  wf_step y' with wf_typ_arrow.
  - wf_step y' with wf_typ_arrow.
    + econstructor; binds_dec.
    + goal_cleanup.
      wf_step z'' with wf_typ_arrow.
      2: goal_cleanup.
      1,2: econstructor; binds_dec.
  - goal_cleanup.
    replace (open_cset 0 y' (cset_union y'' (cset_union y 0)))
      with (cset_union y'' (cset_union y y')).
    2: {
      cset_prep; cset_eq_dec.
    }
    constructor. {
      repeat apply wf_cset_union.
      all : eapply wf_cset_from_binds_typ'; [ binds_dec | fsetdec].
    }
    wf_step z'' with wf_typ_arrow.
    2: goal_cleanup.
    1,2: econstructor; binds_dec.
Qed.
