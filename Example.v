Require Import Fsub_Lemmas.

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

Lemma ezy_pzy_lemon_sqzy : forall E,
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

Lemma ez_pz_lemon_sqz : forall E,
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
    apply ezy_pzy_lemon_sqzy.
    econstructor...
Qed.

Lemma ez_pz_lemon_sqz_electric_boogaloo : forall x,
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
    + apply ez_pz_lemon_sqz...
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

Definition CC_empty (c : captureset) (t : typ) :=
  (exp_tabs
     (typ_capt cset_universal typ_top)
     (exp_abs
        (typ_capt
           {}C
           (typ_arrow
              t
              (typ_capt
                 {}C
                 (typ_arrow 0 0))))
        (exp_abs 0 0))).

Lemma fast_and_furious : forall c t,
  wf_typ_in empty t ->
  wf_cset_in empty c ->
  typing empty (CC_empty c t) (CC_List c t).
Proof with eauto.
  intros.
  unfold CC_empty, CC_List.
  Ltac subst_type tp :=
    match goal with
    | |- typing _ _ ?T =>
      replace T with tp
    end;
    unfold tp.

  epose (T1 := (typ_capt ?[AllS1] ?[AllT1])).
  subst_type T1.
  pick fresh x and apply typing_tabs...
  2: {
    simpl_env.
    cbn.
    epose (T2 := (typ_capt _ _)).
    subst_type T2.
    pick fresh y and apply typing_abs...
    3: {
      cbn.
      epose (T3 := (typ_capt _ _)).
      subst_type T3.
      pick fresh z and apply typing_abs...
      3: {
        cbn.
        simpl_env.
        epose (T4 := _). subst_type T4.
        apply typing_var_tvar...
        - econstructor...
          econstructor...
          econstructor...
          econstructor...
          econstructor...
          apply allbound_typ_if...
          econstructor...
          1,2 : admit.
        - replace (open_ct _ z) with (open_ct x z).
          cbn.
          reflexivity.
          reflexivity.
      }
      - admit.
      - cbn. simpl_env.
        econstructor.
        cbv [binds get].
        simpl.
        assert (x <> y) by notin_solve.
        assert (y <> z) by notin_solve.
        assert (x <> z) by notin_solve.
        destruct (x == z); try easy.
        destruct (x == y); try easy.
        destruct (x == x); try easy.
      - replace (open_ct _ y)
          with (open_ct (typ_capt (free_for_cv 0) (typ_arrow x x)) y).
        cbv.
        Ltac fnset_rl_mem_dec :=
          match goal with
          | |- true = _ => symmetry
          | |- false = _ => symmetry
          | |- _ => idtac
          end;
          match goal with
          | |- NatSet.F.mem _ _ = true => rewrite <- NatSetFacts.mem_iff; fnsetdec
          | |- NatSet.F.mem _ _ = false => rewrite <- NatSetFacts.not_mem_iff; fnsetdec
          end.
        replace_if_cond_with false by fnset_rl_mem_dec.
        reflexivity.
        reflexivity.
    }
    - admit.
    - admit.
    - cbn.
      replace (open_tt _ x)
        with (open_tt
                (typ_capt
                   {}C
                   (typ_arrow (typ_capt {}C (typ_arrow (open_tt_rec 0 x t) (typ_capt {}C (typ_arrow x x))))
                              (typ_capt {}C (typ_arrow x x))))
                x
             ).
      cbn.
      admit.                    (* undoable, need closedness *)
      admit.
  }
  admit.
  cbn.
  admit.                        (* ok, need subtyping slack at the top... *)
Admitted.
