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

Ltac replace_if_cond_with val tac :=
  match goal with
  | _ :_ |- context[if ?c then _ else _] =>
    replace c with val by tac
  end.

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
  pick fresh x and apply typing_abs.
  - simpl_hammer.
    replace_if_cond_with true fnset_mem_dec.
    replace (cset_set (singleton x `union` {})
                      (NatSet.F.union {}N (NatSet.F.remove 0 (NatSet.F.singleton 0))))
      with (cset_fvar x)
      by cset_eq_dec.
    apply typing_var with (C := cset_universal).
    + econstructor...
    + simpl_hammer;
        replace_if_cond_with_left...
  - pick fresh x and apply wf_typ_arrow...
    simpl_hammer.
    replace_if_cond_with true fnset_mem_dec.
    set (c := (cset_set _ _)).
    replace c with (cset_fvar x) by cset_eq_dec.
    apply wf_typ_capt...
    eapply wf_concrete_cset...
    apply allbound_typ_if...
Qed.


Lemma ez_pz_lemon_sqz :
  typing empty
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
  pick fresh X and apply typing_tabs.
  - simpl_hammer.
    apply ezy_pzy_lemon_sqzy.
    econstructor...
  - pick fresh X and apply wf_typ_all...
    simpl_hammer.
    apply wf_typ_capt... {
      eapply wf_concrete_cset...
      apply allbound_typ_if...
    }
    (* just copied from above... *)
    pick fresh x and apply wf_typ_arrow...
    simpl_hammer.
    replace_if_cond_with true fnset_mem_dec.
    replace (cset_set (singleton x `union` {})
                      (NatSet.F.union {}N (NatSet.F.remove 0 (NatSet.F.singleton 0))))
      with (cset_fvar x)
      by cset_eq_dec.
    apply wf_typ_capt...
    eapply wf_concrete_cset...
    apply allbound_typ_if...
Qed.
