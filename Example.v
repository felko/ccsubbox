Require Import Fsub_Soundness.

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

Definition CC_cons :=
  (** forall T <: {*} Top,*)
  (exp_tabs
     (typ_capt cset_universal typ_top)
     (exp_abs
        (** lst : {*} List [T] *)
        (CC_List cset_universal (typ_bvar 0)) (** is this the right type?? *)
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
                    t
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
                    (exp_app (exp_bvar 3) (exp_bvar 1))
                    (exp_bvar 0)))))))))

Definition CC_map :=
  (exp_tabs
    (typ_capt cset_universal typ_top (** forall T <: {*} Top*)
    (exp_tabs
      (typ_capt cset_universal typ_top) (** forall A <: {*} Top, *)
      (exp_abs
        (CC_List cset_universal t) (** lst : {*} List [T] *)
        (exp_abs
          (typ_capt {}C (typ_abs (typ_bvar 1) (typ_bvar 0))) (** f : {}C T -> A *)
          (exp_app
            (exp_app (exp_bvar 1)
              (** \e \a -> (cons (f elem) accum) *)
              (exp_abs t
                (exp_abs (typ_bvar 0)
                  (exp_app 
                    (exp_app (exp_tapp CC_cons t) (exp_app (exp_bvar 2) (exp_bvar 1)))
                    (exp_bvar 0)))))
            (CC_empty {}C t)))))))

Lemma fast_and_furious : forall C T,
  wf_typ_in empty T ->
  wf_cset_in empty C ->
  typing empty (CC_empty C T) (CC_List C T).
Proof with eauto.
  intros.
  unfold CC_empty, CC_List.

  Ltac assert_typing_with tp :=
    match goal with
    | |- typing ?E ?t _ =>
      assert (typing E t tp); [unfold tp|]
    end.

  Ltac replace_type_with tp :=
    match goal with
    | |- typing _ _ ?T =>
      replace T with tp
    end;
    unfold tp.

  Ltac assert_wf_env :=
    match goal with
    | |- typing ?E _ _ =>
      assert (wf_env E)
    | |- sub ?E _ _ =>
      assert (wf_env E)
    end.

  assert (forall k x, (open_tt_rec k x T) = T) as TClsTt. {
    intros.
    erewrite <- open_tt_rec_type...
    eapply type_from_wf_typ...
  }

  assert (forall k D, (open_ct_rec k D T) = T) as TClsCt. {
    intros.
    erewrite <- open_ct_rec_type...
    eapply type_from_wf_typ...
  }

  assert (forall k D, (open_cset k D C) = C) as DCls. {
    intros.
    erewrite <- open_cset_capt...
  }

  assert (forall k C, (open_cset k C {}C) = {}C) as EmptyCls. {
    intros.
    erewrite <- open_cset_capt.
    reflexivity.
    constructor.
  }

  assert (forall E Ap Am T, wf_pretyp E Ap Am T -> wf_typ E Ap Am (typ_capt {}C T)) as HCaptWf. {
    intros.
    constructor.
    - constructor.
      + unfold allbound_typ.
        intros. exfalso; fsetdec.
      + fsetdec.
    - easy.
  }

  Ltac cbn' :=
       cbn [
           open_ee open_te open_ct open_tt
                   open_ct_rec open_cpt_rec open_ee_rec open_te_rec open_tt_rec open_tpt_rec
         ].

  Ltac extract_binding_uniqueness_rec x E :=
    lazymatch E with
    | [(?y, _)] =>
      assert (x <> y) by notin_solve
    | [(?y, _)] ++ ?G =>
      assert (x <> y) by notin_solve; extract_binding_uniqueness_rec x G
    end.

  Ltac extract_binding_uniqueness :=
    lazymatch goal with
    | |- wf_typ_in ([(?x, _)] ++ ?E) _ =>
      extract_binding_uniqueness_rec x E
    | |- wf_typ ([(?x, _)] ++ ?E) _ _ _ =>
      extract_binding_uniqueness_rec x E
    end.

  Ltac binds_dec :=
    cbv [binds get]; simpl;
      repeat first [ reflexivity | destruct_if; try congruence].

  Hint Resolve allbound_typ_if.

  epose (T1 := (typ_capt ?[T1__C] (typ_all ?[T1__A] ?[T1__R]))).
  assert_typing_with T1. {
    (* pick fresh X. *)
    (* lazymatch goal with *)
    (* | H : X `notin` ?L |- typing ?E _ (typ_capt _ (typ_all ?S ?T)) => *)
    (*   enough (forall A, A `notin` L -> wf_typ ([(A, bind_sub S)] ++ E) (dom E) (dom E) (open_tt T A)) *)
    (* end. *)
    (* Ltac instantiate_var X := *)
    (*   lazymatch goal with *)
    (*   | H : X `notin` ?L |-  forall Y, Y `notin` ?L' -> _ => *)
    (*     let Fr' := fresh "Fr" in *)
    (*     unify L L'; clear dependent X; intros X Fr' *)
    (*   end. *)
    (* eapply typing_tabs; try instantiate_var X; simpl_env... *)
    pick fresh X and apply typing_tabs; simpl_env...
    2: {
      assert_wf_env. {
        constructor...
      }

      cbn [open_te open_te_rec open_tt_rec open_tpt_rec].
      destruct_if; try easy.
      rewrite TClsTt.

      epose (T2 := (typ_capt ?[T2__C] (typ_arrow ?[T2__A] ?[T2__R]))).
      assert_typing_with T2. {
        pick fresh y and apply typing_abs.
        3: {
          assert_wf_env. {
            constructor...
            constructor...
            - constructor...
            - pick fresh y' and apply wf_typ_arrow...
              + rewrite_env (empty ++ [(X, bind_sub (typ_capt cset_universal typ_top))] ++ empty).
                eapply wf_typ_weakening...
              + assert (y' <> X) by notin_solve.
                cbn'.
                rewrite EmptyCls.
                constructor.
                * constructor...
                * pick fresh y'' and apply wf_typ_arrow.
                  -- econstructor. binds_dec.
                  -- extract_binding_uniqueness.
                     econstructor. binds_dec.
          }
          cbn'.
          destruct_if; [congruence|].

          epose (T3 := (typ_capt ?[T3__C] (typ_arrow ?[T3__A] ?[T3__R]))).
          assert_typing_with T3. {
            pick fresh z and apply typing_abs.
            3: {
              assert_wf_env. {
                constructor...
              }
              cbn'.
              destruct_if; [|easy].

              epose (T4 := _).
              replace_type_with T4. {
                apply typing_var_tvar with (X := X).
                1: easy.
                cbv [binds get]; simpl.
                destruct_if; easy.
              }
              [T3__R] : exact X.
              cbn'. easy.
            }
            - extract_binding_uniqueness.
              econstructor; binds_dec.
            - cbn'.
              extract_binding_uniqueness.
              assert (y <> X) by notin_solve.
              econstructor; binds_dec.
          }
          replace_type_with T3. easy.
          cbn [free_for_cv].
          [T2__R] : exact (typ_capt {}C (typ_arrow X X)).
          cbn'. rewrite EmptyCls. easy.
        }
        - constructor; simpl_env...
          1 : constructor; simpl_env...
          pick fresh y' and apply wf_typ_arrow.
          match goal with
          | |- wf_typ ?E _ _ T =>
            change E with (empty ++ E ++ empty)
          end.
          eapply wf_typ_weakening; [apply H|eauto ..].
          cbn'. rewrite EmptyCls.
          extract_binding_uniqueness.
          constructor.
          1 : constructor; simpl_env...
          pick fresh y'' and apply wf_typ_arrow.
          1 : econstructor; binds_dec.
          cbn'.
          extract_binding_uniqueness.
          econstructor; binds_dec.
        - cbn'. rewrite EmptyCls.
          apply HCaptWf.
          pick fresh y' and apply wf_typ_arrow.
          + extract_binding_uniqueness.
            econstructor; binds_dec.
          + cbn'.
            extract_binding_uniqueness.
            assert (y <> X) by notin_solve.
            econstructor; binds_dec.
      }
      cbn [free_for_cv] in T2.
      [T1__R] : exact (
                  typ_capt {}C
                           (typ_arrow (typ_capt {}C (typ_arrow T (typ_capt {}C (typ_arrow 0 0))))
                                      (typ_capt {}C (typ_arrow 0 0)))
                ).
      replace_type_with T2. easy.
      cbn'. rewrite TClsTt.
      destruct_if; [|congruence].
      reflexivity.
    }
    cbn'. rewrite TClsTt.
    apply HCaptWf.
    pick fresh y' and apply wf_typ_arrow...
    - apply HCaptWf.
      pick fresh y'' and apply wf_typ_arrow...
      + match goal with
        | |- wf_typ ?E _ _ T =>
          change E with (empty ++ E ++ empty)
        end.
        eapply wf_typ_weakening; simpl_env.
        apply H.
        all : auto.
      + extract_binding_uniqueness.
        cbn'. rewrite EmptyCls.
        apply HCaptWf.
        pick fresh y''' and apply wf_typ_arrow.
        * econstructor; binds_dec.
        * extract_binding_uniqueness.
          cbn'.
          econstructor; binds_dec.
    - cbn'. rewrite EmptyCls.
      extract_binding_uniqueness.
      apply HCaptWf.
      pick fresh y'' and apply wf_typ_arrow.
      + econstructor; binds_dec.
      + extract_binding_uniqueness.
        cbn'.
        econstructor; binds_dec.
  }

  cbv [free_for_cv] in *.
  eapply typing_sub.
  apply H1.
  apply sub_capt.
  { destruct C.
    - constructor...
      constructor.
      2: fsetdec.
      unfold allbound_typ; intros; exfalso; fsetdec.
    - inversion H0; subst.
      constructor...
      intros ? ?; exfalso; fsetdec.
  }

  assert (wf_typ_in empty (typ_capt cset_universal typ_top)). {
    constructor...
  }
  pick fresh X and apply sub_all; simpl_env...
  - apply sub_capt...
  - cbn'.
    destruct_if; [|congruence].
    rewrite TClsTt.
    constructor.
    { match goal with
      | |- wf_cset ?E _ _ =>
        change E with (empty ++ E ++ empty)
      end.
      eapply wf_cset_weakening; simpl_env.
      eauto.
      all : eauto.
    }
    pick fresh y' and apply wf_typ_arrow; [|extract_binding_uniqueness].
    + apply HCaptWf.
      pick fresh y'' and apply wf_typ_arrow.
      {
        match goal with
        | |- wf_typ ?E _ _ T =>
          change E with (empty ++ E ++ empty)
        end.
        eapply wf_typ_weakening; [apply H|simpl_env;eauto ..].
      }
      extract_binding_uniqueness.
      cbn'. rewrite EmptyCls.
      apply HCaptWf.
      pick fresh y''' and apply wf_typ_arrow.
      1 : econstructor; binds_dec.
      cbn'.
      extract_binding_uniqueness.
      econstructor; binds_dec.
    + cbn'. rewrite EmptyCls.
      apply HCaptWf.
      pick fresh y'' and apply wf_typ_arrow; [|extract_binding_uniqueness].
      1 : econstructor; binds_dec.
      cbn'.
      econstructor; binds_dec.
  - cbn'.
    destruct_if; [|congruence].
    rewrite TClsTt.
    apply HCaptWf.
    pick fresh y' and apply wf_typ_arrow; [|extract_binding_uniqueness].
    + apply HCaptWf.
      pick fresh y'' and apply wf_typ_arrow; [|extract_binding_uniqueness].
      {
        lazymatch goal with
        | |- wf_typ ?E _ _ _ =>
          change E with (empty ++ E ++ empty)
        end.
        eapply wf_typ_weakening; [apply H|simpl_env;eauto ..].
      }
      cbn'. rewrite EmptyCls.
      apply HCaptWf.
      pick fresh y''' and apply wf_typ_arrow; [|extract_binding_uniqueness].
      1 : econstructor; binds_dec.
      cbn'.
      econstructor; binds_dec.
    + cbn'. rewrite EmptyCls.
      extract_binding_uniqueness.
      apply HCaptWf.
      pick fresh y'' and apply wf_typ_arrow; [|extract_binding_uniqueness].
      1 : econstructor; binds_dec.
      cbn'.
      econstructor; binds_dec.
  - cbn'.
    destruct_if; [|congruence].
    rewrite TClsTt.
    assert_wf_env. {
      constructor...
    }
    apply sub_capt.
    2: {
      let a := constr:(dom [(X, bind_sub (typ_capt cset_universal typ_top))]) in
      apply sub_pre_reflexivity with (Ap := a) (Am := a); simpl_env...
      pick fresh y' and apply wf_typ_arrow.
      + apply HCaptWf.
        pick fresh y'' and apply wf_typ_arrow.
        {
          lazymatch goal with
          | |- wf_typ ?E _ _ _ =>
            change E with (empty ++ E ++ empty)
          end.
          eapply wf_typ_weakening; [apply H|simpl_env;eauto ..].
        }
        extract_binding_uniqueness.
        cbn'. rewrite EmptyCls.
        apply HCaptWf.
        pick fresh y''' and apply wf_typ_arrow.
        1 : econstructor; binds_dec.
        cbn'.
        extract_binding_uniqueness.
        econstructor; binds_dec.
      + cbn'. rewrite EmptyCls.
        extract_binding_uniqueness.
        apply HCaptWf.
        pick fresh y'' and apply wf_typ_arrow.
        1 : econstructor; binds_dec.
        cbn'.
        extract_binding_uniqueness.
        econstructor; binds_dec.
    }
    { destruct C.
      - constructor...
        constructor.
        2: fsetdec.
        unfold allbound_typ; intros; exfalso; fsetdec.
      - inversion H0; subst.
        constructor...
        intros ? ?; exfalso; fsetdec.
    }
Qed.
