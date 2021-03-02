Require Import Coq.Program.Equality.
Require Export Fsub_Hints.
Require Import Fsub_CVfacts.

Lemma map_subst_cb_id : forall G x C,
  wf_env G ->
  x `notin` dom G ->
  G = map (subst_cb x C) G.
Proof with eauto.
  intros * H.
  induction H; simpl; intros Fr; simpl_env...
  - rewrite <- IHwf_env...
    rewrite <- subst_ct_fresh...
    enough (x `notin` (fv_tt T `union` fv_et T)) by fsetdec.
    eapply notin_fv_wf_typ...
  - rewrite <- IHwf_env...
    rewrite <- subst_ct_fresh...
    enough (x `notin` (fv_tt T `union` fv_et T)) by fsetdec.
    eapply notin_fv_wf_typ...
Qed.

Lemma fv_ee_subset_dom_E : forall E t T,
  typing E t T ->
  fv_ee t `subset` dom E.
Proof.
Admitted.

Lemma ok_trivia1 : forall E, ok E -> ok (empty ++ E). auto. Qed.
Hint Resolve ok_trivia1 : core.


Notation "'wf_typ_inn' E T" := (wf_typ E (dom E) (dom E) T)
                                         (at level 10, E,T at level 9).

Check (wf_typ empty (dom empty) (dom empty) _).

Check (wf_typ_inn empty _).

(** The tactic [select pat tac] finds the last (i.e., bottommost) hypothesis
matching [pat] and passes it to the continuation [tac]. Its main advantage over
using [match goal with ] directly is that it is shorter. If [pat] matches
multiple hypotheses and [tac] fails, then [select tac] will not backtrack on
subsequent matching hypotheses.

The tactic [select] is written in CPS and does not return the name of the
hypothesis due to limitations in the Ltac1 tactic runtime (see
https://gitter.im/coq/coq?at=5e96c82f85b01628f04bbb89). *)
Tactic Notation "select" open_constr(pat) tactic3(tac) :=
  lazymatch goal with
  (** Before running [tac] on the hypothesis [H] we must first unify the
      pattern [pat] with the term it matched against. This forces every evar
      coming from [pat] (and in particular from the holes [_] it contains and
      from the implicit arguments it uses) to be instantiated. If we do not do
      so then shelved goals are produced for every such evar. *)
  | H : pat |- _ => let T := (type of H) in unify T pat; tac H
  end.

(** [select_revert] reverts the first hypothesis matching [pat]. *)
Tactic Notation "revert" "select" open_constr(pat) := select pat (fun H => revert H).

Tactic Notation "rename" "select" open_constr(pat) "into" ident(name) :=
  select pat (fun H => rename H into name).
Lemma reg : forall E T C,
  cv E T C ->
  cv E T C.
  intros.
  rename select (cv _ _ _) into foo.
  pose proof (cv_regular _ _ _ H) as (H1 & H2 & H3).
  select (binds X _ _) as binds__X.
Abort.

Require Import LibTactics.

Lemma ok_trivia1 : forall E, ok E -> ok (empty ++ E). auto. Qed.

Ltac wf_typ__forwards_by_regularity :=
  match goal with
  | |- wf_typ_in ?E ?T =>
    match goal with
    | H : typing E _ ?t |- _ =>
      match t with
      | (typ_capt ?C (typ_arrow ?T ?S)) =>
        let H := fresh "TEMP" in
        enough (wf_typ_in E t) as H; [
          wf_typ_inversion H; assumption
        | ]
      end
    end
  end.

Hint Extern 1 => wf_typ__forwards_by_regularity.

Lemma test : forall E t C T S,
  typing E t (typ_capt C (typ_arrow T S)) ->
  typing E t (typ_capt C (typ_arrow S T)) ->
  wf_typ_in E T.
  auto.
Qed.

Lemma reg : forall E T C,
  cv E T C ->
  cv E T C.
  intros.
  forwards (H1 & H2 & H3): cv_regular H.
  assert (True -> cv E T C -> True -> False) as HA by admit.
  forwards: HA H.

Lemma reg : forall E T C,
  cv E T C ->
  cv E T C.
  intros.
  pose proof (cv_regular _ _ _ H) as (H1 & H2 & H3).
Abort.

          Lemma open_cset_into_union : forall k D C1 C2,
            (open_cset k D (cset_union C1 C2)) = (cset_union (open_cset k D C1) (open_cset k D C2)).
          Proof.
            intros.
            destruct C1; destruct C2; simpl; try reflexivity.
            - unfold open_cset, cset_references_bvar_dec.
              destruct_match; reflexivity.
            - unfold open_cset, cset_references_bvar_dec, cset_union.
              destruct_match; reflexivity.
            - unfold open_cset, cset_references_bvar_dec, cset_union.
              simpl.
              destruct_if.
