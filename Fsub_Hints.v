Require Import Coq.Program.Equality.
Require Export Fsub_Lemmas.

Ltac rewrite_nil_concat :=
  match goal with
  | |- _ ?E0 _ =>
    rewrite <- nil_concat with (E := E0)
  | |- _ ?E0 _ _ =>
    rewrite <- nil_concat with (E := E0)
  | |- _ ?E0 _ _ _ =>
    rewrite <- nil_concat with (E := E0)
  end.

Ltac wf_typ_inversion H :=
  inversion H;
  let t := type of H
  in match t with
  | wf_typ_in ?E (typ_capt _ ?T) =>
    match goal with
    | H : wf_pretyp E _ _ T |- _ =>
      inversion H
    end
  | wf_typ ?E _ _ (typ_capt _ ?T) =>
    match goal with
    | H : wf_pretyp E _ _ T |- _ =>
      inversion H
    end
  | _ => idtac
  end; subst.

Local Lemma test_wf_typ_inversion : forall E Ap Am C S T U,
  wf_typ_in E (typ_capt C (typ_arrow S T)) ->
  wf_typ E Ap Am (typ_capt C (typ_arrow S T)) ->
  wf_typ_in E U ->
  wf_typ_in E S /\ wf_typ E Am Ap S.
Proof.
  intros* H1 H2 H3.
  wf_typ_inversion H1.
  wf_typ_inversion H2.
  wf_typ_inversion H3.          (* shouldn't break *)
  all : split; assumption.
Qed.

Hint Extern 1 (wf_typ_in ?E ?T) =>
match goal with
| H : wf_typ_in ?E (typ_capt _ ?P) |- _ =>
  inversion H; subst; (match goal with
                       | H : wf_pretyp_in ?E (typ_arrow ?T _) |- _ =>
                         inversion H; subst; assumption
                       end)
end : core.

Hint Extern 1 (wf_cset ?E (dom ?E) ?C) =>
match goal with
| H : typing ?E _ (typ_capt ?C _) |- _ =>
  let P := fresh "P" in
  pose proof (proj2 (proj2 (typing_regular _ _ _ H))) as P; inversion P; assumption
end : core.


Hint Extern 1 (wf_env ?E) =>
match goal with
| H : sub_pre ?E _ _ |- _ => apply (proj1 (sub_pre_regular _ _ _ H))
end : core.

