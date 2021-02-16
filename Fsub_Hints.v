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

