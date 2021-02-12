Require Import Coq.Program.Equality.
Require Export Fsub_Lemmas.

Ltac rewrite_nil_concat :=
  match goal with
  | _ : _ |- typing ?E0 _ _ =>
    rewrite <- nil_concat with (E := E0)
  | _ : _ |- sub ?E0 _ _ =>
    rewrite <- nil_concat with (E := E0)
  | _ : _ |- wf_typ ?E0 _ _ _ =>
    rewrite <- nil_concat with (E := E0)
  end.

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

