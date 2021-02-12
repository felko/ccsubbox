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

Ltac rewrite_parenthesise_binding :=
  match goal with
    |- context[[(?x, ?b)] ++ ?F ++ ?E] =>
    rewrite_env (([(x, b)] ++ F) ++ E)
  end.

Ltac unsimpl_env_map f :=
  simpl_env ;
  match goal with
    |- context[[(?x, f ?Z ?P ?b)] ++ map (f ?Z ?P) ?F ++ ?E] =>
    rewrite_env ((map (f Z P) ([(x, b)] ++ F)) ++ E)
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

Lemma ok_ignores_binding : forall (F E: env) x b1 b2,
  ok (F ++ [(x, b1)] ++ E) ->
  ok (F ++ [(x, b2)] ++ E).
Proof with eauto*.
  intros*.
  induction F...
  - simpl_env.
    intros Hok. inversion Hok; subst. constructor...
  - rewrite_env ([a] ++ F ++ [(x, b1)] ++ E).
    rewrite_env ([a] ++ F ++ [(x, b2)] ++ E).
    intros Hok. inversion Hok; subst. constructor...
Qed.

Hint Resolve ok_ignores_binding : core.