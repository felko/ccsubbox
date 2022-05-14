Require Import Coq.Program.Equality.
Require Export CCsub_Lemmas.

Ltac destruct_union_mem H :=
  match type of H with
  | _ `in`A _ => rewrite AtomSetFacts.union_iff in H; destruct H as [H|H]
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

Ltac rewrite_set_facts_in H :=
  match type of H with
  | true = _ => symmetry in H
  | false = _ => symmetry in H
  | _ => idtac
  end;
  match type of H with
  | NatSet.F.mem _ _ = true => rewrite <- NatSetFacts.mem_iff in H
  | NatSet.F.mem _ _ = false => rewrite <- NatSetFacts.not_mem_iff in H
  | AtomSet.F.mem _ _ = true => rewrite <- AtomSetFacts.mem_iff in H
  | AtomSet.F.mem _ _ = false => rewrite <- AtomSetFacts.not_mem_iff in H
  end.

Ltac rewrite_parenthesise_binding_in H :=
  match type of H with
  | context[[(?x, ?b)] ++ ?F ++ ?E] =>
    rewrite_env (([(x, b)] ++ F) ++ E) in H
  end.

