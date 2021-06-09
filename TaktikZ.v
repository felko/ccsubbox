(* ====================================================================== *)
(* ====================================================================== *)
(** * Bespoke *)
Ltac hint := idtac.

Ltac note0 T id tac :=
  assert (T) as id by tac;
  inversion id;
  subst.

Tactic Notation "note" constr(T) :=
  let H := fresh "Note" in note0 T H ltac:(auto).

Tactic Notation "note" constr(T) "by" tactic1(tac) :=
  let H := fresh "Note" in note0 T H tac.

Tactic Notation "note" constr(T) "as" ident(id) :=
  note0 T id ltac:(auto).

Tactic Notation "note" constr(T) "as" ident(id) "by" tactic1(tac) :=
  note0 T id tac.

Local Lemma _test_note :
  True -> True.
Proof. intro.
  (* This should parse as (note True by fail)||(idtac). The other parse fails to
  progress. *)
  note True by fail || idtac.
  auto.
Qed.

(* ====================================================================== *)
(* ====================================================================== *)
(** * Borrowed from LibTactics *)

Set Implicit Arguments.

Require Import Coq.Lists.List.

(* Added instead of LibTactics' custom rapply. *)
Require Import Program.Tactics.

Declare Scope ltac_scope.

(* ********************************************************************** *)
(** * Tools for Programming with Ltac *)

(* ---------------------------------------------------------------------- *)
(** ** Identity Continuation *)

Ltac idcont tt :=
  idtac.

(* ---------------------------------------------------------------------- *)
(** ** Untyped Arguments for Tactics *)

(** Any Coq value can be boxed into the type [Boxer]. This is
    useful to use Coq computations for implementing tactics. *)

Inductive Boxer : Type :=
  | boxer : forall (A:Type), A -> Boxer.


(* ---------------------------------------------------------------------- *)
(** ** Optional Arguments for Tactics  *)

(** [ltac_no_arg] is a constant that can be used to simulate
    optional arguments in tactic definitions.
    Use [mytactic ltac_no_arg] on the tactic invokation,
    and use [match arg with ltac_no_arg => ..] or
    [match type of arg with ltac_No_arg  => ..] to
    test whether an argument was provided. *)

Inductive ltac_No_arg : Set :=
  | ltac_no_arg : ltac_No_arg.


(* ---------------------------------------------------------------------- *)
(** ** Wildcard Arguments for Tactics  *)

(** [ltac_wild] is a constant that can be used to simulate
    wildcard arguments in tactic definitions. Notation is [__]. *)

Inductive ltac_Wild : Set :=
  | ltac_wild : ltac_Wild.

Notation "'__'" := ltac_wild : ltac_scope.

(** [ltac_wilds] is another constant that is typically used to
    simulate a sequence of [N] wildcards, with [N] chosen
    appropriately depending on the context. Notation is [___]. *)

Inductive ltac_Wilds : Set :=
  | ltac_wilds : ltac_Wilds.

Notation "'___'" := ltac_wilds : ltac_scope.

Open Scope ltac_scope.


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

(* [clear_until_mark] is like [gen_until_mark], but clears the hypothesis
   instead. It can be used to clear unwanted hypothesis from inversion, for example. *)
Ltac clear_until_mark :=
  match goal with H: ?T |- _ =>
  match T with
  | ltac_Mark => clear H
  | _ => clear H; clear_until_mark
  end end.


(** [gen_until_mark_with_processing F] is similar to [gen_until_mark]
    except that it calls [F] on each hypothesis immediately before
    generalizing it. This is useful for processing the hypotheses. *)

Ltac gen_until_mark_with_processing cont :=
  match goal with H: ?T |- _ =>
  match T with
  | ltac_Mark => clear H
  | _ => cont H; generalize H; clear H;
         gen_until_mark_with_processing cont
  end end.

(** [intro_until_mark] repeats [intro] until reaching an hypothesis of
    type [Mark]. It throws away the hypothesis [Mark].
    It fails if [Mark] does not appear as an hypothesis in the
    goal. *)

Ltac intro_until_mark :=
  match goal with
  | |- (ltac_Mark -> _) => intros _
  | _ => intro; intro_until_mark
  end.


(* ---------------------------------------------------------------------- *)
(** ** List of Arguments for Tactics  *)

(** A datatype of type [list Boxer] is used to manipulate list of
    Coq values in ltac. Notation is [>> v1 v2 ... vN] for building
    a list containing the values [v1] through [vN]. *)
(* Note: could attempt the use of a recursive notation *)

Notation "'>>'" :=
  (@nil Boxer)
  (at level 0)
  : ltac_scope.
Notation "'>>' v1" :=
  ((boxer v1)::nil)
  (at level 0, v1 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2" :=
  ((boxer v1)::(boxer v2)::nil)
  (at level 0, v1 at level 0, v2 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3 v4" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5 v6" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
   ::(boxer v6)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5 v6 v7" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
   ::(boxer v6)::(boxer v7)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
   ::(boxer v6)::(boxer v7)::(boxer v8)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
   v8 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8 v9" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
   ::(boxer v6)::(boxer v7)::(boxer v8)::(boxer v9)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
   v8 at level 0, v9 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8 v9 v10" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
   ::(boxer v6)::(boxer v7)::(boxer v8)::(boxer v9)::(boxer v10)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
   v8 at level 0, v9 at level 0, v10 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
   ::(boxer v6)::(boxer v7)::(boxer v8)::(boxer v9)::(boxer v10)
   ::(boxer v11)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
   v8 at level 0, v9 at level 0, v10 at level 0, v11 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
   ::(boxer v6)::(boxer v7)::(boxer v8)::(boxer v9)::(boxer v10)
   ::(boxer v11)::(boxer v12)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
   v8 at level 0, v9 at level 0, v10 at level 0, v11 at level 0,
   v12 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
   ::(boxer v6)::(boxer v7)::(boxer v8)::(boxer v9)::(boxer v10)
   ::(boxer v11)::(boxer v12)::(boxer v13)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
   v8 at level 0, v9 at level 0, v10 at level 0, v11 at level 0,
   v12 at level 0, v13 at level 0)
  : ltac_scope.

(** The tactic [list_boxer_of] inputs a term [E] and returns a term
    of type "list boxer", according to the following rules:
    - if [E] is already of type "list Boxer", then it returns [E];
    - otherwise, it returns the list [(boxer E)::nil]. *)
Ltac list_boxer_of E :=
  match type of E with
  | List.list Boxer => constr:(E)
  | _ => constr:((boxer E)::nil)
  end.

(* ---------------------------------------------------------------------- *)
(** ** On-the-Fly Removal of Hypotheses *)

(** In a list of arguments [>> H1 H2 .. HN] passed to a tactic
    such as [lets] or [applys] or [forwards] or [specializes],
    the term [rm], an identity function, can be placed in front
    of the name of an hypothesis to be deleted. *)

Definition rm (A:Type) (X:A) := X.

(** [rm_term E] removes one hypothesis that admits the same
    type as [E]. *)

Ltac rm_term E :=
  let T := type of E in
  match goal with H: T |- _ => try clear H end.

(** [rm_inside E] calls [rm_term Ei] for any subterm
    of the form [rm Ei] found in E *)

Ltac rm_inside E :=
  let go E := rm_inside E in
  match E with
  | rm ?X => rm_term X
  | ?X1 ?X2 =>
     go X1; go X2
  | ?X1 ?X2 ?X3 =>
     go X1; go X2; go X3
  | ?X1 ?X2 ?X3 ?X4 =>
     go X1; go X2; go X3; go X4
  | ?X1 ?X2 ?X3 ?X4 ?X5 =>
     go X1; go X2; go X3; go X4; go X5
  | ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 =>
     go X1; go X2; go X3; go X4; go X5; go X6
  | ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7 =>
     go X1; go X2; go X3; go X4; go X5; go X6; go X7
  | ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7 ?X8 =>
     go X1; go X2; go X3; go X4; go X5; go X6; go X7; go X8
  | ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7 ?X8 ?X9 =>
     go X1; go X2; go X3; go X4; go X5; go X6; go X7; go X8; go X9
  | ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7 ?X8 ?X9 ?X10 =>
     go X1; go X2; go X3; go X4; go X5; go X6; go X7; go X8; go X9; go X10
  | _ => idtac
  end.

(** For faster performance, one may deactivate [rm_inside] by
    replacing the body of this definition with [idtac]. *)

Ltac fast_rm_inside E :=
  rm_inside E.

(* ---------------------------------------------------------------------- *)
(** ** Testing evars and non-evars *)

(** [is_not_evar E] succeeds only if [E] is not an evar;
    it fails otherwise. It thus implements the negation of [is_evar] *)

Ltac is_not_evar E :=
  first [ is_evar E; fail 1
        | idtac ].

(** [is_evar_as_bool E] evaluates to [true] if [E] is an evar
    and to [false] otherwise. *)

Ltac is_evar_as_bool E :=
  constr:(ltac:(first
    [ is_evar E; exact true
    | exact false ])).

(** [has_no_evar E] succeeds if [E] contains no evars. *)

Ltac has_no_evar E :=
  first [ has_evar E; fail 1 | idtac ].


(* ---------------------------------------------------------------------- *)
(** ** Check No Evar in Goal *)

Ltac check_noevar M :=
  first [ has_evar M; fail 2 | idtac ].

Ltac check_noevar_hyp H :=
  let T := type of H in check_noevar T.

Ltac check_noevar_goal :=
  match goal with |- ?G => check_noevar G end.

(* ********************************************************************** *)
(** * Backward and Forward Chaining *)

(* ---------------------------------------------------------------------- *)
(** ** Application *)

(** [lets_base H E] adds an hypothesis [H : T] to the context, where [T] is
    the type of term [E]. If [H] is an introduction pattern, it will
    destruct [H] according to the pattern. *)

Ltac lets_base I E := generalize E; intros I.

(** [applys_to H E] transform the type of hypothesis [H] by
    replacing it by the result of the application of the term
    [E] to [H]. Intuitively, it is equivalent to [lets H: (E H)]. *)

Tactic Notation "applys_to" hyp(H) constr(E) :=
  let H' := fresh "TEMP" in rename H into H';
  (first [ lets_base H (E H')
         | lets_base H (E _ H')
         | lets_base H (E _ _ H')
         | lets_base H (E _ _ _ H')
         | lets_base H (E _ _ _ _ H')
         | lets_base H (E _ _ _ _ _ H')
         | lets_base H (E _ _ _ _ _ _ H')
         | lets_base H (E _ _ _ _ _ _ _ H')
         | lets_base H (E _ _ _ _ _ _ _ _ H')
         | lets_base H (E _ _ _ _ _ _ _ _ _ H') ]
  ); clear H'.

(** [applys_to H1,...,HN E] applys [E] to several hypotheses *)

Tactic Notation "applys_to" hyp(H1) "," hyp(H2) constr(E) :=
  applys_to H1 E; applys_to H2 E.
Tactic Notation "applys_to" hyp(H1) "," hyp(H2) "," hyp(H3) constr(E) :=
  applys_to H1 E; applys_to H2 E; applys_to H3 E.
Tactic Notation "applys_to" hyp(H1) "," hyp(H2) "," hyp(H3) "," hyp(H4) constr(E) :=
  applys_to H1 E; applys_to H2 E; applys_to H3 E; applys_to H4 E.

(* ---------------------------------------------------------------------- *)
(** ** Instantiation and Forward-Chaining *)

(** The instantiation tactics are used to instantiate a lemma [E]
    (whose type is a product) on some arguments. The type of [E] is
    made of implications and universal quantifications, e.g.
    [forall x, P x -> forall y z, Q x y z -> R z].

    The first possibility is to provide arguments in order: first [x],
    then a proof of [P x], then [y] etc... In this mode, called "Args",
    all the arguments are to be provided. If a wildcard is provided
    (written [__]), then an existential variable will be introduced in
    place of the argument.

    It is very convenient to give some arguments the lemma should be
    instantiated on, and let the tactic find out automatically where
    underscores should be insterted. Underscore arguments [__] are
    interpret as follows: an underscore means that we want to skip the
    argument that has the same type as the next real argument provided
    (real means not an underscore). If there is no real argument after
    underscore, then the underscore is used for the first possible argument.

    The general syntax is [tactic (>> E1 .. EN)] where [tactic] is
    the name of the tactic (possibly with some arguments) and [Ei]
    are the arguments. Moreover, some tactics accept the syntax
    [tactic E1 .. EN] as short for [tactic (>> E1 .. EN)] for
    values of [N] up to 5.

    Finally, if the argument [EN] given is a triple-underscore [___],
    then it is equivalent to providing a list of wildcards, with
    the appropriate number of wildcards. This means that all
    the remaining arguments of the lemma will be instantiated.
    Definitions in the conclusion are not unfolded in this case. *)

(* Underlying implementation *)

Ltac app_assert t P cont :=
  let H := fresh "TEMP" in
  assert (H : P); [ | cont(t H); clear H ].

Ltac app_evar t A cont :=
  let x := fresh "TEMP" in
  evar (x:A);
  let t' := constr:(t x) in
  let t'' := (eval unfold x in t') in
  subst x; cont t''.

Ltac app_arg t P v cont :=
  let H := fresh "TEMP" in
  assert (H : P); [ apply v | cont(t H); try clear H ].

Ltac build_app_alls t final :=
  let rec go t :=
    match type of t with
    | ?P -> ?Q => app_assert t P go
    | forall _:?A, _ => app_evar t A go
    | _ => final t
    end in
  go t.

Ltac boxerlist_next_type vs :=
  match vs with
  | nil => constr:(ltac_wild)
  | (boxer ltac_wild)::?vs' => boxerlist_next_type vs'
  | (boxer ltac_wilds)::_ => constr:(ltac_wild)
  | (@boxer ?T _)::_ => constr:(T)
  end.

(* Note: refuse to instantiate a dependent hypothesis with a proposition;
    refuse to instantiate an argument of type Type with one that
    does not have the type Type.
*)

Ltac build_app_hnts t vs final :=
  let rec go t vs :=
    match vs with
    | nil => first [ final t | fail 1 ]
    | (boxer ltac_wilds)::_ => first [ build_app_alls t final | fail 1 ]
    | (boxer ?v)::?vs' =>
      let cont t' := go t' vs in
      let cont' t' := go t' vs' in
      let T := type of t in
      let T := eval hnf in T in
      match v with
      | ltac_wild =>
         first [ let U := boxerlist_next_type vs' in
           match U with
           | ltac_wild =>
             match T with
             | ?P -> ?Q => first [ app_assert t P cont' | fail 3 ]
             | forall _:?A, _ => first [ app_evar t A cont' | fail 3 ]
             end
           | _ =>
             match T with  (* should test T for unifiability *)
             | U -> ?Q => first [ app_assert t U cont' | fail 3 ]
             | forall _:U, _ => first [ app_evar t U cont' | fail 3 ]
             | ?P -> ?Q => first [ app_assert t P cont | fail 3 ]
             | forall _:?A, _ => first [ app_evar t A cont | fail 3 ]
             end
           end
         | fail 2 ]
      | _ =>
          match T with
          | ?P -> ?Q => first [ app_arg t P v cont'
                              | app_assert t P cont
                              | fail 3 ]
           | forall _:Type, _ =>
              match type of v with
              | Type => first [ cont' (t v)
                              | app_evar t Type cont
                              | fail 3 ]
              | _ => first [ app_evar t Type cont
                           | fail 3 ]
              end
          | forall _:?A, _ =>
             let V := type of v in
             match type of V with
             | Prop =>  first [ app_evar t A cont
                              | fail 3 ]
             | _ => first [ cont' (t v)
                          | app_evar t A cont
                          | fail 3 ]
             end
          end
      end
    end in
  go t vs.


(** newer version : support for typeclasses *)

Ltac app_typeclass t cont :=
  let t' := constr:(t _) in
  cont t'.

Ltac build_app_alls t final ::=
  let rec go t :=
    match type of t with
    | ?P -> ?Q => app_assert t P go
    | forall _:?A, _ =>
        first [ app_evar t A go
              | app_typeclass t go
              | fail 3 ]
    | _ => final t
    end in
  go t.

Ltac build_app_hnts t vs final ::=
  let rec go t vs :=
    match vs with
    | nil => first [ final t | fail 1 ]
    | (boxer ltac_wilds)::_ => first [ build_app_alls t final | fail 1 ]
    | (boxer ?v)::?vs' =>
      let cont t' := go t' vs in
      let cont' t' := go t' vs' in
      let T := type of t in
      let T := eval hnf in T in
      match v with
      | ltac_wild =>
         first [ let U := boxerlist_next_type vs' in
           match U with
           | ltac_wild =>
             match T with
             | ?P -> ?Q => first [ app_assert t P cont' | fail 3 ]
             | forall _:?A, _ => first [ app_typeclass t cont'
                                       | app_evar t A cont'
                                       | fail 3 ]
             end
           | _ =>
             match T with  (* should test T for unifiability *)
             | U -> ?Q => first [ app_assert t U cont' | fail 3 ]
             | forall _:U, _ => first
                 [ app_typeclass t cont'
                 | app_evar t U cont'
                 | fail 3 ]
             | ?P -> ?Q => first [ app_assert t P cont | fail 3 ]
             | forall _:?A, _ => first
                 [ app_typeclass t cont
                 | app_evar t A cont
                 | fail 3 ]
             end
           end
         | fail 2 ]
      | _ =>
          match T with
          | ?P -> ?Q => first [ app_arg t P v cont'
                              | app_assert t P cont
                              | fail 3 ]
           | forall _:Type, _ =>
              match type of v with
              | Type => first [ cont' (t v)
                              | app_evar t Type cont
                              | fail 3 ]
              | _ => first [ app_evar t Type cont
                           | fail 3 ]
              end
          | forall _:?A, _ =>
             let V := type of v in
             match type of V with
             | Prop => first [ app_typeclass t cont
                              | app_evar t A cont
                              | fail 3 ]
             | _ => first [ cont' (t v)
                          | app_typeclass t cont
                          | app_evar t A cont
                          | fail 3 ]
             end
          end
      end
    end in
  go t vs.
  (* --Note: use local function for first [...] *)


Ltac build_app args final :=
  first [
    match args with (@boxer ?T ?t)::?vs =>
      let t := constr:(t:T) in
      build_app_hnts t vs final;
      fast_rm_inside args
    end
  | fail 1 "Instantiation fails for:" args].

Ltac unfold_head_until_product T :=
  eval hnf in T.

Ltac args_unfold_head_if_not_product args :=
  match args with (@boxer ?T ?t)::?vs =>
    let T' := unfold_head_until_product T in
    constr:((@boxer T' t)::vs)
  end.

Ltac args_unfold_head_if_not_product_but_params args :=
  match args with
  | (boxer ?t)::(boxer ?v)::?vs =>
     args_unfold_head_if_not_product args
  | _ => constr:(args)
  end.

(** [lets H: (>> E0 E1 .. EN)] will instantiate lemma [E0]
    on the arguments [Ei] (which may be wildcards [__]),
    and name [H] the resulting term. [H] may be an introduction
    pattern, or a sequence of introduction patterns [I1 I2 IN],
    or empty.
    Syntax [lets H: E0 E1 .. EN] is also available. If the last
    argument [EN] is [___] (triple-underscore), then all
    arguments of [H] will be instantiated. *)

Ltac lets_build I Ei :=
  let args := list_boxer_of Ei in
  let args := args_unfold_head_if_not_product_but_params args in
(*    let Ei''' := args_unfold_head_if_not_product Ei'' in*)
  build_app args ltac:(fun R => lets_base I R).

Tactic Notation "lets" simple_intropattern(I) ":" constr(E) :=
  lets_build I E.
Tactic Notation "lets" ":" constr(E) :=
  let H := fresh in lets H: E.
Tactic Notation "lets" ":" constr(E0)
 constr(A1) :=
  lets: (>> E0 A1).
Tactic Notation "lets" ":" constr(E0)
 constr(A1) constr(A2) :=
  lets: (>> E0 A1 A2).
Tactic Notation "lets" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  lets: (>> E0 A1 A2 A3).
Tactic Notation "lets" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  lets: (>> E0 A1 A2 A3 A4).
Tactic Notation "lets" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  lets: (>> E0 A1 A2 A3 A4 A5).

(* DEPRECATED syntax [lets I1 I2] *)
Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2)
 ":" constr(E) :=
  lets [I1 I2]: E.
Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) ":" constr(E) :=
  lets [I1 [I2 I3]]: E.
Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) ":" constr(E) :=
  lets [I1 [I2 [I3 I4]]]: E.
Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 ":" constr(E) :=
  lets [I1 [I2 [I3 [I4 I5]]]]: E.

Tactic Notation "lets" simple_intropattern(I) ":" constr(E0)
 constr(A1) :=
  lets I: (>> E0 A1).
Tactic Notation "lets" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) :=
  lets I: (>> E0 A1 A2).
Tactic Notation "lets" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  lets I: (>> E0 A1 A2 A3).
Tactic Notation "lets" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  lets I: (>> E0 A1 A2 A3 A4).
Tactic Notation "lets" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  lets I: (>> E0 A1 A2 A3 A4 A5).

Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2) ":" constr(E0)
 constr(A1) :=
  lets [I1 I2]: E0 A1.
Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2) ":" constr(E0)
 constr(A1) constr(A2) :=
  lets [I1 I2]: E0 A1 A2.
Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  lets [I1 I2]: E0 A1 A2 A3.
Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  lets [I1 I2]: E0 A1 A2 A3 A4.
Tactic Notation "lets" simple_intropattern(I1) simple_intropattern(I2) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  lets [I1 I2]: E0 A1 A2 A3 A4 A5.


(** [forwards H: (>> E0 E1 .. EN)] is short for
    [forwards H: (>> E0 E1 .. EN ___)].
    The arguments [Ei] can be wildcards [__] (except [E0]).
    [H] may be an introduction pattern, or a sequence of
    introduction pattern, or empty.
    Syntax [forwards H: E0 E1 .. EN] is also available. *)

Ltac forwards_build_app_arg Ei :=
  let args := list_boxer_of Ei in
  let args := (eval simpl in (args ++ ((boxer ___)::nil))) in
  let args := args_unfold_head_if_not_product args in
  args.

Ltac forwards_then Ei cont :=
  let args := forwards_build_app_arg Ei in
  let args := args_unfold_head_if_not_product_but_params args in
  build_app args cont.

Tactic Notation "forwards" simple_intropattern(I) ":" constr(Ei) :=
  let args := forwards_build_app_arg Ei in
  lets I: args.

Tactic Notation "forwards" ":" constr(E) :=
  let H := fresh in forwards H: E.
Tactic Notation "forwards" ":" constr(E0)
 constr(A1) :=
  forwards: (>> E0 A1).
Tactic Notation "forwards" ":" constr(E0)
 constr(A1) constr(A2) :=
  forwards: (>> E0 A1 A2).
Tactic Notation "forwards" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  forwards: (>> E0 A1 A2 A3).
Tactic Notation "forwards" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  forwards: (>> E0 A1 A2 A3 A4).
Tactic Notation "forwards" ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  forwards: (>> E0 A1 A2 A3 A4 A5).

(* --DEPRECATED syntax *)
Tactic Notation "forwards" simple_intropattern(I1) simple_intropattern(I2)
 ":" constr(E) :=
  forwards [I1 I2]: E.
Tactic Notation "forwards" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) ":" constr(E) :=
  forwards [I1 [I2 I3]]: E.
Tactic Notation "forwards" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) ":" constr(E) :=
  forwards [I1 [I2 [I3 I4]]]: E.
Tactic Notation "forwards" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 ":" constr(E) :=
  forwards [I1 [I2 [I3 [I4 I5]]]]: E.

Tactic Notation "forwards" simple_intropattern(I) ":" constr(E0)
 constr(A1) :=
  forwards I: (>> E0 A1).
Tactic Notation "forwards" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) :=
  forwards I: (>> E0 A1 A2).
Tactic Notation "forwards" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) :=
  forwards I: (>> E0 A1 A2 A3).
Tactic Notation "forwards" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  forwards I: (>> E0 A1 A2 A3 A4).
Tactic Notation "forwards" simple_intropattern(I) ":" constr(E0)
 constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  forwards I: (>> E0 A1 A2 A3 A4 A5).

(** [applys (>> E0 E1 .. EN)] instantiates lemma [E0]
    on the arguments [Ei] (which may be wildcards [__]),
    and apply the resulting term to the current goal,
    using the tactic [applys] defined earlier on.
    [applys E0 E1 E2 .. EN] is also available. *)

Ltac applys_build Ei :=
  let args := list_boxer_of Ei in
  let args := args_unfold_head_if_not_product_but_params args in
  build_app args ltac:(fun R =>
   first [ apply R | eapply R | rapply R ]).

Ltac applys_base E :=
  match type of E with
  | list Boxer => applys_build E
  | _ => first [ rapply E | applys_build E ]
  end; fast_rm_inside E.

Tactic Notation "applys" constr(E) :=
  applys_base E.
Tactic Notation "applys" constr(E0) constr(A1) :=
  applys (>> E0 A1).
Tactic Notation "applys" constr(E0) constr(A1) constr(A2) :=
  applys (>> E0 A1 A2).
Tactic Notation "applys" constr(E0) constr(A1) constr(A2) constr(A3) :=
  applys (>> E0 A1 A2 A3).
Tactic Notation "applys" constr(E0) constr(A1) constr(A2) constr(A3) constr(A4) :=
  applys (>> E0 A1 A2 A3 A4).
Tactic Notation "applys" constr(E0) constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  applys (>> E0 A1 A2 A3 A4 A5).


(* ====================================================================== *)
(* ====================================================================== *)
(** * Borrowed from
      https://gitlab.mpi-sws.org/iris/stdpp/-/blob/master/theories/tactics.v *)

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

Tactic Notation "inversion" "select" open_constr(pat) :=
  select pat (fun H => inversion H).

Tactic Notation "destruct" "select" open_constr(pat) :=
  select pat (fun H => destruct H).

Tactic Notation "destruct" "select" open_constr(pat) "as" simple_intropattern(destruct_pat) :=
  select pat (fun H => destruct H as destruct_pat).
