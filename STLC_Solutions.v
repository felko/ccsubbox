(*************************************************************************)
(** The simply-typed lambda calculus in Coq. *)
(*************************************************************************)

(** An interactive tutorial on developing programming language
    metatheory.  This file uses the simply-typed lambda calculus
    (STLC) to demonstrate the locally nameless representation of
    lambda terms and cofinite quantification in judgments.

    This tutorial concentrates on "how" to formalize STLC; for more
    details about "why" we use this style of development see:
    "Engineering Formal Metatheory", Aydemir, Charguéraud, Pierce,
    Pollack, Weirich. POPL 2008.

    Tutorial authors: Brian Aydemir and Stephanie Weirich, with help
    from Aaron Bohannon, Nate Foster, Benjamin Pierce, Jeffrey
    Vaughan, Dimitrios Vytiniotis, and Steve Zdancewic.  Adapted from
    code by Arthur Charguéraud.
*)

(*************************************************************************)
(** * Contents
    - Syntax of STLC
    - Substitution
    - Free variables
    - Open
    - Local closure
    - Properties about basic operations
    - Cofinite quantification
    - Tactic support
    - Typing environments
    - Typing relation
    - Weakening
    - Substitution
    - Values and evaluation
    - Preservation
    - Progress
    - Additional properties

  Solutions to exercises are in [STLC_Solutions.v].
*)
(*************************************************************************)

(* First, we import a number of definition from the Metatheory
   library (see Metatheory.v). The following command makes those
   definitions available in the rest of this file. This command
   will only succeed if you have already run "make" in the tutorial
   directory to compile the Metatheory library.
*)
Require Import Metatheory.

(*************************************************************************)
(** * Syntax of STLC *)
(*************************************************************************)

(** We use a locally nameless representation for the simply-typed
    lambda calculus, where bound variables are represented as natural
    numbers (de Bruijn indices) and free variables are represented as
    [atom]s.  The type [atom], defined in the [Atom] library,
    represents names: equality is decidable on atoms (eq_atom_dec), 
    and it is possible to generate an atom fresh for any given 
    finite set of atoms (atom_fresh_for_set).
*)

Inductive typ : Set :=
  | typ_base  : typ
  | typ_arrow : typ -> typ -> typ.

Inductive exp : Set :=
  | bvar : nat  -> exp    (* bound variables *)
  | fvar : atom -> exp   (* free  variables *)
  | abs  : exp  -> exp
  | app  : exp  -> exp -> exp.

Coercion bvar : nat >-> exp.
Coercion fvar : atom >-> exp.

(** We declare the constructors for indices and variables to be
    coercions. That way, if Coq sees a [nat] where it expects an
    [exp], it will implicitly insert an application of [bvar]; and
    similarly for [atom]s.
*)


(** For example, we can encode the expression (\x. Y x) as below. *)
(** Because "Y" is free variable in this term, we need to assume an
    atom for this name.
*)

Parameter Y : atom.
Definition demo_rep1 := abs (app Y 0).

(** Note that because of the coercions we may write
    [abs (app Y 0)] instead of [abs (app (fvar Y) (bvar 0))]. 
*)

(** Another example: the encoding of (\x. \y. (y x)) *)
Definition demo_rep2 := abs (abs (app 0 1)).

(** *** Exercise [two] *)

(** Convert the following lambda calculus term to locally nameless
representation.
*)

(** "two"    \s. \z. s(s z) **)

Definition two := abs (abs (app 1 (app 1 0))).

(** There are two important advantages of the locally nameless
    representation:
     - Alpha-equivalent terms have a unique representation, 
       we're always working up to alpha-equivalence.
     - Operations such as free variable substitution and free
       variable calculation have simple recursive definitions
      (and therefore are simple to reason about).

    Weighed against these advantages are two drawbacks:
     - The [exp] datatype admits terms, such as [abs 3], where
       indices are unbound. 
       A term is called "locally closed" when it contains 
       no unbound indices. 
     - We must define *both* bound variable & free variable 
       substitution and reason about how these operations 
       interact with eachother.
    
*)


(*************************************************************************)
(** * Substitution *)
(*************************************************************************)

(** Substitution replaces a free variable with a term.  The definition
    below is simple for two reasons:
      - Because bound variables are represented using indices, there
        is no need to worry about variable capture.
      - We assume that the term being substituted in is locally
        closed.  Thus, there is no need to shift indices when
        passing under a binder.
*)

Fixpoint subst (z : atom) (u : exp) (e : exp) {struct e} : exp :=
  match e with
    | bvar i => bvar i
    | fvar x => if x == z then u else (fvar x)
    | abs e1 => abs (subst z u e1)
    | app e1 e2 => app (subst z u e1) (subst z u e2)
  end.
(** The Fixpoint keyword defines a Coq function. As all functions in 
    Coq must be total, the annotation [{struct e}] indicates the termination 
    metric---all recursive calls in this definition are made to
    arguments that are structurally smaller than [e].
*)

(* Note also that subst uses the notation [x == z] for
   decidable atom equality. (This notation is defined in
   [Metatheory].)
*)

(** We define a notation for free variable substitution that mimics
    standard mathematical notation. *)

Notation "[ z ~> u ] e" := (subst z u e) (at level 68).

(** To demonstrate how free variable substitution works, we
    need to reason about decidable equality.
*)
Parameter Z : atom.
Check (Y == Z).

(** The decidable atom equality function returns a sum. If the
    two atoms are equal, the left branch of the sum is returned,
    carrying a proof of the proposition that the atoms are equal.
    If they are not equal, the right branch includes a proof of
    the disequality.
*)

(** The demo below uses three new tactics:
    - The tactic [simpl] reduces a Coq expression to its normal
      form.
    - The tactic [Case] marks cases in the proof script.
      It takes any string as its argument, and puts that string in
      the hypothesis list until the case is finished.
    - The tactic [destruct (Y==Y)] considers the two possible 
      results of the equality test.
*)

Lemma demo_subst1:  [Y ~> Z] (abs (app 0 Y)) = (abs (app 0 Z)).
Proof.
  simpl.
  destruct (Y==Y).
    Case "left".
      auto.
    Case "right".
      destruct n. auto.
Qed.

(*************************************************************************)
(** * Free variables *)
(*************************************************************************)

(** The function [fv], defined below, calculates the set of free
    variables in an expression.  Because we are using locally nameless
    representation, where bound variables are represented as indices,
    any name we see is a free variable of a term.  In particular, this
    makes the [abs] case simple.
*)

Fixpoint fv (e : exp) {struct e} : atoms :=
  match e with
    | bvar i => {}
    | fvar x => singleton x
    | abs e1 => fv e1
    | app e1 e2 => (fv e1) `union` (fv e2)
  end.

(** The type [atoms] represents a finite set of elements of type [atom],
    and the notations for the empty set and infix union are defined in
    the Metatheory library.
*)

(** *** EXERCISE [subst_fresh] *)

(** To show the ease of reasoning with these definitions, we will
    prove a standard result from lambda calculus: if a variable does
    not appear free in a term, then substituting for it has no
    effect.
*)

Lemma subst_fresh : forall (x : atom) e u,
  x `notin` fv e -> [x ~> u] e = e.
Proof.
  intros x e u H.
  induction e.
  Case "bvar".
   auto.
  Case "fvar".
   simpl.
   destruct (a == x).
    SCase "a=x".
      subst. simpl fv in H. fsetdec.
    SCase "a<>x".
      auto.
  Case "abs".
    simpl.
    f_equal.
    auto.
  Case "app".
    simpl in *.
    f_equal.
    auto.
    auto.
Qed.


(*************************************************************************)
(** * Opening *)
(*************************************************************************)

(** Opening replaces an index with a term. It corresponds to informal
    substitution for a bound variable, such as in the rule for beta
    reduction. Note that only "dangling" indices (those that do not
    refer to any abstraction) can be opened. Opening has no effect for
    terms that are locally closed.

    Natural numbers are just an inductive datatype with two
    constructors: O and S, defined in Coq.Init.Datatypes.
    The notation [k === i] is the decidable equality function for
    natural numbers (cf. Coq.Peano_dec.eq_nat_dec).
    This notation is defined in the [Metatheory] library.

    We make several simplifying assumptions in defining [open_rec].

    First, we assume that the argument [u] is locally closed.  This
    assumption simplifies the implementation since we do not need to
    shift indices in [u] when passing under a binder.  Second, we
    assume that this function is initially called with index zero and
    that zero is the only unbound index in the term.  This eliminates
    the need to possibly subtract one in the case of indices.

    There is no need to worry about variable capture because bound
    variables are indices.
*)

Fixpoint open_rec (k : nat) (u : exp) (e : exp) {struct e} : exp :=
  match e with
    | bvar i => if k === i then u else (bvar i)
    | fvar x => fvar x
    | abs e1 => abs (open_rec (S k) u e1)
    | app e1 e2 => app (open_rec k u e1) (open_rec k u e2)
  end.

(** We also define a notation for [open_rec].
*)

Notation "{ k ~> u } t" := (open_rec k u t) (at level 67).

(** Many common applications of opening replace index zero with an
    expression or variable.  The following definition provides a
    convenient shorthand for such uses.  Note that the order of
    arguments is switched relative to the definition above.  For
    example, [(open e x)] can be read as "substitute the variable [x]
    for index [0] in [e]" and "open [e] with the variable [x]."
    Recall that the coercions above let us write [x] in place of
    [(fvar x)].
*)

Definition open e u := open_rec 0 u e.

(** This next demo shows the operation of 'open'.  For example, the
   locally nameless representation of the term (\y. (\x. (y x)) y)
   is [abs (app (abs (app 1 0)) 0)]. To look at the body
   without the outer abstraction, we need to replace the indices that
   refer to that abstraction with a name.
   Therefore, we show that we can open the body of the abs above
   with Y to produce [app (abs (app Y 0)) Y)].
*)

Lemma demo_open :
  open (app (abs (app 1  0))  0) Y =
       (app (abs (app Y 0)) Y).

Proof.
unfold open.
unfold open_rec.
simpl.
auto.
Qed.

(*************************************************************************)
(*                                                                       *)
(*  Stretch break (5 mins)                                               *)
(*                                                                       *)
(*************************************************************************)

(*************************************************************************)
(** * Local closure *)
(*************************************************************************)

(** Recall that [exp] admits terms that contain unbound indices. 
    We say that a term is locally closed, 
    when no indices appearing in it are unbound.  The proposition 
    [lc e] holds when an expression [e] is locally closed.

    The inductive definition below formalizes local closure such that
    the resulting induction principle serves as the structural
    induction principle over (locally closed) expressions.  In
    particular, unlike induction for type exp, there is no cases
    for bound variables.  Thus, the induction principle corresponds more
    closely to informal practice than the one arising from the
    definition of pre-terms.
*)

Inductive lc : exp -> Prop :=
  | lc_var : forall x,
      lc (fvar x)
  | lc_abs : forall L e,
      (forall x:atom, x `notin` L -> lc (open e x)) ->
      lc (abs e)
  | lc_app : forall e1 e2,
      lc e1 ->
      lc e2 ->
      lc (app e1 e2).

Hint Constructors lc.

(*************************************************************************)
(** Properties about basic operations *)
(*************************************************************************)

(** The first property we would like to show is the analogue to subst_fresh:
    that index substitution has no effect for closed terms.

    Here is an initial attempt at the proof.
*)

Lemma open_rec_lc_0 : forall k u e,
  lc e ->
  e = {k ~> u} e.
Proof.
  intros k u e LC.
  induction LC.
  Case "lc_fvar".
    simpl. auto.
  Case "lc_abs".
    simpl.
    f_equal.
Admitted.

(** At this point there are two problems. Our goal is about substitution 
    for index [S k] in term [e], while our induction hypothesis IHLC only 
    tells use about index [k] in term [open e x].

    To solve the first problem, we generalize our IH over all k.
    That way, when k is incremented in the abs case, it will still apply.
    Below, we use the tactic [generalize dependent] to generalize over
    [k] before using induction.
*)

Lemma open_rec_lc_1 : forall k u e,
  lc e ->
  e = {k ~> u} e.
Proof.
  intros k u e LC.
  generalize dependent k.
  induction LC.
  Case "lc_fvar".
    simpl. auto.
  Case "lc_abs".
    simpl.
    intro k.
    f_equal.
Admitted.

(** At this point we are still stuck because the IH concerns
   [open e x] instead of [e]. The result that
   we need is that if an index substitution has no effect for
   an opened term, then it has no effect for the raw term (as long
   as we are *not* substituting for 0, hence S k below).
<<
   open e x = {S k ~> u}(open e x)  -> e = {S k ~> u} e
>>
   In other words, expanding the definition of open:
<<
   {0 ~> x}e = {S k ~> u}({0 ~> x} e)  -> e = {S k ~> u} e
>>
   Of course, to prove this result, we must generalize
   0 and S k to be any pair of inequal numbers to get a strong
   enough induction hypothesis for the abs case.
 *)


Lemma open_rec_lc_core : forall e j v i u,
  i <> j ->
  {j ~> v} e = {i ~> u} ({j ~> v} e) ->
  e = {i ~> u} e.
Proof with eauto*.
  induction e; intros j v i u Neq H; simpl in *;
      try solve [inversion H; f_equal; eauto].
  Case "bvar".
    destruct (j === n)...
    destruct (i === n)...
Qed.

(** With the help of this lemma, we can complete the proof. *)

Lemma open_rec_lc : forall k u e,
  lc e ->
  e = {k ~> u} e.
Proof.
  intros k u e LC.
  generalize dependent k.
  induction LC.
  Case "lc_fvar".
    simpl. auto.
  Case "lc_abs".
    simpl.
    intro k.
    f_equal.
    unfold open in *.
    pick fresh x for L.
    apply open_rec_lc_core with (i := S k) (j := 0) (u := u) (v := x). auto. auto.
  Case "lc_app".
    intro k. simpl. f_equal. auto. auto.
Qed.

(** *** Take-home Exercise [subst_open_rec] *)

(** The next lemma demonstrates that free variable substitution
   distributes over index substitution.

   The proof of this lemma is by straightforward induction over
   e1. When e1 is a free variable, we need to appeal to
   [open_rec_lc], proved above.
*)

Lemma subst_open_rec : forall e1 e2 u x k,
  lc u ->
  [x ~> u] ({k ~> e2} e1) = {k ~> [x ~> u] e2} ([x ~> u] e1).
Proof.
  induction e1; intros e2 u x k H; simpl in *; f_equal; auto.
  Case "bvar".
    destruct (k === n); auto.
  Case "fvar".
    destruct (a == x); subst; auto.
    apply open_rec_lc; auto.
Qed.

(** *** Exercise [subst_open_var] *)

(** The lemma above is most often used with k = 0 and
    e2 as some fresh variable. Therefore, it simplifies matters
    to define the following useful corollary.
*)

Lemma subst_open_var : forall (x y : atom) u e,
  y <> x ->
  lc u ->
  open ([x ~> u] e) y = [x ~> u] (open e y).
Proof.
  intros x y u e Neq H.
  unfold open.
  rewrite subst_open_rec with (e2 := y).
  simpl.
  destruct (y == x).
    Case "y=x".
    destruct Neq. auto.
    Case "y<>x".
    auto.
  auto.
Qed.

(*************************************************************************)
(** Cofinite quantification *)
(*************************************************************************)

(* In the next example, we will reexamine the definition of
   [lc] in the abs case.

   The lemma [subst_lc] says that local closure is preserved by
   substitution. Let's start working through this proof.
*)

Lemma subst_lc_1 : forall (x : atom) u e,
  lc e ->
  lc u ->
  lc ([x ~> u] e).
Proof.
  intros x u e He Hu.
  induction He.
  Case "lc_fvar".
   simpl.
   destruct (x0 == x).
     auto.
     auto.
  Case "lc_abs".
   simpl.
Admitted.

(** Here we are stuck. We don't know that x0 is not the same as x.

    The solution is to change the *definition* of local closure so that
    we get a different induction principle. Currently, in the lc_abs
    case, we show that an abstraction is locally closed by showing
    that the body is locally closed, after it has been opened with
    one particular variable.

<<
  | lc_abs : forall (x:atom) e,
      lc (open e x) ->
      lc (abs e)
>>

   Therefore, our induction hypothesis in this case only applies to that
   variable. From the hypothesis list in the abs case:

    x0 : atom
    IHHe : lc ([x ~> u]open e x0)

   The problem is that we don't have any assumptions about x0. It
   could very well be equal to x.

   A stronger induction principle provides an IH that applies to many
   variables. In that case, we could pick one that is "fresh enough".
   To do so, we need to edit the above definition of lc and
   replace the type of lc_abs with this one:

<<
  | lc_abs : forall L e,
      (forall x:atom, x `notin` L -> lc (open e x)) ->
      lc (abs e)
>>

  This rule says that to show that an abstraction is locally closed,
  we need to show that the body is closed, after it has been opened
  by any atom x, *except* those in some set L. With this rule, the
  IH in this proof is now:

  H0 : forall x0 : atom, x0 `notin` L -> lc ([x ~> u]open e x0)

  We call this "cofinite quantification" because the IH applies to
  an infinite number of atoms x0, except those in some finite set L.

  Changing the rule in this way does not change what terms are locally
  closed.  (For more details about cofinite-quantification see:
  "Engineering Formal Metatheory", Aydemir, Chargu\u00e9raud, Pierce,
  Pollack, Weirich. POPL 2008.)

  So to complete this proof, make the change to lc_abs above.  Note,
  that you will need to go back to the proof of [open_rec_lc] and
  patch it as well.  To fix that proof, add the line
  [pick fresh x for L.]  immediately before [apply open_rec_lc_core].
  This tactic, defined in [Metatheory], introduces a new atom [x] that
  is known not to be in the set [L].

 You will also have to comment out [subst_lc_1].

  Once these changes have been made, we can complete the proof
  of subst_lc.

*)

Lemma subst_lc : forall (x : atom) u e,
  lc e ->
  lc u ->
  lc ([x ~> u] e).
Proof.
  intros x u e He Hu.
  induction He.
  Case "lc_var".
   simpl.
   destruct (x0 == x).
     auto.
     auto.
  Case "lc_abs".
   simpl.
    apply lc_abs with (L := L `union` singleton x).
    intros x0 Fr.
    rewrite subst_open_var. auto. auto. auto.
  Case "lc_app".
     simpl. auto.
Qed.

(*************************************************************************)
(** * Tactic support *)
(*************************************************************************)

(** When picking a fresh atom or applying a rule that uses cofinite
    quantification, choosing a set of atoms to be fresh for can be
    tedious.  In practice, it is simpler to use a tactic to choose the
    set to be as large as possible.

    The first tactic we define, [gather_atoms], is used to collect
    together all the atoms in the context.  It relies on an auxiliary
    tactic from [Atom.v], [gather_atoms_with], which collects together
    the atoms appearing in objects of a certain type.  The argument to
    [gather_atoms_with] is a function that should return the set of
    atoms appearing in its argument. *)

Ltac gather_atoms :=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : list (atom * typ) => dom x) in
  let D := gather_atoms_with (fun x : exp => fv x) in
  constr:(A `union` B `union` C `union` D).

(** We can use [gather_atoms] to define a variant of the [(pick fresh
    x for L)] tactic, which we call [(pick fresh x)].  The tactic
    chooses an atom fresh for "everything" in the context. *)

Tactic Notation "pick" "fresh" ident(x) :=
  let L := gather_atoms in
  (pick fresh x for L).

(** We can also use [gather_atoms] to define a tactic for applying a
    rule that is defined using cofinite quantification.  The tactic
    [(pick fresh x and apply H)] applies a rule [H], just as the
    [apply] tactic would.  However, the tactic also picks a
    sufficiently fresh name [x] to use.

    Note: We define this tactic in terms of another tactic, [(pick
    fresh x excluding L and apply H)], which is defined and documented
    in [Metatheory.v]. *)

Tactic Notation
      "pick" "fresh" ident(atom_name) "and" "apply" constr(lemma) :=
  let L := gather_atoms in
  pick fresh atom_name excluding L and apply lemma.

(** *** Example

    Below, we reprove [subst_lc] using [(pick fresh and apply)].
    Step through the proof below to see how [(pick fresh and apply)]
    works. *)

Lemma subst_lc_alternate_proof : forall (x : atom) u e,
  lc e ->
  lc u ->
  lc ([x ~> u] e).
Proof.
  intros x u e He Hu.
  induction He.
  Case "fvar".
   simpl.
   destruct (x0 == x).
     auto.
     auto.
  Case "abs".
    simpl.
    pick fresh y and apply lc_abs.
    (* Here, take note of the hypothesis [Fr]. *)
    rewrite subst_open_var. auto. auto. auto.
  Case "app".
     simpl. auto.
Qed.

(*************************************************************************)
(*                                                                       *)
(*  Coffee break (30 mins)                                               *)
(*                                                                       *)
(*************************************************************************)

(*************************************************************************)
(** * Typing environments *)
(*************************************************************************)

(** We represent environments as association lists (lists of pairs of
    keys and values) whose keys are [atom]s.  New bindings are added
    to the head of the list.

    Lists are defined in Coq's standard library. *)

Print list.

(** Here, environments bind [atom]s to [typ]s.  We define an
    abbreviation [env] for the type of these environments.  Coq will
    print [list (atom * typ)] as [env], and we can use [env] as a
    shorthand for writing [list (atom * typ)]. *)

Notation env := (list (atom * typ)).

(** The [Environment] library, which is included by the [Metatheory]
    library, provides functions, predicates, tactics, and lemmas that
    simplify working with environments.  Note that everything in the
    library is polymorphic over the type of objects bound in the
    environment.  Look in [Environment.v] for additional details about
    the functions and predicates that we mention below.

    The function [dom] computes the domain of an environment,
    returning a finite set of [atom]s. *)

Check dom.

(** The unary predicate [ok] holds when each atom is bound at most
    once in an environment. *)

Print ok.

(** The ternary predicate [binds] holds when a given binding is
    present in an environment.  More specifically, [binds x a E] holds
    when the binding for [x] closest to the head of [E] binds [x] to
    [a]. *)

Check binds.

(*************************************************************************)
(** * Typing relation *)
(*************************************************************************)

(** The definition of the typing relation is straightforward.  In
    order to ensure that the relation holds for only well-formed
    environments, we check in the [typing_var] case that the
    environment is [ok].  The structure of typing derivations
    implicitly ensures that the relation holds only for locally closed
    expressions.  Finally, note the use of cofinite quantification in
    the [typing_abs] case. *)

Inductive typing : env -> exp -> typ -> Prop :=
  | typing_var : forall E (x : atom) T,
      ok E ->
      binds x T E ->
      typing E (fvar x) T
  | typing_abs : forall L E e T1 T2,
      (forall x : atom, x `notin` L ->
        typing ((x, T1) :: E) (open e x) T2) ->
      typing E (abs e) (typ_arrow T1 T2)
  | typing_app : forall E e1 e2 T1 T2,
      typing E e1 (typ_arrow T1 T2) ->
      typing E e2 T1 ->
      typing E (app e1 e2) T2.

(** We add the constructors of the typing relation as hints to be used
    by the [auto] and [eauto] tactics. *)

Hint Constructors typing.

(*************************************************************************)
(** * Weakening *)
(*************************************************************************)

(** Weakening states that if an expression is typeable in some
    environment, then it is typeable in any well-formed extension of
    that environment.  This property is needed to prove the
    substitution lemma.

    As stated below, this lemma is not directly proveable.  The
    natural way to try proving this lemma proceeds by induction on the
    typing derivation for [e]. *)

Lemma typing_weakening_0 : forall E F e T,
  typing E e T ->
  ok (F ++ E) ->
  typing (F ++ E) e T.
Proof.
  intros E F e T H J.
  induction H; eauto.
  Case "typing_abs".
    pick fresh x and apply typing_abs.
    (* ... stuck here ... *)
Admitted.

(** We are stuck in the [typing_abs] case because the induction
    hypothesis [H0] applies only when we weaken the environment at its
    head.  In this case, however, we need to weaken the environment in
    the middle; compare the conclusion at the point where we're stuck
    to the hypothesis [H], which comes from the given typing derivation.

    We can obtain a more useful induction hypothesis by changing the
    statement to insert new bindings into the middle of the
    environment, instead of at the head.  However, the proof still
    gets stuck, as can be seen by examining each of the cases in
    the proof below.

    Note: To view subgoal n in a proof, use the command "[Show n]".
    To work on subgoal n instead of the first one, use the command
    "[Focus n]". *)

Lemma typing_weakening_strengthened_0 : forall E F G e T,
  typing (G ++ E) e T ->
  ok (G ++ F ++ E) ->
  typing (G ++ F ++ E) e T.
Proof.
  intros E F G e T H J.
  induction H.
  (* ... the E0 looks strange in the [typing_var] case ... *)
  (* ... the [typing_abs] case still does not have a strong enough IH ... *)
Admitted.

(** The hypotheses in the [typing_var] case include an environment
    [E0] that that has no relation to what we need to prove.  The
    missing fact we need is that [E0 = (G ++ E)].

    The problem here arises from the fact that Coq's [induction]
    tactic let's us only prove something about all typing derivations.
    While it's clear to us that weakening applies to all typing
    derivations, it's not clear to Coq, because the environment is
    written using concatenation.  The [induction] tactic expects that
    all arguments to a judgement are variables.  So we see [E0] in the
    proof instead of [(G ++ E)].

    The solution is to restate the lemma.  For example, we can prove

<<
  forall E F E' e T, typing E' e T ->
  forall G, E' = G ++ E -> ok (G ++ F ++ E) -> typing (G ++ F ++ E) e T.
>>

    The equality gets around the problem with Coq's [induction]
    tactic.  The placement of the [(forall G)] quantifier gives us a
    sufficiently strong induction hypothesis in the [typing_abs] case.

    However, we prefer not to state the lemma in the way shown above,
    since it is not as readable as the original statement.  Instead,
    we use a tactic to introduce the equality within the proof itself.
    The tactic [(remember t as t')] replaces an object [t] with the
    identifier [t'] everywhere in the goal and introduces an equality
    [t' = t] into the context.  It is often combined with [generalize
    dependent], as illustrated below. *)

(** *** Exercise

    See how we use [remember as] in the proof below for weakening.
    Then, complete the proof. *)

Lemma typing_weakening_strengthened :  forall E F G e T,
  typing (G ++ E) e T ->
  ok (G ++ F ++ E) ->
  typing (G ++ F ++ E) e T.
Proof.
  intros E F G e T H.
  remember (G ++ E) as E'.
  generalize dependent G.
  induction H; intros G Eq Ok; subst.
  Case "typing_var".
    apply typing_var.
      apply Ok.
      apply binds_weaken. apply H0. apply Ok.
  Case "typing_abs".
    pick fresh x and apply typing_abs.
    rewrite <- cons_concat_assoc.
    apply H0.
      auto.
      rewrite cons_concat_assoc. reflexivity.
      rewrite cons_concat_assoc. apply ok_cons.
        apply Ok.
        auto.
  Case "typing_app".
    eapply typing_app.
      eapply IHtyping1. reflexivity. apply Ok.
      eapply IHtyping2. reflexivity. apply Ok.
Qed.

(** *** Example

    We can now prove our original statement of weakening.  The only
    interesting step is the use of the lemma [nil_concat], which is
    defined in [Environment.v]. *)

Lemma typing_weakening : forall E F e T,
    typing E e T ->
    ok (F ++ E) ->
    typing (F ++ E) e T.
Proof.
  intros E F e T H J.
  rewrite <- (nil_concat _ (F ++ E)).
  apply typing_weakening_strengthened; auto.
Qed.

(*************************************************************************)
(** * Substitution *)
(*************************************************************************)

(** Having proved weakening, we can now prove the usual substitution
    lemma, which we state both in the form we need and in the
    strengthened form needed to make the proof go through.

<<
  typing_subst : forall E e u S T z,
    typing ((z, S) :: E) e T ->
    typing E u S ->
    typing E ([z ~> u] e) T

  typing_subst_strengthened : forall E F e u S T z,
    typing (F ++ (z, S) :: E) e T ->
    typing E u S ->
    typing (F ++ E) ([z ~> u] e) T
>>

    The proof of the strengthened statement proceeds by induction on
    the given typing derivation for [e].  The most involved case is
    the one for variables; the others follow from the induction
    hypotheses. *)

(** *** Exercise

    Below, we state what needs to be proved in the [typing_var] case
    of the substitution lemma.  Fill in the proof.

    Proof sketch: The proof proceeds by a case analysis on [(x == z)],
    i.e., whether the two variables are the same or not.

      - If [(x = z)], then we need to show [(typing (F ++ E) u T)].
        This follows from the given typing derivation for [u] by
        weakening and the fact that [T] must equal [S].

      - If [(x <> z)], then we need to show [(typing (F ++ E) x T)].
        This follows by the typing rule for variables. *)

Lemma typing_subst_var_case : forall E F u S T z x,
  binds x T (F ++ (z, S) :: E) ->
  ok (F ++ (z, S) :: E) ->
  typing E u S ->
  typing (F ++ E) ([z ~> u] x) T.
Proof.
  intros E F u S T z x H J K.
  simpl.
  destruct (x == z).
  Case "x = z".
    subst.
    assert (T = S).
      eapply binds_mid_eq_cons. apply H. apply J.
    subst.
    apply typing_weakening.
      apply K.
      eapply ok_remove_mid_cons. apply J.
  Case "x <> z".
    apply typing_var.
      eapply ok_remove_mid_cons. apply J.
      eapply binds_remove_mid_cons. apply H. apply n.
Qed.

(** *** Note

    The other two cases of the proof of the substitution lemma are
    relatively straightforward.  However, the case for [typing_abs]
    needs the fact that the typing relation holds only for
    locally-closed expressions. *)

Lemma typing_regular_lc : forall E e T,
  typing E e T -> lc e.
Proof.
  intros E e T H. induction H; eauto.
Qed.

(** *** Exercise

    Complete the proof of the substitution lemma. The proof proceeds
    by induction on the typing derivation for [e].  The initial steps
    should use [remember as] and [generalize dependent] in a manner
    similar to the proof of weakening. *)

Lemma typing_subst_strengthened : forall E F e u S T z,
  typing (F ++ (z, S) :: E) e T ->
  typing E u S ->
  typing (F ++ E) ([z ~> u] e) T.
Proof.
  intros E F e u S T z He Hu.
  remember (F ++ (z, S) :: E) as E'.
  generalize dependent F.
  induction He.
  Case "typing_var".
    intros F Eq.
    subst.
    eapply typing_subst_var_case. apply H0. apply H. apply Hu.
  Case "typing_abs".
    intros F Eq.
    subst.
    simpl.
    pick fresh y and apply typing_abs.
    rewrite subst_open_var.
    rewrite <- cons_concat_assoc.
    apply H0.
      auto.
      rewrite cons_concat_assoc. auto.
    (* The following subgoals are from [rewrite subst_open_var]. *)
    auto.
    eapply typing_regular_lc. apply Hu.
  Case "typing_app".
    intros F Eq. subst. simpl. eapply typing_app.
      apply IHHe1. reflexivity.
      apply IHHe2. reflexivity.
Qed.

(** *** Exercise

    Complete the proof of the substitution lemma stated in the form we
    need it.  The proof is similar to that of [typing_weakening].  In
    particular, recall the lemma [nil_concat]. *)

Lemma typing_subst : forall E e u S T z,
  typing ((z, S) :: E) e T ->
  typing E u S ->
  typing E ([z ~> u] e) T.
Proof.
  intros E e u S T z H J.
  rewrite <- (nil_concat _ E).
  eapply typing_subst_strengthened.
    rewrite nil_concat. apply H.
    apply J.
Qed.

(*************************************************************************)
(** * Values and Evaluation *)
(*************************************************************************)

(** In order to state the preservation lemma, we first need to define
    values and the small-step evaluation relation.  These inductive
    relations are straightforward to define.

    Note the hypotheses which ensure that the relations hold only for
    locally closed terms.  Below, we prove that this is actually the
    case, since it is not completely obvious from the definitions
    alone. *)

Inductive value : exp -> Prop :=
  | value_abs : forall e,
      lc (abs e) ->
      value (abs e).

Inductive eval : exp -> exp -> Prop :=
  | eval_beta : forall e1 e2,
      lc (abs e1) ->
      value e2 ->
      eval (app (abs e1) e2) (open e1 e2)
  | eval_app_1 : forall e1 e1' e2,
      lc e2 ->
      eval e1 e1' ->
      eval (app e1 e2) (app e1' e2)
  | eval_app_2 : forall e1 e2 e2',
      value e1 ->
      eval e2 e2' ->
      eval (app e1 e2) (app e1 e2').

(** We add the constructors for these two relations as hints to be used
    by Coq's [auto] and [eauto] tactics. *)

Hint Constructors value eval.

(*************************************************************************)
(** * Preservation *)
(*************************************************************************)

(** *** Note

    In order to prove preservation, we need one more lemma, which
    states that when we open a term, we can instead open the term with
    a fresh variable and then substitute for that variable.

    Technically, the [(lc u)] hypothesis is not needed to prove the
    conclusion.  However, it makes the proof simpler. *)

Lemma subst_intro : forall (x : atom) u e,
  x `notin` (fv e) ->
  lc u ->
  open e u = [x ~> u](open e x).
Proof.
  intros x u e H J.
  unfold open.
  rewrite subst_open_rec; auto.
  simpl.
  destruct (x == x).
  Case "x = x".
    rewrite subst_fresh; auto.
  Case "x <> x".
    destruct n; auto.
Qed.

(** *** Exercise

    Complete the proof of preservation.  In this proof, we proceed by
    induction on the given typing derivation.  The induction
    hypothesis has already been appropriately generalized by the given
    proof fragment.

    Proof sketch: By induction on the typing derivation for [e].

      - [typing_var] case: Variables don't step.

      - [typing_abs] case: Abstractions don't step.

      - [typing_app] case: By case analysis on how [e] steps. The
        [eval_beta] case is interesting, since it follows by the
        substitution lemma.  The others follow directly from the
        induction hypotheses. *)

Lemma preservation : forall E e e' T,
  typing E e T ->
  eval e e' ->
  typing E e' T.
Proof.
  intros E e e' T H.
  generalize dependent e'.
  induction H; intros e' J.
  Case "typing_var".
    inversion J.
  Case "typing_abs".
    inversion J.
  Case "typing_app".
    inversion J; subst; eauto.
    SCase "eval_beta".
      inversion H; subst.
      pick fresh y.
      rewrite (subst_intro y); auto.
      eapply typing_subst; auto.
      eapply typing_regular_lc; eauto.
Qed.

(*************************************************************************)
(** * Progress *)
(*************************************************************************)

(** *** Exercise

    Complete the proof of the progress lemma.  The induction
    hypothesis has already been appropriately generalized by the given
    proof fragment.

    Proof sketch: By induction on the typing derivation for [e].

      - [typing_var] case: Can't happen; the empty environment doesn't
        bind anything.

      - [typing_abs] case: Abstractions are values.

      - [typing_app] case: Applications reduce.  The result follows
        from an exhaustive case analysis on whether the two components
        of the application step or are values and the fact that a
        value must be an abstraction. *)

Lemma progress : forall e T,
  typing nil e T ->
  value e \/ exists e', eval e e'.
Proof.
  intros e T H.

  (* It will be useful to have a "non-destructed" form of the given
     typing derivation, since [induction] takes apart the derivation
     it is called on. *)
  assert (typing nil e T); auto.

  (* [remember nil as E] fails here because [nil] takes an implicit
     argument that Coq is unable to infer.  By prefixing [nil] with
     [@], we can supply the argument to nil explicitly. *)
  remember (@nil (atom * typ)) as E.

  induction H; subst.

  Case "typing_var".
    inversion H1.
  Case "typing_abs".
    left.
    apply value_abs.
    eapply typing_regular_lc; eauto.
  Case "typing_app".
    right.
    destruct IHtyping1 as [V1 | [e1' Eval1]]; auto.
      destruct IHtyping2 as [V2 | [e2' Eval2]]; auto.
        inversion V1; subst. exists (open e e2); auto.
        exists (app e1 e2'); auto.
      exists (app e1' e2).
        apply eval_app_1.
          eapply typing_regular_lc; eauto.
          assumption.
Qed.

(*************************************************************************)
(** * Additional properties *)
(*************************************************************************)

(** While none of the lemmas below are needed to prove preservation or
    progress, they verify that our relations do indeed hold only for
    locally closed expressions.  This serves as a check that we have
    correctly defined the relations. *)

(** *** Example

    The lemma directly below, [open_abs], is needed to show that the
    evaluation relation holds only for locally closed terms.  The
    proof is straightforward, but we can use it to illustrate another
    feature of Coq's tactic language.

    If we start a proof with "[Proof with tac]" instead of simply
    "[Proof]", every time we end a step with "[...]", Coq will
    automatically apply [tac] to all the subgoals generated by that
    step.  This makes proof scripts somewhat more concise without
    hiding the details of the proof script in some far away
    location. *)

Lemma open_abs : forall e u,
  lc (abs e) ->
  lc u ->
  lc (open e u).
Proof with auto using subst_lc.
  intros e u H J.
  inversion H; subst.
  pick fresh y.
  rewrite (subst_intro y)...
  (* The previous line is equivalent to:
     [rewrite (subst_intro y); auto using subst_lc] *)
Qed.

(** *** Note

    The three lemmas below are straightforward to prove.  They do not
    illustrate any new concepts or tactics. *)

Lemma value_regular : forall e,
  value e -> lc e.
Proof.
  intros e H. induction H; auto.
Qed.

Lemma eval_regular : forall e1 e2,
  eval e1 e2 -> lc e1 /\ lc e2.
Proof.
  intros e1 e2 H. induction H; intuition; auto using value_regular, open_abs.
Qed.

Lemma typing_regular_ok : forall E e T,
  typing E e T -> ok E.
Proof with auto.
  induction 1...
  Case "typing_abs".
    pick fresh x.
    assert (ok ((x, T1) :: E))...
    inversion H1...
Qed.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U") ***
*** End: ***
 *)
