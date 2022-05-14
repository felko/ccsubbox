Require Export TaktikZ.
Require Export Metatheory.
Require Export CaptureSets.
Require Import Coq.Program.Wf.

(* ********************************************************************** *)
(** * #<a name="syntax"></a># Syntax (pre-terms) *)

(** We use a locally nameless representation for Fsub, where bound
    variables are represented as natural numbers (de Bruijn indices)
    and free variables are represented as [atom]s.  The type [atom],
    defined in the [Atom] library, represents names: there are
    infinitely many atoms, equality is decidable on atoms, and it is
    possible to generate an atom fresh for any given finite set of
    atoms.

    We say that the definitions below define pre-types ([typ]) and
    pre-expressions ([exp]), collectively pre-terms, since the
    datatypes admit terms, such as [(typ_all typ_top (typ_bvar 3))],
    where indices are unbound.  A term is locally closed when it
    contains no unbound indices.

    Note that indices for bound type variables are distinct from
    indices for bound expression variables.  We make this explicit in
    the definitions below of the opening operations. *)
Inductive typ : Type :=
  (* C P *)
  | typ_capt : cap -> pretyp -> typ
  (* X *)
  | typ_bvar : nat -> typ
  | typ_fvar : atom -> typ
with pretyp : Type :=
  | typ_top : pretyp
  | typ_arrow : typ -> typ -> pretyp
  | typ_all : typ -> typ -> pretyp.

Inductive exp : Type :=
  | exp_var : var -> exp
  | exp_abs : typ -> exp -> exp
  | exp_app : var -> var -> exp
  | exp_let : exp -> exp -> exp
  | exp_tabs : typ -> exp -> exp
  | exp_tapp : var -> typ -> exp.

(** We declare the constructors for indices and variables to be
    coercions.  For example, if Coq sees a [nat] where it expects an
    [exp], it will implicitly insert an application of [exp_bvar];
    similar behavior happens for [atom]s.  Thus, we may write
    [(exp_abs typ_top (exp_app 0 x))] instead of [(exp_abs typ_top
    (exp_app (exp_bvar 0) (exp_fvar x)))]. *)

Coercion typ_bvar : nat >-> typ.
Coercion typ_fvar : atom >-> typ.
Coercion exp_var : var >-> exp.

(* Coercion cset_bvar : nat >-> cap. *)
(* Coercion cset_fvar : atom >-> cap. *)

(* ********************************************************************** *)
(** * #<a name="open"></a># Opening terms *)

(** Opening replaces an index with a term.  This operation is required
    if we wish to work only with locally closed terms when going under
    binders (e.g., the typing rule for [exp_abs]).  It also
    corresponds to informal substitution for a bound variable, which
    occurs in the rule for beta reduction.

    We need to define three functions for opening due the syntax of
    Fsub, and we name them according to the following convention.
      - [tt]: Denotes an operation involving types appearing in types.
      - [te]: Denotes an operation involving types appearing in
        expressions.
      - [ee]: Denotes an operation involving expressions appearing in
        expressions.

    The notation used below for decidable equality on atoms and
    natural numbers (e.g., [K === J]) is defined in the [Metatheory]
    library.  The order of arguments to each "open" function is the
    same.  For example, [(open_tt_rec K U T)] can be read as
    "substitute [U] for index [K] in [T]."

    Note that we assume that [U] is locally closed (and similarly for
    the other opening functions).  This assumption simplifies the
    implementations of opening by letting us avoid shifting.  Since
    bound variables are indices, there is no need to rename variables
    to avoid capture.  Finally, we assume that these functions are
    initially called with index zero and that zero is the only unbound
    index in the term.  This eliminates the need to possibly subtract
    one in the case of indices. *)

Definition cv (T : typ) : cap :=
  match T with
  | typ_bvar n => {}      (* TODO is there a better way to do this? *)
  | typ_fvar x => `cset_fvar` x (* REVIEW: why is the capture set referring to type variables? *)
  | typ_capt C _ => C
  end.

Fixpoint open_tt_rec (K : nat) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_bvar J => if K === J then U else typ_bvar J
  | typ_fvar X => typ_fvar X
  | typ_capt C P => typ_capt (open_cset K (cv U) C) (open_tpt_rec K U P)
  end
with open_tpt_rec (K : nat) (U : typ) (T : pretyp)  {struct T} : pretyp :=
  match T with
  | typ_top => typ_top
  | typ_arrow T1 T2 => typ_arrow (open_tt_rec K U T1) (open_tt_rec (S K) U T2)
  | typ_all T1 T2 => typ_all (open_tt_rec K U T1) (open_tt_rec (S K) U T2)
  end.

Fixpoint open_te_rec (K : nat) (U : typ) (e : exp) {struct e} : exp :=
  match e with
  | exp_var v => exp_var v
  | exp_abs V e1 => exp_abs (open_tt_rec K U V) (open_te_rec (S K) U e1)
  | exp_app f x => exp_app f x
  | exp_let e C => exp_let (open_te_rec K U e) (open_te_rec (S K) U C)
  | exp_tabs V e1 => exp_tabs (open_tt_rec K U V)  (open_te_rec (S K) U e1)
  | exp_tapp x V => exp_tapp x (open_tt_rec K U V)
  end.

Fixpoint open_ct_rec (k : nat) (c : cap) (T : typ)  {struct T} : typ :=
  match T with
  | typ_bvar i => i
  | typ_fvar x => x
  | typ_capt C P => typ_capt (open_cset k c C) (open_cpt_rec k c P)
  end
with open_cpt_rec (k : nat) (c : cap) (T : pretyp)  {struct T} : pretyp :=
  match T with
  | typ_top => typ_top
  | typ_arrow T1 T2 => typ_arrow (open_ct_rec k c T1) (open_ct_rec (S k) c T2)
  | typ_all T1 T2 => typ_all (open_ct_rec k c T1) (open_ct_rec (S k) c T2)
  end.

Definition open_vv (k : nat) (z : atom) (v : var) : var :=
  match v with
  | var_b i => if k === i then z else i
  | var_f x => x
  end.

Fixpoint open_ve_rec (k : nat) (z : atom) (c : cap) (e : exp)  {struct e} : exp :=
  match e with
  | exp_var v => open_vv k z v
  | exp_abs t e1 => exp_abs (open_ct_rec k c t) (open_ve_rec (S k) z c e1)
  | exp_app f x => exp_app (open_vv k z f) (open_vv k z x)
  | exp_let e C => exp_let (open_ve_rec k z c e) (open_ve_rec (S k) z c C)
  | exp_tabs t e1 => exp_tabs (open_ct_rec k c t) (open_ve_rec (S k) z c e1)
  | exp_tapp x t => exp_tapp (open_vv k z x) (open_ct_rec k c t)
  end.


(** Many common applications of opening replace index zero with an
    expression or variable.  The following definitions provide
    convenient shorthands for such uses.  Note that the order of
    arguments is switched relative to the definitions above.  For
    example, [(open_tt T X)] can be read as "substitute the variable
    [X] for index [0] in [T]" and "open [T] with the variable [X]."
    Recall that the coercions above let us write [X] in place of
    [(typ_fvar X)], assuming that [X] is an [atom]. *)

Definition open_tt T U := open_tt_rec 0 U T.
Definition open_tpt T U := open_tpt_rec 0 U T.
Definition open_te e U := open_te_rec 0 U e.
Definition open_ve e x c := open_ve_rec 0 x c e.
Definition open_ct T c := open_ct_rec 0 c T.
Definition open_cpt T c := open_cpt_rec 0 c T.

(* ********************************************************************** *)
(** * #<a name="lc"></a># Local closure *)

(** Recall that [typ] and [exp] define pre-terms; these datatypes
    admit terms that contain unbound indices.  A term is locally
    closed, or syntactically well-formed, when no indices appearing in
    it are unbound.  The proposition [(type T)] holds when a type [T]
    is locally closed, and [(expr e)] holds when an expression [e] is
    locally closed.

    The inductive definitions below formalize local closure such that
    the resulting induction principles serve as structural induction
    principles over (locally closed) types and (locally closed)
    expressions.  In particular, unlike the situation with pre-terms,
    there are no cases for indices.  Thus, these induction principles
    correspond more closely to informal practice than the ones arising
    from the definitions of pre-terms.

    The interesting cases in the inductive definitions below are those
    that involve binding constructs, e.g., [typ_all].  Intuitively, to
    check if the pre-term [(typ_all T1 T2)] is locally closed we much
    check that [T1] is locally closed, and that [T2] is locally closed
    when opened with a variable.  However, there is a choice as to how
    many variables to quantify over.  One possibility is to quantify
    over only one variable ("existential" quantification), as in
<<
  type_all : forall X T1 T2,
      type T1 ->
      type (open_tt T2 X) ->
      type (typ_all T1 T2)
>>  or we could quantify over as many variables as possible ("universal"
    quantification), as in
<<
  type_all : forall T1 T2,
      type T1 ->
      (forall X : atom, type (open_tt T2 X)) ->
      type (typ_all T1 T2)
>>  It is possible to show that the resulting relations are equivalent.
    The former makes it easy to build derivations, while the latter
    provides a strong induction principle.  McKinna and Pollack used
    both forms of this relation in their work on formalizing Pure Type
    Systems.

    We take a different approach here and use "cofinite
    quantification": we quantify over all but finitely many variables.
    This approach provides a convenient middle ground: we can build
    derivations reasonably easily and get reasonably strong induction
    principles.  With some work, one can show that the definitions
    below are equivalent to ones that use existential, and hence also
    universal, quantification. *)

Inductive type : typ -> Prop :=
  | type_var : forall X,
      type (typ_fvar X)
  | type_capt : forall C P,
      capt C ->
      pretype P ->
      type (typ_capt C P)
with pretype : pretyp -> Prop :=
  | type_top : pretype typ_top
  | type_arrow : forall L T1 T2,
    type T1 ->
    (forall X : atom, X `notin` L -> type (open_ct T2 (`cset_fvar` X))) ->
    pretype (typ_arrow T1 T2)
  | type_all : forall L T1 T2,
    type T1 ->
    (forall X : atom, X `notin` L -> type (open_tt T2 X)) ->
    pretype (typ_all T1 T2).

Inductive expr : exp -> Prop :=
  | expr_var : forall (x : atom),
      expr x
  | expr_abs : forall L T e1,
      type T ->
      (forall x : atom, x `notin` L -> expr (open_ve e1 x (`cset_fvar` x))) ->
      expr (exp_abs T e1)
  | expr_app : forall (f x : atom),
      expr (exp_app f x)
  | expr_let : forall L e C,
      expr e ->
      (forall x : atom, x `notin` L -> expr (open_ve C x (`cset_fvar` x))) ->
      expr (exp_let e C)
  | expr_tabs : forall L T e1,
      type T ->
      (forall X : atom, X `notin` L -> expr (open_te e1 X)) ->
      expr (exp_tabs T e1)
  | expr_tapp : forall (x : atom) V,
      type V ->
      expr (exp_tapp x V).

(* ********************************************************************** *)
(** * #<a name="env"></a># Environments *)

(** In our presentation of System F with subtyping, we use a single
    environment for both typing and subtyping assumptions.  We
    formalize environments by representing them as association lists
    (lists of pairs of keys and values) whose keys are atoms.

    The [Metatheory] and [Environment] libraries provide functions,
    predicates, tactics, notations and lemmas that simplify working
    with environments.  The [Environment] library treats environments
    as lists of type [list (atom * A)].

    Since environments map [atom]s, the type [A] should encode whether
    a particular binding is a typing or subtyping assumption.  Thus,
    we instantiate [A] with the type [binding], defined below. *)

Inductive binding : Type :=
  | bind_sub : typ -> binding
  | bind_typ : typ -> binding.

(** A binding [(X, bind_sub T)] records that a type variable [X] is a
    subtype of [T], and a binding [(x, bind_typ U)] records that an
    expression variable [x] has type [U].

    We define an abbreviation [env] for the type of environments, and
    an abbreviation [empty] for the empty environment.

    Note: Each instance of [Notation] below defines an abbreviation
    since the left-hand side consists of a single identifier that is
    not in quotes.  These abbreviations are used for both parsing (the
    left-hand side is equivalent to the right-hand side in all
    contexts) and printing (the right-hand side is pretty-printed as
    the left-hand side).  Since [nil] is normally a polymorphic
    constructor whose type argument is implicit, we prefix the name
    with "[@]" to signal to Coq that we are going to supply arguments
    to [nil] explicitly. *)

Notation env := (list (atom * binding)).
Notation empty := (@nil (atom * binding)).

(** We also define a notation that makes it convenient to write one
    element lists.  This notation is useful because of our convention
    for building environments; see the examples below. *)

Notation "[ x ]" := (x :: nil).

(** #<b>#Examples:#</b># We use a convention where environments are
    never built using a cons operation [((x, a) :: E)] where [E] is
    non-[nil].  This makes the shape of environments more uniform and
    saves us from excessive fiddling with the shapes of environments.
    For example, Coq's tactics sometimes distinguish between consing
    on a new binding and prepending a one element list, even though
    the two operations are convertible with each other.

    Consider the following environments written in informal notation.
<<
  1. (empty environment)
  2. x : T
  3. x : T, Y <: S
  4. E, x : T, F
>>  In the third example, we have an environment that binds an
    expression variable [x] to [T] and a type variable [Y] to [S].
    In Coq, we would write these environments as follows.
<<
  1. empty
  2. [(x, bind_typ T)]
  3. [(Y, bind_sub S)] ++ [(x, bind_typ T)]
  4. F ++ [(x, bind_typ T)] ++ E
>> The symbol "[++]" denotes list concatenation and associates to the
    right.  (That notation is defined in Coq's [List] library.)  Note
    that in Coq, environments grow on the left, since that is where
    the head of a list is. *)


(* ********************************************************************** *)
(** * #<a name="wf"></a># Well-formedness *)

(** A type [T] is well-formed with respect to an environment [E],
    denoted [(wf_typ E T)], when [T] is locally-closed and its free
    variables are bound in [E].  We need this relation in order to
    restrict the subtyping and typing relations, defined below, to
    contain only well-formed types.  (This relation is missing in the
    original statement of the POPLmark Challenge.)

    Note: It is tempting to define the premise of [wf_typ_var] as [(X
    `in` dom E)], since that makes the rule easier to apply (no need
    to guess an instantiation for [U]).  Unfortunately, this is
    incorrect.  We need to check that [X] is bound as a type-variable,
    not an expression-variable; [(dom E)] does not distinguish between
    the two kinds of bindings. *)

(** For our current calculus, we disallow type variables from showing up in capture
  sets -- only term variables are allowed. *)
Inductive bound (x : atom) (T : typ) (E : env) : Prop :=
  | bound_typ :
    binds x (bind_typ T) E ->
    bound x T E
  | bound_sub :
    binds x (bind_sub T) E ->
    bound x T E.

Definition allbound (E : env) (fvars : atoms) : Prop :=
  forall x, x `in`A fvars -> exists T, bound x T E.

Inductive wf_cset : env -> atoms -> cap -> Prop :=
  | wf_concrete_cset : forall E A fvars univ,
    allbound E fvars ->
    fvars `c`A A ->
    wf_cset E A (cset_set fvars {}N univ).

Definition wf_cset_in (E : env) (C : cap) : Prop :=
  wf_cset E (dom E) C.

(* Wellformedness of types where locally bound variables are only
   allowed in positive positions. *)
Inductive wf_typ : env -> atoms -> atoms -> typ -> Prop :=
  | wf_typ_var : forall U E Ap Am (X : atom),
      binds X (bind_sub U) E ->
      X `in`A Ap ->
      wf_typ E Ap Am (typ_fvar X)
  | wf_typ_capt : forall E Ap Am C P,
      wf_cset E Ap C ->
      wf_pretyp E Ap Am P ->
      wf_typ E Ap Am (typ_capt C P)
with wf_pretyp : env -> atoms -> atoms -> pretyp -> Prop :=
  | wf_typ_top : forall E Ap Am,
      wf_pretyp E Ap Am typ_top
  | wf_typ_arrow : forall L E Ap Am T1 T2,
      wf_typ E Am Ap T1 ->
      (forall X : atom, X `notin` L ->
                  wf_typ ([(X, bind_typ T1)] ++ E)
                          (Ap `union` singleton X)
                          Am
                          (open_ct T2 (`cset_fvar` X))) ->
      wf_pretyp E Ap Am (typ_arrow T1 T2)
  | wf_typ_all : forall L E Ap Am T1 T2,
      wf_typ E Am Ap T1 ->
      (forall X : atom, X `notin` L ->
                  wf_typ ([(X, bind_sub T1)] ++ E)
                          (Ap `u`A {X}A)
                          (Am `u`A {X}A) (open_tt T2 X)) ->
      wf_pretyp E Ap Am (typ_all T1 T2).

Definition wf_typ_in (E : env) (T : typ) : Prop :=
  wf_typ E (dom E) (dom E) T.

Definition wf_pretyp_in (E : env) (U : pretyp) : Prop :=
  wf_pretyp E (dom E) (dom E) U.

Hint Unfold wf_typ_in : core.
Hint Unfold wf_pretyp_in : core.

(** An environment E is well-formed, denoted [(wf_env E)], if each
    atom is bound at most at once and if each binding is to a
    well-formed type.  This is a stronger relation than the [ok]
    relation defined in the [Environment] library.  We need this
    relation in order to restrict the subtyping and typing relations,
    defined below, to contain only well-formed environments.  (This
    relation is missing in the original statement of the POPLmark
    Challenge.)  *)

Inductive wf_env : env -> Prop :=
  | wf_env_empty :
      wf_env empty
  | wf_env_sub : forall (E : env) (X : atom) (T : typ),
      wf_env E ->
      wf_typ_in E T ->
      X `notin` dom E ->
      wf_env ([(X, bind_sub T)] ++ E)
  | wf_env_typ : forall (E : env) (x : atom) (T : typ),
      wf_env E ->
      wf_typ_in E T ->
      x `notin` dom E ->
      wf_env ([(x, bind_typ T)] ++ E).

(* ********************************************************************** *)
(** * #<a name="sub"></a># Subtyping *)

Inductive subcapt : env -> cap -> cap -> Prop :=
  | subcapt_universal : forall E C xs,
      wf_cset_in E (cset_set xs {}N true) ->
      wf_cset_in E C ->
      subcapt E C (cset_set xs {}N true)
  | subcapt_in : forall E x xs b,
      wf_cset_in E (`cset_fvar` x) ->
      wf_cset_in E (cset_set xs {}N b) ->
      x `in` xs ->
      subcapt E (`cset_fvar` x) (cset_set xs {}N b)
  | subcapt_in_univ : forall E D,
      wf_cset_in E D ->
      `* in` D ->
      subcapt E {*} D
  | subcapt_var : forall E x T C,
      binds x (bind_typ T) E ->
      subcapt E (cv T) C ->
      subcapt E (`cset_fvar` x) C
  | subcapt_tvar : forall E x T C,
      binds x (bind_sub T) E ->
      subcapt E (cv T) C ->
      subcapt E (`cset_fvar` x) C
  | subcapt_set : forall E xs b D,
      wf_cset_in E D ->
      AtomSet.F.For_all (fun x => subcapt E (`cset_fvar` x) D) xs ->
      implb b (`* mem` D) = true ->
      subcapt E (cset_set xs {}N b) D.

(** The definition of subtyping is straightforward.  It uses the
    [binds] relation from the [Environment] library (in the
    [sub_trans_tvar] case) and cofinite quantification (in the
    [sub_all] case). *)

Inductive sub : env -> typ -> typ -> Prop :=

  (* Instead of having rules for refl and trans, the original Fsub calculus special cases
     those rules to type variables. Refl and Trans are then defined externally in sub_reflexivity
     and sub_transitivity. *)
  | sub_refl_tvar : forall E (X : atom),
      wf_env E ->
      wf_typ_in E X ->
      sub E X X

  | sub_trans_tvar : forall U E T X,
      binds X (bind_sub U) E ->
      sub E U T ->
      sub E X T

  | sub_capt : forall E C1 C2 P1 P2,
      subcapt E C1 C2 ->
      sub_pre E P1 P2 ->
      sub E (typ_capt C1 P1) (typ_capt C2 P2)

with sub_pre : env -> pretyp -> pretyp -> Prop :=
  (*
      cv(S, E) = {}
      -------------
      E ⊢ S <: ⊤
  *)
  | sub_top : forall E S,
      wf_env E ->
      wf_pretyp_in E S ->
      sub_pre E S typ_top

  (*
      E ⊢ T₁ <: S₁    E, x: T₁ ⊢ S₂ <: T₂
      ------------------------------------
          E ⊢ ∀(x: S₁)S₂ <: ∀(x: T₁)T₂

      New: Here we open S2 and T2 with x
  *)
  | sub_arrow : forall L E S1 S2 T1 T2,
      sub E T1 S1 ->
      wf_typ_in E T1 ->
      wf_typ_in E S1 ->
      (forall x : atom, x `notin` L ->
          wf_typ ([(x, bind_typ T1)] ++ E) (dom E `union` singleton x) (dom E) (open_ct T2 (`cset_fvar` x))) ->
      (forall x : atom, x `notin` L ->
          wf_typ ([(x, bind_typ S1)] ++ E) (dom E `union` singleton x) (dom E) (open_ct S2 (`cset_fvar` x))) ->
      (forall x : atom, x `notin` L ->
          sub ([(x, bind_typ T1)] ++ E) (open_ct S2 (`cset_fvar` x)) (open_ct T2 (`cset_fvar` x))) ->
      sub_pre E (typ_arrow S1 S2) (typ_arrow T1 T2)

  (*
      E ⊢ T₁ <: S₁    E, X<:T₁ ⊢ S₂ <: T₂
      ------------------------------------
        E ⊢ ∀[X<:S₁]S₂ <: ∀[X<:T₁]T₂
  *)
  | sub_all : forall L E S1 S2 T1 T2,
      sub E T1 S1 ->
      wf_typ_in E T1 ->
      wf_typ_in E S1 ->
      (forall X : atom, X `notin` L ->
          (* REVIEW: difference between dom E and dom E `u`A {X}A? *)
          wf_typ ([(X, bind_sub T1)] ++ E) (dom E `u`A {X}A) (dom E `u`A {X}A) (open_tt T2 X)) ->
      (forall X : atom, X `notin` L ->
          wf_typ ([(X, bind_sub S1)] ++ E) (dom E `u`A {X}A) (dom E `u`A {X}A) (open_tt S2 X)) ->
      (forall X : atom, X `notin` L ->
          sub ([(X, bind_sub T1)] ++ E) (open_tt S2 X) (open_tt T2 X)) ->
      sub_pre E (typ_all S1 S2) (typ_all T1 T2).


(* ********************************************************************** *)
(** * #<a name="typing_doc"></a># Typing *)

Definition free_for_cv_var (v : var) : cap :=
  match v with
  | var_f x => (`cset_fvar` x)
  | var_b _ => {}
  end.

(** The definition of "fv" used in typing jdmgnts*)
Fixpoint free_for_cv (e : exp) : cap :=
  match e with
  | exp_var v => free_for_cv_var v
  | exp_abs t e1 => (free_for_cv e1)
  | exp_app f x => (cset_union (free_for_cv_var f) (free_for_cv_var x))
  | exp_let e C => (cset_union (free_for_cv e) (free_for_cv C))
  | exp_tabs t e1 => (free_for_cv e1)
  | exp_tapp x t => (free_for_cv_var x)
  end.

Inductive typing : env -> exp -> typ -> Prop :=
  | typing_var_tvar : forall E (x X : atom),
      wf_env E ->
      binds x (bind_typ X) E ->
      typing E x (typ_fvar X)
  | typing_var : forall E x C P,
      wf_env E ->
      binds x (bind_typ (typ_capt C P)) E ->
      typing E x (typ_capt (`cset_fvar` x) P)
  | typing_abs : forall L E V e1 T1,
      wf_typ_in E V ->
      (forall x : atom, x `notin` L ->
          wf_typ ([(x, bind_typ V)] ++ E) (dom E `union` singleton x) (dom E) (open_ct T1 (`cset_fvar` x))) ->
      (forall x : atom, x `notin` L ->
        typing ([(x, bind_typ V)] ++ E) (open_ve e1 x (`cset_fvar` x)) (open_ct T1 (`cset_fvar` x))) ->
      typing E (exp_abs V e1) (typ_capt (free_for_cv e1) (typ_arrow V T1))
  | typing_app : forall T1 E (f x : atom) T2 Cf T1',
      typing E f (typ_capt Cf (typ_arrow T1 T2)) ->
      typing E x T1' ->
      sub E T1' T1 ->
      typing E (exp_app f x) (open_ct T2 (cv T1'))
  | typing_let : forall L T1 T2 E e C,
      typing E e T1 ->
      (forall x : atom, x `notin` L ->
        typing ([(x, bind_typ T1)] ++ E) (open_ve C x (`cset_fvar` x)) T2) ->
      typing E (exp_let e C) T2
  | typing_tabs : forall L E V e1 T1,
      wf_typ_in E V ->
      (forall x : atom, x `notin` L ->
        wf_typ ([(x, bind_sub V)] ++ E) (dom E) (dom E) (open_tt T1 x)) ->
      (forall X : atom, X `notin` L ->
        typing ([(X, bind_sub V)] ++ E) (open_te e1 X) (open_tt T1 X)) ->
      typing E (exp_tabs V e1) (typ_capt (free_for_cv e1) (typ_all V T1))
  | typing_tapp : forall T1 E (x : atom) T T2 C,
      typing E x (typ_capt C (typ_all T1 T2)) ->
      sub E T T1 ->
      typing E (exp_tapp x T) (open_tt T2 T)
  | typing_sub : forall S E e T,
      typing E e S ->
      sub E S T ->
      typing E e T.

(* ********************************************************************** *)
(** * #<a name="values"></a># Values *)

Inductive value : exp -> Prop :=
  | value_abs : forall T e1,
      expr (exp_abs T e1) ->
      value (exp_abs T e1)
  | value_tabs : forall T e1,
      expr (exp_tabs T e1) ->
      value (exp_tabs T e1).

Inductive answer : exp -> Prop :=
  | answer_val : forall v,
      value v ->
      answer v
  | answer_var : forall (x : atom),
      answer x.

(* States *)

Inductive store_frame : Type :=
  | store v : value v -> store_frame.

Definition store_ctx : Type := list (atom * store_frame).
Definition stores (S : store_ctx) (x : atom) (v : exp) (v_value : value v) : Prop :=
    binds x (store v v_value) S.

Inductive scope (c : cap) (e : exp) : Type :=
  | mk_scope L : (forall x, x `notin` L -> expr (open_ve e x c)) -> scope c e.

Inductive eval_frame : Type :=
  | cont c e : scope c e -> eval_frame.

Definition eval_ctx : Type := (list eval_frame).

Inductive state : Type :=
  | mk_state : store_ctx -> eval_ctx -> exp -> state.

Notation "⟨ S | E | e ⟩" := (mk_state S E e) (at level 1).

Inductive state_final : state -> Prop :=
  | final_state : forall S a,
      answer a ->
      state_final ⟨ S | nil | a ⟩.

Inductive store_typing : store_ctx -> env -> Prop :=
  | typing_store_nil : store_typing nil nil
  | typing_store_cons : forall x T v v_value S E,
      store_typing S E ->
      typing E v T ->
      x `notin` dom E ->
      store_typing ([(x, store v v_value)] ++ S) ([(x, bind_typ T)] ++ E).

Inductive eval_typing (E : env) : eval_ctx -> typ -> typ -> Prop :=
  | typing_eval_nil : forall T U,
      wf_env E ->
      sub E T U ->
      eval_typing E nil T U
  | typing_eval_cons : forall L c k (k_scope : scope c k) K T U V,
      (forall x : atom, x `notin` L ->
        typing ([(x, bind_typ T)] ++ E) (open_ve k x c) U) ->
      eval_typing E K U V ->
      eval_typing E (cont c k k_scope :: K) T V.

Inductive state_typing : state -> typ -> Prop :=
  | typing_state : forall S K e E T U,
      store_typing S E ->
      eval_typing E K T U ->
      typing E e T ->
      state_typing ⟨ S | K | e ⟩ U.

(* ********************************************************************** *)
(** * #<a name="reduction"></a># Reduction *)

Inductive red (L : atoms) : state -> state -> Prop :=
  | red_lift : forall x v (v_value : value v) c k (k_scope : scope c k) S E,
      x `notin` L ->
      red L ⟨ S | cont c k k_scope :: E | v ⟩
            ⟨ [(x, store v v_value)] ++ S | E | open_ve k x c ⟩
  | red_let_var : forall (x y : atom) v (v_value : value v) c k (k_scope : scope c k) S E,
      stores S x v v_value ->
      y `notin` L ->
      red L ⟨ S | cont c k k_scope :: E | x ⟩
            ⟨ [(y, store v v_value)] ++ S | E | open_ve k y c ⟩
  | red_let_val : forall x v (v_value : value v) c k (k_scope : scope c k) S E,
      x `notin` L ->
      red L ⟨ S | E | exp_let v k ⟩
            ⟨ [(x, store v v_value)] ++ S | E | open_ve k x c ⟩
  | red_let_exp : forall e c k (k_scope : scope c k) S E,
      red L ⟨ S | E | exp_let e k ⟩
            ⟨ S | cont c k k_scope :: E | e ⟩
  | red_app : forall f x U e v (v_value : value v) (abs_value : value (exp_abs U e)) S E,
      stores S f (exp_abs U e) abs_value ->
      stores S x v v_value ->
      x `notin` L ->
      red L ⟨ S | E | exp_app f x ⟩
            ⟨ S | E | open_ve e x (free_for_cv e) ⟩
  | red_tapp : forall x T U e (tabs_value : value (exp_tabs U e)) S E,
      stores S x (exp_tabs U e) tabs_value ->
      type T ->
      x `notin` L ->
      red L ⟨ S | E | exp_tapp x T ⟩
            ⟨ S | E | open_te e T ⟩.


(* ********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

(** We declare most constructors as [Hint]s to be used by the [auto]
    and [eauto] tactics.  We exclude constructors from the subtyping
    and typing relations that use cofinite quantification.  It is
    unlikely that [eauto] will find an instantiation for the finite
    set [L], and in those cases, [eauto] can take some time to fail.
    (A priori, this is not obvious.  In practice, one adds as hints
    all constructors and then later removes some constructors when
    they cause proof search to take too long.) *)

Hint Constructors type pretype expr bound wf_cset wf_typ wf_pretyp wf_env value red sub subcapt typing : core.
Hint Resolve sub_top sub_refl_tvar sub_arrow : core.
Hint Resolve typing_var_tvar typing_var typing_app typing_tapp typing_sub : core.
Hint Unfold wf_typ_in wf_pretyp_in wf_cset_in allbound : core.

Local Ltac cset_unfold_union0 :=
  match goal with
  | _ : _ |- context G [?C `u` (cset_set ?xs ?ns ?us)] =>
    match C with
    | cset_set _ _ _ =>
      rewrite cset_concrete_union
    | C =>
      let HA := match goal with
                | H : wf_cset_in _ C |- _ => H
                | H : wf_cset _ _ C |- _ => H
                | _ =>
                  let H := fresh "WF" in
                  (* NOTE: avoid asserting (wf_cset _ _ C), it takes long to solve. *)
                  assert (wf_cset_in _ C) as HA by eauto; H
                end
      in
      (* Invert, subst and clean up unnecessary hypothesis. *)
      pose proof ltac_mark; inversion HA; subst; clear_until_mark;
      (* Rewrite to avoid matching the same union twice, not sure if necessary. *)
      rewrite cset_concrete_union
    end
  end.

(* We can only define this tactic here, since in CaptureSets we don't have wf_cset. *)
Ltac cset_unfold_union := repeat cset_unfold_union0.

Ltac _csetsimpl_hook ::= cset_unfold_union.

Local Lemma __test_cset_concrete_unfold : forall C xs us,
  wf_cset_in nil C ->
  wf_cset_in nil (C `u` (cset_set xs {}N us)) ->
  exists xs' us', wf_cset_in nil (cset_set (xs' `u`A xs) {}N (us' || us)).
Proof. intros * H; csetsimpl; eauto. Qed.
