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
  | typ_all : typ -> typ -> pretyp
  .


Inductive exp : Type :=
  | exp_bvar : nat -> exp
  | exp_fvar : atom -> exp
  | exp_abs : typ -> exp -> exp
  | exp_app : exp -> exp -> exp
  | exp_tabs : typ -> exp -> exp
  | exp_tapp : exp -> typ -> exp
.

(** We declare the constructors for indices and variables to be
    coercions.  For example, if Coq sees a [nat] where it expects an
    [exp], it will implicitly insert an application of [exp_bvar];
    similar behavior happens for [atom]s.  Thus, we may write
    [(exp_abs typ_top (exp_app 0 x))] instead of [(exp_abs typ_top
    (exp_app (exp_bvar 0) (exp_fvar x)))]. *)

Coercion typ_bvar : nat >-> typ.
Coercion typ_fvar : atom >-> typ.
Coercion exp_bvar : nat >-> exp.
Coercion exp_fvar : atom >-> exp.
Coercion cset_bvar : nat >-> cap.
Coercion cset_fvar : atom >-> cap.

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

Fixpoint open_tt_rec (K : nat) (U : typ) (T : typ)  {struct T} : typ :=
  match T with
  | typ_bvar J => if K === J then U else (typ_bvar J)
  | typ_fvar X => typ_fvar X
  | typ_capt C P => typ_capt C (open_tpt_rec K U P)
  end
with open_tpt_rec (K : nat) (U : typ) (T : pretyp)  {struct T} : pretyp :=
  match T with
  | typ_top => typ_top
  | typ_arrow T1 T2 => typ_arrow (open_tt_rec K U T1) (open_tt_rec (S K) U T2)
  | typ_all T1 T2 => typ_all (open_tt_rec K U T1) (open_tt_rec (S K) U T2)
  end
.

Fixpoint open_te_rec (K : nat) (U : typ) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_abs V e1 => exp_abs  (open_tt_rec K U V)  (open_te_rec (S K) U e1)
  | exp_app e1 e2 => exp_app  (open_te_rec K U e1) (open_te_rec K U e2)
  | exp_tabs V e1 => exp_tabs (open_tt_rec K U V)  (open_te_rec (S K) U e1)
  | exp_tapp e1 V => exp_tapp (open_te_rec K U e1) (open_tt_rec K U V)
  end.

Fixpoint open_ct_rec (k : nat) (c : cap) (T : typ)  {struct T} : typ :=
  match T with
  | typ_bvar i => typ_bvar i
  | typ_fvar x => typ_fvar x
  | typ_capt C P => typ_capt (open_cset k c C) (open_cpt_rec k c P)
  end
with open_cpt_rec (k : nat) (c : cap) (T : pretyp)  {struct T} : pretyp :=
  match T with
  | typ_top => typ_top
  | typ_arrow T1 T2 => typ_arrow (open_ct_rec k c T1) (open_ct_rec (S k) c T2)
  | typ_all T1 T2 => typ_all (open_ct_rec k c T1) (open_ct_rec (S k) c T2)
  end.

Fixpoint open_ee_rec (k : nat) (f : exp) (c : cap) (e : exp)  {struct e} : exp :=
  match e with
  | exp_bvar i => if k === i then f else (exp_bvar i)
  | exp_fvar x => exp_fvar x
  | exp_abs t e1 => exp_abs (open_ct_rec k c t) (open_ee_rec (S k) f c e1)
  | exp_app e1 e2 => exp_app (open_ee_rec k f c e1) (open_ee_rec k f c e2)
  | exp_tabs t e1 => exp_tabs (open_ct_rec k c t) (open_ee_rec (S k) f c e1)
  | exp_tapp e1 t => exp_tapp (open_ee_rec k f c e1) (open_ct_rec k c t)
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
Definition open_ee e1 e2 c := open_ee_rec 0 e2 c e1.
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
    (forall X : atom, X `notin` L -> type (open_ct T2 (cset_fvar X))) ->
    pretype (typ_arrow T1 T2)
  | type_all : forall L T1 T2,
    type T1 ->
    (forall X : atom, X `notin` L -> type (open_tt T2 X)) ->
    pretype (typ_all T1 T2)
.

Inductive expr : exp -> Prop :=
  | expr_var : forall x,
      expr (exp_fvar x)
  | expr_abs : forall L T e1,
      type T ->
      (forall x : atom, x `notin` L -> expr (open_ee e1 x x)) ->
      expr (exp_abs T e1)
  | expr_app : forall e1 e2,
      expr e1 ->
      expr e2 ->
      expr (exp_app e1 e2)
  | expr_tabs : forall L T e1,
      type T ->
      (forall X : atom, X `notin` L -> expr (open_te e1 X)) ->
      expr (exp_tabs T e1)
  | expr_tapp : forall e1 V,
      expr e1 ->
      type V ->
      expr (exp_tapp e1 V)
.


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
Definition allbound_typ (E : env) (X : atoms) : Prop :=
  forall x, AtomSet.F.In x X -> exists T, binds x (bind_typ T) E.

Inductive wf_cset : env -> atoms -> cap -> Prop :=
  | wf_concrete_cset : forall E A fvars univ,
    allbound_typ E fvars ->
    AtomSet.F.Subset fvars A ->
    wf_cset E A (cset_set fvars {}N univ)
.

Definition wf_cset_in (E : env) (C : cap) : Prop :=
  wf_cset E (dom E) C.

(* Wellformedness of types where locally bound variables are only
   allowed in positive positions. *)
Inductive wf_typ : env -> atoms -> atoms -> typ -> Prop :=
  | wf_typ_var : forall U E Ap Am (X : atom),
      binds X (bind_sub U) E ->
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
        wf_typ ([(X, bind_typ T1)] ++ E) (Ap `union` singleton X) Am (open_ct T2 X)) ->
      wf_pretyp E Ap Am (typ_arrow T1 T2)
  | wf_typ_all : forall L E Ap Am T1 T2,
      wf_typ E Am Ap T1 ->
      (forall X : atom, X `notin` L ->
      wf_typ ([(X, bind_sub T1)] ++ E) Ap Am (open_tt T2 X)) ->
      wf_pretyp E Ap Am (typ_all T1 T2)
.

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

(** Dealing with cv -- as a fixpoint is problematic. *)
Inductive cv : env -> typ -> cap -> Prop :=
  (** Looking up in the environment; we ask that T is wf in the environment
      and that the environment is well formed so lookup is well defined. *)
  | cv_typ_var : forall (X : atom) T E CT,
    binds X (bind_sub T) E ->
    wf_env E ->
    cv E T CT ->
    cv E (typ_fvar X) CT
  | cv_typ_capt : forall E C P,
    wf_env E ->
    wf_pretyp_in E P ->
    wf_cset_in E C ->
    cv E (typ_capt C P) C.

(* ********************************************************************** *)
(** * #<a name="sub"></a># Subtyping *)

Inductive subcapt : env -> cap -> cap -> Prop :=
  | subcapt_universal : forall E x xs,
      wf_cset_in E (cset_fvar x) ->
      wf_cset_in E (cset_set xs {}N true) ->
      subcapt E (cset_fvar x) (cset_set xs {}N true)
  | subcapt_in : forall E x xs,
      wf_cset_in E (cset_fvar x) ->
      wf_cset_in E (cset_set xs {}N false) ->
      x `in` xs ->
      subcapt E (cset_fvar x) (cset_set xs {}N false)
  | subcapt_var : forall E x T C D,
      binds x (bind_typ T) E ->
      cv E T C ->
      subcapt E C D ->
      subcapt E (cset_fvar x) D
  | subcapt_set : forall E xs D,
      wf_cset_in E D ->
      AtomSet.F.For_all (fun x => subcapt E (cset_fvar x) D) xs ->
      subcapt E (cset_set xs {}N false) D
  | subcapt_set_univ : forall E xs D,
      wf_cset_in E D ->
      cset_references_univ D ->
      subcapt E (cset_set xs {}N true) D.

(** The definition of subtyping is straightforward.  It uses the
    [binds] relation from the [Environment] library (in the
    [sub_trans_tvar] case) and cofinite quantification (in the
    [sub_all] case). *)

Inductive sub : env -> typ -> typ -> Prop :=

  (* Instead of having rules for refl and trans, the original Fsub calculus special cases
     those rules to type variables. Refl and Trans are then defined externally in sub_reflexivity
     and sub_transitivity. *)
  | sub_refl_tvar : forall E X,
      wf_env E ->
      wf_typ_in E (typ_fvar X) ->
      sub E (typ_fvar X) (typ_fvar X)

  | sub_trans_tvar : forall U E T X,
      binds X (bind_sub U) E ->
      sub E U T ->
      sub E (typ_fvar X) T

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
          wf_typ ([(x, bind_typ T1)] ++ E) (dom E `union` singleton x) (dom E) (open_ct T2 x)) ->
      (forall x : atom, x `notin` L ->
          wf_typ ([(x, bind_typ S1)] ++ E) (dom E `union` singleton x) (dom E) (open_ct S2 x)) ->
      (forall x : atom, x `notin` L ->
          sub ([(x, bind_typ T1)] ++ E) (open_ct S2 x) (open_ct T2 x)) ->
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
          wf_typ ([(X, bind_sub T1)] ++ E) (dom E) (dom E) (open_tt T2 X)) ->
      (forall X : atom, X `notin` L ->
          wf_typ ([(X, bind_sub S1)] ++ E) (dom E) (dom E) (open_tt S2 X)) ->
      (forall X : atom, X `notin` L ->
          sub ([(X, bind_sub T1)] ++ E) (open_tt S2 X) (open_tt T2 X)) ->
      sub_pre E (typ_all S1 S2) (typ_all T1 T2)
.


(* ********************************************************************** *)
(** * #<a name="typing_doc"></a># Typing *)

(** The definition of "fv" used in typing jdmgnts*)
Fixpoint free_for_cv (e : exp) : cap :=
match e with
  | exp_bvar i => {}
  | exp_fvar x => (cset_fvar x)
  | exp_abs t e1 => (free_for_cv e1)
  | exp_app e1 e2 => (cset_union (free_for_cv e1) (free_for_cv e2))
  | exp_tabs t e1 => (free_for_cv e1)
  | exp_tapp e1 t => (free_for_cv e1)
  end.

Inductive typing : env -> exp -> typ -> Prop :=
  | typing_var_tvar : forall E x X,
      wf_env E ->
      binds x (bind_typ (typ_fvar X)) E ->
      typing E (exp_fvar x) (typ_fvar X)
  | typing_var : forall E x C P,
      wf_env E ->
      binds x (bind_typ (typ_capt C P)) E ->
      typing E (exp_fvar x) (typ_capt x P)
  | typing_abs : forall L E V e1 T1,
      wf_typ_in E V ->
      (forall x : atom, x `notin` L ->
          wf_typ ([(x, bind_typ V)] ++ E) (dom E `union` singleton x) (dom E) (open_ct T1 x)) ->
      (forall x : atom, x `notin` L ->
        typing ([(x, bind_typ V)] ++ E) (open_ee e1 x x) (open_ct T1 x)) ->
      typing E (exp_abs V e1) (typ_capt (free_for_cv e1) (typ_arrow V T1))
  | typing_app : forall T1 E e1 e2 T2 Cf Cv' T1',
      typing E e1 (typ_capt Cf (typ_arrow T1 T2)) ->
      typing E e2 T1' ->
      sub E T1' T1 ->
      cv E T1' Cv' ->
      typing E (exp_app e1 e2) (open_ct T2 Cv')
  | typing_tabs : forall L E V e1 T1,
      wf_typ_in E V ->
      (forall x : atom, x `notin` L ->
        wf_typ ([(x, bind_sub V)] ++ E) (dom E) (dom E) (open_tt T1 x)) ->
      (forall X : atom, X `notin` L ->
        typing ([(X, bind_sub V)] ++ E) (open_te e1 X) (open_tt T1 X)) ->
      typing E (exp_tabs V e1) (typ_capt (free_for_cv e1) (typ_all V T1))
  | typing_tapp : forall T1 E e1 T T2 C,
      typing E e1 (typ_capt C (typ_all T1 T2)) ->
      sub E T T1 ->
      typing E (exp_tapp e1 T) (open_tt T2 T)
  | typing_sub : forall S E e T,
      typing E e S ->
      sub E S T ->
      typing E e T
.


(* ********************************************************************** *)
(** * #<a name="values"></a># Values *)

Inductive value : exp -> Prop :=
  | value_abs : forall T e1,
      expr (exp_abs T e1) ->
      value (exp_abs T e1)
  | value_tabs : forall T e1,
      expr (exp_tabs T e1) ->
      value (exp_tabs T e1)
.


(* ********************************************************************** *)
(** * #<a name="reduction"></a># Reduction *)

Inductive red : exp -> exp -> Prop :=
  | red_app_1 : forall e1 e1' e2,
      expr e2 ->
      red e1 e1' ->
      red (exp_app e1 e2) (exp_app e1' e2)
  | red_app_2 : forall e1 e2 e2',
      value e1 ->
      red e2 e2' ->
      red (exp_app e1 e2) (exp_app e1 e2')
  | red_tapp : forall e1 e1' V,
      type V ->
      red e1 e1' ->
      red (exp_tapp e1 V) (exp_tapp e1' V)
  | red_abs : forall T e1 v2,
      expr (exp_abs T e1) ->
      value v2 ->
      red (exp_app (exp_abs T e1) v2)
        (** is this the right reduction semantics? *)
        (open_ee e1 v2 (free_for_cv v2))
  | red_tabs : forall T1 e1 T2,
      expr (exp_tabs T1 e1) ->
      type T2 ->
      red (exp_tapp (exp_tabs T1 e1) T2) (open_te e1 T2)
.


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

Hint Constructors type pretype expr wf_typ wf_pretyp wf_env value red cv sub subcapt typing wf_cset : core.
Hint Resolve sub_top sub_refl_tvar sub_arrow : core.
Hint Resolve typing_var_tvar typing_var typing_app typing_tapp typing_sub : core.
Hint Unfold wf_typ_in wf_pretyp_in wf_cset_in allbound_typ : core.