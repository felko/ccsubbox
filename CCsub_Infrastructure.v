Require Export CCsub_Definitions.
Require Import Program.Equality.
Require Import Lia.

(** Automation *)
Lemma cset_eq_injectivity : forall a1 a2 n1 n2,
    a1 = a2 ->
    n1 = n2 ->
    cset_set a1 n1 = cset_set a2 n2.
Proof.
  intros. congruence.
Qed.

Ltac fnset_mem_dec :=
  match goal with
  | |- true = _ => symmetry
  | |- false = _ => symmetry
  | |- _ => idtac
  end;
  match goal with
  | |- NatSet.F.mem _ _ = true => rewrite <- NatSetFacts.mem_iff; fnsetdec
  | |- NatSet.F.mem _ _ = false => rewrite <- NatSetFacts.not_mem_iff; fnsetdec
  end.

Ltac fset_mem_dec :=
  match goal with
  | |- true = _ => symmetry
  | |- false = _ => symmetry
  | |- _ => idtac
  end;
  match goal with
  | |- AtomSet.F.mem _ _ = true => rewrite <- AtomSetFacts.mem_iff; fsetdec
  | |- AtomSet.F.mem _ _ = false => rewrite <- AtomSetFacts.not_mem_iff; fsetdec
  end.

Ltac cset_eq_dec :=
  apply cset_eq_injectivity; [try fsetdec | try fnsetdec].

Ltac destruct_if :=
  match goal with
  | |- context[if ?t then _ else _] =>
    destruct t eqn:?
  end.

Ltac destruct_if_in_as t id :=
  match type of t with
  | context[if ?t then _ else _] =>
    destruct t eqn:id
  end.

Tactic Notation "destruct_if" :=
  destruct_if.

Tactic Notation "destruct_if" "in" constr(t) "as" simple_intropattern(id) :=
  destruct_if_in_as t id.

Tactic Notation "destruct_if" "in" constr(t) :=
  destruct_if in t as ?.

Ltac destruct_match :=
  match goal with
  | |- context[match ?t with _ => _ end] =>
    destruct t eqn:?
  end.


(* ********************************************************************** *)
(** * #<a name="fv"></a># Free variables *)

(** In this section, we define free variable functions.  The functions
    [fv_tt] and [fv_te] calculate the set of atoms used as free type
    variables in a type or expression, respectively.  The function
    [fv_ee] calculates the set of atoms used as free expression
    variables in an expression.  Cases involving binders are
    straightforward since bound variables are indices, not names, in
    locally nameless representation. *)

(* These are the TYPE variables in types *)
Fixpoint fv_tt (T : typ) {struct T} : atoms :=
  match T with
  | typ_bvar J => {}A
  | typ_fvar X => singleton X
  | typ_capt C P => (cset_fvars C) `u`A fv_tpt P
  end
with fv_tpt (T : pretyp) {struct T} : atoms :=
  match T with
  | typ_top => {}A
  | typ_arrow T1 T2 => (fv_tt T1) `u`A (fv_tt T2)
  | typ_all T1 T2 => (fv_tt T1) `u`A (fv_tt T2)
  end
.

(* Only in TERM variables in types should capture sets be mentioned *)
Fixpoint fv_et (T : typ) {struct T} : atoms :=
  match T with
  | typ_bvar J => {}A
  | typ_fvar X => {}A
  | typ_capt C P => (cset_fvars C) `u`A (fv_ept P)
  end
with fv_ept (T : pretyp) {struct T} : atoms :=
  match T with
  | typ_top => {}A
  | typ_arrow T1 T2 => (fv_et T1) `u`A (fv_et T2)
  | typ_all T1 T2 => (fv_et T1) `u`A (fv_et T2)
  end.

Fixpoint fv_te (e : exp) {struct e} : atoms :=
  match e with
  | exp_bvar i => {}A
  | exp_fvar x => {}A
  | exp_abs V e1  => (fv_tt V) `u`A (fv_te e1)
  | exp_app e1 e2 => (fv_te e1) `u`A (fv_te e2)
  | exp_tabs V e1 => (fv_tt V) `u`A (fv_te e1)
  | exp_tapp e1 V => (fv_tt V) `u`A (fv_te e1)
  end.

Fixpoint fv_ee (e : exp) {struct e} : atoms :=
  match e with
  | exp_bvar i => {}A
  | exp_fvar x => singleton x
  | exp_abs V e1 => (fv_et V) `u`A (fv_ee e1)
  | exp_app e1 e2 => (fv_ee e1) `u`A (fv_ee e2)
  | exp_tabs V e1 => (fv_et V) `u`A (fv_ee e1)
  | exp_tapp e1 V => (fv_et V) `u`A (fv_ee e1)
  end.



(* ********************************************************************** *)
(** * #<a name="subst"></a># Substitution *)

(** In this section, we define substitution for expression and type
    variables appearing in types, expressions, and environments.
    Substitution differs from opening because opening replaces indices
    whereas substitution replaces free variables.  The definitions
    below are relatively simple for two reasons.
      - We are using locally nameless representation, where bound
        variables are represented using indices.  Thus, there is no
        need to rename variables to avoid capture.
      - The definitions below assume that the term being substituted
        in, i.e., the second argument to each function, is locally
        closed.  Thus, there is no need to shift indices when passing
        under a binder. *)

Fixpoint subst_tt (Z : atom) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_bvar J => typ_bvar J
  | typ_fvar X => if X == Z then U else T
  | typ_capt C P => typ_capt (subst_cset Z (cv U) C) (subst_tpt Z U P)
  end
with subst_tpt (Z : atom) (U : typ) (T : pretyp) {struct T} : pretyp :=
  match T with
  | typ_top => typ_top
  | typ_arrow T1 T2 => typ_arrow (subst_tt Z U T1) (subst_tt Z U T2)
  | typ_all T1 T2 => typ_all (subst_tt Z U T1) (subst_tt Z U T2)
  end.

Fixpoint subst_ct (z : atom) (c : cap) (T : typ) {struct T} : typ :=
  match T with
  | typ_bvar J => typ_bvar J
  | typ_fvar X => typ_fvar X
  | typ_capt C P => typ_capt (subst_cset z c C) (subst_cpt z c P)
  end
with subst_cpt (z : atom) (c : cap) (T : pretyp) {struct T} : pretyp :=
  match T with
  | typ_top => typ_top
  | typ_arrow T1 T2 => typ_arrow (subst_ct z c T1) (subst_ct z c T2)
  | typ_all T1 T2 => typ_all (subst_ct z c T1) (subst_ct z c T2)
  end.

Fixpoint subst_te (Z : atom) (U : typ) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_abs V e1 => exp_abs   (subst_tt Z U V)  (subst_te Z U e1)
  | exp_app e1 e2 => exp_app  (subst_te Z U e1) (subst_te Z U e2)
  | exp_tabs V e1 => exp_tabs (subst_tt Z U V)  (subst_te Z U e1)
  | exp_tapp e1 V => exp_tapp (subst_te Z U e1) (subst_tt Z U V)
  end.

Fixpoint subst_ee (z : atom) (u : exp) (c : cap) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => if x == z then u else e
  | exp_abs t e1 => exp_abs (subst_ct z c t) (subst_ee z u c e1)
  | exp_app e1 e2 => exp_app (subst_ee z u c e1) (subst_ee z u c e2)
  | exp_tabs t e1 => exp_tabs (subst_ct z c t) (subst_ee z u c e1)
  | exp_tapp e1 t => exp_tapp (subst_ee z u c e1) (subst_ct z c t)
  end.

Definition subst_tb (Z : atom) (P : typ) (b : binding) : binding :=
  match b with
  | bind_sub T => bind_sub (subst_tt Z P T)
  | bind_typ T => bind_typ (subst_tt Z P T)
  end.

Definition subst_cb (Z : atom) (c : cap) (b : binding) : binding :=
  match b with
  | bind_sub T => bind_sub (subst_ct Z c T)
  | bind_typ T => bind_typ (subst_ct Z c T)
  end.

(* ********************************************************************** *)
(** * #<a name="pick_fresh"></a># The "[pick fresh]" tactic *)

(** The "[pick fresh]" tactic introduces a fresh atom into the context.
    We define it in two steps.

    The first step is to define an auxiliary tactic [gather_atoms],
    meant to be used in the definition of other tactics, which returns
    a set of atoms in the current context.  The definition of
    [gather_atoms] follows a pattern based on repeated calls to
    [gather_atoms_with].  The one argument to this tactic is a
    function that takes an object of some particular type and returns
    a set of atoms that appear in that argument.  It is not necessary
    to understand exactly how [gather_atoms_with] works.  If we add a
    new inductive datatype, say for kinds, to our language, then we
    would need to modify [gather_atoms].  On the other hand, if we
    merely add a new type, say products, then there is no need to
    modify [gather_atoms]; the required changes would be made in
    [fv_tt]. *)

Ltac gather_atoms :=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : exp => fv_te x) in
  let D := gather_atoms_with (fun x : exp => fv_ee x) in
  let E := gather_atoms_with (fun x : typ => fv_tt x) in
  let F := gather_atoms_with (fun x : env => dom x) in
  let G := gather_atoms_with (fun x : cap => cset_fvars x) in
  let H := gather_atoms_with (fun x : typ => fv_et x) in
  constr:(A `union` B `union` C `union` D `union` E `union` F `union` G `union` H).

(** The second step in defining "[pick fresh]" is to define the tactic
    itself.  It is based on the [(pick fresh ... for ...)] tactic
    defined in the [Atom] library.  Here, we use [gather_atoms] to
    construct the set [L] rather than leaving it to the user to
    provide.  Thus, invoking [(pick fresh x)] introduces a new atom
    [x] into the current context that is fresh for "everything" in the
    context. *)

Tactic Notation "pick" "fresh" ident(x) :=
  let L := gather_atoms in (pick fresh x for L).


(* *********************************************************************** *)
(** * #<a name="apply_fresh"></a># The "[pick fresh and apply]" tactic *)

(** This tactic is implementation specific only because of its
    reliance on [gather_atoms], which is itself implementation
    specific.  The definition below may be copied between developments
    without any changes, assuming that the other other developments
    define an appropriate [gather_atoms] tactic.  For documentation on
    the tactic on which the one below is based, see the
    [Metatheory] library. *)

Tactic Notation
      "pick" "fresh" ident(atom_name) "and" "apply" constr(lemma) :=
  let L := gather_atoms in
  pick fresh atom_name excluding L and apply lemma.


(* ********************************************************************** *)
(** * #<a name="properties"></a># Properties of opening and substitution *)

(** The following lemmas provide useful structural properties of
    substitution and opening.  While the exact statements are language
    specific, we have found that similar properties are needed in a
    wide range of languages.

    Below, we indicate which lemmas depend on which other lemmas.
    Since [te] functions depend on their [tt] counterparts, a similar
    dependency can be found in the lemmas.

    The lemmas are split into three sections, one each for the [tt],
    [te], and [ee] functions.  The most important lemmas are the
    following:
      - Substitution and opening commute with each other, e.g.,
        [subst_tt_open_tt_var].
      - Opening a term is equivalent to opening the term with a fresh
        name and then substituting for that name, e.g.,
        [subst_tt_intro].

    We keep the sections as uniform in structure as possible.  In
    particular, we state explicitly strengthened induction hypotheses
    even when there are more concise ways of proving the lemmas of
    interest. *)


(* ********************************************************************** *)
(** ** Properties of type substitution in types *)

(** The next lemma is the strengthened induction hypothesis for the
    lemma that follows, which states that opening a locally closed
    term is the identity.  This lemma is not otherwise independently
    useful. *)

Notation "`succ`" := Datatypes.S.

Inductive typeN : nat -> typ -> Prop :=
  | typeN_bvar : forall n m,
      m < n ->
      typeN n (typ_bvar m)
  | typeN_fvar : forall n x,
      typeN n (typ_fvar x)
  | typeN_capt : forall n C P,
      NatSet.F.For_all (fun m => m < n) (cset_bvars C) ->
      pretypeN n P ->
      typeN n (typ_capt C P)
with pretypeN : nat -> pretyp -> Prop :=
  | typeN_top : forall n, pretypeN n typ_top
  | typeN_arrow : forall n T1 T2,
    typeN n T1 ->
    typeN (`succ` n) T2 ->
    pretypeN n (typ_arrow T1 T2)
  | typeN_all : forall n T1 T2,
    typeN n T1 ->
    typeN (`succ` n) T2 ->
    pretypeN n (typ_all T1 T2).

Lemma into_typeN_type_aux : forall n S T,
  typeN n (open_tt_rec n S T) ->
  typeN (`succ` n) T
with into_pretypeN_type_aux : forall n S T,
  pretypeN n (open_tpt_rec n S T) ->
  pretypeN (`succ` n) T.
Proof with eauto*.
{ intros * H.
  dependent induction T.
  - inversion H; subst.
    econstructor.
    2: eapply into_pretypeN_type_aux...
    unfold open_cset, cset_references_bvar_dec in H3.
    destruct_set_mem n (cset_bvars c).
    2: intros i iIn; specialize (H3 i iIn)...
    intros i iIn.
    destruct (i === n).
    + subst...
    + specialize (H3 i ltac:(csetdec))...
  - unfold open_tt_rec in H.
    destruct (n === n0)...
    + subst; constructor...
    + inversion H; subst.
      constructor...
  - constructor.
}
{ intros * H.
  dependent induction T.
  - constructor.
  - inversion H; subst.
    constructor...
  - inversion H; subst.
    constructor...
}
Qed.

Lemma into_typeN_capt_aux : forall n S T,
  typeN n (open_ct_rec n S T) ->
  typeN (`succ` n) T
with into_pretypeN_capt_aux : forall n S T,
  pretypeN n (open_cpt_rec n S T) ->
  pretypeN (`succ` n) T.
Proof with eauto*.
{ intros * H.
  dependent induction T.
  - inversion H; subst.
    econstructor.
    2: eapply into_pretypeN_capt_aux...
    unfold open_cset, cset_references_bvar_dec in H3.
    destruct_set_mem n (cset_bvars c).
    2: intros i iIn; specialize (H3 i iIn)...
    intros i iIn.
    destruct (i === n).
    + subst...
    + specialize (H3 i ltac:(csetdec))...
  - inversion H; subst.
    constructor...
  - constructor.
}
{ intros * H.
  dependent induction T.
  - constructor.
  - inversion H; subst.
    constructor...
  - inversion H; subst.
    constructor...
}
Qed.

Lemma into_typeN : forall t,
  type t -> typeN 0 t
with into_pretypeN : forall t,
  pretype t -> pretypeN 0 t.
Proof with eauto.
{ intros * H.
  dependent induction H.
  - constructor.
  - constructor...
    intros i iIn.
    unfold capt in H.
    exfalso; fnsetdec.
}
{ intros * H.
  dependent induction H.
  - constructor.
  - constructor...
    pick fresh X.
    unfold open_ct in H0.
    eapply (into_typeN_capt_aux 0 X)...
  - constructor...
    pick fresh X.
    unfold open_ct in H0.
    eapply (into_typeN_type_aux 0 X)...
  }
Qed.

Lemma natset_inclusion_lemma : forall (A B : nats),
  B = NatSet.F.union A B ->
  NatSet.F.Subset A B.
Proof.
  intros. unfold NatSet.F.Subset. intros.
  rewrite H. fnsetdec.
Qed.

Lemma atomset_inclusion_lemma : forall (A B : atoms),
  B = AtomSet.F.union A B ->
  AtomSet.F.Subset A B.
Proof.
  intros. unfold AtomSet.F.Subset. intros.
  rewrite H. fsetdec.
Qed.

Lemma idempotent_typeN_open_tt : forall n m S T,
  typeN n T ->
  m >= n ->
  T = (open_tt_rec m S T)
with idempotent_pretypeN_open_tt : forall n m S T,
  pretypeN n T ->
  m >= n ->
  T = (open_tpt_rec m S T).
Proof with eauto*.
{ intros * H1 H2.
  induction T; simpl.
  - inversion H1; subst.
    f_equal...
    unfold open_cset, cset_references_bvar_dec.
    destruct_set_mem m (cset_bvars c)...
    specialize (H4 m mIn); lia.
  - inversion H1; subst.
    destruct_if...
    subst.
    exfalso; lia.
  - easy.
}
{ intros * H1 H2.
  induction T; simpl...
  - inversion H1; subst.
    f_equal...
    eapply idempotent_typeN_open_tt...
    lia.
  - inversion H1; subst.
    f_equal...
    eapply idempotent_typeN_open_tt...
    lia.
}
Qed.

Lemma open_tt_rec_type : forall T U k,
  type T ->
  T = open_tt_rec k U T
with open_tpt_rec_type : forall T U k,
  pretype T ->
  T = open_tpt_rec k U T.
Proof with auto*.
------
  intros T U k Htyp. revert k.
  induction Htyp; intros k; simpl; f_equal...
------
  intros T U k Htyp. revert k.
  induction Htyp; intros k; simpl; f_equal...
  - Case "typ_arrow".
    unfold open_ct in *.
    pick fresh X.
    eapply (idempotent_typeN_open_tt 1).
    2: induction k; auto.
    eapply into_typeN_capt_aux with (S0 := X)...
    eapply into_typeN ...
  - Case "typ_all".
    unfold open_tt in *.
    pick fresh X.
    eapply (idempotent_typeN_open_tt 1).
    2: induction k; auto.
    eapply into_typeN_type_aux with (S0 := X)...
    eapply into_typeN ...
Qed.

(** If a name is fresh for a term, then substituting for it is the
    identity. *)

Lemma subst_tt_fresh : forall Z U T,
   Z `notin` fv_tt T ->
   T = subst_tt Z U T
with subst_tpt_fresh : forall Z U T,
  Z `notin` fv_tpt T ->
  T = subst_tpt Z U T.
Proof with auto*.
------
  induction T; simpl; intro H; f_equal...
  - Case "typ_capt".
    apply subst_cset_fresh...
  - Case "typ_fvar".
    destruct (a == Z)...
    contradict H; fsetdec.
------
  induction T; simpl; intro H; f_equal...
Qed.

(** Substitution commutes with opening under certain conditions.  This
    lemma depends on the fact that opening a locally closed term is
    the identity. *)

Lemma type_implies_capt_cv : forall T,
  type T -> capt (cv T).
Proof with eauto.
  intros. induction H...
  * csetdec.
Qed.

Hint Resolve type_implies_capt_cv : core.

Lemma cv_subst_correspondence : forall x S T,
  (cv (subst_tt x S T)) =
  (subst_cset x (cv S) (cv T)).
Proof with eauto*.
  intros *.
  destruct T; simpl... {
    unfold subst_cset, cset_references_fvar_dec. simpl.
    destruct_set_mem x {}A...
    exfalso; fsetdec.
  }
  destruct (a == x)...
  2: {
    unfold subst_cset, cset_references_fvar_dec. simpl.
    destruct_set_mem x {a}A...
    exfalso; csetdec.
  }
  unfold subst_cset, cset_references_fvar_dec. simpl.
  destruct_set_mem x {a}A.
  2: exfalso; csetdec.
  subst.
  destruct S; csetdec. {
    unfold empty_cset. csetdec.
  }
  unfold cset_fvar. csetdec.
Qed.

Lemma subst_tt_open_tt_rec : forall T1 T2 X P k,
  type P ->
  subst_tt X P (open_tt_rec k T2 T1) =
    open_tt_rec k (subst_tt X P T2) (subst_tt X P T1)
with subst_tpt_open_tpt_rec : forall T1 T2 X P k,
  type P ->
  subst_tpt X P (open_tpt_rec k T2 T1) =
    open_tpt_rec k (subst_tt X P T2) (subst_tpt X P T1).
Proof with auto*.
------
  intros T1 T2 X P k WP. revert k.
  induction T1; intros k; simpl; f_equal...
  - replace (cv (subst_tt X P T2))
      with (subst_cset X (cv P) (cv T2)).
    eapply subst_cset_open_cset_rec...
    symmetry; apply cv_subst_correspondence.
  - Case "typ_bvar".
    destruct (k === n); subst...
  - Case "typ_fvar".
    destruct (a == X); subst... apply open_tt_rec_type...
------
  intros T1 T2 X P k WP. revert k.
  induction T1; intros k; simpl; f_equal...
Qed.

(** The next lemma is a direct corollary of the immediately preceding
    lemma---the index is specialized to zero. *)

Lemma subst_tt_open_tt : forall T1 T2 (X:atom) P,
  type P ->
  subst_tt X P (open_tt T1 T2) = open_tt (subst_tt X P T1) (subst_tt X P T2).
Proof with auto*.
  intros.
  unfold open_tt.
  apply subst_tt_open_tt_rec...
Qed.


(** The next lemma is a direct corollary of the immediately preceding
    lemma---here, we're opening the term with a variable.  In
    practice, this lemma seems to be needed as a left-to-right rewrite
    rule, when stated in its current form. *)

Lemma subst_tt_open_tt_var : forall (X Y:atom) P T,
  Y <> X ->
  type P ->
  open_tt (subst_tt X P T) Y = subst_tt X P (open_tt T Y).
Proof with auto*.
  intros X Y P T Neq Wu.
  unfold open_tt.
  rewrite subst_tt_open_tt_rec...
  simpl.
  destruct (Y == X)...
Qed.

(** The next lemma states that opening a term is equivalent to first
    opening the term with a fresh name and then substituting for the
    name.  This is actually the strengthened induction hypothesis for
    the version we use in practice. *)

Lemma subst_tt_intro_rec : forall X T2 U k,
  X `notin` fv_tt T2 ->
  open_tt_rec k U T2 = subst_tt X U (open_tt_rec k X T2)
with subst_tpt_intro_rec : forall X T2 U k,
  X `notin` fv_tpt T2 ->
  open_tpt_rec k U T2 = subst_tpt X U (open_tpt_rec k X T2).
Proof with auto*.
------
  induction T2; intros U k Fr; simpl in *; f_equal...
  - Case "typ_capt".
    apply subst_cc_intro_rec...
  - Case "typ_bvar".
    destruct (k === n)... simpl. destruct (X == X)...
  - Case "typ_fvar".
    destruct (a == X)... contradict Fr; fsetdec.
------
  induction T2; intros U k Fr; simpl in *; f_equal...
Qed.

(** The next lemma is a direct corollary of the immediately preceding
    lemma---the index is specialized to zero.  *)

Lemma subst_tt_intro : forall X T2 U,
  X `notin` fv_tt T2 ->
  open_tt T2 U = subst_tt X U (open_tt T2 X).
Proof with auto*.
  intros.
  unfold open_tt.
  apply subst_tt_intro_rec...
Qed.


(* ********************************************************************** *)
(** ** Properties of type substitution in expressions *)

(** This section follows the structure of the previous section.  The
    one notable difference is that we require two auxiliary lemmas to
    show that substituting a type in a locally-closed expression is
    the identity. *)

Lemma open_te_rec_expr_aux : forall e j u i P c ,
  open_ee_rec j u c e = open_te_rec i P (open_ee_rec j u c e) ->
  e = open_te_rec i P e.
Proof with eauto.
  induction e; intros j u i P c' H; simpl in *; inversion H; f_equal...
Qed.

Lemma open_te_rec_type_aux : forall e j Q i P,
  i <> j ->
  open_te_rec j Q e = open_te_rec i P (open_te_rec j Q e) ->
  e = open_te_rec i P e.
Proof with eauto using open_tt_rec_type_aux.
  induction e; intros j Q i P Neq Heq; simpl in *; inversion Heq; f_equal...
Qed.


Lemma open_te_rec_expr : forall e U k,
  expr e ->
  e = open_te_rec k U e.
Proof with auto using open_tt_rec_type.
  intros e U k WF; revert k;
  induction WF; intros k; simpl; f_equal; auto using open_tt_rec_type.
  - pick fresh x. eapply open_te_rec_expr_aux. apply H1 with (x := x)...
  - pick fresh x. eapply open_te_rec_type_aux with (j := 0)... apply H1 with (X := x)...
Qed.

Lemma open_te_expr : forall e U,
  expr e ->
  e = open_te e U.
Proof with auto*.
  intros e U Ee.
  apply open_te_rec_expr...
Qed.

Lemma subst_te_fresh : forall X U e,
  X `notin` fv_te e ->
  e = subst_te X U e.
Proof.
  induction e; simpl; intros; f_equal; auto using subst_tt_fresh.
Qed.

Lemma subst_te_open_te_rec : forall e T X U k,
  type U ->
  subst_te X U (open_te_rec k T e) =
    open_te_rec k (subst_tt X U T) (subst_te X U e).
Proof.
  intros e T X U k WU. revert k.
  induction e; intros k; simpl; f_equal; auto using subst_tt_open_tt_rec.
Qed.

Lemma subst_te_open_te : forall e T X U,
  type U ->
  subst_te X U (open_te e T) = open_te (subst_te X U e) (subst_tt X U T).
Proof with auto*.
  intros.
  unfold open_te.
  apply subst_te_open_te_rec...
Qed.

Lemma subst_te_open_te_var : forall (X Y:atom) U e,
  Y <> X ->
  type U ->
  open_te (subst_te X U e) Y = subst_te X U (open_te e Y).
Proof with auto*.
  intros X Y U e Neq WU.
  unfold open_te.
  rewrite subst_te_open_te_rec...
  simpl.
  destruct (Y == X)...
Qed.

Lemma subst_te_intro_rec : forall X e U k,
  X `notin` fv_te e ->
  open_te_rec k U e = subst_te X U (open_te_rec k X e).
Proof.
  induction e; intros U k Fr; simpl in *; f_equal;
    auto using subst_tt_intro_rec.
Qed.

Lemma subst_te_intro : forall X e U,
  X `notin` fv_te e ->
  open_te e U = subst_te X U (open_te e X).
Proof with auto*.
  intros.
  unfold open_te.
  apply subst_te_intro_rec...
Qed.

(* ********************************************************************** *)
(** ** Properties of capture substitution in types *)
(*
(** A warmup, to get started with. *)
Lemma open_cset_singleton : forall i c,
  open_cset i i c = c.
Proof with eauto*.
  intros i c.
  unfold open_cset, cset_union, cset_remove_bvar.
  case_eq (cset_references_bvar_dec i c)...
  destruct c; simpl; unfold cset_references_bvar_dec; intro...
  (* If i isn't in C, this is trivial.  Now we assume i is in C,
     and C isn't the univeral set, as that's also trivial. *)
  f_equal.
  * fsetdec.
  * rewrite_set_facts_in H. fnsetdec.
Qed.

(*
  TODO clean up the proof
*)
Lemma subst_cset_singleton : forall k c C x,
  x `notin` fv_cset C ->
  open_cset k c C = subst_cset x c (open_cset k x C).
Proof with auto.
  intros k c C x H. unfold not in H.
  destruct C...
  destruct (cset_references_bvar_dec k (cset_set t t0)) eqn:Ck...
  - destruct (cset_references_fvar_dec x (cset_set t t0)) eqn:Cf...
    * exfalso. csetdec. rewrite cset_references_fvar_eq in Cf. csetdec.
    * csetdec. simpl in *.
      replace (AtomSet.F.mem x (singleton x `union` t)) with true.
      replace (AtomSet.F.remove x (singleton x `union` t)) with t by fsetdec.
      replace (NatSet.F.union {}N (NatSet.F.remove k t0)) with (NatSet.F.remove k t0) by fnsetdec...
      symmetry.
      rewrite <- AtomSetFacts.mem_iff. fsetdec.
  - autounfold with cset_scope.
    rewrite Ck.
    simpl in *.
    rewrite AtomSetFacts.mem_iff in H.
    destruct (AtomSet.F.mem x t)... contradiction.
Qed.


(** Why fnsetdec doesn't do this for us, I really don't know... *)
Lemma elim_empty_nat_set : forall C,
  NatSet.F.union {}N C = C.
Proof.
  intros. fnsetdec.
Qed.

(** NEW: Opening by a subset is the identity, if the subset contains the index one is opening by. *)
Lemma open_cset_subset_with_index : forall i C c,
  cset_subset_prop C c ->
  cset_references_bvar i C ->
  c = open_cset i C c.
Proof with eauto*.
  intros i C c S.
  unfold open_cset.
  (* Two cases : i in C and i not in C *)
  case_eq (cset_references_bvar_dec i c); intro.
  (* Two more cases : C is universal or not. *)
  * case_eq C; intros.
    ** rewrite H0 in S. inversion S. destruct (cset_remove_bvar i c); destruct c...
    (* Two cases : c is universal or it's not *)
    ** case_eq (c); intros; rewrite H0 in S; rewrite H2 in S; inversion S.
      (** The cases where c is universal are trivial. *)
      *** intuition.
      (** The cases where c isn't universal are a bit more work. *)
      *** csetdec. f_equal...
        **** fsetdec.
        **** fnsetdec.
  * rewrite cset_not_references_bvar_eq in H. intuition.
Qed.


Lemma cset_open_unused_bvar : forall i C c,
  ~ (cset_references_bvar i c) ->
  c = open_cset i C c.
Proof.
  intros i C c H.
  unfold open_cset.
  rewrite <- cset_not_references_bvar_eq in H.
  rewrite H.
  reflexivity.
Qed.


Lemma cset_references_bvar_iff : forall i t1 t2,
  cset_references_bvar i (cset_set t1 t2) <-> NatSet.F.In i t2.
Proof.
  intros. simpl. reflexivity.
Qed.


Hint Resolve cset_references_bvar_iff : cset_scope.

Lemma cset_open_idempotent : forall i C c,
  c = open_cset i C c <->
  ~ (cset_references_bvar i c) \/ (cset_subset_prop C c /\ cset_references_bvar i C).
Proof.
  intros i C c.
  split.
  (* -> *)
  - intros H. destruct (cset_references_bvar_dec i c) eqn:Hic.
    * csethyp. destruct c ; auto.
      simpl in Hic.
      destruct C.
      ** discriminate H.
      ** inversion H. right. split.
        *** eapply cset_subset_elem ; csetdec.
        *** inversion H. rewrite H2 in Hic. csetdec.
    * left. apply cset_not_references_bvar_eq. auto.
  (* <-  *)
  - intros H. destruct H.
    * auto using cset_open_unused_bvar.
    * destruct H ; auto using open_cset_subset_with_index.
Qed.


Lemma capt_from_empty_cset_bvars : forall C,
  empty_cset_bvars C ->
  capt C.
Proof with auto.
  intros C H.
  destruct C.
  - constructor...
  - assert (t0 = {}N). { unfold empty_cset_bvars in *. unfold cset_all_bvars in *. fnsetdec. }
    subst.
    econstructor.
Qed.

Lemma open_cset_capt : forall i C c,
  capt C ->
  C = open_cset i c C.
Proof with eauto*.
  intros i C c H.
  destruct H; cset_split; destruct c eqn:Hc...
  - exfalso. unfold cset_references_bvar_dec in *. apply NatSetFacts.mem_iff in H_destruct.
    fnsetdec.
  - exfalso. unfold cset_references_bvar_dec in *. apply NatSetFacts.mem_iff in H_destruct.
    fnsetdec.
Qed.

(** NEW: Commuting local closure, when opening by disjoint capture sets with no bound variables,
    which are not universal.

    c[j -> D] = c[j -> D][i -> C] implies that i \notin c and in particular c[i -> C] = c,
    so long as D references no free variables (and isn't the universal set).

    Can that lemma be strengthened to

      i <> j ->
      open_ct_rec i c1 t = open_ct_rec j c2 (open_ct_rec i c1 t) ->
      t = open_ct_rec j c2 t.
    ?
*)
Lemma open_cset_aux : forall j D i C c,
  i <> j ->
  empty_cset_bvars D ->
  (fv_cset C) `disjoint` (fv_cset D) ->
  open_cset j D c = open_cset i C (open_cset j D c) ->
  c = open_cset i C c.
Proof with eauto*.
  intros j D i C c Neq Closed Disj H.

  rewrite (cset_open_idempotent i C (open_cset j D c)) in H.

  rewrite cset_open_idempotent.

  destruct (cset_references_bvar_dec i c) eqn:Hic.
  (* i is in c *)
  - destruct (cset_references_bvar_dec j c) eqn:Hjc ; csethyp...
    destruct H.
    * destruct D ; destruct c ; csethyp ; auto.
      left. fnsetdec.
    * destruct H. destruct C eqn:HC.
      ** contradiction.
      ** unfold empty_cset_bvars in Closed. unfold cset_all_bvars in *. destruct D ; destruct c eqn:Hc ; eauto.
         right. split...
         inversion H ; csethyp ; simpl in *. constructor. unfold disjoint in *. fsetdec. fnsetdec.
  (* i is not in c *)
  - left. apply cset_not_references_bvar_eq. apply Hic.
Qed.
*)

Hint Unfold disjoint : core.

(** Opening a capture set under some circumstances is the identity *)
Lemma open_ct_rec_capt_aux : forall T j Df Du i C,
  i <> j ->
  (cset_fvars C) `disjoint` Df ->
  (andb Du (cset_has_universal C)) = false ->
  open_ct_rec j (cset_set Df {}N Du) T = open_ct_rec i C (open_ct_rec j (cset_set Df {}N Du) T) ->
  T = open_ct_rec i C T
with open_cpt_rec_capt_aux : forall T j Df Du i C,
  i <> j ->
  (cset_fvars C) `disjoint` Df ->
  (andb Du (cset_has_universal C)) = false ->
  open_cpt_rec j (cset_set Df {}N Du) T = open_cpt_rec i C (open_cpt_rec j (cset_set Df {}N Du) T) ->
  T = open_cpt_rec i C T.
Proof with eauto*.
------
  induction T; intros j Df Du i C Neq; intros HCommon HCommonU H;
    simpl in *; inversion H; f_equal...
  apply open_cset_rec_capt_aux with (j := j) (V := cset_set Df {}N Du) ; simpl in *...
  * autounfold in *. simpl in *; fsetdec.
------
  induction T; intros j Df Du i C Neq; intros HCommon HCommonU H;
    simpl in *; inversion H; f_equal...
Qed.

Lemma open_ct_rec_capt : forall T j D i C,
  i <> j ->
  (* can't change this to `capt D` since then D can be universal. *)
  capt D ->
  (cset_fvars C) `disjoint` (cset_fvars D) ->
  (andb (cset_has_universal C) (cset_has_universal D)) = false ->
  open_ct_rec j D T = open_ct_rec i C (open_ct_rec j D T) ->
  T = open_ct_rec i C T
with open_cpt_rec_capt : forall T j D i C,
  i <> j ->
  (* can't change this to `capt D` since then D can be universal. *)
  capt D ->
  (cset_fvars C) `disjoint` (cset_fvars D) ->
  (andb (cset_has_universal C) (cset_has_universal D)) = false ->
  open_cpt_rec j D T = open_cpt_rec i C (open_cpt_rec j D T) ->
  T = open_cpt_rec i C T.
Proof with eauto using open_cset_rec_capt_aux.
------
  induction T; intros j D i C Neq Closed; intros HCommon HcommonU H; simpl in *; inversion H; f_equal...
    eapply open_cset_rec_capt_aux with (V := D)...
  * destruct C; destruct D; simpl; destr_bool...
  * autounfold in *; fsetdec...
------
  induction T; intros j D i C Neq Closed; intros HCommon HcommonU H; simpl in *; inversion H; f_equal...
Qed.

(** NEW: Opening with a type and capture variable commute... *)
Lemma open_ct_rec_type_aux : forall T j S i C,
  open_tt_rec j S T = open_ct_rec i C (open_tt_rec j S T) ->
  T = open_ct_rec i C T
with open_cpt_rec_type_aux : forall T j S i C,
  open_tpt_rec j S T = open_cpt_rec i C (open_tpt_rec j S T) ->
  T = open_cpt_rec i C T.
Proof with eauto*.
------
  induction T; intros j C i S H; simpl in *; inversion H; f_equal...
  replace c with (open_cset j c c)...
------
  induction T; intros j C i S H; simpl in *; inversion H; f_equal...
Qed.

(** NEW: The new lemma for opening a locally closed type by a capture set
    Hint: it's the identity function. *)
Lemma open_ct_rec_type : forall T C k,
  type T ->
  T = open_ct_rec k C T
with open_cpt_rec_type : forall T C k,
  pretype T ->
  T = open_cpt_rec k C T.
Proof with auto*.
------
  intros T C k Htyp. revert k.
  induction Htyp; intros k; simpl; f_equal...
------
  intros T C k Htyp. revert k.
  induction Htyp; intros k; simpl; f_equal...
  (* Case typ_arrow *)
  * (* Here, we are opening (\ T1 -> T2), assuming that this is locally closed.
       Hence T1 is locally closed, so by the induction hypothesis it goes away.
       T2 isn't locally closed, but the only open capture variable in it is bound by \0. *)
    pick fresh X.
    unfold open_ct in *.
    unfold cset_fvar in H0.
    assert (X `notin` L) by fsetdec.
    apply open_ct_rec_capt_aux with (Du := false) (i := S k) (j := 0) (Df := (AtomSet.F.singleton X)) (C := C) (T := T2)...
    unfold disjoint.
    fsetdec.
  (* Case typ_all *)
  * pick fresh X.
    unfold open_tt in *.
    apply open_ct_rec_type_aux with (j := 0) (S := X)...
Qed.




(*
   TODO maybe we need to strengthen the lemma again for other use cases?
 *)
Lemma subst_tt_open_ct_rec : forall (X : atom) P T C k,
  type P ->
  X `notin` cset_fvars C ->
  subst_tt X P (open_ct_rec k C T) = open_ct_rec k C (subst_tt X P T)
with subst_tpt_open_cpt_rec : forall (X : atom) P T C k,
  type P ->
  X `notin` cset_fvars C ->
  subst_tpt X P (open_cpt_rec k C T) = open_cpt_rec k C (subst_tpt X P T).
Proof with auto using open_cset_capt, open_cpt_rec_type.
------
  intros X P T C.
  induction T ; intros ; simpl; f_equal...
  - assert (C = subst_cset X (cv P) C). apply subst_cset_fresh...
    rewrite H1 at 2.
    eapply subst_cset_open_cset_rec...
  - destruct (a == X)...
    inversion H ; simpl ; f_equal; subst...
------
  intros X P T C.
  induction T ; intros ; simpl; f_equal...
Qed.

(* T[0 !-> C][X !-> P] = T[X !-> P][0 !-> C] *)
Lemma subst_tt_open_ct : forall (X : atom) P T C,
  type P ->
  X `notin` cset_fvars C ->
  subst_tt X P (open_ct T C) = open_ct (subst_tt X P T) C.
Proof with auto*.
  intros X P T C.
  unfold open_ct.
  apply subst_tt_open_ct_rec...
Qed.

(* ********************************************************************** *)
(** ** Properties of expression substitution in expressions *)

(** This section follows the structure of the previous two sections. *)

Lemma open_ee_rec_expr_aux : forall e j v u C D i,
  i <> j ->
  (* Does D _need_ to be a concrete capture set here?
     open_ct_rec_capt requires this.
   *)
  capt D ->
  (cset_fvars C) `disjoint` (cset_fvars D) ->
  (andb (cset_has_universal C) (cset_has_universal D)) = false ->
  open_ee_rec j v D e = open_ee_rec i u C (open_ee_rec j v D e) ->
  e = open_ee_rec i u C e.
Proof with eauto using open_ct_rec_capt.
  induction e; intros j v u C D i Neq Closed Disj DisjU H; simpl in *; inversion H; f_equal...
  - Case "exp_bvar".
    destruct (j===n)... destruct (i===n)... subst. destruct Neq...
Qed.

Lemma open_ee_rec_type_aux : forall e j V u c i,
  open_te_rec j V e = open_ee_rec i u c (open_te_rec j V e) ->
  e = open_ee_rec i u c e.
Proof with eauto using open_ct_rec_type_aux.
  induction e; intros j V u c' i H; simpl; inversion H; f_equal...
Qed.

Lemma open_ee_rec_expr : forall u c e k,
  expr e ->
  e = open_ee_rec k u c e.
Proof with auto*.
  intros u c e k Hexpr. revert k.
  induction Hexpr; intro k; simpl; f_equal; auto*.
  - pick fresh x. apply open_ct_rec_type...
  - pick fresh x.
    specialize H1 with (x := x) (k := S k).
    apply open_ee_rec_expr_aux with (j := 0) (v := x) (D := (cset_fvar x));
      simpl...
    * autounfold in *. fsetdec.
  - apply open_ct_rec_type...
  - pick fresh x. eapply open_ee_rec_type_aux with (V := x). apply H1...
  - apply open_ct_rec_type...
Qed.

Lemma subst_ct_fresh : forall (x: atom) c t,
  x `notin` fv_et t ->
  t = subst_ct x c t
with subst_cpt_fresh : forall (x: atom) c t,
  x `notin` fv_ept t ->
  t = subst_cpt x c t.
Proof with eauto using subst_cset_fresh.
------
  intros x c t. induction t; intro H ; simpl in *; f_equal...
------
  intros x c t. induction t; intro H ; simpl in *; f_equal...
Qed.

Lemma subst_ee_fresh : forall (x: atom) u c e,
  x `notin` fv_ee e ->
  e = subst_ee x u c e.
Proof with auto using subst_ct_fresh.
  intros x u c e; induction e; simpl ; intro H ; f_equal...
  - Case "exp_fvar".
    destruct (a==x)...
    contradict H; fsetdec.
Qed.

Lemma subst_ct_open_rec : forall x k c1 c2 t,
  capt c1 ->
  subst_ct x c1 (open_ct_rec k c2 t) =
  open_ct_rec k (subst_cset x c1 c2) (subst_ct x c1 t)
with subst_cpt_open_rec : forall x k c1 c2 t,
  capt c1 ->
  subst_cpt x c1 (open_cpt_rec k c2 t) =
  open_cpt_rec k (subst_cset x c1 c2) (subst_cpt x c1 t).
Proof with auto using subst_cset_open_cset_rec.
------
  intros x k c1 c2 t. revert c1 c2 k x.
  induction t ; intros c1 c2 k x c1empt;
    unfold open_ct_rec; unfold subst_ct; fold open_ct_rec; fold subst_ct;
    f_equal; try solve [apply subst_cset_open_cset_rec; eauto].
  apply subst_cpt_open_rec.
  trivial.
------
  intros x k c1 c2 t. revert c1 c2 k x.
  induction t ; intros c1 c2 k x c1empt;
    unfold open_cpt_rec; unfold subst_ct; unfold subst_cpt; f_equal...
Qed.

Lemma subst_ee_open_ee_rec : forall e1 e2 x u c1 c2 k,
  expr u ->
  capt c1 ->
  subst_ee x u c1 (open_ee_rec k e2 c2 e1) =
    open_ee_rec k (subst_ee x u c1 e2) (subst_cset x c1 c2) (subst_ee x u c1 e1).
Proof with auto using subst_ct_open_rec.
  intros e1 e2 x u c1 c2 k Wu Wc. revert k.
  induction e1; intros k; simpl; f_equal...
  Case "exp_bvar".
    destruct (k === n); subst...
  Case "exp_fvar".
    destruct (a == x); subst... apply open_ee_rec_expr...
Qed.

Lemma subst_ee_open_ee : forall e1 e2 x u c1 c2,
  expr u ->
  capt c1 ->
  subst_ee x u c1 (open_ee e1 e2 c2) =
    open_ee (subst_ee x u c1 e1) (subst_ee x u c1 e2) (subst_cset x c1 c2).
Proof with auto*.
  intros.
  unfold open_ee.
  apply subst_ee_open_ee_rec...
Qed.

Lemma subst_ee_open_ee_var : forall (x y:atom) u c e,
  y <> x ->
  expr u ->
  capt c ->
  open_ee (subst_ee x u c e) y (cset_fvar y) = subst_ee x u c (open_ee e y (cset_fvar y)).
Proof with auto*.
  intros x y u c e Neq Wu Wc.
  unfold open_ee.
  rewrite subst_ee_open_ee_rec...
  simpl.
  destruct (y == x)...

  (* TODO factor into a tactic *)
  unfold subst_cset; simpl.
  destruct_set_mem x (cset_fvar y)...
  unfold cset_references_fvar, cset_fvars, cset_fvar in *; fsetdec.
Qed.

(** This should move into infrastructure probably at some point. **)
(** The next lemma states that opening a term is equivalent to first
    opening the term with a fresh name and then substituting for the
    name.  This is actually the strengthened induction hypothesis for
    the version we use in practice. *)

Lemma subst_ct_intro_rec : forall X T2 C k,
  X `notin` fv_et T2 ->
  open_ct_rec k C T2 = subst_ct X C (open_ct_rec k X T2)
with subst_cpt_intro_rec : forall X T2 C k,
  X `notin` fv_ept T2 ->
  open_cpt_rec k C T2 = subst_cpt X C (open_cpt_rec k X T2).
Proof with auto*.
------
  induction T2; intros C k Fr; simpl in *; f_equal...
  - Case "typ_cset".
    apply subst_cc_intro_rec.
    csetdec; destruct c...
------
  induction T2; intros C k Fr; simpl in *; f_equal...
Qed.

(** The next lemma is a direct corollary of the immediately preceding
    lemma---the index is specialized to zero.  *)
Lemma subst_ct_intro : forall X T2 C,
  X `notin` fv_et T2 ->
  open_ct T2 C = subst_ct X C (open_ct T2 X).
Proof with auto*.
  intros.
  unfold open_tt.
  apply subst_ct_intro_rec...
Qed.

Lemma subst_cset_open_cset_fresh : forall k X C1 C2 c,
  capt C1 ->
  capt C2 ->
  ~ cset_references_fvar X C2 ->
  subst_cset X C1 (open_cset k C2 c) = open_cset k C2 (subst_cset X C1 c).
Proof with auto*.
  intros.
  assert (C2 = subst_cset X C1 C2). {
    unfold subst_cset; rewrite_set_facts_back_in H1...
    rewrite H1...
  }
  rewrite H2 at 2.
  eapply subst_cset_open_cset_rec...
Qed.

(* unfold subst_cset; unfold open_cset;
  cset_split; cset_cleanup;
  destruct C2 eqn:HC2; destruct C1 eqn:HC1; try destruct c eqn:Hc;
  f_equal; subst; try fsetdec; try fnsetdec. *)
(* all: inversion H; inversion H0; subst; fnsetdec. *)

Lemma subst_ct_open_ct_rec : forall (X : atom) C1 T C2 k,
  capt C1 ->
  capt C2 ->
  ~ cset_references_fvar X C2 ->
  subst_ct X C1 (open_ct_rec k C2 T) = open_ct_rec k C2 (subst_ct X C1 T)
with subst_cpt_open_cpt_rec : forall (X : atom) C1 T C2 k,
  capt C1 ->
  capt C2 ->
  ~ cset_references_fvar X C2 ->
  subst_cpt X C1 (open_cpt_rec k C2 T) = open_cpt_rec k C2 (subst_cpt X C1 T).
Proof with auto.
------
  intros X C1 T C2.
  induction T; intros; simpl; try trivial.

  f_equal.
  - apply subst_cset_open_cset_fresh...
  - apply subst_cpt_open_cpt_rec...
------
  intros X C1 T C2.
  induction T; intros; simpl; try trivial.
  - f_equal; apply subst_ct_open_ct_rec...
  - f_equal; apply subst_ct_open_ct_rec...
Qed.



Lemma subst_ct_open_tt_rec_fresh : forall c z P t k,
  capt c ->
  z `notin` fv_et P ->
  subst_ct z c (open_tt_rec k P t) = open_tt_rec k P (subst_ct z c t)
with subst_cpt_open_tpt_rec_fresh : forall c z P t k,
  capt c ->
  z `notin` fv_et P ->
  subst_cpt z c (open_tpt_rec k P t) = open_tpt_rec k P (subst_cpt z c t).
Proof with eauto.
------
  induction t ; intros ; simpl ; f_equal...
  - rewrite <- idempotent_open_cset_self.
    rewrite <- idempotent_open_cset_self...
  - Case "exp_bvar".
    destruct (k === n)... symmetry.
    apply subst_ct_fresh...
------
  induction t ; intros ; simpl ; f_equal...
Qed.

Lemma subst_ct_open_tt_var : forall (X Y:atom) C T,
  Y <> X ->
  capt C ->
  open_tt (subst_ct X C T) Y = subst_ct X C (open_tt T Y).
Proof with auto*.
  intros X Y P T Neq Wu.
  unfold open_tt.
  rewrite subst_ct_open_tt_rec_fresh...
Qed.

Lemma subst_ct_open_ct_var : forall (x y:atom) c t,
  y <> x ->
  capt c ->
  (open_ct (subst_ct x c t) (cset_fvar y)) = (subst_ct x c (open_ct t (cset_fvar y))).
Proof with auto*.
  intros *; intros Neq Wu.
  unfold open_ct.
  symmetry.
  apply subst_ct_open_ct_rec...
  - cbv [cset_references_fvar cset_fvars cset_fvar]. (* like unfold but a bit different *)
    fsetdec.
Qed.

Lemma subst_te_open_ee_rec : forall e1 e2 c Z P k,
  type P ->
  Z `notin` cset_fvars c ->
  subst_te Z P (open_ee_rec k e2 c e1) =
    open_ee_rec k (subst_te Z P e2) c (subst_te Z P e1).
Proof with eauto using subst_tt_open_ct_rec.
  induction e1; intros e2 c' Z P k Tpe Zfr; simpl; f_equal...
  Case "exp_bvar".
    destruct (k === n)...
Qed.

Lemma subst_te_open_ee : forall e1 e2 c Z P,
  type P ->
  Z `notin` cset_fvars c ->
  subst_te Z P (open_ee e1 e2 c) = open_ee (subst_te Z P e1) (subst_te Z P e2) c.
Proof with auto*.
  intros.
  unfold open_ee.
  apply subst_te_open_ee_rec...
Qed.

Lemma subst_te_open_ee_var : forall Z (x:atom) P e c,
  type P ->
  Z `notin` cset_fvars c ->
  open_ee (subst_te Z P e) x c = subst_te Z P (open_ee e x c).
Proof with auto*.
  intros.
  rewrite subst_te_open_ee...
Qed.

Lemma subst_ee_open_te_rec : forall e P z u c k,
  expr u ->
  capt c ->
  z `notin` fv_et P ->
  subst_ee z u c (open_te_rec k P e) = open_te_rec k P (subst_ee z u c e).
Proof with eauto using subst_ct_open_tt_rec_fresh.
  induction e; intros P z u c' k H Hc Hfv; simpl; f_equal...
  Case "exp_fvar".
    destruct (a == z)... apply open_te_rec_expr...
Qed.

Lemma subst_ee_open_te : forall e P z u c,
  expr u ->
  capt c ->
  z `notin` fv_et P ->
  subst_ee z u c (open_te e P) = open_te (subst_ee z u c e) P.
Proof with auto*.
  intros.
  unfold open_te.
  apply subst_ee_open_te_rec...
Qed.

Lemma subst_ee_open_te_var : forall z (X:atom) u c e,
  expr u ->
  capt c ->
  open_te (subst_ee z u c e) X = subst_ee z u c (open_te e X).
Proof with auto*.
  intros z X u c e Wu Wc.
  rewrite subst_ee_open_te...
Qed.

(* if x is fresh, opening with {x} and then substituting is the same as opening directly. *)
Lemma open_ct_subst_ct_var : forall x c t k,
  x `notin` fv_et t ->
  open_ct_rec k c t = subst_ct x c (open_ct_rec k (cset_fvar x) t)
with open_cpt_subst_cpt_var : forall x c t k,
  x `notin` fv_ept t ->
  open_cpt_rec k c t = subst_cpt x c (open_cpt_rec k (cset_fvar x) t).
Proof with auto.
------
  induction t ; intros ; simpl in * ; f_equal...
  apply subst_cc_intro_rec...
------
  induction t ; intros ; simpl in * ; f_equal...
Qed.



Lemma subst_ee_intro_rec : forall x e u c k,
  x `notin` fv_ee e ->
  open_ee_rec k u c e = subst_ee x u c (open_ee_rec k (exp_fvar x) (cset_fvar x) e).
Proof with eauto using open_ct_subst_ct_var.
  induction e; intros u c' k Fr; simpl in *; f_equal...
  - Case "exp_bvar".
    destruct (k === n)... simpl. destruct (x == x)... contradiction.
  - Case "exp_fvar".
    destruct (a == x)... contradict Fr; fsetdec.
Qed.

Lemma subst_ee_intro : forall x e u c,
  x `notin` fv_ee e ->
  open_ee e u c = subst_ee x u c (open_ee e x (cset_fvar x)).
Proof with auto*.
  intros.
  unfold open_ee.
  apply subst_ee_intro_rec...
Qed.


(* *********************************************************************** *)
(** * #<a name="lc"></a># Local closure is preserved under substitution *)

(** While these lemmas may be considered properties of substitution, we
    separate them out due to the lemmas that they depend on. *)

(** The following lemma depends on [subst_tt_open_tt_var]. *)

Lemma subst_tt_type : forall Z P T,
  type T ->
  type P ->
  type (subst_tt Z P T)
with subst_tpt_type : forall Z P T,
  pretype T ->
  type P ->
  pretype (subst_tpt Z P T).
Proof with auto.
------
  intros Z P T HT HP.
  induction HT; simpl...
  - Case "type_fvar".
    destruct (X == Z)...
------
  intros Z P T HT HP.
  induction HT; simpl...
  - Case "type_arrow".
    pick fresh Y and apply type_arrow...
    rewrite <- subst_tt_open_ct...
  - Case "type_all".
    pick fresh Y and apply type_all...
    rewrite subst_tt_open_tt_var...
Qed.


(** The following lemma depends on [subst_tt_type] and
    [subst_te_open_ee_var]. *)

Lemma subst_te_expr : forall Z P e,
  expr e ->
  type P ->
  expr (subst_te Z P e).
Proof with eauto using subst_tt_type.
  intros Z P e He Hp.
  induction He; simpl ; econstructor...
  (* case exp_abs *)
  - instantiate (1 := L `union` singleton Z). intros.
   rewrite subst_te_open_ee_var.
   apply H1.
   fsetdec.
   apply Hp...
   csetdec.

  (* case exp_tabs *)
  - instantiate (1 := L `union` singleton Z). intros.
    rewrite subst_te_open_te_var. apply H1. fsetdec. fsetdec. auto.
Qed.

(** The following lemma depends on [subst_ee_open_ee_var] and
    [subst_ee_open_te_var].

    This lemma can be cleaned up quite a bit -- just making it go through for now.
*)

Local Hint Extern 1 (~ AtomSet.F.In _ _) => simpl_env in *; [fsetdec] : core.

Lemma subst_ct_open_fresh : forall k z C T X,
  (* X fresh requirement here in z c T *)
  X `notin` (singleton z `union` fv_tt T `union` fv_et T) 
    /\ X `notin` cset_fvars C ->
  capt C ->
  (open_ct_rec k (cset_fvar X) (subst_ct z C T)) =
    (subst_ct z C (open_ct_rec k (cset_fvar X) T))
with subst_cpt_open_fresh : forall k z C T X,
    (* X fresh requirement here in z c T *)
    X `notin` (singleton z `union` fv_tpt T `union` fv_ept T)
      /\ X `notin` cset_fvars C ->
    capt C ->
    (open_cpt_rec k (cset_fvar X) (subst_cpt z C T)) =
      (subst_cpt z C (open_cpt_rec k (cset_fvar X) T)).
Proof with eauto*.
------
  intros k z C T X HXfresh HCfresh. revert k.
  induction T; intro k; simpl in *; try reflexivity.
  * (* Case typ_capt *)
    f_equal...
    (** pull this out into a tactic.*)
    symmetry.
    assert (cset_fvar X = subst_cset z C X). {
      cbv [subst_cset]; csetdec.
    }
    rewrite H at 2.
    apply subst_cset_open_cset_rec...
------
  intros k z C T X HXfresh HCfresh. revert k.
  induction T; intro k; simpl in *; try reflexivity; f_equal...
Qed.

Lemma open_tt_subst_ct_aux : forall k X z C T,
  X `notin` cset_fvars C ->
  open_tt_rec k X (subst_ct z C T) =
  subst_ct z C (open_tt_rec k X T)
with open_tpt_subst_ct_aux : forall k X z C T,
  X `notin` cset_fvars C ->
  open_tpt_rec k X (subst_cpt z C T) =
  subst_cpt z C (open_tpt_rec k X T).
Proof with eauto*.
------
  intros k X z C T HXfresh. revert k. induction T; intro k; simpl in *; f_equal...
  - rewrite <- idempotent_open_cset_self.
    rewrite <- idempotent_open_cset_self...
  - destruct (k === n)...
------
  intros k X z C T HXfresh. revert k. induction T; intro k; simpl in *; f_equal...
Qed.

Lemma subst_ct_type : forall T z c,
  type T ->
  capt c ->
  type (subst_ct z c T)
with subst_cpt_type : forall T z c,
  pretype T ->
  capt c ->
  pretype (subst_cpt z c T).
Proof with auto.
------
  intros T z c Tpe Closed.
  induction Tpe; simpl; try econstructor...
------
  intros T z c Tpe Closed.
  induction Tpe; simpl; try econstructor...
  - let F := gather_atoms in instantiate (1 := F).
    intros X HXfresh.
    assert ((open_ct (subst_ct z c T2) (cset_fvar X)) =
            (subst_ct z c (open_ct T2 (cset_fvar X)))).
    { apply subst_ct_open_fresh. split. fsetdec. destruct c; fsetdec. apply Closed. }
    rewrite H1...
  (* Can we use subst_ct_fresh??? -- no, that requires z to be fresh; but we get a simple
      helper lemma above for the equality. *)
  - let F := gather_atoms in instantiate (1 := F).
    intros X HXfresh.
    assert ((open_tt (subst_ct z c T2) X) = (subst_ct z c (open_tt T2 X))).
    { apply open_tt_subst_ct_aux. destruct c... }
    rewrite H1...
Qed.

(* TODO clean up the proof here *)
Lemma subst_ee_expr : forall z e1 e2 c,
  expr e1 ->
  expr e2 ->
  capt c ->
  expr (subst_ee z e2 c e1).
Proof with eauto using subst_ct_type.
  intros z e1 e2 c He1 He2 Closed. revert z.

  induction He1; intro z; simpl; auto;
  try solve [
    econstructor; eauto using subst_ct_type;
    try let F := gather_atoms in instantiate (1 := F);
    intros;
    try rewrite subst_ee_open_ee_var;
    try rewrite subst_ee_open_te_var;
    eauto
  ].
  - destruct (x == z)...
Qed.



(* *********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

(** We add as hints the fact that local closure is preserved under
    substitution.  This is part of our strategy for automatically
    discharging local-closure proof obligations. *)

Hint Resolve subst_tt_type subst_te_expr subst_ee_expr : core.



(** When reasoning about the [binds] relation and [map], we
    occasionally encounter situations where the binding is
    over-simplified.  The following hint undoes that simplification,
    thus enabling [Hint]s from the [Environment] library. *)

Hint Extern 1 (binds _ (?F (subst_tt ?X ?U ?T)) _) =>
  unsimpl (subst_tb X U (F T)) : core.

Hint Extern 1 (binds _ (?F (subst_ct ?X ?U ?C)) _) =>
  unsimpl (subst_cb X U (F C)) : core.

(** Tactic that matches the goal for `open_ct ?T ?C` and tries
    to prove that `type ?T`. *)

Ltac closed_type :=
  repeat (match goal with
    | [ |- context[open_ct ?T ?C] ] =>
      replace (open_ct T C) with T ;
      auto ;
      try apply open_ct_rec_type ;
      auto
    | [ |- context[open_tt ?T ?C] ] =>
      replace (open_tt T C) with T ;
      auto ;
      try apply open_tt_rec_type ;
      auto
  end).

(** More substitution lemmas *)
  
Lemma subst_ct_open_tt_rec : forall c z P t k,
  capt c ->
  subst_ct z c (open_tt_rec k P t) = open_tt_rec k (subst_ct z c P) (subst_ct z c t)
with subst_cpt_open_tpt_rec : forall c z P t k,
  capt c ->
  subst_cpt z c (open_tpt_rec k P t) = open_tpt_rec k (subst_ct z c P) (subst_cpt z c t).
Proof with eauto.
------
  induction t ; intros ; simpl ; f_equal...
  - rewrite <- idempotent_open_cset_self.
    rewrite <- idempotent_open_cset_self...
  - Case "exp_bvar".
    destruct (k === n)... 
------
  induction t ; intros ; simpl ; f_equal...
Qed.

Lemma subst_ct_open_tt : forall x c t1 t2,
  capt c ->
  subst_ct x c (open_tt t1 t2) = (open_tt (subst_ct x c t1) (subst_ct x c t2)).
Proof with auto using open_cset_capt, open_cpt_rec_type, subst_ct_open_tt_rec.
  intros * Hcapt.
  cbv [open_tt].
  apply subst_ct_open_tt_rec...
Qed.

Lemma subst_ct_open_ct : forall x c1 T c2,
  capt c1 ->
  subst_ct x c1 (open_ct T c2) = (open_ct (subst_ct x c1 T) (subst_cset x c1 c2)).
Proof with auto using open_cset_capt, open_cpt_rec_type, subst_ct_open_rec.
  intros * Hcapt.
  induction T... eapply subst_ct_open_rec...
Qed.

Lemma open_ct_subst_tt : forall x C S T,
  type S ->
  x `notin` cset_fvars C ->
  open_ct (subst_tt x S T) C = subst_tt x S (open_ct T C).
Proof with auto using open_cset_capt, open_cpt_rec_type, subst_ct_open_rec,
  subst_ct_open_tt_var, open_ct_subst_ct_var.
  intros * HS Hfr.
  cbv [open_ct]...
  pick fresh y for (fv_et (subst_tt x S T)).
  erewrite open_ct_subst_ct_var. 
  erewrite subst_tt_open_ct_rec.
  erewrite <-subst_ct_intro_rec.
  all: eauto.
Qed.

Lemma subst_tt_open_ct_var : forall (X y:atom) P T,
  y <> X ->
  type P ->
  (open_ct (subst_tt X P T) (cset_fvar y)) = (subst_tt X P (open_ct T (cset_fvar y))).
Proof with auto*.
  intros *; intros Neq Wu.
  unfold open_ct.
  symmetry.
  apply subst_tt_open_ct_rec; trivial.
  notin_solve.
Qed.

Lemma subst_ct_useless_repetition : forall x C D T,
  x `notin` cset_fvars D ->
  subst_ct x C (subst_ct x D T) = (subst_ct x D T)
with subst_cpt_useless_repetition : forall x C D T,
  x `notin` cset_fvars D ->
  subst_cpt x C (subst_cpt x D T) = (subst_cpt x D T).
Proof with auto.
{ intros.
  induction T; simpl; try reflexivity.
  rewrite subst_cset_useless_repetition.
  rewrite subst_cpt_useless_repetition.
  all : trivial.
}
{ intros.
  induction T; simpl; try reflexivity.
  - rewrite subst_ct_useless_repetition.
    rewrite subst_ct_useless_repetition.
    all : trivial.
  - rewrite subst_ct_useless_repetition.
    rewrite subst_ct_useless_repetition.
    all : trivial.
}
Qed.
