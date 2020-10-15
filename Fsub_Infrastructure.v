(** Infrastructure lemmas and tactic definitions for Fsub.

    Authors: Brian Aydemir and Arthur Chargu\u00e9raud, with help from
    Aaron Bohannon, Jeffrey Vaughan, and Dimitrios Vytiniotis.

    This file contains a number of definitions, tactics, and lemmas
    that are based only on the syntax of the language at hand.  While
    the exact statements of everything here would change for a
    different language, the general structure of this file (i.e., the
    sequence of definitions, tactics, and lemmas) would remain the
    same.

    Table of contents:
      - #<a href="##fv">Free variables</a>#
      - #<a href="##subst">Substitution</a>#
      - #<a href="##pick_fresh">The "pick fresh" tactic</a>#
      - #<a href="##apply_fresh">The "pick fresh and apply" tactic</a>#
      - #<a href="##properties">Properties of opening and substitution</a>#
      - #<a href="##lc">Local closure is preserved under substitution</a>#
      - #<a href="##auto">Automation</a># *)


Require Export Fsub_Definitions.


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
  | typ_top => {}
  | typ_bvar J => {}
  | typ_fvar X => singleton X
  | typ_arrow T1 T2 => (fv_tt T1) `union` (fv_tt T2)
  | typ_all T1 T2 => (fv_tt T1) `union` (fv_tt T2)
  | typ_capt C T => fv_tt T
  end.

(* Only in TERM variables in types should capture sets be mentioned *)
Fixpoint fv_et (T : typ) {struct T} : atoms :=
  match T with
  | typ_top => {}
  | typ_bvar J => {}
  | typ_fvar X => {}
  | typ_arrow T1 T2 => (fv_et T1) `union` (fv_et T2)
  | typ_all T1 T2 => (fv_et T1) `union` (fv_et T2)
  | typ_capt C T => (cset_fvar C) `union` (fv_et T)
  end.

Fixpoint fv_te (e : exp) {struct e} : atoms :=
  match e with
  | exp_bvar i => {}
  | exp_fvar x => {}
  | exp_abs V e1  => (fv_tt V) `union` (fv_te e1)
  | exp_app e1 e2 => (fv_te e1) `union` (fv_te e2)
  | exp_tabs V e1 => (fv_tt V) `union` (fv_te e1)
  | exp_tapp e1 V => (fv_tt V) `union` (fv_te e1)
  end.

Fixpoint fv_ee (e : exp) {struct e} : atoms :=
  match e with
  | exp_bvar i => {}
  | exp_fvar x => singleton x
  | exp_abs V e1 => (fv_et V) `union` (fv_ee e1)
  | exp_app e1 e2 => (fv_ee e1) `union` (fv_ee e2)
  | exp_tabs V e1 => (fv_et V) `union` (fv_ee e1)
  | exp_tapp e1 V => (fv_et V) `union` (fv_ee e1)
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
  | typ_top => typ_top
  | typ_bvar J => typ_bvar J
  | typ_fvar X => if X == Z then U else T
  | typ_arrow T1 T2 => typ_arrow (subst_tt Z U T1) (subst_tt Z U T2)
  | typ_all T1 T2 => typ_all (subst_tt Z U T1) (subst_tt Z U T2)
  | typ_capt C T1 => typ_capt C (subst_tt Z U T1)
  end.

Fixpoint subst_te (Z : atom) (U : typ) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_abs V e1 => exp_abs  (subst_tt Z U V)  (subst_te Z U e1)
  | exp_app e1 e2 => exp_app  (subst_te Z U e1) (subst_te Z U e2)
  | exp_tabs V e1 => exp_tabs (subst_tt Z U V)  (subst_te Z U e1)
  | exp_tapp e1 V => exp_tapp (subst_te Z U e1) (subst_tt Z U V)
  end.

Fixpoint subst_ct (z : atom) (c : captureset) (T : typ) {struct T} : typ :=
  match T with
  | typ_top => typ_top
  | typ_bvar J => typ_bvar J
  | typ_fvar X => typ_fvar X
  | typ_arrow T1 T2 => typ_arrow (subst_ct z c T1) (subst_ct z c T2)
  | typ_all T1 T2 => typ_all (subst_ct z c T1) (subst_ct z c T2)
  | typ_capt C T1 => typ_capt (substitute_captureset_fvar z c C) (subst_ct z c T1)
  end.

Fixpoint subst_ee (z : atom) (u : exp) (c : captureset) (e : exp) {struct e} : exp :=
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
  let G := gather_atoms_with (fun x : captureset => cset_fvar x) in
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

Lemma open_tt_rec_type_aux : forall T j V i U,
  i <> j ->
  open_tt_rec j V T = open_tt_rec i U (open_tt_rec j V T) ->
  T = open_tt_rec i U T.
Proof with eauto*.
  induction T; intros j V i U Neq H; simpl in *; inversion H; f_equal...
  Case "typ_bvar".
    destruct (j === n)... destruct (i === n)...
Qed.

(** NEW: Opening with a type and capture variable commute... *)
Lemma open_tt_rec_capt_aux : forall T j C i S,
  open_ct_rec j C T = open_tt_rec i S (open_ct_rec j C T) ->
  T = open_tt_rec i S T.
Proof with eauto*.
  induction T; intros j C i S H; simpl in *; inversion H; f_equal...
Qed.

(** Opening a locally closed term is the identity.  This lemma depends
    on the immediately preceding lemma. *)

Lemma open_tt_rec_type : forall T U k,
  type T ->
  T = open_tt_rec k U T.
Proof with auto*.
  intros T U k Htyp. revert k.
  induction Htyp; intros k; simpl; f_equal...
  (** NEW: Just dealing with the case when we open a capture set in the -> constructor. *)
  Case "typ_arrow".
    unfold open_ct in *.
    pick fresh X.
    apply (open_tt_rec_capt_aux T2 0 (cset_singleton_fvar X))...
  Case "typ_all".
    unfold open_tt in *.
    pick fresh X.
    apply (open_tt_rec_type_aux T2 0 (typ_fvar X))...
Qed.

(** If a name is fresh for a term, then substituting for it is the
    identity. *)

Lemma subst_tt_fresh : forall Z U T,
   Z `notin` fv_tt T ->
   T = subst_tt Z U T.
Proof with auto*.
  induction T; simpl; intro H; f_equal...
  Case "typ_fvar".
    destruct (a == Z)...
    contradict H; fsetdec.
Qed.

(** Substitution commutes with opening under certain conditions.  This
    lemma depends on the fact that opening a locally closed term is
    the identity. *)

Lemma subst_tt_open_tt_rec : forall T1 T2 X P k,
  type P ->
  subst_tt X P (open_tt_rec k T2 T1) =
    open_tt_rec k (subst_tt X P T2) (subst_tt X P T1).
Proof with auto*.
  intros T1 T2 X P k WP. revert k.
  induction T1; intros k; simpl; f_equal...
  Case "typ_bvar".
    destruct (k === n); subst...
  Case "typ_fvar".
    destruct (a == X); subst... apply open_tt_rec_type...
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
  open_tt_rec k U T2 = subst_tt X U (open_tt_rec k (typ_fvar X) T2).
Proof with auto*.
  induction T2; intros U k Fr; simpl in *; f_equal...
  Case "typ_bvar".
    destruct (k === n)... simpl. destruct (X == X)...
  Case "typ_fvar".
    destruct (a == X)... contradict Fr; fsetdec.
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
Proof with eauto using open_tt_rec_capt_aux.
  induction e; intros j u i P c H; simpl in *; inversion H; f_equal...
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
  open_te_rec k U e = subst_te X U (open_te_rec k (typ_fvar X) e).
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

(** TODO: These opening lemmas should go in CaptureSet.v at some point (Edward). *)
(** A warmup, to get started with. *)
Lemma open_captureset_bvar_singleton : forall i c,
  open_captureset_bvar i (cset_singleton_bvar i) c = c.
Proof with eauto*.
  intros i c.
  unfold open_captureset_bvar.
  case_eq (cset_references_bvar_dec i c)...
  destruct c; simpl; intro...
  (* If i isn't in C, this is trivial.  Now we assume i is in C,
     and C isn't the univeral set, as that's also trivial. *)
  f_equal.
  * fsetdec.
  * rewrite <- NatSetFacts.mem_iff in H. fnsetdec.
Qed.

(* 
  TODO clean up the proof
*)
Lemma substitute_captureset_singleton : forall k c C x,
  ~ cset_references_fvar x C ->
  open_captureset_bvar k c C = 
    substitute_captureset_fvar x c (open_captureset_bvar k (cset_singleton_fvar x) C).
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
Lemma open_captureset_subset_with_index : forall i C c,
  cset_subset_prop C c ->
  cset_references_bvar i C ->
  c = open_captureset_bvar i C c.
Proof with eauto*.
  intros i C c S.
  unfold open_captureset_bvar.  
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
  c = open_captureset_bvar i C c.
Proof.
  intros i C c H.
  unfold open_captureset_bvar.
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
  c = open_captureset_bvar i C c <->
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
    * destruct H ; auto using open_captureset_subset_with_index.
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
Lemma open_captureset_bvar_aux : forall j D i C c,
  i <> j ->
  empty_cset_bvars D ->
  cset_disjoint_fvars C D ->
  open_captureset_bvar j D c = open_captureset_bvar i C (open_captureset_bvar j D c) ->
  c = open_captureset_bvar i C c.
Proof with eauto*.
  intros j D i C c Neq Closed Disj H.

  rewrite (cset_open_idempotent i C (open_captureset_bvar j D c)) in H.

  rewrite cset_open_idempotent. 

  destruct (cset_references_bvar_dec i c) eqn:Hic.
  (* i is in c *)
  - destruct (cset_references_bvar_dec j c) eqn:Hjc ; csethyp...
    destruct H. 
    * destruct D ; destruct c ; csethyp ; auto.
      left. fnsetdec.
    * destruct H. destruct C eqn:HC.
      ** contradiction. 
      ** unfold empty_cset_bvars in Closed. unfold cset_bvars in *. destruct D ; destruct c eqn:Hc ; eauto.
         right. split...
         inversion H ; csethyp ; simpl in *. constructor. fsetdec. fnsetdec.          
  (* i is not in c *)     
  - left. apply cset_not_references_bvar_eq. apply Hic.
Qed.
  
(** Opening a capture set under some circumstances is the identity *)
Lemma open_ct_rec_capt_aux : forall T j Df i C,
  i <> j ->
  AtomSet.F.Empty (AtomSet.F.inter (cset_fvar C) Df) ->
  open_ct_rec j (cset_set Df {}N) T = open_ct_rec i C (open_ct_rec j (cset_set Df {}N) T) ->
  T = open_ct_rec i C T.
Proof with eauto*.
  induction T; intros j Df i C Neq; unfold empty_cset_bvars; intros HCommon H;
    simpl in *; inversion H; f_equal...
  apply open_captureset_bvar_aux with (j := j) (D := cset_set Df {}N) ; simpl in *; try fnsetdec...
  unfold cset_disjoint_fvars in *. destruct C...
Qed.

Lemma open_ct_rec_capt : forall T j D i C,
  i <> j ->
  empty_cset_bvars D ->
  cset_disjoint_fvars C D ->
  open_ct_rec j D T = open_ct_rec i C (open_ct_rec j D T) ->
  T = open_ct_rec i C T.
Proof with eauto using open_captureset_bvar_aux.
  induction T; intros j D i C Neq Closed; intros HCommon H; simpl in *; inversion H; f_equal...
Qed.

(** NEW: Opening with a type and capture variable commute... *)
Lemma open_ct_rec_type_aux : forall T j S i C,
  open_tt_rec j S T = open_ct_rec i C (open_tt_rec j S T) ->
  T = open_ct_rec i C T.
Proof with eauto*.
  induction T; intros j C i S H; simpl in *; inversion H; f_equal...
Qed.

(** NEW: The new lemma for opening a locally closed type by a capture set
    Hint: it's the identity function. *)
Lemma open_ct_rec_type : forall T C k,
  type T ->
  T = open_ct_rec k C T.
Proof with auto*.
  intros T C k Htyp. revert k.
  induction Htyp; intros k; simpl; f_equal...
  (* Case typ_arrow *)
  * (* Here, we are opening (\ T1 -> T2), assuming that this is locally closed.
       Hence T1 is locally closed, so by the induction hypothesis it goes away.
       T2 isn't locally closed, but the only open capture variable in it is bound by \0. *)
    pick fresh X.
    unfold open_ct in *.
    unfold cset_singleton_fvar in H0.
    assert (X `notin` L) by fsetdec.
    apply open_ct_rec_capt_aux with (i := S k) (j := 0) (Df := (AtomSet.F.singleton X)) (C := C) (T := T2)...
    fsetdec.
  (* Case typ_all *)
  * pick fresh X.
    unfold open_tt in *.
    apply open_ct_rec_type_aux with (j := 0) (S := X)...
  (* Case typ_capt *)
  * unfold open_captureset_bvar.
    case_eq (cset_references_bvar_dec k C0); intros.
    ** unfold empty_cset_bvars in H. unfold cset_bvars in H.
       assert (cset_references_bvar_dec k C0 = false).
        { unfold cset_references_bvar_dec. destruct C0 ; auto. apply NatSetFacts.not_mem_iff.
          nnotin_solve. }
       csethyp. discriminate H0.
    ** auto.
Qed.


(* 
   TODO maybe we need to strengthen the lemma again for other use cases?
 *)
Lemma subst_tt_open_ct_rec : forall (X : atom) P T C k,
  type P ->
  subst_tt X P (open_ct_rec k C T) = open_ct_rec k C (subst_tt X P T).
Proof with auto*.
  intros X P T C.
  induction T ; intros ; simpl; f_equal...
  destruct (a == X)...
  generalize dependent k.
  induction P...
  - intro. apply open_ct_rec_type with (T := typ_arrow P1 P2). apply H.
  - intro. apply open_ct_rec_type with (T := typ_all P1 P2). apply H.
  - intro ; inversion H ; simpl ; f_equal... 
    unfold empty_cset_bvars in H3.
    unfold cset_bvars in H3.
    destruct c...
    unfold open_captureset_bvar.
    unfold cset_singleton_fvar.
    destruct (cset_references_bvar_dec k (cset_set t t0)) eqn:Hb.    
    * rewrite cset_references_bvar_eq in Hb. unfold cset_references_bvar in Hb. unfold cset_bvars in Hb.
      contradict Hb. nnotin_solve.
    * reflexivity.
Qed.

(* T[0 !-> C][X !-> P] = T[X !-> P][0 !-> C] *)
Lemma subst_tt_open_ct : forall (X : atom) P T C,
  type P ->
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
  empty_cset_bvars D ->
  cset_disjoint_fvars C D ->
  open_ee_rec j v D e = open_ee_rec i u C (open_ee_rec j v D e) ->
  e = open_ee_rec i u C e.
Proof with eauto using open_ct_rec_capt.
  induction e; intros j v u C D i Neq Closed Disj H; simpl in *; inversion H; f_equal...
  Case "exp_bvar".
    destruct (j===n)... destruct (i===n)... subst. destruct Neq...
Qed.

Lemma open_ee_rec_type_aux : forall e j V u c i,
  open_te_rec j V e = open_ee_rec i u c (open_te_rec j V e) ->
  e = open_ee_rec i u c e.
Proof with eauto using open_ct_rec_type_aux.
  induction e; intros j V u c i H; simpl; inversion H; f_equal...
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
    apply open_ee_rec_expr_aux with (j := 0) (v := x) (D := (cset_singleton_fvar x))...
    simpl. fnsetdec.
    (* that should go into a tactic *)
    unfold cset_disjoint_fvars. destruct c... simpl. fsetdec.
  - apply open_ct_rec_type...
  - pick fresh x. eapply open_ee_rec_type_aux with (V := typ_fvar x). apply H1...
  - apply open_ct_rec_type...
Qed.

Lemma subst_captureset_fresh : forall x c C,
  x `notin` (cset_fvar c)  ->
  c = substitute_captureset_fvar x C c.
Proof with auto*.
  intros x c C H.
  unfold substitute_captureset_fvar.
  destruct (cset_references_fvar_dec x c) eqn:Hd...

  (* TODO factor into a tactic *)
  rewrite cset_references_fvar_eq in Hd. csetdec. destruct c...
Qed.
  
Lemma subst_ct_fresh : forall (x: atom) c t,
  x `notin` fv_et t ->
  t = subst_ct x c t.
Proof with eauto using subst_captureset_fresh.
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

Ltac cset_split := repeat (
  try csethyp;
  match goal with
  | H : _ |- context R [(cset_references_bvar_dec ?I ?C)] =>
    idtac "Destructing" I "in" C; let H_destruct := fresh "H_destruct" in case_eq (cset_references_bvar_dec I C); 
      intro H_destruct; try rewrite H_destruct in *
  | H : _ |- context R [(cset_references_fvar_dec ?I ?C)] =>
    idtac "Destructing" I "in" C; let H_destruct := fresh "H_destruct" in case_eq (cset_references_fvar_dec I C);
      intro H_destruct; try rewrite H_destruct in *
  end
).

Ltac cset_cleanup :=
  try rewrite cset_references_bvar_eq in *;
  try rewrite cset_references_fvar_eq in *;
  try rewrite cset_not_references_fvar_eq in *;
  try rewrite cset_not_references_bvar_eq in *;
  csetdec;
  eauto*;
  try (f_equal; try fsetdec; try fnsetdec).

Lemma subst_capt_open_rec : forall x k c1 c2 c,
  empty_cset_bvars c1 ->
  substitute_captureset_fvar x c1 (open_captureset_bvar k c2 c) =
  open_captureset_bvar k (substitute_captureset_fvar x c1 c2)
    (substitute_captureset_fvar x c1 c).
Proof with eauto*.
  intros x k c1 c2 c c1empt.
  (* There really should be a nice proof of this lemma.  Probably
     wants some automation here. *)
  csetdec.
  destruct c eqn:Hc; destruct c1 eqn:Hc1; destruct c2 eqn:Hc2;
  cset_split; cset_cleanup.
  (* This is not a good proof.  But it works... *)
  all: try solve [
    (* A bunch of cases that are not useful as they assume k is in c1. *)
    (unfold empty_cset_bvars in *; unfold cset_bvars in *;
      exfalso; assert (~ NatSet.F.In k (NatSet.F.union t2 t0)) by nnotin_solve; 
      contradict H; eauto*)
    ||
    (* An artifact that comes up???? *)
    (unfold empty_cset_bvars in *; unfold cset_bvars in *;
      fnsetdec)
  ].
Qed.

Lemma subst_ct_open_rec : forall x k c1 c2 t,
  empty_cset_bvars c1 ->
  subst_ct x c1 (open_ct_rec k c2 t) =
  open_ct_rec k (substitute_captureset_fvar x c1 c2) (subst_ct x c1 t).
Proof with auto.
  intros x k c1 c2 t. revert c1 c2 k x.
  induction t ; intros c1 c2 k x c1empt;
    unfold open_ct_rec; unfold subst_ct; fold open_ct_rec; fold subst_ct;
    f_equal...
  (* The arrow / abstraction cases go away after we fold and unfold definitions
      appropriately.  The remaining case that is left is dealing with a capture set. *)
  - Case "typ_cset".
    apply subst_capt_open_rec. apply c1empt.
Qed.

Lemma subst_ee_open_ee_rec : forall e1 e2 x u c1 c2 k,
  expr u ->
  empty_cset_bvars c1 ->
  subst_ee x u c1 (open_ee_rec k e2 c2 e1) =
    open_ee_rec k (subst_ee x u c1 e2) (substitute_captureset_fvar x c1 c2) (subst_ee x u c1 e1).
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
  empty_cset_bvars c1 ->
  subst_ee x u c1 (open_ee e1 e2 c2) =
    open_ee (subst_ee x u c1 e1) (subst_ee x u c1 e2) (substitute_captureset_fvar x c1 c2).
Proof with auto*.
  intros.
  unfold open_ee.
  apply subst_ee_open_ee_rec...
Qed.

Lemma subst_ee_open_ee_var : forall (x y:atom) u c e,
  y <> x ->
  expr u ->
  empty_cset_bvars c ->
  open_ee (subst_ee x u c e) y (cset_singleton_fvar y) = subst_ee x u c (open_ee e y (cset_singleton_fvar y)).
Proof with auto*.
  intros x y u c e Neq Wu Wc.
  unfold open_ee.
  rewrite subst_ee_open_ee_rec...
  simpl.
  destruct (y == x)...

  (* TODO factor into a tactic *)
  unfold substitute_captureset_fvar. simpl. 
  destruct (AtomSet.F.mem x (singleton y)) eqn:Heq...
  rewrite <- AtomSetFacts.mem_iff in Heq.  
  fsetdec.
Qed.

Lemma subst_ct_open_tt_rec : forall c z P t k,
  empty_cset_bvars c ->
  z `notin` fv_et P ->
  subst_ct z c (open_tt_rec k P t) = open_tt_rec k P (subst_ct z c t).
Proof with eauto.
  induction t ; intros ; simpl ; f_equal...
  Case "exp_bvar".
    destruct (k === n)... symmetry. apply subst_ct_fresh...
Qed.


Lemma subst_te_open_ee_rec : forall e1 e2 c Z P k,
  type P -> (* Jonathan: I added this here, does this make sense? *)
  subst_te Z P (open_ee_rec k e2 c e1) =
    open_ee_rec k (subst_te Z P e2) c (subst_te Z P e1).
Proof with eauto using subst_tt_open_ct_rec.
  induction e1; intros e2 c Z P k Tpe; simpl; f_equal...
  Case "exp_bvar".
    destruct (k === n)...
Qed.

Lemma subst_te_open_ee : forall e1 e2 c Z P,
  type P -> (* Jonathan: I added this here, does this make sense? *)
  subst_te Z P (open_ee e1 e2 c) = open_ee (subst_te Z P e1) (subst_te Z P e2) c.
Proof with auto*.
  intros.
  unfold open_ee.
  apply subst_te_open_ee_rec...
Qed.

Lemma subst_te_open_ee_var : forall Z (x:atom) P e c,
  type P -> (* Jonathan: I added this here, does this make sense? *)
  open_ee (subst_te Z P e) x c = subst_te Z P (open_ee e x c).
Proof with auto*.
  intros.
  rewrite subst_te_open_ee...
Qed.

Lemma subst_ee_open_te_rec : forall e P z u c k,
  expr u ->
  empty_cset_bvars c ->
  z `notin` fv_et P -> (* Jonathan: I added this here, does this make sense? *)
  subst_ee z u c (open_te_rec k P e) = open_te_rec k P (subst_ee z u c e).
Proof with eauto using subst_ct_open_tt_rec.
  induction e; intros P z u c k H Hc Hfv; simpl; f_equal...
  Case "exp_fvar".
    destruct (a == z)... apply open_te_rec_expr...
Qed.

Lemma subst_ee_open_te : forall e P z u c,
  expr u ->
  empty_cset_bvars c ->
  z `notin` fv_et P -> (* Jonathan: I added this here, does this make sense? *)
  subst_ee z u c (open_te e P) = open_te (subst_ee z u c e) P.
Proof with auto*.
  intros.
  unfold open_te.
  apply subst_ee_open_te_rec...
Qed.

Lemma subst_ee_open_te_var : forall z (X:atom) u c e,
  expr u ->
  empty_cset_bvars c ->
  open_te (subst_ee z u c e) X = subst_ee z u c (open_te e X).
Proof with auto*.
  intros z X u c e Wu Wc.
  rewrite subst_ee_open_te...
Qed.

(* if x is fresh, opening with {x} and then substituting is the same as opening directly. *)
Lemma open_ct_subst_ct_var : forall x c t k,
  x `notin` fv_et t ->
  open_ct_rec k c t = subst_ct x c (open_ct_rec k (cset_singleton_fvar x) t).
Proof with auto.
  induction t ; intros ; simpl in * ; f_equal...

  (* TODO factor into a tactic *)
  apply substitute_captureset_singleton. intro.
  destruct c0... simpl in *.
  fsetdec.
Qed.

Lemma subst_ee_intro_rec : forall x e u c k,
  x `notin` fv_ee e ->
  open_ee_rec k u c e = subst_ee x u c (open_ee_rec k (exp_fvar x) (cset_singleton_fvar x) e).
Proof with eauto using open_ct_subst_ct_var.
  induction e; intros u c k Fr; simpl in *; f_equal...
  Case "exp_bvar".
    destruct (k === n)... simpl. destruct (x == x)... contradiction.
  Case "exp_fvar".
    destruct (a == x)... contradict Fr; fsetdec.
Qed.

Lemma subst_ee_intro : forall x e u c,
  x `notin` fv_ee e ->
  open_ee e u c = subst_ee x u c (open_ee e x (cset_singleton_fvar x)).
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
  type (subst_tt Z P T).
Proof with auto.
  intros Z P T HT HP.
  induction HT; simpl...
  - Case "type_fvar".
    destruct (X == Z)...
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
   apply Hp.
   
  (* case exp_tabs *)
  - instantiate (1 := L `union` singleton Z). intros. 
    rewrite subst_te_open_te_var. apply H1. fsetdec. fsetdec. auto.
Qed.

(** The following lemma depends on [subst_ee_open_ee_var] and
    [subst_ee_open_te_var]. 

    This lemma can be cleaned up quite a bit -- just making it go through for now.
*)

Lemma open_capt_subst_aux : forall k x z C' C,
  ~ cset_references_fvar x C ->
  ~ cset_references_fvar x C' ->
  z <> x ->
  ~ cset_references_bvar k C' ->
  open_captureset_bvar k (cset_singleton_fvar x) (substitute_captureset_fvar z C' C) =
  substitute_captureset_fvar z C' (open_captureset_bvar k (cset_singleton_fvar x) C).
Proof.
  intros k x z C C' HxfC HxfC' Hxfz HkfC'. 
  (* There really should be a nice proof of this lemma.  Probably
     wants some automation here. *)
  unfold cset_singleton_fvar.
  csetdec.
  destruct C eqn:HC; destruct C' eqn:HC';
  cset_split; cset_cleanup.
Qed.
Lemma subst_ct_open_fresh : forall k z C T X,
  (* X fresh requirement here in z c T *)
  X `notin` (singleton z `union` fv_tt T `union` fv_et T) /\ ~ cset_references_fvar X C ->
  (* c is locally closed / no bound variables *)
  empty_cset_bvars C ->
  (open_ct_rec k (cset_singleton_fvar X) (subst_ct z C T)) =
    (subst_ct z C (open_ct_rec k (cset_singleton_fvar X) T)).
Proof with eauto*.
  intros k z C T X HXfresh HCfresh. revert k. 
  induction T; intro k; simpl in *; try reflexivity.
  * (* Case typ_arrow *)
    f_equal.
    + apply IHT1. split. fsetdec. apply HXfresh.
    + apply IHT2. split. fsetdec. apply HXfresh.
  * (* Case typ_all *)
    f_equal.
    + apply IHT1. split. fsetdec. apply HXfresh.
    + apply IHT2. split. fsetdec. apply HXfresh.
  * (* Case typ_capt *)    
    f_equal.
    + apply open_capt_subst_aux.
      (* csetdec; destruct .... should be a tactic at some point .*)
      csetdec; destruct c...
      csetdec; destruct C...
      fsetdec.
      csetdec; destruct C...
    + apply IHT. split. fsetdec. apply HXfresh.
Qed.    

Lemma open_tt_subst_ct_aux : forall k X z C T,
  ~ cset_references_fvar X C ->
  open_tt_rec k X (subst_ct z C T) =
  subst_ct z C (open_tt_rec k X T).
Proof with eauto*.
  intros k X z C T HXfresh. revert k. induction T; intro k; simpl in *; f_equal...
  destruct (k === n)...
Qed.


Lemma subst_ct_type : forall T z c,
  type T -> 
  empty_cset_bvars c ->
  type (subst_ct z c T).
Proof with auto.
  intros T z c Tpe Closed.
  induction Tpe; simpl; econstructor...
  - let L' := gather_atoms in instantiate (1 := L').
    intros X HXfresh.
    assert ((open_ct (subst_ct z c T2) (cset_singleton_fvar X)) =
            (subst_ct z c (open_ct T2 (cset_singleton_fvar X)))).
    { apply subst_ct_open_fresh. split. fsetdec. csetdec; destruct c; fsetdec. apply Closed. }
    rewrite H1. apply H0...
  (* Can we use subst_ct_fresh??? -- no, that requires z to be fresh; but we get a simple
      helper lemma above for the equality. *)
  - let L' := gather_atoms in instantiate (1 := L'). intro X. intro HXfresh.
    assert ((open_tt (subst_ct z c T2) X) = (subst_ct z c (open_tt T2 X))).
    { apply open_tt_subst_ct_aux. csetdec; destruct c... }
    rewrite H1. apply H0...
  (* TODO: This should probably go in a tactic *)
  - csetdec. destruct c eqn:Hc; destruct C eqn:HC; cset_split; cset_cleanup.
    unfold empty_cset_bvars in *. csetdec.
Qed.

(* TODO clean up the proof here *)
Lemma subst_ee_expr : forall z e1 e2 c,
  expr e1 ->
  expr e2 ->
  empty_cset_bvars c ->
  expr (subst_ee z e2 c e1).
Proof with eauto using subst_ct_type.
  intros z e1 e2 c He1 He2 Closed. revert z.
  induction He1; intro z; simpl; auto;
  try solve [
    econstructor;
    try instantiate (1 := L `union` singleton z);
    intros;
    try rewrite subst_ee_open_ee_var;
    try rewrite subst_ee_open_te_var;
    eauto
  ].
  - destruct (x == z)...
  - econstructor...
    instantiate (1 := L `union` singleton z).
    intros.
    rewrite subst_ee_open_ee_var...
  - econstructor...
    instantiate (1 := L `union` singleton z).
    intros.
    rewrite subst_ee_open_te_var...
  - econstructor...
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