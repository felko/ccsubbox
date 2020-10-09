(** Infrastructure lemmas and tactic definitions for Fsub.

    Authors: Brian Aydemir and Arthur Charguéraud, with help from
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

Fixpoint fv_tt (T : typ) {struct T} : atoms :=
  match T with
  | typ_top => {}
  | typ_bvar J => {}
  | typ_fvar X => singleton X
  | typ_arrow T1 T2 => (fv_tt T1) `union` (fv_tt T2)
  | typ_all T1 T2 => (fv_tt T1) `union` (fv_tt T2)
  (** NEW: Capture set free variables need to also be mentioned. *)
  | typ_capt C T => (cset_fvar C) `union` (fv_tt T)
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
  | exp_abs V e1 => (fv_ee e1)
  | exp_app e1 e2 => (fv_ee e1) `union` (fv_ee e2)
  | exp_tabs V e1 => (fv_ee e1)
  | exp_tapp e1 V => (fv_ee e1)
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

Fixpoint subst_ee (z : atom) (u : exp) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => if x == z then u else e
  | exp_abs V e1 => exp_abs V (subst_ee z u e1)
  | exp_app e1 e2 => exp_app (subst_ee z u e1) (subst_ee z u e2)
  | exp_tabs V e1 => exp_tabs V (subst_ee z u e1)
  | exp_tapp e1 V => exp_tapp (subst_ee z u e1) V
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
  constr:(A `union` B `union` C `union` D `union` E `union` F `union` G).

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
  open_tc_rec j C T = open_tt_rec i S (open_tc_rec j C T) ->
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
    unfold open_tc in *.
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
    absurd_hyp H; fsetdec.
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
    destruct (a == X)... absurd_hyp Fr; fsetdec.
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

Lemma open_te_rec_expr_aux : forall e j u i P ,
  open_ee_rec j u e = open_te_rec i P (open_ee_rec j u e) ->
  e = open_te_rec i P e.
Proof with eauto*.
  induction e; intros j u i P H; simpl in *; inversion H; f_equal...
Qed.

Lemma open_te_rec_type_aux : forall e j Q i P,
  i <> j ->
  open_te_rec j Q e = open_te_rec i P (open_te_rec j Q e) ->
  e = open_te_rec i P e.
Proof.
  induction e; intros j Q i P Neq Heq; simpl in *; inversion Heq;
    f_equal; eauto using open_tt_rec_type_aux.
Qed.

Lemma open_te_rec_capt_aux : forall e j C i P,
  open_ec_rec j C e = open_te_rec i P (open_ec_rec j C e) ->
  e = open_te_rec i P e.
Proof with eauto*.
  induction e;
  intros j C i P H;
  simpl in *; inversion H; f_equal...
  (** Three cases introduced by the new capture variables. *)
  * apply open_tt_rec_capt_aux with (j := j) (C := C); auto.
  * apply open_tt_rec_capt_aux with (j := j) (C := C); auto.
  * apply open_tt_rec_capt_aux with (j := j) (C := C); auto.
Qed.

Lemma open_te_rec_expr : forall e U k,
  expr e ->
  e = open_te_rec k U e.
Proof with auto*.
  intros e U k WF; revert k;
  induction WF; intros k; simpl; f_equal; auto using open_tt_rec_type;
  try solve [
    (** NEW: Dealing with capture variables; need to unwrap the capture sets.*)
    unfold open_ec in *; unfold open_ee in *;
    pick fresh x;
    eapply open_te_rec_expr_aux with (j := 0) (u := exp_fvar x);
    eapply open_te_rec_capt_aux with (j := 0) (C := {}C);
    auto*
  | unfold open_te in *;
    pick fresh X;
    eapply open_te_rec_type_aux with (j := 0) (Q := typ_fvar X);
    auto*
  ].
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
      *** unfold cset_union. unfold cset_remove_bvar. unfold cset_references_bvar in H1. unfold cset_bvars in H1.
        f_equal.
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
*)
Lemma open_captureset_bvar_aux : forall j D Df i C c,
  i <> j ->
  D = cset_set Df {}N ->
  cset_disjoint_fvars C D ->
  open_captureset_bvar j D c = open_captureset_bvar i C (open_captureset_bvar j D c) ->
  c = open_captureset_bvar i C c.
Proof with eauto*.
  intros j D Df i C c Neq DDef Disj H.

  rewrite (cset_open_idempotent i C (open_captureset_bvar j D c)) in H.

  rewrite cset_open_idempotent. 

  destruct (cset_references_bvar_dec i c) eqn:Hic.
  (* i is in c *)
  - destruct (cset_references_bvar_dec j c) eqn:Hjc ; csethyp...
    destruct H. 
    * rewrite DDef in H. destruct c ; csethyp ; auto.
      left. fnsetdec.      
    * destruct H. destruct C eqn:HC.
      ** contradiction. 
      ** destruct c eqn:Hc ; eauto.
         right. split...
         inversion H ; rewrite DDef in H3 ; csethyp. 
         + discriminate H3.
         + injection H3. intros. subst.
           rewrite elim_empty_nat_set in *.
           unfold cset_disjoint_fvars in Disj.
           apply cset_subset_elem ; csetdec.
  (* i is not in c *)     
  - left. apply cset_not_references_bvar_eq. apply Hic.
Qed.
  
Lemma open_tc_rec_type_aux : forall T j Df i C,
  i <> j ->
  AtomSet.F.Empty (AtomSet.F.inter (cset_fvar C) Df) ->
  open_tc_rec j (cset_set Df {}N) T = open_tc_rec i C (open_tc_rec j (cset_set Df {}N) T) ->
  T = open_tc_rec i C T.
Proof with eauto*.
  (*induction T; intros j V i U Neq H; simpl in *; inversion H; f_equal...
  Case "typ_bvar".
    destruct (j === n)... destruct (i === n)...*)
  induction T; intros j Df i C Neq; unfold empty_cset_bvar_references; intros HCommon H;
    simpl in *; inversion H; f_equal...
  apply open_captureset_bvar_aux with (j := j) (C := C) (D := cset_set Df {}N) (Df := Df)...
  unfold cset_disjoint_fvars. destruct C...
Qed.

(** NEW: Opening with a type and capture variable commute... *)
Lemma open_tc_rec_capt_aux : forall T j S i C,
  open_tt_rec j S T = open_tc_rec i C (open_tt_rec j S T) ->
  T = open_tc_rec i C T.
Proof with eauto*.
  induction T; intros j C i S H; simpl in *; inversion H; f_equal...
Qed.

Lemma open_tc_rec_type : forall T C k,
  type T ->
  T = open_tc_rec k C T.
Proof with auto*.
  intros T C k Htyp. revert k.
  induction Htyp; intros k; simpl; f_equal...
  (* Case typ_arrow *)
  * (* Here, we are opening (\ T1 -> T2), assuming that this is locally closed.
       Hence T1 is locally closed, so by the induction hypothesis it goes away.
       T2 isn't locally closed, but the only open capture variable in it is bound by \0. *)
    pick fresh X.
    unfold open_tc in *.
    unfold cset_singleton_fvar in H0.
    assert (X `notin` L) by fsetdec.
    apply open_tc_rec_type_aux with (i := S k) (j := 0) (Df := (AtomSet.F.singleton X)) (C := C) (T := T2)...
    fsetdec.
  (* Case typ_all *)
  * pick fresh X.
    unfold open_tt in *.
    apply open_tc_rec_capt_aux with (j := 0) (S := X)...
  (* Case typ_capt *)
  * unfold open_captureset_bvar.
    case_eq (cset_references_bvar_dec k C0); intros.
    ** unfold empty_cset_bvar_references in H. unfold cset_bvars in H.
       assert (cset_references_bvar_dec k C0 = false).
        { unfold cset_references_bvar_dec. destruct C0 ; auto. apply NatSetFacts.not_mem_iff.
          nnotin_solve. }
       csethyp. discriminate H0.
    ** auto.
Qed.

Lemma open_tc_type_inversion : forall (C : captureset) T,
  type (open_tc T C) -> 
  type T.
Proof.
Admitted.

Lemma open_tt_type_inversion : forall (Z : atom) T,
  type (open_tt T Z) -> 
  type T.
Proof.
Admitted.

(* 
   TODO maybe we need to strengthen the lemma again for other use cases?
 *)
Lemma subst_tt_open_tc_rec : forall (X Y:atom) P T k,
  Y <> X ->
  type P ->
  subst_tt X P (open_tc_rec k (cset_singleton_fvar Y) T) = open_tc_rec k (cset_singleton_fvar Y) (subst_tt X P T).
Proof with auto*.
  intros X Y P T.
  induction T ; intros ; simpl; f_equal...
  destruct (a == X)...
  generalize dependent k.
  (* The induction on P requires us to prove `type P1` for the components!
     But `type P` is necessary to show that `k` can't occur in any capture set in P *)
  induction P...
  - intro ; inversion H0 ; simpl ; f_equal... apply IHP2.
    pick fresh Z.
    assert (type (open_tc P2 (cset_singleton_fvar Z))). { apply H4. fsetdec. }
    eapply open_tc_type_inversion. apply H5.
  - intro ; inversion H0 ; simpl ; f_equal... apply IHP2.
    pick fresh Z.
    assert (type (open_tt P2 Z)). { apply H4. fsetdec. }
    eapply open_tt_type_inversion. apply H5.
  - intro ; inversion H0 ; simpl ; f_equal... 
    unfold empty_cset_bvar_references in H4.
    unfold cset_bvars in H4.
    destruct c...
    unfold open_captureset_bvar.
    unfold cset_singleton_fvar.
    destruct (cset_references_bvar_dec k (cset_set t t0)) eqn:Hb.    
    * rewrite cset_references_bvar_eq in Hb. unfold cset_references_bvar in Hb. unfold cset_bvars in Hb.
      exfalso. fnsetdec.
    * reflexivity.
Qed.

(* T[0 !-> C][X !-> P] = T[X !-> P][0 !-> C] *)
Lemma subst_tt_open_tc : forall (X Y:atom) P T,
  Y <> X ->
  type P ->
  subst_tt X P (open_tc T (cset_singleton_fvar Y)) = open_tc (subst_tt X P T) (cset_singleton_fvar Y).
Proof with auto*.
  intros X P T C.
  unfold open_tc.
  apply subst_tt_open_tc_rec...
Qed.

(* ********************************************************************** *)
(** ** Properties of expression substitution in expressions *)

(** This section follows the structure of the previous two sections. *)

Lemma open_ee_rec_expr_aux : forall e j v u i,
  i <> j ->
  open_ee_rec j v e = open_ee_rec i u (open_ee_rec j v e) ->
  e = open_ee_rec i u e.
Proof with eauto*.
  induction e; intros j v u i Neq H; simpl in *; inversion H; f_equal...
  Case "exp_bvar".
    destruct (j===n)... destruct (i===n)...
Qed.

Lemma open_ee_rec_type_aux : forall e j V u i,
  open_te_rec j V e = open_ee_rec i u (open_te_rec j V e) ->
  e = open_ee_rec i u e.
Proof.
  induction e; intros j V u i H; simpl; inversion H; f_equal; eauto.
Qed.

Lemma open_ee_rec_capt_aux : forall e j C u i,
  open_ec_rec j C e = open_ee_rec i u (open_ec_rec j C e) ->
  e = open_ee_rec i u e.
Proof.
  induction e; intros j C u i H; simpl; inversion H; f_equal; eauto.
Qed.

Lemma open_ee_rec_expr : forall u e k,
  expr e ->
  e = open_ee_rec k u e.
Proof with auto*.
  intros u e k Hexpr. revert k.
  induction Hexpr; intro k; simpl; f_equal; auto*;
  try solve [
    (** NEW: Something to deal with capture sets. *)
    unfold open_ee in *; unfold open_ec in *;
    pick fresh x;
    eapply open_ee_rec_expr_aux with (j := 0) (v := exp_fvar x);
    auto*;
    eapply open_ee_rec_capt_aux with (j := 0) (C := {}C);
    auto*
  | unfold open_te in *;
    pick fresh X;
    eapply open_ee_rec_type_aux with (j := 0) (V := typ_fvar X);
    auto*
  ].
Qed.

Lemma subst_ee_fresh : forall (x: atom) u e,
  x `notin` fv_ee e ->
  e = subst_ee x u e.
Proof with auto*.
  intros x u e; induction e; simpl; intro H; f_equal...
  Case "exp_fvar".
    destruct (a==x)...
    absurd_hyp H; fsetdec.
Qed.

Lemma subst_ee_open_ee_rec : forall e1 e2 x u k,
  expr u ->
  subst_ee x u (open_ee_rec k e2 e1) =
    open_ee_rec k (subst_ee x u e2) (subst_ee x u e1).
Proof with auto*.
  intros e1 e2 x u k WP. revert k.
  induction e1; intros k; simpl; f_equal...
  Case "exp_bvar".
    destruct (k === n); subst...
  Case "exp_fvar".
    destruct (a == x); subst... apply open_ee_rec_expr...
Qed.

Lemma subst_ee_open_ee : forall e1 e2 x u,
  expr u ->
  subst_ee x u (open_ee e1 e2) =
    open_ee (subst_ee x u e1) (subst_ee x u e2).
Proof with auto*.
  intros.
  unfold open_ee.
  apply subst_ee_open_ee_rec...
Qed.

Lemma subst_ee_open_ee_var : forall (x y:atom) u e,
  y <> x ->
  expr u ->
  open_ee (subst_ee x u e) y = subst_ee x u (open_ee e y).
Proof with auto*.
  intros x y u e Neq Wu.
  unfold open_ee.
  rewrite subst_ee_open_ee_rec...
  simpl.
  destruct (y == x)...
Qed.

Lemma subst_te_open_ee_rec : forall e1 e2 Z P k,
  subst_te Z P (open_ee_rec k e2 e1) =
    open_ee_rec k (subst_te Z P e2) (subst_te Z P e1).
Proof with auto*.
  induction e1; intros e2 Z P k; simpl; f_equal...
  Case "exp_bvar".
    destruct (k === n)...
Qed.

Lemma subst_te_open_ee : forall e1 e2 Z P,
  subst_te Z P (open_ee e1 e2) = open_ee (subst_te Z P e1) (subst_te Z P e2).
Proof with auto*.
  intros.
  unfold open_ee.
  apply subst_te_open_ee_rec...
Qed.

Lemma subst_te_open_ee_var : forall Z (x:atom) P e,
  open_ee (subst_te Z P e) x = subst_te Z P (open_ee e x).
Proof with auto*.
  intros.
  rewrite subst_te_open_ee...
Qed.

Lemma subst_ee_open_te_rec : forall e P z u k,
  expr u ->
  subst_ee z u (open_te_rec k P e) = open_te_rec k P (subst_ee z u e).
Proof with auto*.
  induction e; intros P z u k H; simpl; f_equal...
  Case "exp_fvar".
    destruct (a == z)... apply open_te_rec_expr...
Qed.

Lemma subst_ee_open_te : forall e P z u,
  expr u ->
  subst_ee z u (open_te e P) = open_te (subst_ee z u e) P.
Proof with auto*.
  intros.
  unfold open_te.
  apply subst_ee_open_te_rec...
Qed.

Lemma subst_ee_open_te_var : forall z (X:atom) u e,
  expr u ->
  open_te (subst_ee z u e) X = subst_ee z u (open_te e X).
Proof with auto*.
  intros z X u e H.
  rewrite subst_ee_open_te...
Qed.

Lemma subst_ee_intro_rec : forall x e u k,
  x `notin` fv_ee e ->
  open_ee_rec k u e = subst_ee x u (open_ee_rec k (exp_fvar x) e).
Proof with auto*.
  induction e; intros u k Fr; simpl in *; f_equal...
  Case "exp_bvar".
    destruct (k === n)... simpl. destruct (x == x)...
  Case "exp_fvar".
    destruct (a == x)... absurd_hyp Fr; fsetdec.
Qed.

Lemma subst_ee_intro : forall x e u,
  x `notin` fv_ee e ->
  open_ee e u = subst_ee x u (open_ee e x).
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
    rewrite <- subst_tt_open_tc...    
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
  induction He; simpl ; econstructor ; eauto using subst_tt_type.
  (* case exp_abs *)
  - instantiate (1 := L `union` singleton Z). intros. rewrite subst_te_open_ee_var. 
    (* requires a new lemma:
        (subst_te Z P (open_ec e c)) = (open_ec (subst_te Z P e) c)
   *)
    admit.

  (* case exp_tabs *)
  - instantiate (1 := L `union` singleton Z). intros. rewrite subst_te_open_te_var. apply H1. fsetdec. fsetdec. auto.
Admitted.

(** The following lemma depends on [subst_ee_open_ee_var] and
    [subst_ee_open_te_var]. *)

Lemma subst_ee_expr : forall z e1 e2,
  expr e1 ->
  expr e2 ->
  expr (subst_ee z e2 e1).
Proof with auto.
  intros z e1 e2 He1 He2.
  induction He1; simpl; auto;
  try solve [
    econstructor;
    try instantiate (1 := L `union` singleton z);
    intros;
    try rewrite subst_ee_open_ee_var;
    try rewrite subst_ee_open_te_var;
    auto
  ].
  Case "expr_var".
    destruct (x == z)...
Admitted.







(* *********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

(** We add as hints the fact that local closure is preserved under
    substitution.  This is part of our strategy for automatically
    discharging local-closure proof obligations. *)

Hint Resolve subst_tt_type subst_te_expr subst_ee_expr.



(** When reasoning about the [binds] relation and [map], we
    occasionally encounter situations where the binding is
    over-simplified.  The following hint undoes that simplification,
    thus enabling [Hint]s from the [Environment] library. *)

Hint Extern 1 (binds _ (?F (subst_tt ?X ?U ?T)) _) =>
  unsimpl (subst_tb X U (F T)).
