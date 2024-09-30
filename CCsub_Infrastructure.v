Require Export CCsub_Definitions.
Require Import Program.Equality.
Require Import Lia.

Fixpoint fv_ct (T : typ) {struct T} : atoms :=
  match T with
  | typ_var _ => {}A
  | C # R => `cse_fvars` C `u`A fv_ct R
  | ⊤ => {}A
  | ∀ (S') T => fv_ct S' `u`A fv_ct T
  | ∀ [R] T => fv_ct R `u`A fv_ct T
  | □ T => fv_ct T
  end.

Fixpoint fv_tt (T : typ) {struct T} : atoms :=
  match T with
  | var_b J => {}A
  | var_f X => singleton X
  | C # R => fv_tt R
  | ⊤ => {}A
  | ∀ (S') T => fv_tt S' `u`A fv_tt T
  | ∀ [R] T => fv_tt R `u`A fv_tt T
  | □ T => fv_tt T
  end.

Fixpoint fv_ce (e : exp) {struct e} : atoms :=
  match e with
  | exp_var _ => {}A
  | λ (V) e1 => fv_ct V `u`A fv_ce e1
  | _ @ _ => {}A
  | let= e in C => fv_ce e `u`A fv_ce C
  | Λ [V] e1 => fv_ct V `u`A fv_ce e1
  | _ @ [V] => fv_ct V
  | box _ => {}A
  | C ⟜ x => `cse_fvars` C
  end.

Fixpoint fv_te (e : exp) {struct e} : atoms :=
  match e with
  | exp_var _ => {}A
  | λ (V) e1  => fv_tt V `u`A fv_te e1
  | _ @ _ => {}A
  | let= e in C => fv_te e `u`A fv_te C
  | Λ [V] e1 => fv_tt V `u`A fv_te e1
  | _ @ [V] => fv_tt V
  | box _ => {}A
  | C ⟜ x => {}A
  end.

Definition fv_vv (v : var) : atoms :=
  match v with
  | var_f x => singleton x
  | var_b _ => {}A
  end.

Fixpoint fv_ve (e : exp) {struct e} : atoms :=
  match e with
  | exp_var v => fv_vv v
  | λ (V) e1 => fv_ve e1
  | x @ y => fv_vv x `u`A fv_vv y
  | let= e in C => fv_ve e `u`A fv_ve C
  | Λ [V] e1 => fv_ve e1
  | x @ [V] => fv_vv x
  | box x => fv_vv x
  | C ⟜ x => `cse_fvars` C `u`A fv_vv x
  end.

Fixpoint fv_cctx (E : env) {struct E} : atoms :=
  match E with
  | nil => {}A
  | (_, bind_typ T) :: F => fv_ct T `u`A fv_cctx F
  | (_, bind_sub T) :: F => fv_ct T `u`A fv_cctx F
  end.

Fixpoint subst_tt (Z : atom) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | var_b J => J
  | var_f X => if X == Z then U else X
  | C # R => C # subst_tt Z U R
  | ⊤ => typ_top
  | ∀ (S') T => ∀ (subst_tt Z U S') (subst_tt Z U T)
  | ∀ [R] T => ∀ [subst_tt Z U R] (subst_tt Z U T)
  | □ T => □ (subst_tt Z U T)
  end.

Fixpoint subst_ct (z : atom) (c : cse) (T : typ) {struct T} : typ :=
  match T with
  | var_b J => J
  | var_f X => X
  | C # R => subst_cse z c C # subst_ct z c R
  | ⊤ => ⊤
  | ∀ (S') T => ∀ (subst_ct z c S') (subst_ct z c T)
  | ∀ [R] T => ∀ [subst_ct z c R] (subst_ct z c T)
  | □ T => □ (subst_ct z c T)
  end.

Fixpoint subst_te (Z : atom) (U : typ) (e : exp) {struct e} : exp :=
  match e with
  | exp_var v => v
  | λ (V) e1 => λ (subst_tt Z U V) (subst_te Z U e1)
  | f @ x => f @ x
  | let= e in C => let= subst_te Z U e in subst_te Z U C
  | Λ [V] e1 => Λ [subst_tt Z U V]  (subst_te Z U e1)
  | x @ [V] => x @ [subst_tt Z U V]
  | box x => box x
  | C ⟜ x => C ⟜ x
  end.

Definition subst_vv (z : atom) (u : atom) (v : var) : var :=
  match v with
  | var_f x => if x == z then u else v
  | var_b i => i
  end.

Fixpoint subst_ve (z : atom) (u : atom) (c : cse) (e : exp) {struct e} : exp :=
  match e with
  | exp_var v => subst_vv z u v
  | λ (t) e1 => exp_abs (subst_ct z c t) (subst_ve z u c e1)
  | f @ x => subst_vv z u f @ subst_vv z u x
  | let= e in C => let= subst_ve z u c e in subst_ve z u c C
  | Λ [t] e1 => Λ [subst_ct z c t] (subst_ve z u c e1)
  | x @ [t] => subst_vv z u x @ [subst_ct z c t]
  | box x => box (subst_vv z u x)
  | C ⟜ x => subst_cse z (cse_fvar u) C ⟜ subst_vv z u x
  end.

Definition subst_tb (Z : atom) (P : typ) (b : binding) : binding :=
  match b with
  | bind_sub T => bind_sub (subst_tt Z P T)
  | bind_typ T => bind_typ (subst_tt Z P T)
  end.

Definition subst_cb (Z : atom) (c : cse) (b : binding) : binding :=
  match b with
  | bind_sub T => bind_sub (subst_ct Z c T)
  | bind_typ T => bind_typ (subst_ct Z c T)
  end.

Ltac gather_atoms :=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : exp => fv_te x) in
  let D := gather_atoms_with (fun x : exp => fv_ve x) in
  let E := gather_atoms_with (fun x : typ => fv_tt x) in
  let F := gather_atoms_with (fun x : env => dom x) in
  let G := gather_atoms_with (fun x : cse => `cse_fvars` x) in
  let H := gather_atoms_with (fun x : typ => fv_ct x) in
  let I := gather_atoms_with (fun x : exp => fv_ce x) in
  let J := gather_atoms_with (fun x : env => fv_cctx x) in
  constr:(A `u`A B `u`A C `u`A D `u`A E `u`A F `u`A G `u`A H `u`A I `u`A J).

Tactic Notation "pick" "fresh" ident(x) :=
  let L := gather_atoms in (pick fresh x for L).

Tactic Notation
      "pick" "fresh" ident(atom_name) "and" "apply" constr(lemma) :=
  let L := gather_atoms in
  pick fresh atom_name excluding L and apply lemma.

Tactic Notation
      "pick" "fresh" ident(atom_name) "and" "destruct" constr(lemma) :=
  let L := gather_atoms in
  pick fresh atom_name excluding L and destruct lemma.

Tactic Notation
      "pick" "fresh" ident(atom_name) "and" "destruct" constr(lemma) "as" simple_intropattern(pat) :=
  let L := gather_atoms in
  pick fresh atom_name excluding L and destruct lemma as pat.

Tactic Notation
      "pick" "fresh" ident(atom_name) "and" "specialize" constr(lemma) :=
  let L := gather_atoms in
  pick fresh atom_name excluding L and specialize lemma.

Notation "`succ`" := Datatypes.S.

Inductive varN : nat -> var -> Prop :=
  | varN_b : forall n (m : nat),
      m < n ->
      varN n m
  | varN_f : forall n (x : atom),
      varN n x.
  
(* For all bound vars in C, bound var is less than n *)
Inductive csetN : nat -> cse -> Prop :=
  | csetN_join : forall n C1 C2, 
      csetN n C1 -> csetN n C2 -> csetN n (cse_join C1 C2)
  | csetN_bvar : forall n m,
      m < n -> csetN n (cse_bvar m)
  | csetN_fvar : forall n a,
      csetN n (cse_fvar a)
  | csetN_bot : forall n,
      csetN n cse_bot
  | csetN_top : forall n,
      csetN n cse_top.

(* old definition, leave here for reference *)
(* Definition csetN (n : nat) (C : cse) : Prop :=
  NatSet.F.For_all (fun m => m < n) (`cse_bvars` C). *)

Inductive typeN : nat -> typ -> Prop :=
  | typeN_pure : forall n R, pure_typeN n R -> typeN n R
  | typeN_cset : forall n C R,
      csetN n C ->
      pure_typeN n R ->
      typeN n (C # R)
with pure_typeN : nat -> typ -> Prop :=
  | typeN_var : forall n v,
      varN n v ->
      pure_typeN n v
  | typeN_top : forall n,
      pure_typeN n typ_top
  | typeN_arr : forall n S' T,
      typeN n S' ->
      typeN (`succ` n) T ->
      pure_typeN n (∀ (S') T)
  | typeN_all : forall n R T,
      pure_typeN n R ->
      typeN (`succ` n) T ->
      pure_typeN n (∀ [R] T)
  | typeN_box : forall n T,
      typeN n T ->
      pure_typeN n (□ T).

Hint Constructors varN typeN pure_typeN : core.

Lemma varN_weakening : forall n m v,
  varN n v ->
  n <= m ->
  varN m v.
Proof with eauto*.
  intros.
  induction H; constructor; lia.
Qed.

Lemma csetN_weakening : forall n m C,
  csetN n C ->
  n <= m ->
  csetN m C.
Proof with eauto*.
  intros.
  induction H.
  - apply csetN_join; auto.
  - apply csetN_bvar. lia.
  - apply csetN_fvar.
  - apply csetN_bot.
  - apply csetN_top.
Qed.

Lemma typeN_weakening : forall n m T,
  typeN n T ->
  n <= m ->
  typeN m T
with pure_typeN_weakening : forall n m R,
  pure_typeN n R ->
  n <= m ->
  pure_typeN m R.
Proof with eauto using varN_weakening, csetN_weakening.
{ clear typeN_weakening.
  intros.
  destruct H...
}
{ clear pure_typeN_weakening.
  intros.
  induction H...
  all: constructor...
  all: eapply typeN_weakening...
  all: lia.
}
Qed.

Lemma open_vt_typeN_aux : forall n S v,
  typeN n (open_vt n S v) ->
  typeN (`succ` n) v.
Proof with eauto*.
  intros.
  destruct v...
  unfold open_vt in H.
  destruct (n === n0); subst...
  inversion H; inversion H0; inversion H5; subst...
  apply typeN_pure, typeN_var, varN_b.
  lia.
Qed.

Lemma open_tt_rec_typeN_aux : forall n S T,
  typeN n (open_tt_rec n S T) ->
  typeN (`succ` n) T
with open_tt_rec_pure_typeN_aux : forall n S R,
  pure_typeN n (open_tt_rec n S R) ->
  pure_typeN (`succ` n) R.
Proof with eauto using open_vt_typeN_aux.
{ clear open_tt_rec_typeN_aux.
  intros * H.
  inversion H; subst...
  destruct T; simpl in *; try discriminate H0...
  injection H0 as HC HR; subst.
  unfold open_cse in H1.
  apply typeN_cset.
  - apply (csetN_weakening n (`succ` n) c); auto.
  - eapply open_tt_rec_pure_typeN_aux, H3.
}
{ clear open_tt_rec_pure_typeN_aux.
  intros * H.
  dependent induction H.
  - Case "bound variable".
    unfold open_tt_rec in x.
    destruct R; simpl in x.
    1: {
      destruct v0...
      unfold open_vt in x.
      destruct (n === n0); subst...
      injection x as x; subst.
      apply typeN_var, varN_b.
      inversion H; subst.
      lia.
    }
    all: discriminate x.
  - Case "⊤".
    destruct R; simpl in x...
    1: {
      destruct v...
      simpl in x.
      destruct (n === n0); subst...
      inversion x.
    }
    all: discriminate x.
  - Case "∀ (S') T".
    destruct R; simpl in x...
    1: {
      destruct v...  
      simpl in x.
      destruct (n === n0); subst...
      inversion x.
    }
    injection x as x; subst.
    apply typeN_arr...
    all: discriminate x.
  - Case "∀ [R] T". 
    destruct R; simpl in x...
    1: {
      destruct v...
      simpl in x.
      destruct (n === n0); subst...
      inversion x.
    }
    2: {
      injection x as x1 x2.
      apply typeN_all...
      eapply open_tt_rec_typeN_aux with (S0 := S).
      rewrite <- x2.
      apply H0.
    }
    all: discriminate x.
  - Case "□ T".
    destruct R; simpl in x...
    1: {
      unfold open_vt in x.
      destruct v...  
      destruct (n === n0); subst...
      discriminate x.
    }
    3: {
      injection x as x; subst.
      apply typeN_box...
    }
    all: discriminate x.
}
Qed.

Lemma open_ct_rec_typeN_aux : forall n S T,
  typeN n (open_ct_rec n S T) ->
  typeN (`succ` n) T
with open_ct_rec_pure_typeN_aux : forall n S R,
  pure_typeN n (open_ct_rec n S R) ->
  pure_typeN (`succ` n) R.
Proof with eauto*.
{ clear open_ct_rec_typeN_aux.
  intros * H.
  dependent induction H...
  Case "C # R".
  destruct T; simpl in x.
  1: destruct v...
  all: try (discriminate x).
  inversion x; subst; clear x.
  unfold open_cse in H.
  apply typeN_cset.
  - induction c.
    + apply (csetN_weakening n (`succ` n) {*}); auto.
    + destruct (n === n0).
      -- rewrite <- e. apply csetN_bvar. lia.
      -- apply (csetN_weakening n (`succ` n) (cse_bvar n0)); auto.
    + apply csetN_fvar.
    + apply csetN_join.
      -- apply IHc1. inversion H. auto.
      -- apply IHc2. inversion H. auto.
    + apply csetN_bot. 
  - eapply open_ct_rec_pure_typeN_aux, H0.
}
{ clear open_ct_rec_pure_typeN_aux.
  intros * H.
  dependent induction H; destruct R; simpl in x...
  1: destruct v; destruct v0; inversion H; injection x as x; subst...
  all: injection x; intros; subst...
}
Qed.

Lemma type_to_type0 : forall T,
  type T -> typeN 0 T
with pure_type_to_pure_type0 : forall R,
  pure_type R -> pure_typeN 0 R.
Proof with eauto.
{ clear type_to_type0.
  intros * H.
  dependent induction H...
  apply typeN_cset...
  induction H.
  - apply csetN_top.
  - apply csetN_fvar.
  - apply csetN_join; auto.
  - apply csetN_bot.
}
{ clear pure_type_to_pure_type0.
  intros * H.
  dependent induction H...
  - constructor...
    pick fresh X.
    unfold open_ct in H0.
    eapply (open_ct_rec_typeN_aux 0 (cse_fvar X))...
  - constructor...
    pick fresh X.
    unfold open_ct in H0.
    eapply (open_tt_rec_typeN_aux 0 X)...
}
Qed.

Hint Extern 1 (_ >= _) => lia : core.

Lemma open_vt_typeN : forall n m S v,
  varN n v ->
  m >= n ->
  typ_var v = open_vt m S v.
Proof with eauto*.
  intros.
  unfold open_vt.
  destruct v...
  destruct (m === n0); subst...
  inversion H.
  lia.
Qed.

Lemma open_tt_rec_typeN : forall n m S T,
  typeN n T ->
  m >= n ->
  T = open_tt_rec m S T.
Proof with eauto using open_vt_typeN.
  intros n m S T.
  generalize dependent m.
  generalize dependent n.
  induction T; intros * H1 H2; simpl; inversion H1; inversion H; subst; f_equal...
Qed.

Lemma open_tt_rec_type : forall T U k,
  type T ->
  T = open_tt_rec k U T.
Proof with auto*.
  intros * [R | C R].
  - Case "R".
    apply open_tt_rec_typeN with (n := k)...
    apply typeN_pure.
    apply pure_type_to_pure_type0 in H. 
    apply pure_typeN_weakening with (m := k) in H...
    lia.
  - Case "C # R".
    simpl.
    f_equal...
    apply open_tt_rec_typeN with (n := k)...
    apply typeN_pure.
    apply pure_type_to_pure_type0 in H0.
    apply pure_typeN_weakening with (m := k) in H0...
    lia.
Qed.

(** If a name is fresh for a term, then substituting for it is the
    identity. *)

Lemma subst_tt_fresh : forall Z U T,
  Z ∉ (fv_tt T `u`A fv_ct T) ->
  T = subst_tt Z U T.
Proof with auto*.
  intros Z U T.
  induction T; simpl; intro H; f_equal...
  - Case "variable".
    destruct v...
    destruct (a == Z)...
    contradict H.
    fsetdec.
Qed.

Lemma subst_tt_open_tt_rec : forall T1 T2 X P k,
  type P ->
  subst_tt X P (open_tt_rec k T2 T1) =
  open_tt_rec k (subst_tt X P T2) (subst_tt X P T1).
Proof with auto*.
  intros.
  generalize dependent k.
  induction T1; intros k; simpl; f_equal...
  destruct v; simpl.
  - Case "a".
    destruct (a == X); subst...
    apply open_tt_rec_type, H.
  - Case "n".
    destruct (k === n); subst...
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
  X ∉ (fv_tt T2 `u`A fv_ct T2) ->
  open_tt_rec k U T2 = subst_tt X U (open_tt_rec k X T2).
Proof with auto*.
  induction T2; intros U k Fr; simpl in *; f_equal...
  - Case "variable".
    unfold open_vt.
    destruct v.
    + SCase "a".
      unfold subst_tt; simpl.
      destruct (a == X); subst...
      exfalso; fsetdec.
    + SCase "n".
      destruct (k === n); subst...
      simpl.
      destruct (X == X); try (contradict n; reflexivity)...
Qed.

(** The next lemma is a direct corollary of the immediately preceding
    lemma---the index is specialized to zero.  *)

Lemma subst_tt_intro : forall X T2 U,
  X ∉ (fv_tt T2 `u`A fv_ct T2) ->
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

Inductive exprN : nat -> exp -> Prop :=
  | exprN_var : forall n v,
      varN n v ->
      exprN n v
  | exprN_abs : forall n T e1,
      typeN n T ->
      exprN (S n) e1 ->
      exprN n (exp_abs T e1)
  | exprN_app : forall n f x,
      varN n f ->
      varN n x ->
      exprN n (exp_app f x)
  | exprN_let : forall n e C,
      exprN n e ->
      exprN (S n) C ->
      exprN n (exp_let e C)
  | exprN_tabs : forall n T e1,
      typeN n T ->
      exprN (S n) e1 ->
      exprN n (exp_tabs T e1)
  | exprN_tapp : forall n x V,
      varN n x ->
      typeN n V ->
      exprN n (exp_tapp x V)
  | exprN_box : forall n x,
      varN n x ->
      exprN n (box x)
  | exprN_unbox : forall n C x,
      csetN n C ->
      varN n x ->
      exprN n (C ⟜ x).

Hint Resolve csetN_weakening varN_weakening typeN_weakening : core.

Lemma open_cset_csetN : forall n C D,
  csetN n C ->
  C = open_cse n D C.
Proof with eauto*.
  intros.
  unfold open_cse.
  induction C; auto; inversion H; simpl in *.
  - destruct (n === n0); try lia; try auto.
  - f_equal; auto.
Qed.

Lemma cse_join_in :
  forall X C1 C2, X ∉ `cse_fvars` (cse_join C1 C2) -> X ∉ `cse_fvars` C1 /\ X ∉ `cse_fvars` C2.
Proof with eauto*.
  intros; split; unfold not; intros; unfold not in H; apply H; simpl;
  apply AtomSetFacts.union_iff; auto.
Qed.

Lemma subst_cset_intro : forall X k D C,
  X ∉ `cse_fvars` C ->
  open_cse k D C = subst_cse X D (open_cse k (cse_fvar X) C).
 Proof with eauto*.
  intros.
  unfold open_cse.
  (* destruct_set_mem k C. *)
  - induction C.
    -- auto.
    -- destruct (k === n); simpl.
      + destruct (X == X). (* TODO: This proof can be simplified, how? *)
        ++ reflexivity.
        ++ unfold not in n0. exfalso. apply n0. reflexivity.
      + reflexivity.
    -- simpl. destruct (X == a).
      + exfalso. unfold not in H. simpl in H. apply H. rewrite e.
        apply AtomSetFacts.singleton_iff. auto.
      + auto.
    -- simpl. f_equal; apply cse_join_in in H; destruct H; auto. 
    -- auto.
Qed.


Lemma subst_te_open_te_rec : forall e T X U k,
  pure_type U ->
  subst_te X U (open_te_rec k T e) =
    open_te_rec k (subst_tt X U T) (subst_te X U e).
Proof with eauto*.
  intros.
  generalize dependent k.
  induction e; intros k; simpl; f_equal; auto using subst_tt_open_tt_rec.
Qed.

Lemma subst_te_open_te_var : forall (X Y:atom) U e,
  Y <> X ->
  pure_type U ->
  open_te (subst_te X U e) Y = subst_te X U (open_te e Y).
Proof with auto*.
  intros X Y U e Neq WU.
  unfold open_te.
  rewrite subst_te_open_te_rec...
  simpl.
  destruct (Y == X)...
Qed.

Lemma subst_te_intro_rec : forall X e U k,
  X ∉ (fv_te e `u`A fv_ce e) ->
  open_te_rec k U e = subst_te X U (open_te_rec k X e).
Proof.
  induction e; intros U k Fr; simpl in *; f_equal;
    auto using subst_cset_intro, subst_tt_intro_rec.
Qed.

Lemma subst_te_intro : forall X e U,
  X ∉ (fv_te e `u`A fv_ce e) ->
  open_te e U = subst_te X U (open_te e X).
Proof with auto*.
  intros.
  unfold open_te.
  apply subst_te_intro_rec...
Qed.

Lemma open_ct_rec_type_aux : forall n T i C,
  typeN n T ->
  i >= n ->
  T = open_ct_rec i C T.
Proof with eauto using open_cset_csetN, csetN_weakening.
  intros n T.
  generalize dependent n.
  induction T; intros; simpl; f_equal; inversion H; inversion H1; subst...
Qed.

Lemma open_ct_rec_type : forall T C k,
  type T ->
  T = open_ct_rec k C T.
Proof with auto using type_to_type0.
  intros.
  generalize dependent k.
  induction T; intros k; simpl; f_equal; inversion H; inversion H0; subst...
  (* TODO: Should I simply the first two cases? *)
  - pick fresh x and specialize H5.
    apply open_ct_rec_type_aux with (n := 1)...
    apply open_ct_rec_typeN_aux with (S0 := cse_fvar x)...
  - pick fresh X and specialize H5.
    apply open_ct_rec_type_aux with (n := 1)...
    apply open_tt_rec_typeN_aux with (S0 := X)...
  - induction H2; auto.
    -- simpl. f_equal; try apply IHcset1; try apply IHcset2; auto. 
Qed.

(*
   TODO maybe we need to strengthen the lemma again for other use cases?
 *)
Lemma subst_tt_open_ct_rec : forall (X : atom) P T C k,
  type P ->
  X ∉ `cse_fvars` C ->
  subst_tt X P (open_ct_rec k C T) = open_ct_rec k C (subst_tt X P T).
Proof with auto using open_ct_rec_type.
  intros.
  generalize dependent k.
  induction T; intros k; simpl; f_equal...
  destruct v...
  destruct (a == X); subst...   
Qed.

(* T[0 !-> C][X !-> P] = T[X !-> P][0 !-> C] *)
Lemma subst_tt_open_ct : forall (X : atom) P T C,
  type P ->
  X ∉ `cse_fvars` C ->
  subst_tt X P (open_ct T C) = open_ct (subst_tt X P T) C.
Proof with auto*.
  intros X P T C.
  unfold open_ct.
  apply subst_tt_open_ct_rec...
Qed.

(* ********************************************************************** *)
(** ** Properties of expression substitution in expressions *)

(** This section follows the structure of the previous two sections. *)

Lemma subst_cse_fresh : forall x C1 C2,
  x `notin` (cse_fvars C1) ->
  C1 = subst_cse x C2 C1.
Proof with eauto.
  intros. induction C1; auto.
  - simpl. destruct (x == a).
    -- subst. exfalso. unfold not in H. apply H. simpl. fsetdec.
    -- reflexivity.
  - simpl. f_equal; try apply IHC1_1; try apply IHC1_2;
    apply cse_join_in in H; destruct H; auto.
Qed.

Lemma subst_ct_fresh : forall (x : atom) c t,
  x ∉ fv_ct t ->
  t = subst_ct x c t.
Proof with eauto using subst_cse_fresh.
  intros x c t.
  induction t; intro H ; simpl in *; f_equal...
  destruct v...
Qed.

Lemma subst_vv_fresh : forall (x : atom) u v,
  x ∉ fv_vv v ->
  v = subst_vv x u v.
Proof with eauto*.
  intros.
  unfold fv_vv, subst_vv in *.
  destruct v...
  destruct (a == x); subst...
  fsetdec.
Qed.

Lemma subst_ve_fresh : forall (x : atom) u c e,
  x ∉ (fv_ve e `u`A fv_ce e) ->
  e = subst_ve x u c e.
Proof with auto using subst_vv_fresh, subst_ct_fresh, subst_cse_fresh.
  induction e; intros; simpl in *; f_equal...
Qed.

Lemma subst_ct_open_rec : forall t x k c1 c2,
  cset c1 ->
  subst_ct x c1 (open_ct_rec k c2 t) =
  open_ct_rec k (subst_cse x c1 c2) (subst_ct x c1 t).
Proof with auto using subst_cse_open_cset_rec.
  induction t; intros; simpl; f_equal...
  destruct v...
Qed.

(** The next lemma states that opening a term is equivalent to first
    opening the term with a fresh name and then substituting for the
    name.  This is actually the strengthened induction hypothesis for
    the version we use in practice. *)

Lemma subst_ct_intro_rec : forall X T2 C k,
  X ∉ fv_ct T2 ->
  open_ct_rec k C T2 = subst_ct X C (open_ct_rec k (cse_fvar X) T2).
Proof with auto*.
  induction T2; intros C k Fr; simpl in *; f_equal...
  - Case "v".
    destruct v...
  - Case "c # T2".
    apply subst_cc_intro_rec.
    fsetdec.
Qed.

(** The next lemma is a direct corollary of the immediately preceding
    lemma---the index is specialized to zero.  *)
Lemma subst_ct_intro : forall X T2 C,
  X ∉ fv_ct T2 ->
  open_ct T2 C = subst_ct X C (open_ct T2 (cse_fvar X)).
Proof with auto*.
  intros.
  unfold open_tt.
  apply subst_ct_intro_rec...
Qed.

Lemma subst_cset_open_cset_fresh : forall k X C1 C2 c,
  cset C1 ->
  cset C2 ->
  ~ X A`in` C2 ->
  subst_cse X C1 (open_cse k C2 c) = open_cse k C2 (subst_cse X C1 c).
Proof with auto*.
  intros.
  assert (C2 = subst_cse X C1 C2). { apply subst_cse_fresh. apply H1. }
  rewrite H2 at 2. 
  eapply subst_cse_open_cset_rec...
Qed.

(* Unprovable *)
(* Lemma subst_cset_open_cset_not_fresh : forall x c d k,
  open_cse k c (subst_cse x c d)  = subst_cse x c (open_cse k (cse_fvar x) d).
Proof with eauto*.
  intros.
  induction d; auto.
  - simpl. destruct (k === n).
    -- simpl. destruct (x == x); auto. unfold not in n0. exfalso. apply n0.
       reflexivity.
    -- auto.
  - simpl. destruct (x == a).*)

(* Lemma subst_ct_open_ct_rec_not_fresh : forall x t c k,
  open_ct_rec k c (subst_ct x c t) = subst_ct x c (open_ct_rec k (cse_fvar x) t).
Proof with eauto using subst_cset_open_cset_not_fresh.
  intros.
  revert k.
  induction t; intros k; simpl in *; f_equal...
  destruct v...
Qed. *)

(* Lemma subst_ct_open_ct_not_fresh : forall x t c,
  open_ct (subst_ct x c t) c = subst_ct x c (open_ct t (cse_fvar x)).
Proof.
  intros.
  apply subst_ct_open_ct_rec_not_fresh.
Qed. *)

Lemma subst_ct_open_ct_rec : forall (X : atom) C1 T C2 k,
  cset C1 ->
  cset C2 ->
  ~ X A`in` C2 ->
  subst_ct X C1 (open_ct_rec k C2 T) = open_ct_rec k C2 (subst_ct X C1 T).
Proof with eauto using subst_cset_open_cset_fresh.
  intros X C1 T C2.
  induction T; intros; simpl; f_equal; try trivial...
  destruct v...
Qed.

Lemma subst_ct_open_ct_var : forall (x y : atom) c t,
  y <> x ->
  cset c ->
  open_ct (subst_ct x c t) (cse_fvar y) = subst_ct x c (open_ct t (cse_fvar y)).
Proof with auto*.
  intros *; intros Neq Wu.
  unfold open_ct.
  symmetry.
  apply subst_ct_open_ct_rec...
Qed.

Lemma subst_te_open_ve_rec : forall e z c Z P k,
  type P ->
  Z ∉ (`cse_fvars` c `u`A {z}A) ->
  subst_te Z P (open_ve_rec k z c e) =
    open_ve_rec k z c (subst_te Z P e).
Proof with eauto using subst_tt_open_ct_rec, subst_cset_open_cset_fresh.
  induction e; intros; simpl in *; f_equal...
Qed.

Lemma subst_te_open_ve : forall e z c Z P,
  type P ->
  Z ∉ (`cse_fvars` c `u`A {z}A) ->
  subst_te Z P (open_ve e z c) = open_ve (subst_te Z P e) z c.
Proof with auto*.
  intros.
  unfold open_ve.
  apply subst_te_open_ve_rec...
Qed.

Lemma subst_te_open_ve_var : forall Z (x : atom) P e c,
  type P ->
  Z ∉ (`cse_fvars` c `u`A {x}A) ->
  open_ve (subst_te Z P e) x c = subst_te Z P (open_ve e x c).
Proof with auto*.
  intros.
  rewrite subst_te_open_ve...
Qed.

Lemma subst_ct_open_vt_fresh : forall z c k P v,
  cset c ->
  z ∉ (fv_ct P `u`A fv_tt P) ->
  subst_ct z c (open_vt k P v) = open_tt_rec k P v.
Proof with eauto.
  intros * Capt NotIn.
  induction P; unfold open_vt; destruct v; simpl in *...
  all: destruct (k === n); subst; simpl; f_equal...
  - destruct v0...
  - symmetry. apply subst_cse_fresh...
Qed.

Lemma subst_ct_open_tt_rec_fresh : forall c z P t k,
  cset c ->
  z ∉ (fv_ct P `u`A fv_tt P) ->
  subst_ct z c (open_tt_rec k P t) = open_tt_rec k P (subst_ct z c t).
Proof with eauto using subst_ct_open_vt_fresh.
  induction t; intros; simpl; f_equal...
  destruct v...
Qed.

Lemma subst_ve_open_te_rec_fresh : forall e P z u c k,
  cset c ->
  z ∉ (fv_ct P `u`A fv_tt P) ->
  subst_ve z u c (open_te_rec k P e) = open_te_rec k P (subst_ve z u c e).
Proof with eauto using subst_cset_open_cset_fresh, subst_ct_open_tt_rec_fresh.
  induction e; intros * Hc Hfv; simpl; f_equal...
Qed.

Lemma subst_ve_open_te_fresh : forall e P z u c,
  cset c ->
  z ∉ (fv_ct P `u`A fv_tt P) ->
  subst_ve z u c (open_te e P) = open_te (subst_ve z u c e) P.
Proof with auto*.
  intros.
  unfold open_te.
  apply subst_ve_open_te_rec_fresh...
Qed.

Lemma subst_ve_open_te_var : forall z (X : atom) u c e,
  z <> X ->
  cset c ->
  open_te (subst_ve z u c e) X = subst_ve z u c (open_te e X).
Proof with auto*.
  intros.
  rewrite subst_ve_open_te_fresh...
Qed.

(* if x is fresh, opening with {x} and then substituting is the same as opening directly. *)
Lemma open_ct_subst_ct_var : forall x c t k,
  x ∉ fv_ct t ->
  open_ct_rec k c t = subst_ct x c (open_ct_rec k (cse_fvar x) t).
Proof with auto.
  induction t; intros; simpl in *; f_equal...
  1: destruct v...
  apply subst_cc_intro_rec...
Qed.

Lemma subst_ct_open_tt_var : forall (X Y:atom) C T,
  Y <> X ->
  cset C ->
  open_tt (subst_ct X C T) Y = subst_ct X C (open_tt T Y).
Proof with auto*.
  intros X Y P T Neq Wu.
  unfold open_tt.
  rewrite subst_ct_open_tt_rec_fresh...
Qed.

Lemma subst_vv_intro : forall k x u v,
  x ∉ fv_vv v ->
  open_vv k u v = subst_vv x u (open_vv k x v).
Proof with eauto*.
  intros.
  unfold open_vv, fv_vv, subst_vv in *.
  destruct v.
  * destruct (a == x); subst...
    fsetdec.
  * destruct (k === n); subst...
    destruct (x == x)...
Qed.

Lemma subst_vv_open_vv : forall x u k y v,
  y <> x ->
  subst_vv x u (open_vv k y v) = open_vv k y (subst_vv x u v).
Proof with eauto*.
  intros * Neq.
  destruct v; simpl.
  - destruct (a == x); simpl...
  - destruct (k === n); simpl...
    destruct (y == x); simpl; subst...
Qed.

Lemma subst_ve_intro_rec : forall x e u c k,
  x ∉ (fv_ve e `u`A fv_ce e) ->
  open_ve_rec k u c e = subst_ve x u c (open_ve_rec k x (cse_fvar x) e).
Proof with eauto using open_ct_subst_ct_var, subst_vv_intro, subst_cset_intro.
  induction e; intros u c' k Fr; simpl in *; f_equal...
Qed.

Lemma subst_ve_intro : forall x e u c,
  x ∉ (fv_ve e `u`A fv_ce e) ->
  open_ve e u c = subst_ve x u c (open_ve e x (cse_fvar x)).
Proof with auto*.
  intros.
  unfold open_ve.
  apply subst_ve_intro_rec...
Qed.

Lemma subst_ve_open_ve_rec : forall e x y u c1 c2 k,
  y <> x ->
  cset c1 ->
  subst_ve x u c1 (open_ve_rec k y c2 e) =
    open_ve_rec k y (subst_cse x c1 c2) (subst_ve x u c1 e).
Proof with auto using subst_vv_open_vv, subst_ct_open_rec, subst_cset_open_cset_fresh.
  intros * Neq Capt.
  revert k.
  induction e; intros k; simpl; f_equal...
Qed.

Lemma subst_ve_open_ve_var : forall (x y u : atom) c e,
  y <> x ->
  expr u ->
  cset c ->
  open_ve (subst_ve x u c e) y (cse_fvar y) =
  subst_ve x u c (open_ve e y (cse_fvar y)).
Proof with auto*.
  intros x y u c e Neq Wu Wc.
  unfold open_ve.
  rewrite subst_ve_open_ve_rec...
  simpl.
  destruct (x == y)...
Qed.

(* *********************************************************************** *)
(** * #<a name="lc"></a># Local closure is preserved under substitution *)

(** While these lemmas may be considered properties of substitution, we
    separate them out due to the lemmas that they depend on. *)

(** The following lemma depends on [subst_tt_open_tt_var]. *)

Lemma subst_tt_type : forall Z P T,
  type T ->
  pure_type P ->
  type (subst_tt Z P T)
with subst_tt_pure_type : forall Z P T,
  pure_type T ->
  pure_type P ->
  pure_type (subst_tt Z P T).
Proof with auto.
{ clear subst_tt_type.
  intros Z P T HT HP.
  induction HT; simpl...
}
{ clear subst_tt_pure_type.
  intros Z P T HT HP.
  induction HT; simpl...
  - Case "X".
    destruct (X == Z); subst...
  - Case "∀ (S') T".
    pick fresh Y and apply type_arr...
    rewrite <- subst_tt_open_ct...
  - Case "∀ [R] T".
    pick fresh Y and apply type_all...
    rewrite subst_tt_open_tt_var...
}
Qed.

Local Hint Extern 1 (~ AtomSet.F.In _ _) => simpl_env in *; [fsetdec] : core.

Lemma subst_ct_open_fresh : forall k z C T X,
  (* X fresh requirement here in z c T *)
  X ∉ (singleton z `u`A fv_tt T `u`A fv_ct T)
    /\ X ∉ `cse_fvars` C ->
  cset C ->
  (open_ct_rec k (cse_fvar X) (subst_ct z C T)) =
    (subst_ct z C (open_ct_rec k (cse_fvar X) T)).
Proof with eauto.
  intros k z C T X HXfresh HCfresh.
  revert k.
  induction T; intro k; simpl in *; try reflexivity; try destruct v; f_equal...
  symmetry.
  apply subst_cset_open_cset_fresh.
  - exact HCfresh.
  - constructor.
  - destruct HXfresh. notin_simpl. simpl. fsetdec.
Qed.

Lemma subst_cse_cset: forall X C D,
  cset C ->
  cset D ->
  cset (subst_cse X C D).
Proof with auto.
  intros X C D HC HD.
  induction D; simpl...
  - destruct (X == a); subst...
  - apply cset_join; inversion HD...
Qed.

Lemma subst_ct_type : forall T z c,
  type T ->
  cset c ->
  type (subst_ct z c T)
with subst_ct_pure_type : forall R z c,
  pure_type R ->
  cset c ->
  pure_type (subst_ct z c R).
 Proof with auto*.
{ clear subst_ct_type.
  intros * Typ ?.
  induction Typ; simpl...
  apply type_cse.
  apply subst_cse_cset...
  apply subst_ct_pure_type...
}
{ clear subst_ct_pure_type.
  intros * Typ Cap.
  induction Typ; simpl...
  - Case "∀ (S') T".
    pick fresh x and apply type_arr...
    assert ((open_ct (subst_ct z c T) (cse_fvar x)) =
    (subst_ct z c (open_ct T (cse_fvar x)))).
    { apply subst_ct_open_fresh.
      split.
      - fsetdec.
      - destruct c. fsetdec. auto. auto. auto. auto.
      - apply Cap.
    }
    rewrite H1...
  - Case "∀ [R] T".
    pick fresh X and apply type_all...
    assert ((open_tt (subst_ct z c T) X) =
    (subst_ct z c (open_tt T X))).
    { symmetry.
      apply subst_ct_open_tt_rec_fresh; simpl...
    }
    rewrite H0...
}
Qed.

(* *********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

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
  cset c ->
  z ∉ fv_tt P ->
  subst_ct z c (open_tt_rec k P t) = open_tt_rec k (subst_ct z c P) (subst_ct z c t).
Proof with eauto.
  induction t ; intros ; simpl ; f_equal...
  destruct v; simpl...
  destruct (k === n); subst...
Qed.

Lemma subst_ct_open_tt : forall x c t1 t2,
  cset c ->
  x ∉ fv_tt t2 ->
  subst_ct x c (open_tt t1 t2) = (open_tt (subst_ct x c t1) (subst_ct x c t2)).
Proof with auto using open_cse_cset, open_ct_rec_type, subst_ct_open_tt_rec.
  intros.
  cbv [open_tt].
  apply subst_ct_open_tt_rec...
Qed.

Lemma open_ct_subst_tt : forall x C S T,
  type S ->
  x ∉ `cse_fvars` C ->
  open_ct (subst_tt x S T) C = subst_tt x S (open_ct T C).
Proof with auto
    using open_cse_cset,
          open_ct_rec_type,
          subst_ct_open_rec,
          subst_ct_open_tt_var,
          open_ct_subst_ct_var.
  intros * HS Hfr.
  cbv [open_ct]...
  pick fresh y for (fv_ct (subst_tt x S T)).
  erewrite open_ct_subst_ct_var.
  erewrite subst_tt_open_ct_rec.
  erewrite <-subst_ct_intro_rec.
  all: eauto.
Qed.

Lemma subst_tt_open_ct_var : forall (X y:atom) P T,
  y <> X ->
  type P ->
  open_ct (subst_tt X P T) (cse_fvar y) = subst_tt X P (open_ct T (cse_fvar y)).
Proof with auto*.
  intros *; intros Neq Wu.
  unfold open_ct.
  symmetry.
  apply subst_tt_open_ct_rec; trivial.
  notin_solve.
Qed.
