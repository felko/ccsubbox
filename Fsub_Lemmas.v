(** Administrative lemmas for Fsub.

    Authors: Brian Aydemir and Arthur Chargu\u00e9raud, with help from
    Aaron Bohannon, Jeffrey Vaughan, and Dimitrios Vytiniotis.

    This file contains a number of administrative lemmas that we
    require for proving type-safety.  The lemmas mainly concern the
    relations [wf_typ] and [wf_env].

    This file also contains regularity lemmas, which show that various
    relations hold only for locally closed terms.  In addition to
    being necessary to complete the proof of type-safety, these lemmas
    help demonstrate that our definitions are correct; they would be
    worth proving even if they are unneeded for any "real" proofs.

    Table of contents:
      - #<a href="##wft">Properties of wf_typ</a>#
      - #<a href="##oktwft">Properties of wf_env and wf_typ</a>#
      - #<a href="##okt">Properties of wf_env</a>#
      - #<a href="##subst">Properties of substitution</a>#
      - #<a href="##regularity">Regularity lemmas</a>#
      - #<a href="##auto">Automation</a># *)

Require Export Fsub_Infrastructure.


(* ********************************************************************** *)
(** * #<a name="wft"></a># Properties of [wf_typ] *)

(** If a type is well-formed in an environment, then it is locally
    closed. *)

Lemma capt_from_wf_cset : forall E C,
  wf_cset E C -> capt C.
Proof with auto.
  intros.
  inversion H...
Qed.
  
Lemma type_from_wf_typ : forall E T,
  wf_typ E T -> type T.
Proof with eauto.
  intros E T H; induction H...
  destruct H0...
Qed.

(** This is a useful helper tactic for clearing away
    capture set wellformedness. *)

Ltac wf_cset_simpl instantiate_ext :=
  match goal with 
  | H : _ |- (wf_cset _ cset_universal) =>
    constructor
  | H : (wf_cset _ ?C) |- (wf_cset _ ?C) =>
    let Hdestruct := fresh "Hdestruct" in
    let x  := fresh "x" in
    let Hx := fresh "Hxin" in
    let Hexists := fresh "Hexists" in
    let T := fresh "T" in
    let Hbound := fresh "Hbound" in
    let E := fresh "E" in
    let fvars := fresh "fvars" in
    let Hclosed := fresh "Hclosed" in
      inversion H as [|E fvars Hbound Hclosed]; subst; [ auto | 
        constructor;
        unfold allbound_typ in Hbound;
        intros x Hx;
        destruct (Hbound x Hx) as [T Hexists];
        lazymatch instantiate_ext with
        | True => exists T
        | False => idtac
      end ]
  end.
  
Lemma wf_cset_weakening : forall E F G C,
    wf_cset (G ++ E) C ->
    ok (G ++ F ++ E) ->
    wf_cset (G ++ F ++ E) C.
Proof with auto*.
  intros E F G C Hcset Henv.
  wf_cset_simpl True...
Qed.

Lemma wf_cset_weaken_head : forall C E F,
  wf_cset E C ->
  ok (F ++ E) ->
  wf_cset (F ++ E) C.
Proof.
  intros.
  rewrite_env (empty ++ F++ E).
  auto using wf_cset_weakening.
Qed.

Lemma wf_typ_weakening : forall T E F G,
  wf_typ (G ++ E) T ->
  ok (G ++ F ++ E) ->
  wf_typ (G ++ F ++ E) T.
Proof with simpl_env; eauto using wf_cset_weakening.
  intros.
  remember (G ++ E).
  generalize dependent G.
  induction H; intros G Hok Heq; subst...
  (* typ_arrow case *)
  - pick fresh Y and apply wf_typ_arrow...
    assert (Y `notin` L) as P by fsetdec.
    apply (H1 Y P ([(Y, bind_typ T1)] ++ G))...
  (* typ_all case *)
  - pick fresh Y and apply wf_typ_all...
    assert (Y `notin` L) as P by fsetdec.
    apply (H1 Y P ([(Y, bind_sub T1)] ++ G))...
Qed.

Lemma wf_typ_weaken_head : forall T E F,
  wf_typ E T ->
  ok (F ++ E) ->
  wf_typ (F ++ E) T.
Proof.
  intros.
  rewrite_env (empty ++ F ++ E).
  auto using wf_typ_weakening.
Qed.


(* Type bindings don't matter at all! *)
Lemma wf_cset_narrowing : forall V U C E F X,
  wf_cset (F ++ [(X, bind_sub V)] ++ E) C ->
  ok (F ++ [(X, bind_sub U)] ++ E) ->
  wf_cset (F ++ [(X, bind_sub U)] ++ E) C.
Proof with simpl_env; eauto.
  intros V U C E F X Hwf Hok.
  wf_cset_simpl True...
  binds_cases Hexists...
Qed.

Lemma wf_typ_narrowing : forall V U T E F X,
  wf_typ (F ++ [(X, bind_sub V)] ++ E) T ->
  ok (F ++ [(X, bind_sub U)] ++ E) ->
  wf_typ (F ++ [(X, bind_sub U)] ++ E) T.
Proof with simpl_env; eauto using wf_cset_narrowing.
  intros.
  remember (F ++ [(X, bind_sub V)] ++ E).
  generalize dependent F.
  induction H; intros F Hok Heq; subst; auto.
  (* typ_var *)
  - binds_cases H...
  (* typ_arrow *)
  - pick fresh Y and apply wf_typ_arrow...
    apply H1 with (X0 := Y) (F0 := [(Y, bind_typ T1)] ++ F)...
  (* typ_all *)
  - pick fresh Y and apply wf_typ_all...
    rewrite <- concat_assoc.
    apply H1 with (X0 := Y) (F0 := [(Y, bind_sub T1)] ++ F)...
  (* typ_capt *)
  - eapply wf_typ_capt...
Qed.


(* JONATHAN: Maybe those _sub variants are not needed afterall! *)
Lemma wf_cset_narrowing_typ : forall C1 C2 C E F X,
  wf_cset (F ++ [(X, bind_typ C1)] ++ E) C ->
  ok (F ++ [(X, bind_typ C2)] ++ E) ->
  wf_cset (F ++ [(X, bind_typ C2)] ++ E) C.
Proof with simpl_env; eauto.
  intros C1 C2 C E F X Hwf Hok.
  wf_cset_simpl False.
  binds_cases Hexists...
Qed.

Lemma wf_typ_narrowing_typ : forall C1 C2 T E F X,
  wf_typ (F ++ [(X, bind_typ C1)] ++ E) T ->
  ok (F ++ [(X, bind_typ C2)] ++ E) ->
  wf_typ (F ++ [(X, bind_typ C2)] ++ E) T.
Proof with simpl_env; eauto using wf_cset_narrowing_typ.
  intros C1 C2 T E F X Hwf_typ Hok.
  remember (F ++ [(X, bind_typ C1)] ++ E).
  generalize dependent F.
  induction Hwf_typ; intros F Hok Heq; subst...
  - Case "wf_typ_var".
    binds_cases H...
  - Case "typ_arrow".
    pick fresh Y and apply wf_typ_arrow...
    rewrite <- concat_assoc.
    apply H0...
  - Case "typ_all".
    pick fresh Y and apply wf_typ_all...
    rewrite <- concat_assoc.
    apply H0...
Qed.

(** Substitution lemmas *)
Lemma wf_cset_subst_tb : forall F Q E Z P C,
  wf_cset (F ++ [(Z, bind_sub Q)] ++ E) C ->
  wf_typ E P ->
  ok (map (subst_tb Z P) F ++ E) ->
  wf_cset (map (subst_tb Z P) F ++ E) C.
Proof with simpl_env; eauto*.
  intros F Q E Z P C HwfC HwfP Hok.
  wf_cset_simpl False...
  binds_cases Hexists...
  * exists (subst_tt Z P T)...
Qed.

Lemma wf_typ_subst_tb : forall F Q E Z P T,
  wf_typ (F ++ [(Z, bind_sub Q)] ++ E) T ->
  (** NOTE here that P needs to be well formed in both the + and - environments,
      as we're substituting in both places. *)
  wf_typ E P ->
  ok (map (subst_tb Z P) F ++ E) ->
  wf_typ (map (subst_tb Z P) F ++ E) (subst_tt Z P T).
Proof with simpl_env; eauto using wf_typ_weaken_head, type_from_wf_typ, wf_cset_subst_tb.
  intros F Q E Z P T HwfT HwfP Hok.
  remember (F ++ [(Z, bind_sub Q)] ++ E).
  generalize dependent F.
  induction HwfT; intros F EQF Hok; subst; simpl subst_tt...
  - Case "wf_typ_var".
    destruct (X == Z); subst...
    + SCase "X <> Z".
      binds_cases H...
      apply (wf_typ_var (subst_tt Z P U))...
  - Case "wf_typ_arrow".
    pick fresh Y and apply wf_typ_arrow...
    + SCase "T2".
      unfold open_ct in *...
      rewrite <- subst_tt_open_ct_rec...
      rewrite_env (map (subst_tb Z P) ([(Y, bind_typ T1)] ++ F) ++ E).
      apply H0...
  - Case "wf_typ_all".
    pick fresh Y and apply wf_typ_all...
    + SCase "T2".
      unfold open_ct in *...
      rewrite subst_tt_open_tt_var...
      rewrite_env (map (subst_tb Z P) ([(Y, bind_sub T1)] ++ F) ++ E).
      apply H0...
Qed.

Lemma wf_typ_open : forall E U T1 T2,
  ok E ->
  wf_typ E (typ_all T1 T2) ->
  wf_typ E U ->
  wf_typ E (open_tt T2 U).
Proof with simpl_env; eauto.
  intros E U T1 T2 O WA WU.
  inversion WA; subst.
  pick fresh X.
  rewrite (subst_tt_intro X)...
  rewrite_env (map (subst_tb X U) empty ++ E).
  apply wf_typ_subst_tb with (Q := T1)...
Qed.

(** This should move into infrastructure probably at some point. **)
(** The next lemma states that opening a term is equivalent to first
    opening the term with a fresh name and then substituting for the
    name.  This is actually the strengthened induction hypothesis for
    the version we use in practice. *)

Lemma subst_ct_intro_rec : forall X T2 C k,
  X `notin` fv_et T2 ->
  open_ct_rec k C T2 = subst_ct X C (open_ct_rec k X T2).
Proof with auto*.
  induction T2; intros C k Fr; simpl in *; f_equal...
  - Case "typ_cset".
    apply subst_capt_cset_swap.
    csetdec; destruct c...
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

Definition subst_cb (Z : atom) (C : captureset) (b : binding) : binding :=
  match b with
  | bind_sub T => bind_sub (subst_ct Z C T)
  | bind_typ T => bind_typ (subst_ct Z C T)
  end.
Hint Extern 1 (binds _ (?F (subst_ct ?X ?U ?C)) _) =>
  unsimpl (subst_cb X U (F C)) : core.

  
Lemma subst_ct_open_ct_rec : forall (X : atom) C1 T C2 k,
  capt C1 ->
  capt C2 ->
  ~ cset_references_fvar X C2 ->
  subst_ct X C1 (open_ct_rec k C2 T) = open_ct_rec k C2 (subst_ct X C1 T).
Proof with auto*.
  intros X C1 T C2.
  induction T; intros; simpl; f_equal...
  (** most of the cases go away with some awful automation. *)
  unfold subst_cset; unfold open_cset;
    cset_split; cset_cleanup; 
    destruct C2 eqn:HC2; destruct C1 eqn:HC1; try destruct c eqn:Hc;
    f_equal; try fsetdec; try fnsetdec...
  (* the remaining cases are either contradictions in the assumptions
      that can be discharged using fnsetdec,
      or just facts about how capture sets behave. *)
  all: inversion H; inversion H0; subst; fnsetdec.
Qed.

Lemma subst_ct_open_tt_var : forall (X Y:atom) C T,
  Y <> X ->
  capt C ->
  open_tt (subst_ct X C T) Y = subst_ct X C (open_tt T Y).
Proof with auto*.
  intros X Y P T Neq Wu.
  unfold open_tt.
  rewrite subst_ct_open_tt_rec...
Qed.

Lemma wf_typ_subst_cb : forall F Q E Z C T,
  wf_typ (F ++ [(Z, bind_typ Q)] ++ E) T ->
  (** NOTE here that P needs to be well formed in both the + and - environments,
      as we're substituting in both places. *)
  wf_cset E C ->
  ok (map (subst_cb Z C) F ++ E) ->
  wf_typ (map (subst_cb Z C) F ++ E) (subst_ct Z C T).
Proof with simpl_env; eauto using wf_typ_weaken_head, type_from_wf_typ, wf_cset_subst_tb,
    capt_from_wf_cset.
  intros F Q E Z C T HwfT HwfC Hok.
  remember (F ++ [(Z, bind_typ Q)] ++ E).
  generalize dependent F.
  induction HwfT; intros F EQF Hok; subst; simpl subst_ct...
  - Case "wf_typ_var".
      binds_cases H...
      apply (wf_typ_var (subst_ct Z C U))...
  - Case "wf_typ_arrow".
    pick fresh Y and apply wf_typ_arrow...
    + SCase "T2".
      unfold open_ct in *...
      rewrite <- subst_ct_open_ct_rec...
      rewrite_env (map (subst_cb Z C) ([(Y, bind_typ T1)] ++ F) ++ E).
      apply H0...
      constructor.
      simpl. fsetdec.
  - Case "wf_typ_all".
    pick fresh Y and apply wf_typ_all...
    + SCase "T2".
      unfold open_ct in *...
      rewrite subst_ct_open_tt_var...
      rewrite_env (map (subst_cb Z C) ([(Y, bind_sub T1)] ++ F) ++ E).
      apply H0...
  - Case "wf_typ_capt".
    eapply wf_typ_capt...
    (** This should probably go in another lemma, likely.  It's
        true though. *)
    admit.
Admitted.

Lemma wf_typ_open_capt : forall E C T1 T2,
  ok E ->
  wf_typ E (typ_arrow T1 T2) ->
  wf_cset E C ->
  wf_typ E (open_ct T2 C).
Proof with simpl_env; eauto.
  intros E U T1 T2 O WA WC.
  inversion WA; subst.
  pick fresh X.
  rewrite (subst_ct_intro X)...
  (** Needs new lemmas for opening a type with a capture set;
      probably wf_typ_subst_eb and subst_ct_intro X *)
  rewrite_env (map (subst_cb X U) empty ++ E).
  apply wf_typ_subst_cb with (Q := T1)...
Qed.


(* ********************************************************************** *)
(** * #<a name="oktwft"></a># Properties of [wf_env] and [wf_typ] *)

Lemma ok_from_wf_env : forall E,
  wf_env E ->
  ok E.
Proof.
  intros E H; induction H; auto.
Qed.

(** We add [ok_from_wf_env] as a hint here since it helps blur the
    distinction between [wf_env] and [ok] in proofs.  The lemmas in
    the [Environment] library use [ok], whereas here we naturally have
    (or can easily show) the stronger [wf_env].  Thus,
    [ok_from_wf_env] serves as a bridge that allows us to use the
    environments library. *)

Hint Resolve ok_from_wf_env : core.

Lemma wf_typ_from_binds_typ : forall x U E,
  wf_env E ->
  binds x (bind_typ U) E ->
  wf_typ E U.
Proof with eauto using wf_typ_weaken_head.
  intros x U E Hwf Hbinds.
  (* remember m; generalize dependent m. *)
  induction Hwf; binds_cases Hbinds...
  inversion H3; subst...
Qed.

Lemma wf_typ_from_binds_sub : forall x U E,
  wf_env E ->
  binds x (bind_sub U) E ->
  wf_typ E U.
Proof with eauto using wf_typ_weaken_head.
  intros x U E Hwf Hbinds.
  (* remember m; generalize dependent m. *)
  induction Hwf; binds_cases Hbinds...
  inversion H3; subst...
Qed.

Lemma wf_typ_from_wf_env_typ : forall x T E,
  wf_env ([(x, bind_typ T)] ++ E) ->
  wf_typ E T.
Proof.
  intros x T E H. inversion H; auto.
Qed.

Lemma wf_typ_from_wf_env_sub : forall x T E,
  wf_env ([(x, bind_sub T)] ++ E) ->
  wf_typ E T.
Proof.
  intros x T E H. inversion H; auto.
Qed.

(* ********************************************************************** *)
(** * #<a name="okt"></a># Properties of [wf_env] *)

(** These properties are analogous to the properties that we need to
    show for the subtyping and typing relations. *)

Lemma wf_env_narrowing : forall V E F U X,
  wf_env (F ++ [(X, bind_sub V)] ++ E) ->
  wf_typ E U ->
  wf_env (F ++ [(X, bind_sub U)] ++ E).
Proof with eauto 6 using wf_typ_narrowing.
  induction F; intros U X Wf_env Wf;
    inversion Wf_env; subst; simpl_env in *...
Qed.

Lemma wf_env_narrowing_typ : forall V E F U X,
  wf_env (F ++ [(X, bind_typ V)] ++ E) ->
  wf_typ E U ->
  wf_env (F ++ [(X, bind_typ U)] ++ E).
Proof with eauto 6 using wf_typ_narrowing_typ, wf_cset_narrowing_typ.
  induction F; intros U X Wf_env Wf;
    inversion Wf_env; subst; simpl_env in *...
Qed.

Lemma wf_env_subst_tb : forall Q Z P E F,
  wf_env (F ++ [(Z, bind_sub Q)] ++ E) ->
  wf_typ E P ->
  wf_env (map (subst_tb Z P) F ++ E).
Proof with eauto 6 using wf_typ_subst_tb.
  induction F; intros Wf_env WP; simpl_env;
    inversion Wf_env; simpl_env in *; simpl subst_tb...
Qed.

Lemma wf_env_inv : forall F Z b E,
  wf_env (F ++ [(Z, b)] ++ E) ->
  wf_env E /\ Z `notin` dom E.
Proof with eauto.
  induction F ; intros ; simpl_env in *.
  inversion H ; subst...
  inversion H ; subst...
Qed.

(* ********************************************************************** *)
(** * #<a name="subst"></a># Environment is unchanged by substitution for a fresh name *)

(** These proofs are all the same, but Coq isn't smart enough unfortunately... *)
Local Lemma notin_fv_tt_open_tt : forall (Y X : atom) T,
  X `notin` fv_tt (open_tt T Y) ->
  X `notin` fv_tt T.
Proof.
 intros Y X T. unfold open_tt.
 generalize 0.
 induction T; simpl; intros k Fr; notin_simpl; try apply notin_union; eauto.
Qed.

Local Lemma notin_fv_tt_open_et : forall (Y X : atom) T,
  X `notin` fv_et (open_tt T Y) ->
  X `notin` fv_et T.
Proof.
 intros Y X T. unfold open_tt.
 generalize 0.
 induction T; simpl; intros k Fr; notin_simpl; try apply notin_union; eauto.
Qed.

Local Lemma notin_fv_tt_open : forall (Y X : atom) T,
  X `notin` fv_tt (open_tt T Y) ->
  X `notin` fv_et (open_tt T Y) ->
  X `notin` (fv_tt T `union` fv_et T).
Proof with auto.
 intros. apply notin_union.
 - apply notin_fv_tt_open_tt with (Y := Y)...
 - apply notin_fv_tt_open_et with (Y := Y)...
Qed.

(** Again, these proofs are all the same, but Coq isn't smart enough unfortunately. *)
Local Lemma notin_fv_ct_open_tt : forall (X : atom) T C,
  X `notin` fv_tt (open_ct T C) ->
  X `notin` fv_tt T.
Proof with auto.
  intros X T C. unfold open_ct.
  generalize 0.
  induction T ; simpl ; intros k Fr ; try apply notin_union; eauto.
  - specialize (IHT1 k). specialize (IHT2 (S k))...
  - specialize (IHT1 k). specialize (IHT2 (S k))...
  - specialize (IHT1 k). specialize (IHT2 k)...
  - specialize (IHT1 k). specialize (IHT2 k)...
Qed.

Local Lemma notin_fv_ct_open_et : forall (X : atom) T C,
  C <> cset_universal ->
  X `notin` fv_et (open_ct T C) ->
  X `notin` fv_et T.
Proof with auto.
  intros X T C Hc. unfold open_ct.
  generalize 0.
  induction T ; simpl ; intros k Fr ; try apply notin_union; eauto.
  - specialize (IHT1 k). specialize (IHT2 (S k))...
  - specialize (IHT1 k). specialize (IHT2 (S k))...
  - specialize (IHT1 k). specialize (IHT2 k)...
  - specialize (IHT1 k). specialize (IHT2 k)...
  - notin_simpl. clear IHT H0.
    revert H. 

    (** Sets suck; this should be a tactic *)
    unfold fv_cset. unfold open_cset. 
    cset_split; destruct C eqn:HC; destruct c eqn:Hcd...
  - specialize (IHT k)...
Qed.

Local Lemma notin_fv_ct_open_ct : forall (Y X : atom) T,
  X `notin` fv_et (open_ct T Y) ->
  X <> Y ->
  X `notin` fv_et T.
Proof with eauto*.
  intros Y X T. unfold open_ct.
  generalize 0.
  induction T; simpl; intros k Fr1 Fr2; notin_simpl; try apply notin_union; eauto.
  clear H0. clear IHT.

  (* Sets suck; this should be a tactic *)
  unfold fv_cset in *; unfold open_cset in *;
  destruct (cset_references_bvar_dec k c) eqn:Hkc1;
  unfold cset_union in *;
  unfold cset_fvar in *;
  destruct (cset_remove_bvar k c) eqn:Hkc2;
  destruct c eqn:Hc...

  - unfold cset_remove_bvar in *. contradict Hkc2...
  - unfold cset_remove_bvar in *. inversion Hkc2. fsetdec.
Qed.

Lemma notin_fv_ct_open : forall (X : atom) T C,
  C <> cset_universal ->
  X `notin` fv_et (open_ct T C) ->
  X `notin` fv_tt (open_ct T C) ->
  X `notin` (fv_tt T `union` fv_et T).
Proof with auto.
  intros. apply notin_union...
  - apply notin_fv_ct_open_tt with (C := C)...
  - apply notin_fv_ct_open_et with (C := C)...
Qed.


Lemma notin_fv_wf_typ : forall E (X : atom) T,
  wf_typ E T ->
  X `notin` dom E ->
  X `notin` (fv_tt T `union` fv_et T).
Proof with eauto.
  intros E X T Wf_typ.
  induction Wf_typ; intros FrE; simpl...
  (* Var *)
  - assert (X0 `in` dom E) by (eapply binds_In; eauto)...
  (* typ_arrow *)
  - pick fresh Y.
    assert (Y `notin` L) by fsetdec.
    assert (X `notin` dom ([(Y, bind_typ T1)] ++ E)). {
      simpl_env. fsetdec.
    }
    specialize (H0 Y H1 H2).
    notin_simpl.
    repeat apply notin_union...
    + apply notin_fv_ct_open_tt with (C := Y)...
    + apply notin_fv_ct_open_et with (C := Y).
      discriminate. intuition.
  (* typ_all *)
  - pick fresh Y.
    assert (Y `notin` L) by fsetdec.
    assert (X `notin` dom ([(Y, bind_typ T1)] ++ E)). {
      simpl_env. fsetdec.
    }
    specialize (H0 Y H1 H2).
    notin_simpl.
    repeat apply notin_union...
    + apply notin_fv_tt_open_tt with (Y := Y)...
    + apply notin_fv_tt_open_et with (Y := Y)...
  (* typ_cset *)
  - specialize (IHWf_typ FrE).
    inversion H;
    destruct C.
    + fsetdec.
    + repeat apply notin_union; try fsetdec.
    + contradict H2; discriminate.
    + repeat apply notin_union; try fsetdec.
      unfold fv_cset in *.
      unfold allbound_typ in *.
      unfold cset_fvar.
      intro.
      specialize (H0 X H3).
      inversion H2; subst.
      destruct H0.
      assert (X `in` dom E). { eapply binds_In... }
      contradiction.
Qed.

Lemma notin_fv_wf : forall E (X : atom) T,
  wf_typ E T ->
  X `notin` dom E ->
  X `notin` fv_tt T.
Proof with eauto.
  intros E X T Wf_typ F.
  assert (X `notin` (fv_tt T `union` fv_et T)). {
    eapply notin_fv_wf_typ...
  }
  fsetdec.
Qed.

Lemma map_subst_tb_id : forall G Z P,
  wf_env G ->
  Z `notin` dom G ->
  G = map (subst_tb Z P) G.
Proof with auto.
  intros G Z P H.
  induction H; simpl; intros Fr; simpl_env...
  rewrite <- IHwf_env...
    rewrite <- subst_tt_fresh... eapply notin_fv_wf; eauto.
  rewrite <- IHwf_env...
    rewrite <- subst_tt_fresh... eapply notin_fv_wf; eauto.
Qed.

(* ********************************************************************** *)
(** * #<a name="regularity"></a># Regularity of relations *)

Lemma subcapt_regular : forall E C1 C2,
  subcapt E C1 C2 ->
  wf_cset E C1 /\ wf_cset E C2.
Proof with eauto*.
  intros. inversion H...
Qed.

(* Lemma captures_regular : forall E C x,
  captures E C x ->
  wf_env E /\ wf_cset E C.
Proof with eauto*.
  intros. inversion H...
  - pose proof (subcapt_regular _ _ _ H1) as [WFenv [_ WfC]]...
  - pose proof (subcapt_regular _ _ _ H1) as [WFenv [_ WfC]]...
Qed. *)

Lemma sub_regular : forall E S T,
  sub E S T ->
  wf_env E /\ wf_typ E S /\ wf_typ E T.
Proof with simpl_env; auto*.
  intros E S T H.
  induction H...
  - Case "sub_trans_tvar".
    eauto*.
  - Case  "sub_trans_arrow".
    repeat split...
    + (* S1 -> S2 wf *)
      pick fresh Y and apply wf_typ_arrow...
      assert (Y `notin` L) by fsetdec.
      rewrite_env (empty ++ [(Y, bind_typ S1)] ++ E).
      apply wf_typ_narrowing_typ with (C1 := T1)...
      apply H1...
    + (* T1 -> T2 wf *)
      pick fresh Y and apply wf_typ_arrow...
      assert (Y `notin` L) by fsetdec.
      apply H1...
  - Case "sub_all".
    repeat split...
    SCase "Second of original three conjuncts".
      pick fresh Y and apply wf_typ_all...
      destruct (H1 Y)...
      rewrite_env (empty ++ [(Y, bind_sub S1)] ++ E).
      apply (wf_typ_narrowing T1)...
    SCase "Third of original three conjuncts".
      pick fresh Y and apply wf_typ_all...
      destruct (H1 Y)...
  - Case "sub_capt".
    assert (wf_cset E C1 /\ wf_cset E C2). { apply subcapt_regular... }
    repeat split...
Qed.

Lemma cv_free_is_bvar_free : forall e,
  empty_cset_bvars (free_for_cv e).
Proof with eauto*.
  intros. induction e... 
  - simpl; fnsetdec...
  - simpl; fnsetdec...
  - unfold free_for_cv.
    fold free_for_cv.
    admit.
Admitted.

Lemma cv_free_atom : forall (x : atom),
  free_for_cv x = x.
Proof with auto*.
  intros.
  unfold free_for_cv...
Qed.

Lemma singleton_set_eq : forall (x y : atom),
  singleton x = singleton y <-> x = y.
Proof.
  split; intros.
  * assert (y `in` singleton x).
    { rewrite H. fsetdec. }
    fsetdec.
  * fsetdec.
Qed.
(*
Lemma cv_open : forall (x y : atom) e,
  expr e ->
  cv_free e x ->
  cv_free (open_ee e y y) x.
Proof with eauto*.
  intros.
  unfold open_ee.
  rewrite <- open_ee_rec_expr with (e := e) (k := 0) (u := y) (c := y)...
Qed.
*)

Require Import Coq.Program.Equality.
Lemma typing_atom : forall E (x : atom) T,
  typing E x T ->
  wf_cset E (free_for_cv x).
Proof with auto*.
  intros E x T Htyp.
  (** Use dependent induction when you want to remember the shape of
      arguments in the typ.  Here we know that x is an atom so the only
      judgment rules that can show up in the typing judgment is either
      a lookup rule or a subtyping rule. *)
  dependent induction Htyp...
  - constructor. 
    (** TODO: tactic *)
    unfold allbound_typ. intros. assert (x0 = x) by fsetdec; subst.
    exists T...
Qed.

(*
Inductive cv_free : exp -> captureset -> Prop :=
  | cv_free_bvar : forall n,
                    cv_free (exp_bvar n) {}C
  | cv_free_fvar : forall x,
                    cv_free (exp_fvar x) (cset_fvar x)
  | cv_free_abs : forall T e1 C,
                    cv_free e1 C ->
                    cv_free (exp_abs T e1) C
  | cv_free_app : forall e1 e2 C1 C2 C,
                    cv_free e1 C1 ->
                    cv_free e2 C2 ->
                    cv_free (exp_app e1 C e2) (cset_union C1 C2)
  | cv_free_tabs : forall T e1 C,
                    cv_free e1 C ->
                    cv_free (exp_tabs T e1) C
  | cv_free_tapp : forall e1 T C,
                    cv_free e1 C ->
                    cv_free (exp_tapp e1 T) C
*)

(** This should be easily true: free variables
    are all bound if a term has a type.... *)
Lemma typing_cv : forall E e T,
  typing E e T ->
  wf_cset E (free_for_cv e).
Proof with auto*.
  intros E e T Htyp.
  induction Htyp.
  - admit.
  - pick fresh y.
    assert (y `notin` L) by fsetdec.
    (* assert (y `notin` (free_for_cv (exp_abs V e1))). *)
    (* free_for_cv (open_ee e1 y y) = {y} \cup (free_for_cv e1) *)
    specialize (H0 y H1).
Admitted.

(** The things that the cv relation returns are all well-formed,
    assuming the type is well formed... *)
Lemma cv_wf : forall E T C,
  wf_env E ->
  wf_typ E T ->
  cv T E C ->
  wf_cset E C.
Proof with simpl_env; eauto*.
  intros E T C WE WT HC.
  induction HC...
  * inversion WT; subst...
    specialize (IHHC WE H2).
    inversion IHHC;
    inversion H3; subst...
    unfold cset_union...
    assert (NatSet.F.union {}N {}N = {}N) by fnsetdec; rewrite H0...
    apply wf_concrete_cset.
    unfold allbound_typ in *.
    intros.
    (** union --> \/ should be simple *)
    assert (x `in` fvars0 \/ x `in`fvars) by fsetdec.
    inversion H5. apply H4... apply H...
  * assert (wf_typ E T) by (apply wf_typ_from_binds_sub with (x := X); eauto*).
    specialize (IHHC WE H0)...
  * constructor; unfold allbound_typ; intros; fsetdec.
  * constructor; unfold allbound_typ; intros; fsetdec.
  * constructor; unfold allbound_typ; intros; fsetdec.
Qed.

Lemma typing_regular : forall E e T,
  typing E e T ->
  wf_env E /\ expr e /\ wf_typ E T.
Proof with simpl_env; auto*.
  intros E e T H. induction H...
  (* typing rule: x : T \in E --> E |- x : {x} T *)
  - repeat split...
    constructor...
    + apply wf_typ_from_binds_typ with (x := x)...
    + constructor...
      unfold allbound_typ. intros. assert (x0 = x) by fsetdec. subst; eauto.
  (* typing rule: (\x e) has type fv((\x e)) T1 -> T2 *)
  - pick fresh y; assert (y `notin` L) by fsetdec...
    specialize (H0 y H1) as H3; inversion H3 as [Henv [Hexpr Hwf]]...
    repeat split...
    (* wf_env *)
    + inversion Henv...
    (* expr *)
    + pick fresh x and apply expr_abs.
      * eauto using type_from_wf_typ, wf_typ_from_wf_env_typ.
      * destruct (H0 x)...
    (* wf_typ *)
    + constructor...
      pick fresh x and apply wf_typ_arrow...
      * eauto using type_from_wf_typ, wf_typ_from_wf_env_typ.
      * destruct (H0 x)...
      * (* Lemma here -- E |- e : T --> cv_free(e) \in E *)
        assert (typing E (exp_abs V e1) (typ_capt (free_for_cv e1) (typ_arrow V T1))).
        { apply typing_abs with (L := L). apply H. }
        apply typing_cv with (e := (exp_abs V e1)) (T := (typ_capt (free_for_cv e1) (typ_arrow V T1)))...
  (* typing rule: app *)
  - destruct IHtyping1 as [Hwf [Hexpr1 HwfF]].
    inversion HwfF...
    assert (wf_cset E C /\ wf_cset _ _) by (apply subcapt_regular; eauto*)...
    repeat split...
    constructor...
    repeat destruct H11...
    apply wf_typ_open_capt with (T1 := T1)...
  (* typing rule: (/\ X e) has type fv(/\ X e) X <: T1 -> T2 *)
  - pick fresh Y. assert (Y `notin` L) by fsetdec...
    specialize (H0 Y H1) as H3; inversion H3...
    repeat split...
    (* wf_env *)
    + inversion H2...
    (* expr *)
    + econstructor...
      * apply type_from_wf_typ with (E := E).
        apply wf_typ_from_wf_env_sub with (x := Y)...
      * instantiate (1 := L). intros...
        specialize (H0 X H5) as H8...
    (* wf_typ *)
    + constructor...
      pick fresh X and apply wf_typ_all...
      * eauto using type_from_wf_typ, wf_typ_from_wf_env_sub.
      * destruct (H0 X)...
      * (* Lemma here -- E |- e : T --> cv_free(e) \in E *)
        assert (typing E (exp_tabs V e1) (typ_capt (free_for_cv e1) (typ_all V T1))).
        { apply typing_tabs with (L := L). apply H. }
        apply typing_cv with (e := (exp_tabs V e1)) (T := (typ_capt (free_for_cv e1) (typ_all V T1)))...
  (* typing rule: t-app *)
  - repeat split...
    constructor...
    pose proof (sub_regular E T T1 H0).
    apply type_from_wf_typ with (E := E)...
    destruct (sub_regular _ _ _ H0) as [R1 [R2 R3]].
    apply wf_typ_open with (T1 := T1)...
    inversion IHtyping as [Henv [Hexpr Hwf_capt]].
    inversion Hwf_capt; subst...
  - repeat split...
    pose proof (sub_regular E S T H0)...
Qed.

Lemma value_regular : forall e,
  value e ->
  expr e.
Proof.
  intros e H. induction H; auto.
Qed.

Lemma red_regular : forall e e',
  red e e' ->
  expr e /\ expr e'.
Proof with auto*.
  intros e e' H.
  induction H; assert(J := value_regular); split...
  - Case "red_abs".
    inversion H. pick fresh y. rewrite (subst_ee_intro y)...
  - Case "red_tabs".
    inversion H. pick fresh Y. rewrite (subst_te_intro Y)...
Qed.


(* *********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

(** The lemma [ok_from_wf_env] was already added above as a hint since it
    helps blur the distinction between [wf_env] and [ok] in proofs.

    As currently stated, the regularity lemmas are ill-suited to be
    used with [auto] and [eauto] since they end in conjunctions.  Even
    if we were, for example, to split [sub_regularity] into three
    separate lemmas, the resulting lemmas would be usable only by
    [eauto] and there is no guarantee that [eauto] would be able to
    find proofs effectively.  Thus, the hints below apply the
    regularity lemmas and [type_from_wf_typ] to discharge goals about
    local closure and well-formedness, but in such a way as to
    minimize proof search.

    The first hint introduces an [wf_env] fact into the context.  It
    works well when combined with the lemmas relating [wf_env] and
    [wf_typ].  We choose to use those lemmas explicitly via [(auto
    using ...)] tactics rather than add them as hints.  When used this
    way, the explicitness makes the proof more informative rather than
    more cluttered (with useless details).

    The other three hints try outright to solve their respective
    goals. *)

Hint Extern 1 (wf_cset ?E) =>
  match goal with
  | H: subcapt _ _ _ |- _ => apply (proj1 (subcapt_regular _ _ _ H))
  end
: core.

Hint Extern 1 (wf_env ?E) =>
  match goal with
  | H: sub _ _ _ |- _ => apply (proj1 (sub_regular _ _ _ H))
  | H: typing _ _ _ |- _ => apply (proj1 (typing_regular _ _ _ H))
  end
: core.

Hint Extern 1 (wf_typ ?E ?T) =>
  match goal with
  | H: typing E _ T |- _ => apply (proj2 (proj2 (typing_regular _ _ _ H)))
  | H: sub E T _ |- _ => apply (proj1 (proj2 (sub_regular _ _ _ H)))
  | H: sub E _ T |- _ => apply (proj2 (proj2 (sub_regular _ _ _ H)))
  end
: core.

Hint Extern 1 (type ?T) =>
  let go E := apply (type_from_wf_typ E); auto in
  match goal with
  | H: typing ?E _ T |- _ => go E
  | H: sub ?E T _ |- _ => go E
  | H: sub ?E _ T |- _ => go E
  | H: wf_typ ?E T |- _ => go E
  end
: core.

Hint Extern 1 (capt ?C) =>
  let go E := apply (capt_from_wf_cset E); auto in
  match goal with
  | H: subcapt ?E C _ |- _ => go E
  | H: subcapt ?E _ C |- _ => go E
  end
: core.

Hint Extern 1 (expr ?e) =>
  match goal with
  | H: typing _ ?e _ |- _ => apply (proj1 (proj2 (typing_regular _ _ _ H)))
  | H: red ?e _ |- _ => apply (proj1 (red_regular _ _ H))
  | H: red _ ?e |- _ => apply (proj2 (red_regular _ _ H))
  end
: core.
