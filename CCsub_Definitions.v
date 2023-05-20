Require Export TaktikZ.
Require Export Metatheory.
Require Export CaptureSets.
Require Import Coq.Program.Wf.

Notation "* ∈ C" := (`* in` C) (at level 80, no associativity).
Notation "x '∈' L" := (x `in` L) (at level 80, no associativity).
Notation "x '∉' L" := (x `notin` L) (at level 80, no associativity).
Notation "xs '⊆' ys" := (xs `subset` ys) (at level 80, no associativity).

Inductive typ : Type :=
  | typ_var : var -> typ
  | typ_top : typ
  | typ_arr : typ -> typ -> typ
  | typ_all : typ -> typ -> typ
  | typ_box : typ -> typ
  | typ_capt : cap -> typ -> typ.

Coercion typ_var : var >-> typ.
Notation "'⊤'" := typ_top (at level 80, no associativity).
Notation "'∀' '(' S ')' T" := (typ_arr S T) (at level 60, S at next level, T at next level, right associativity).
Notation "'∀' '[' R ']' T" := (typ_all R T) (at level 60, R at next level, T at next level, right associativity).
Notation "'□' T" := (typ_box T) (at level 70, no associativity).
Notation "C '#' R" := (typ_capt C R) (at level 65, R at next level, right associativity).

Inductive exp : Type :=
  | exp_var : var -> exp
  | exp_abs : typ -> exp -> exp
  | exp_app : var -> var -> exp
  | exp_let : exp -> exp -> exp
  | exp_tabs : typ -> exp -> exp
  | exp_tapp : var -> typ -> exp
  | exp_box : var -> exp
  | exp_unbox : cap -> var -> exp.

Coercion exp_var : var >-> exp.
Notation "'λ' '(' T ')' Γ" := (exp_abs T Γ) (at level 60, T at next level, Γ at next level, right associativity).
Notation "'Λ' '[' R ']' Γ" := (exp_tabs R Γ) (at level 60, R at next level, Γ at next level, right associativity).
Notation "x '@' y" := (exp_app x y) (at level 61, y at next level, left associativity).
Notation "'let=' e1 'in' e2" := (exp_let e1 e2) (at level 59, e1 at next level, e2 at next level, right associativity).
Notation "x  '@' '[' R ']'" := (exp_tapp x R) (at level 61, R at next level, left associativity).
Notation "'box' Γ" := (exp_box Γ) (at level 70, Γ at next level, no associativity).
Notation "C '⟜' x" := (exp_unbox  C x) (at level 60, x at next level, right associativity).

Definition var_cv (v : var) : cap :=
  match v with
  | var_b _ => {}
  | var_f x => `cset_fvar` x
  end.

Definition open_vt (K : nat) (U : typ) (v : var) : typ :=
  match v with
  | var_b J => if K === J then U else J
  | var_f X => X
  end.

Fixpoint open_tt_rec (K : nat) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | C # R => C # open_tt_rec K U R
  | typ_var v => open_vt K U v
  | ⊤ => ⊤
  | ∀ (T1) T2 => ∀ (open_tt_rec K U T1) (open_tt_rec (S K) U T2)
  | ∀ [T1] T2 => ∀ [open_tt_rec K U T1] (open_tt_rec (S K) U T2)
  | □ T => □ (open_tt_rec K U T)
  end.

Fixpoint open_te_rec (K : nat) (U : typ) (Γ : exp) {struct Γ} : exp :=
  match Γ with
  | exp_var v => exp_var v
  | λ (V) e1 => λ (open_tt_rec K U V) (open_te_rec (S K) U e1)
  | f @ x => exp_app f x
  | let= e1 in e2 => let= (open_te_rec K U e1) in (open_te_rec (S K) U e2)
  | Λ [V] e1 => Λ [open_tt_rec K U V] (open_te_rec (S K) U e1)
  | x @ [V] => x @ [open_tt_rec K U V]
  | box x => box x
  | C ⟜ x => C ⟜ x
  end.

Fixpoint open_ct_rec (k : nat) (c : cap) (T : typ)  {struct T} : typ :=
  match T with
  | typ_var v => v
  | C # R => open_cset k c C # open_ct_rec k c R
  | ⊤ => ⊤
  | ∀ (T1) T2 => ∀ (open_ct_rec k c T1) (open_ct_rec (S k) c T2)
  | ∀ [T1] T2 => ∀ [open_ct_rec k c T1] (open_ct_rec (S k) c T2)
  | □ T => □ (open_ct_rec k c T)
  end.

Definition open_vv (k : nat) (z : atom) (v : var) : var :=
  match v with
  | var_b i => if k === i then z else i
  | var_f x => x
  end.

Fixpoint open_ve_rec (k : nat) (z : atom) (c : cap) (Γ : exp)  {struct Γ} : exp :=
  match Γ with
  | exp_var v => open_vv k z v
  | λ (t) e1 => λ (open_ct_rec k c t) (open_ve_rec (S k) z c e1)
  | f @ x => open_vv k z f @ open_vv k z x
  | let= Γ in C => let= open_ve_rec k z c Γ in open_ve_rec (S k) z c C
  | Λ [t] e1 => exp_tabs (open_ct_rec k c t) (open_ve_rec (S k) z c e1)
  | x @ [t] => exp_tapp (open_vv k z x) (open_ct_rec k c t)
  | box x => box open_vv k z x
  | C ⟜ x => open_cset k (`cset_fvar` z) C ⟜ open_vv k z x
  end.

Definition open_tt T U := open_tt_rec 0 U T.
Definition open_te Γ U := open_te_rec 0 U Γ.
Definition open_ve Γ x c := open_ve_rec 0 x c Γ.
Definition open_ct T c := open_ct_rec 0 c T.

Fixpoint exp_cv (Γ : exp) : cap :=
  match Γ with
  | exp_var v => var_cv v
  | λ (t) e1 => exp_cv e1
  | f @ x => var_cv f `u` var_cv x
  | let= Γ in C => exp_cv Γ `u` exp_cv C
  | Λ [t] e1 => exp_cv e1
  | x @ [t] => var_cv x
  | box x => {}
  | C ⟜ x => cset_set (`cset_fvars` C) {}N (`cset_uvar` C) `u` var_cv x
  end.

Inductive type : typ -> Prop :=
  | type_pure : forall R,
      pure_type R ->
      type R
  | type_capt : forall C R,
      capt C ->
      pure_type R ->
      type (C # R)
with pure_type : typ -> Prop :=
  | type_var : forall X : atom,
      pure_type X
  | type_top : pure_type typ_top
  | type_arr : forall L S' T,
      type S' ->
      (forall X : atom, X ∉ L -> type (open_ct T (`cset_fvar` X))) ->
      pure_type (∀ (S') T)
  | type_all : forall L R T,
      pure_type R ->
      (forall X : atom, X ∉ L -> type (open_tt T X)) ->
      pure_type (∀ [R] T)
  | type_box : forall T,
      type T ->
      pure_type (□ T).

Inductive expr : exp -> Prop :=
  | expr_var : forall (x : atom),
      expr x
  | expr_abs : forall L T e1,
      type T ->
      (forall x : atom, x ∉ L -> expr (open_ve e1 x (`cset_fvar` x))) ->
      expr (λ (T) e1)
  | expr_app : forall (f x : atom),
      expr (f @ x)
  | expr_let : forall L e1 e2,
      expr e1 ->
      (forall x : atom, x ∉ L -> expr (open_ve e2 x (`cset_fvar` x))) ->
      expr (let= e1 in e2)
  | expr_tabs : forall L R e1,
      pure_type R ->
      (forall X : atom, X ∉ L -> expr (open_te e1 X)) ->
      expr (Λ [R] e1)
  | expr_tapp : forall (x : atom) R,
      pure_type R ->
      expr (x @ [R])
  | expr_box : forall x : atom,
      expr (box x)
  | expr_unbox : forall C (x : atom),
      capt C ->
      expr (C ⟜ x).

Inductive binding : Type :=
  | bind_sub : typ -> binding
  | bind_typ : typ -> binding.

Notation env := (list (atom * binding)).
Notation "∅" := (@nil (atom * binding)).

Notation "[ x ]" := (x :: nil).

Definition allbound (Γ : env) (fvars : atoms) : Prop :=
  forall x,
    x `in`A fvars ->
    exists C R, binds x (bind_typ (C # R)) Γ.

Reserved Notation "Γ '⊢ₛ' C 'wf'" (at level 40, C at next level, no associativity).

Inductive wf_cset (Γ : env) : cap -> Prop :=
  | wf_concrete_cset : forall fvars univ,
    allbound Γ fvars ->
    wf_cset Γ (cset_set fvars {}N univ)
where "Γ '⊢ₛ' C 'wf'" := (wf_cset Γ C).

Reserved Notation "Γ '⊢' T 'wf'" (at level 40, T at next level, no associativity).

Inductive wf_typ : env -> typ -> Prop :=
  | wf_typ_var : forall Γ X T,
      binds X (bind_sub T) Γ ->
      Γ ⊢ X wf
  | wf_typ_top : forall Γ,
      Γ ⊢ ⊤ wf
  | wf_typ_arr : forall L Γ C R T,
      Γ ⊢ (C # R) wf ->
      (forall x : atom, x ∉ L -> ([(x, bind_typ (C # R))] ++ Γ) ⊢ (open_ct T (`cset_fvar` x)) wf) ->
      Γ ⊢ ∀ (C # R) T wf
  | wf_typ_all : forall L Γ R T,
      Γ ⊢ R wf ->
      pure_type R ->
      (forall X : atom, X ∉ L -> ([(X, bind_sub R)] ++ Γ) ⊢ (open_tt T X) wf) ->
      Γ ⊢ ∀ [R] T wf
  | wf_typ_box : forall Γ T,
      Γ ⊢ T wf ->
      Γ ⊢ □ T wf
  | wf_typ_capt : forall Γ C R,
      Γ ⊢ₛ C wf ->
      Γ ⊢ R wf ->
      pure_type R ->
      Γ ⊢ C # R wf
where "Γ '⊢' T 'wf'" := (wf_typ Γ T).

Reserved Notation "Γ '⊢' 'wf'" (at level 40, no associativity).
Reserved Notation "Γ '⊢ₛ' C1 '<:' C2" (at level 40, C1 at next level, C2 at next level, no associativity). 
Reserved Notation "Γ '⊢' T1 '<:' T2" (at level 40, T1 at next level, T2 at next level, no associativity).
Reserved Notation "Γ '⊢' e ':' T" (at level 40, e at next level, T at next level, no associativity).
Reserved Notation "S '∷' Γ" (at level 40, Γ at next level, no associativity).
Reserved Notation "Γ '⊢' E ':' S '⇒' T" (at level 40, E at next level, S at next level, T at next level, no associativity).
Reserved Notation "Σ1 '-->' Σ2" (at level 40, Σ2 at next level, no associativity).

Inductive wf_env : env -> Prop :=
  | wf_env_empty :
      ∅ ⊢ wf
  | wf_env_sub : forall (Γ : env) (X : atom) (T : typ),
      Γ ⊢ wf ->
      Γ ⊢ T wf ->
      pure_type T ->
      X ∉ dom Γ ->
      ([(X, bind_sub T)] ++ Γ) ⊢ wf
  | wf_env_typ : forall (Γ : env) (x : atom) (C : cap) (R : typ),
      Γ ⊢ wf ->
      Γ ⊢ (C # R) wf ->
      x ∉ dom Γ ->
      ([(x, bind_typ (C # R))] ++ Γ) ⊢ wf
where "Γ '⊢' 'wf'" := (wf_env Γ).

Inductive subcapt : env -> cap -> cap -> Prop :=
  | subcapt_universal : forall Γ C xs,
      Γ ⊢ₛ cset_set xs {}N true wf ->
      Γ ⊢ₛ C wf ->
      Γ ⊢ₛ C <: cset_set xs {}N true
  | subcapt_in : forall Γ x xs b,
      Γ ⊢ₛ `cset_fvar` x wf ->
      Γ ⊢ₛ cset_set xs {}N b wf ->
      x ∈ xs ->
      Γ ⊢ₛ `cset_fvar` x <: cset_set xs {}N b
  | subcapt_in_univ : forall Γ D,
      Γ ⊢ₛ D wf ->
      * ∈ D ->
      Γ ⊢ₛ {*} <: D
  | subcapt_var : forall Γ x C1 R C2,
      binds x (bind_typ (C1 # R)) Γ ->
      Γ ⊢ₛ C1 <: C2 ->
      Γ ⊢ₛ `cset_fvar` x <: C2
  | subcapt_set : forall Γ xs b D,
      Γ ⊢ₛ D wf ->
      AtomSet.F.For_all (fun x => Γ ⊢ₛ `cset_fvar` x <: D) xs ->
      implb b (`* mem` D) = true ->
      Γ ⊢ₛ cset_set xs {}N b <: D
where "Γ '⊢ₛ' C1 <: C2" := (subcapt Γ C1 C2).

Inductive sub : env -> typ -> typ -> Prop :=
  | sub_refl_tvar : forall Γ (X : atom),
      Γ ⊢ wf ->
      Γ ⊢ X wf ->
      Γ ⊢ X <: X
  | sub_trans_tvar : forall U Γ T X,
      binds X (bind_sub U) Γ ->
      Γ ⊢ U <: T ->
      Γ ⊢ X <: T
  | sub_capt : forall Γ C1 C2 R1 R2,
      Γ ⊢ₛ C1 <: C2 ->
      Γ ⊢ R1 <: R2 ->
      pure_type R1 ->
      pure_type R2 ->
      Γ ⊢ (C1 # R1) <: (C2 # R2)
  | sub_top : forall Γ T,
      Γ ⊢ wf ->
      Γ ⊢ T wf ->
      pure_type T ->
      Γ ⊢ T <: ⊤
  | sub_arr : forall L Γ C1 R1 C2 R2 T1 T2,
      Γ ⊢ R2 <: R1 ->
      pure_type R1 ->
      pure_type R2 ->
      Γ ⊢ₛ C2 <: C1 ->
      (forall x : atom, x ∉ L -> ([(x, bind_typ (C2 # R2))] ++ Γ) ⊢ open_ct T1 (`cset_fvar` x) <: open_ct T2 (`cset_fvar` x)) ->
      Γ ⊢ (∀ (C1 # R1) T1) <: (∀ (C2 # R2) T2)
  | sub_all : forall L Γ R1 R2 T1 T2,
      Γ ⊢ R2 <: R1 ->
      pure_type R1 ->
      pure_type R2 ->
      (forall X : atom, X ∉ L -> ([(X, bind_sub R2)] ++ Γ) ⊢ open_tt T1 X <: open_tt T2 X) ->
      Γ ⊢ (∀ [R1] T1) <: (∀ [R2] T2)
  | sub_box : forall Γ T1 T2,
      Γ ⊢ T1 <: T2 ->
      Γ ⊢ (□ T1) <: (□ T2)
where "Γ '⊢' T1 '<:' T2" := (sub Γ T1 T2).

Inductive typing : env -> exp -> typ -> Prop :=
  | typing_var : forall Γ x C R,
      Γ ⊢ wf ->
      binds x (bind_typ (C # R)) Γ ->
      Γ ⊢ x : (`cset_fvar` x # R)
  | typing_abs : forall L Γ C R e1 T1,
      Γ ⊢ (C # R) wf ->
      (forall x : atom, x ∉ L ->
        ([(x, bind_typ (C # R))] ++ Γ) ⊢ open_ve e1 x (`cset_fvar` x) : open_ct T1 (`cset_fvar` x)) ->
      Γ ⊢ (λ (C # R) e1) : (exp_cv e1 # ∀ (C # R) T1)
  | typing_app : forall D Q Γ (f x : atom) T C,
      Γ ⊢ f : (C # (∀ (D # Q) T)) ->
      Γ ⊢ x : (D # Q) ->
      Γ ⊢ (f @ x) : open_ct T (`cset_fvar` x)
  | typing_let : forall L C1 T1 T2 Γ e k,
      Γ ⊢ e : (C1 # T1) ->
      (forall x : atom, x ∉ L ->
        ([(x, bind_typ (C1 # T1))] ++ Γ) ⊢ open_ve k x (`cset_fvar` x) : T2) ->
      Γ ⊢ (let= e in k) : T2
  | typing_tabs : forall L Γ V e1 T1,
      Γ ⊢ V wf ->
      pure_type V ->
      (forall X : atom, X ∉ L ->
        ([(X, bind_sub V)] ++ Γ) ⊢ open_te e1 X : open_tt T1 X) ->
      Γ ⊢ (Λ [V] e1) : (exp_cv e1 # ∀ [V] T1)
  | typing_tapp : forall Γ (x : atom) P Q T C,
      Γ ⊢ x : (C # ∀ [Q] T) ->
      Γ ⊢ P <: Q ->
      Γ ⊢ (x @ [P]) : open_tt T P
  | typing_box : forall Γ (x : atom) C R,
      Γ ⊢ x : (C # R) ->
      `cset_fvars` C `subset` dom Γ ->
      Γ ⊢ (box x) : ({} # □ (C # R))
  | typing_unbox : forall Γ (x : atom) C R,
      Γ ⊢ x : ({} # □ (C # R)) ->
      Γ ⊢ₛ C wf ->
      Γ ⊢ (C ⟜ x) : (C # R)
  | typing_sub : forall S Γ e T,
      Γ ⊢ e : S ->
      Γ ⊢ S <: T ->
      Γ ⊢ e : T
where "Γ '⊢' e ':' T" := (typing Γ e T).

Inductive value : exp -> Prop :=
  | value_abs : forall T e1,
      expr (λ (T) e1) ->
      value (λ (T) e1)
  | value_tabs : forall T e1,
      expr (Λ [T] e1) ->
      value (Λ [T] e1)
  | value_box : forall e1,
      expr (box e1) ->
      value (box e1).

Inductive answer : exp -> Prop :=
  | answer_val : forall v,
      value v ->
      answer v
  | answer_var : forall (x : atom),
      answer x.

Inductive store_frame : Type :=
  | store (v : exp) : store_frame.

Definition store_ctx : Type := list (atom * store_frame).
Definition stores (S : store_ctx) (x : atom) (v : exp) : Prop :=
    binds x (store v) S.

Inductive scope (k : exp) : Type :=
  | mk_scope : forall L, (forall x, x ∉ L -> expr (open_ve k x (`cset_fvar` x))) -> scope k.

Definition eval_ctx : Type := (list exp).

Inductive state : Type :=
  | mk_state : store_ctx -> eval_ctx -> exp -> state.

Notation "⟨ S | E | Γ ⟩" := (mk_state S E Γ) (at level 1).

Inductive state_final : state -> Prop :=
  | final_state : forall S a,
      answer a ->
      state_final ⟨ S | nil | a ⟩.

Inductive store_typing : store_ctx -> env -> Prop :=
  | typing_store_nil : nil ∷ nil
  | typing_store_cons : forall x C R v S Γ,
      S ∷ Γ ->
      value v ->
      Γ ⊢ v : (C # R) ->
      x ∉ dom Γ ->
      ([(x, store v)] ++ S) ∷ ([(x, bind_typ (C # R))] ++ Γ)
where "S '∷' Γ" := (store_typing S Γ).

Inductive eval_typing (Γ : env) : eval_ctx -> typ -> typ -> Prop :=
  | typing_eval_nil : forall C1 R1 C2 R2,
      Γ ⊢ (C1 # R1) <: (C2 # R2) ->
      Γ ⊢ nil : (C1 # R1) ⇒ (C2 # R2)
  | typing_eval_cons : forall L k E C1 R1 C2 R2 C3 R3,
      scope k ->
      (forall x, x ∉ L ->
        ([(x, bind_typ (C1 # R1))] ++ Γ) ⊢ open_ve k x (`cset_fvar` x) : (C2 # R2)) ->
      Γ ⊢ E : (C2 # R2) ⇒ (C3 # R3) ->
      Γ ⊢ (k :: E) : (C1 # R1) ⇒ (C3 # R3)
where "Γ '⊢' E ':' T '⇒' U" := (eval_typing Γ E T U).

Inductive state_typing : state -> typ -> Prop :=
  | typing_state : forall S Γ E e C1 R1 C2 R2,
      S ∷ Γ ->
      Γ ⊢ E : (C1 # R1) ⇒ (C2 # R2) ->
      Γ ⊢ e : (C1 # R1) ->
      state_typing ⟨ S | E | e ⟩ (C2 # R2).

Inductive red : state -> state -> Prop :=
  | red_lift : forall x v k S K,
      value v ->
      x ∉ dom S ->
          ⟨ S | k :: K | v ⟩
      --> ⟨ [(x, store v)] ++ S | K | open_ve k x (`cset_fvar` x) ⟩
  | red_let_var : forall (x : atom) v k S K,
      stores S x v ->
          ⟨ S | k :: K | x ⟩
      --> ⟨ S | K | open_ve k x (`cset_fvar` x) ⟩
  | red_let_val : forall x v k S K,
      value v ->
      x ∉ dom S ->
          ⟨ S | K | let= v in k ⟩
      --> ⟨ [(x, store v )] ++ S | K | open_ve k x (`cset_fvar` x) ⟩
  | red_let_exp : forall e k (k_scope : scope k) S K,
          ⟨ S | K | let= e in k ⟩
      --> ⟨ S | k :: K | e ⟩
  | red_app : forall f x U e v S K,
      stores S f (λ (U) e) ->
      stores S x v ->
          ⟨ S | K | f @ x ⟩
      --> ⟨ S | K | open_ve e x (`cset_fvar` x) ⟩
  | red_tapp : forall x R U e S K,
      stores S x (Λ [U] e) ->
      pure_type R ->
          ⟨ S | K | x @ [R] ⟩
      --> ⟨ S | K | open_te e R ⟩
  | red_open : forall C x y S K,
      stores S x (box y) ->
          ⟨ S | K | C ⟜ x ⟩
      --> ⟨ S | K | y ⟩
where "Σ1 --> Σ2" := (red Σ1 Σ2).

Hint Constructors type pure_type expr wf_cset wf_typ wf_env value sub subcapt typing : core.
Hint Resolve sub_top sub_refl_tvar sub_arr sub_all sub_box : core.
Hint Resolve typing_var typing_app typing_tapp typing_box typing_unbox typing_sub : core.

Local Ltac cset_unfold_union0 :=
  match goal with
  | _ : _ |- context G [?C `u` (cset_set ?xs ?ns ?us)] =>
    match C with
    | cset_set _ _ _ =>
      rewrite cset_concrete_union
    | C =>
      let HA := match goal with
                | H : wf_cset _ C |- _ => H
                | _ =>
                  let H := fresh "WF" in
                  (* NOTE: avoid asserting (wf_cset _ _ C), it takes long to solve. *)
                  assert (wf_cset _ C) as HA by eauto; H
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
