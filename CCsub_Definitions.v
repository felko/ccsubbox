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

Definition typ_cv (T : typ) : cap :=
  match T with
  | typ_var v => var_cv v
  | C # R => C
  | ⊤ => {}
  | ∀ (S') T => {}
  | ∀ [R] T => {}
  | □ T => {}
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
  | C ⟜ x => open_cset K (typ_cv U) C ⟜ x
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
  | expr_tapp : forall (x : atom) V,
      type V ->
      expr (x @ [V])
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

Inductive bound (x : atom) (T : typ) (Γ : env) : Prop :=
  | bound_typ :
      binds x (bind_typ T) Γ ->
      bound x T Γ
  | bound_sub :
      binds x (bind_sub T) Γ ->
      bound x T Γ.

Definition allbound (Γ : env) (fvars : atoms) : Prop :=
  forall x,
    x `in`A fvars ->
    exists T, bound x T Γ.

Reserved Notation "Γ '⊢ₛ' C 'wf'" (at level 40, C at next level, no associativity).

Inductive wf_cset : env -> cap -> Prop :=
  | wf_concrete_cset : forall Γ fvars univ,
    allbound Γ fvars ->
    fvars `c`A dom Γ ->
    wf_cset Γ (cset_set fvars {}N univ)
where "Γ '⊢ₛ' C 'wf'" := (wf_cset Γ C).

Reserved Notation "Γ '⊢' T 'wf'" (at level 40, T at next level, no associativity).

Inductive wf_typ : env -> typ -> Prop :=
  | wf_typ_var : forall Γ X T,
      binds X (bind_sub T) Γ ->
      Γ ⊢ X wf
  | wf_typ_top : forall Γ,
      Γ ⊢ ⊤ wf
  | wf_typ_arr : forall L Γ S T,
      Γ ⊢ S wf ->
      (forall x : atom, x ∉ L -> ([(x, bind_typ S)] ++ Γ) ⊢ (open_ct T (`cset_fvar` x)) wf) ->
      Γ ⊢ ∀ (S) T wf
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
      X ∉ dom Γ ->
      ([(X, bind_sub T)] ++ Γ) ⊢ wf
  | wf_env_typ : forall (Γ : env) (x : atom) (T : typ),
      Γ ⊢ wf ->
      Γ ⊢ T wf ->
      x ∉ dom Γ ->
      ([(x, bind_typ T)] ++ Γ) ⊢ wf
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
  | subcapt_var : forall Γ x T C,
      binds x (bind_typ T) Γ ->
      Γ ⊢ₛ typ_cv T <: C ->
      Γ ⊢ₛ `cset_fvar` x <: C
  | subcapt_tvar : forall Γ x T C,
      binds x (bind_sub T) Γ ->
      Γ ⊢ₛ typ_cv T <: C ->
      Γ ⊢ₛ `cset_fvar` x <: C
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
      Γ ⊢ ({} # X) <: T
  | sub_capt : forall Γ C1 C2 R1 R2,
      Γ ⊢ₛ C1 <: C2 ->
      Γ ⊢ R1 <: R2 ->
      Γ ⊢ (C1 # R1) <: (C2 # R2)
  | sub_top : forall Γ T,
      Γ ⊢ wf ->
      Γ ⊢ T wf ->
      Γ ⊢ T <: ⊤
  | sub_arr : forall L Γ S1 S2 T1 T2,
      Γ ⊢ S2 <: S1 ->
      (forall x : atom, x ∉ L -> ([(x, bind_typ S1)] ++ Γ) ⊢ open_ct T1 (`cset_fvar` x) <: open_ct T2 (`cset_fvar` x)) ->
      Γ ⊢ (∀ (S1) T1) <: (∀ (S2) T2)
  | sub_all : forall L Γ R1 R2 T1 T2,
      Γ ⊢ R2 <: R1 ->
      (forall X : atom, X ∉ L -> ([(X, bind_sub R1)] ++ Γ) ⊢ open_tt T1 X <: open_tt T2 X) ->
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
  | typing_abs : forall L Γ V e1 T1,
      Γ ⊢ V wf ->
      (forall x : atom, x ∉ L ->
        ([(x, bind_typ V)] ++ Γ) ⊢ open_ve e1 x (`cset_fvar` x) : open_ct T1 (`cset_fvar` x)) ->
      Γ ⊢ (λ (V) e1) : (exp_cv e1 # ∀ (V) T1)
  | typing_app : forall T1 Γ (f x : atom) T2 C,
      Γ ⊢ f : (C # (∀ (T1) T2)) ->
      Γ ⊢ x : T1 ->
      Γ ⊢ (f @ x) : open_ct T2 (`cset_fvar` x)
  | typing_let : forall L T1 T2 Γ e k,
      Γ ⊢ e : T1 ->
      (forall x : atom, x ∉ L ->
        ([(x, bind_typ T1)] ++ Γ) ⊢ open_ve k x (`cset_fvar` x) : T2) ->
      Γ ⊢ (let= e in k) : T2
  | typing_tabs : forall L Γ V e1 T1,
      Γ ⊢ V wf ->
      (forall X : atom, X ∉ L ->
        ([(X, bind_sub V)] ++ Γ) ⊢ open_te e1 X : open_tt T1 X) ->
      Γ ⊢ (Λ [V] e1) : (exp_cv e1 # ∀ [V] T1)
  | typing_tapp : forall T1 Γ (x : atom) T T2 C,
      Γ ⊢ x : (C # ∀ [T1] T2) ->
      Γ ⊢ T <: T1 ->
      Γ ⊢ (x @ [T]) : open_tt T2 T
  | typing_box : forall Γ (x : atom) C R,
      Γ ⊢ x : (C # R) ->
      `cset_fvars` C `subset` dom Γ ->
      Γ ⊢ (box x) : (□ (C # R))
  | typing_unbox : forall Γ (x : atom) C R,
      Γ ⊢ x : (□ (C # R)) ->
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
      value (Λ [T] e1).

Inductive answer : exp -> Prop :=
  | answer_val : forall v,
      value v ->
      answer v
  | answer_var : forall (x : atom),
      answer x.

Inductive store_frame : Type :=
  | store v : value v -> store_frame.

Definition store_ctx : Type := list (atom * store_frame).
Definition stores (S : store_ctx) (x : atom) (v : exp) (v_value : value v) : Prop :=
    binds x (store v v_value) S.

Inductive scope (Γ : exp) : Type :=
  | mk_scope L : (forall x, x ∉ L -> expr (open_ve Γ x (`cset_fvar` x))) -> scope Γ.

Inductive eval_frame : Type :=
  | cont Γ : scope Γ -> eval_frame.

Definition eval_ctx : Type := (list eval_frame).

Inductive state : Type :=
  | mk_state : store_ctx -> eval_ctx -> exp -> state.

Notation "⟨ S | E | Γ ⟩" := (mk_state S E Γ) (at level 1).

Inductive state_final : state -> Prop :=
  | final_state : forall S a,
      answer a ->
      state_final ⟨ S | nil | a ⟩.

Inductive store_typing : store_ctx -> env -> Prop :=
  | typing_store_nil : nil ∷ nil
  | typing_store_cons : forall x T v v_value S Γ,
      S ∷ Γ ->
      Γ ⊢ v : T ->
      x ∉ dom Γ ->
      ([(x, store v v_value)] ++ S) ∷ ([(x, bind_typ T)] ++ Γ)
where "S '∷' Γ" := (store_typing S Γ).

Inductive eval_typing (Γ : env) : eval_ctx -> typ -> typ -> Prop :=
  | typing_eval_nil : forall T U,
      Γ ⊢ wf ->
      Γ ⊢ T <: U ->
      Γ ⊢ nil : T ⇒ U
  | typing_eval_cons : forall L k (k_scope : scope k) E T U V,
      (forall x, x ∉ L ->
        ([(x, bind_typ T)] ++ Γ) ⊢ open_ve k x (`cset_fvar` x) : U) ->
      Γ ⊢ E : U ⇒ V ->
      Γ ⊢ (cont k k_scope :: E) : T ⇒ V
where "Γ '⊢' E ':' T '⇒' U" := (eval_typing Γ E T U).

Inductive state_typing : state -> typ -> Prop :=
  | typing_state : forall S Γ E e T U,
      S ∷ Γ ->
      Γ ⊢ E : T ⇒ U ->
      Γ ⊢ e : T ->
      state_typing ⟨ S | E | e ⟩ U.

Inductive red : state -> state -> Prop :=
  | red_lift : forall x v (v_value : value v) k (k_scope : scope k) S K,
      x ∉ dom S ->
          ⟨ S | cont k k_scope :: K | v ⟩
      --> ⟨ [(x, store v v_value)] ++ S | K | open_ve k x (`cset_fvar` x) ⟩
  | red_let_var : forall (x : atom) v (v_value : value v) k (k_scope : scope k) S K,
      stores S x v v_value ->
          ⟨ S | cont k k_scope :: K | x ⟩
      --> ⟨ S | K | open_ve k x (`cset_fvar` x) ⟩
  | red_let_val : forall x v (v_value : value v) k (k_scope : scope k) S K,
      x ∉ dom S ->
          ⟨ S | K | let= v in k ⟩
      --> ⟨ [(x, store v v_value)] ++ S | K | open_ve k x (`cset_fvar` x) ⟩
  | red_let_exp : forall e k (k_scope : scope k) S K,
          ⟨ S | K | let= e in k ⟩
      --> ⟨ S | cont k k_scope :: K | e ⟩
  | red_app : forall f x U e v (v_value : value v) (abs_value : value (exp_abs U e)) S K,
      stores S f (λ (U) e) abs_value ->
      stores S x v v_value ->
          ⟨ S | K | f @ x ⟩
      --> ⟨ S | K | open_ve e x (`cset_fvar` x) ⟩
  | red_tapp : forall x R U e (tabs_value : value (Λ [U] e)) S K,
      stores S x (Λ [U] e) tabs_value ->
      pure_type R ->
          ⟨ S | K | x @ [R] ⟩
      --> ⟨ S | K | open_te e R ⟩
  | red_open : forall C x y (box_value : value (box y)) S K,
      stores S x (box y) box_value ->
          ⟨ S | K | C ⟜ x ⟩
      --> ⟨ S | K | y ⟩
where "Σ1 --> Σ2" := (red Σ1 Σ2).

Hint Constructors type pure_type expr bound wf_cset wf_typ wf_env value sub subcapt typing : core.
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

Local Lemma __test_cset_concrete_unfold : forall C xs us,
  wf_cset nil C ->
  wf_cset nil (C `u` (cset_set xs {}N us)) ->
  exists xs' us', wf_cset nil (cset_set (xs' `u`A xs) {}N (us' || us)).
Proof. intros * H; csetsimpl; eauto. Qed.
