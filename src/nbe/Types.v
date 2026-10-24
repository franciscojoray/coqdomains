(** printing ⊢ #&vdash;# *) (** printing ⦂ #&colon;# *)
(*begin hide*)
Require Import Categories PredomCore.
Require Import Lang.
Require Import Program.
Require Import Utils.

(** new in 8.4! *)
Set Automatic Coercions Import.
Unset Automatic Introduction.
(** endof new in 8.4 *)

Set Implicit Arguments.
Unset Strict Implicit.

Require Import PredomLift.
(*end hide*)

(** *)
(*** Chapter 4: Extended Language Type System ***)
(** *)

(** *Definition 3.5: Types and contexts *)
Inductive LType :=
| FunTy  : LType -> LType -> LType
| UnitTy : LType
.

(* Contexts are plain lists; the context length is implicit. *)
Definition LCtx := list LType.

(** *Notation *)
Infix "⇥" := (FunTy) (at level 0, right associativity).
Notation "★" := (UnitTy) (at level 0, no associativity).

Notation "'[]'" := (nil LType) (at level 1, no associativity).
Notation "θ × Γ" := (cons θ Γ) (at level 0, right associativity).

Reserved Notation "Γ ⊢ t ⦂ θ" (at level 1, no associativity).

(* Lookup of the variable of de Bruijn index v (0 = freshest = head).
   Out-of-range indices fall back to UnitTy (total function). *)
Fixpoint lookupType (Γ : LCtx) (v : Var) {struct Γ} : LType :=
  match Γ with
  | nil => UnitTy
  | cons θ Γ' => match v with
                 | O => θ
                 | S v' => lookupType Γ' v'
                 end
  end.

Notation "Γ ∋ v" := (lookupType Γ v) (at level 1, no associativity).


(** SACAR TODO LO DE SEM DE JUICIOS DE TIPADO **)

(** *Definition 43: Typing rules *)
Inductive TypeJudge : LCtx -> Term -> LType -> Type :=
| VarRule  : forall (Γ : LCtx) (v : Var),
             v < length Γ ->
             (Γ ⊢ (VAR v) ⦂ (Γ ∋ v))
| FunRule  : forall (Γ : LCtx) (e : Term) (θ' θ : LType),
             ((θ' × Γ) ⊢ e ⦂ θ) ->
             (Γ ⊢ λ e ⦂ (θ' ⇥ θ))
| AppRule  : forall (Γ : LCtx) (t t' : Term) (θ θ' : LType),
             (Γ ⊢ t ⦂ (θ' ⇥ θ)) -> (Γ ⊢ t' ⦂ θ') ->
             (Γ ⊢ (t @ t') ⦂ θ)
where "Γ ⊢ t ⦂ θ" := (TypeJudge Γ t θ).

(** *Sanity checks *)
(* index 0 is the head (freshest); index 1 the second element *)
Compute ((cons ★ (cons (★ ⇥ ★) nil)) ∋ 1).

(* the identity abstraction is typable in the empty context *)
Example typing_id : (nil ⊢ λ (VAR 0) ⦂ (★ ⇥ ★)).
Proof. apply: FunRule. apply: VarRule. done. Qed.
