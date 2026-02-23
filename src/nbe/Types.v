(** printing e⊢ #e&vdash;# *) (** printing ⦂ #&colon;# *)
(*begin hide*)
Require Import Categories PredomCore.
Require Import Coq.Vectors.Vector.
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

Definition LCtx (E : Env) := t LType E.

(** *Notation *)
Infix "⇥" := (FunTy) (at level 0, right associativity).
Notation "★" := (UnitTy) (at level 0, no associativity).

Notation "'[]'" := (nil LType) (at level 1, no associativity).
Notation "θ × Γ" := (@cons LType θ _ Γ) (at level 0, right associativity).

Reserved Notation "Γ 'v⊢' v ⦂ θ" (at level 201, no associativity).
Reserved Notation "Γ 'e⊢' e ⦂ θ" (at level 201, no associativity).

(** VER DE SIMPLIFICAR (YA QUE TODOS LOS TIPOS DE LAS VAR SON UNIT) *)
Definition lookupType  := 
fix nth_fix {E} (Γ : t LType E) (v : Var E) {struct Γ} : LType :=
match v in Var E' return t LType E' -> LType with
 |ZVAR _    => fun Γ' => caseS (fun _ _ => LType) (fun θ n t => θ) Γ'
 |SVAR _ v' => fun Γ' => (caseS (fun E' _ => Var E' -> LType)
                              (fun _ n Γ'' w => nth_fix Γ'' w) Γ') v'
end Γ.


(** SACAR TODO LO DE SEM DE JUICIOS DE TIPADO **)

(** *Definition 43: Typing rules *)
Inductive TypeJudgeV : forall (E : Env), LCtx E -> V E -> LType -> Type :=
| VarRule  : forall (E : Env) (Γ : LCtx E) (v : Var E),
             (Γ v⊢ (VAR v) ⦂ (lookupType Γ v))
| FunRule  : forall (E : Env) (Γ : LCtx E) (e : Expr E.+1) (θ' θ : LType),
             ((θ' × Γ) e⊢ e ⦂ θ) ->
             (Γ v⊢ λ e ⦂ (θ' ⇥ θ))
with TypeJudgeE : forall (E : Env), LCtx E -> Expr E -> LType -> Type :=
| ValRule : forall (E : Env) (Γ : LCtx E) (v : V E) (θ : LType),
                               (Γ v⊢ v ⦂ θ) -> (Γ e⊢ (VAL v) ⦂ θ)
| AppRule : forall (E : Env) (Γ : LCtx E) (v v' : V E) (θ θ' : LType),
                              (Γ v⊢ v ⦂ (θ' ⇥ θ)) -> (Γ v⊢ v' ⦂ θ') ->
                              (Γ e⊢ (v @ v') ⦂ θ)
where "Γ v⊢ v ⦂ θ" := (TypeJudgeV Γ v θ) and "Γ e⊢ e ⦂ θ" := (TypeJudgeE Γ e θ).

(** *Definition 44: Intrinsic semantics of types *)
(* Fixpoint SemType (θ : LType) : cpoType :=
  match θ with
  | θ ⇥ θ' => (SemType θ) -=> (SemType θ') _BOT
  | ★ => 
  end.

Definition SemBoolToNatRule : bool_cpoType =-> nat_cpoType
  := Fcont_app ((CURRY (@IfB one_cpoType nat_cpoType))
                 ((const one_cpoType 0), (const one_cpoType 1))) ().

Definition SemSubFunRule
           (θ0 θ0' θ1 θ1' : LType)
           (f : SemType θ0' =-> SemType θ0) (g : SemType θ1 =-> SemType θ1') :
  SemType (θ0 ⇥ θ1) =-> SemType (θ0' ⇥ θ1')
  := exp_fun (kleisli (eta << g) << ev << Id >< f).
Arguments SemSubFunRule [θ0 θ0' θ1 θ1'] _ _.

(** *Definition 45: Intrinsic semantics of Subtyping *)
Fixpoint SemTypeJudgeL (θ θ' : LType) (tjl : TypeJudgeL θ θ') :
    SemType θ =-> SemType θ' :=
  match tjl with
  | BoolToNatRule                  => B_to_N
  | ReflRule θ                     => Id (A:=SemType θ)
  | TransRule _ _ _ tjl' tjl''     => SemTypeJudgeL tjl'' << SemTypeJudgeL tjl'
  | SubPairRule _ _ _ _ tjl' tjl'' => SemTypeJudgeL tjl' >< SemTypeJudgeL tjl''
  | SubFunRule _ _ _ _ tjl' tjl''  => SemSubFunRule (SemTypeJudgeL tjl')
                                                   (SemTypeJudgeL tjl'')
  end
where "'t⟦' tjl '⟧l'" := (SemTypeJudgeL tjl).
Arguments SemTypeJudgeL [θ θ'] _.

Fixpoint SemCtx (E : Env) (Γ : LCtx E) : cpoType :=
  match Γ with
  | nil => One
  | cons θ _ Γ => SemCtx Γ * SemType θ
  end.

(** *Functions and Properties *)
Definition lookupV  := 
  fix nth_v {E} (Γ : LCtx E) (v : Var E) {struct Γ} :
    SemCtx Γ =-> SemType (lookupType Γ v) :=
    match v in Var E' return
          forall (Γ' : LCtx E'), SemCtx Γ' =-> SemType (lookupType Γ' v) with
    |ZVAR _    => fun Γ' => caseS (fun E' Γ'' =>
                                 SemCtx Γ'' =-> SemType (lookupType Γ'' (ZVAR _)))
                                (fun θ n t => pi2 (A:= SemCtx t)) Γ'
    |SVAR n v' => fun Γ' => (caseS (fun E' Γ'' => forall (w : Var E'),
                                    SemCtx Γ'' =->
                                           SemType (lookupType Γ'' (SVAR w))))
                                 (fun t n Γ''' w => nth_v Γ''' w << pi1) n Γ' v'
    end Γ.
   *)
