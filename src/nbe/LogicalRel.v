(*begin hide*)

Require Import Utils.
Require Import Program.
Require Import Lang.

(** new in 8.4! *)
Set Automatic Coercions Import.
Unset Automatic Introduction.
(** endof new in 8.4 *)

Require Import DomainStuff.
Require Import PredomAll.
Require Import PredomProd.
Require Import Domains.
Require Import ExSem.
Require Import Types.
Require Import TypedNbE.
Require Import Validity.
Require Import TypedEq.
Require Import NbE.
Require Import Weakening.
From Stdlib Require Import List.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
(*end hide*)

(** *)
(*** Logical relations (paper Defs 8–9, Thm 2) — statements ***)
(** *)

(* ISSUE-015a: the old environment-parametrised relation was false.  The
   relation below is the Kripke/readback-carrying version; the proofs are
   filled in by ISSUE-015d … 015f. *)

(** *Readback-carrying relation *)

Definition ReifRel (Gamma : LCtx) (t : Term) (d : VInf) (theta : LType) : Prop :=
  forall (Theta : LCtx),
    exists t' : Term,
      R (length Theta + length Gamma)%N d =-= eta t' /\
      (Theta ++ Gamma) ⊢ wk (length Theta) t ≡ t' ⦂ theta.

(** *Term relation (paper Def. 8) *)

Fixpoint TermRel (Gamma : LCtx) (t : Term) (d : VInf) (theta : LType) : Prop :=
  match theta with
  | UnitTy => ReifRel Gamma t d UnitTy
  | FunTy theta1 theta2 =>
      ReifRel Gamma t d (FunTy theta1 theta2) /\
      forall (Theta : LCtx) (s : Term) (a : VInf),
        @TermRel (Theta ++ Gamma) s a theta1 ->
        exists w : VInf,
          AppV (d, eta a) =-= eta w /\
          @TermRel (Theta ++ Gamma) (APP (wk (length Theta) t) s) w theta2
  end.

Arguments TermRel : clear implicits.

Notation "Gamma ⊩ t ∼ d ⦂ theta" := (TermRel Gamma t d theta)
  (at level 1, no associativity).

(** *Related substitutions (paper Def. 9) *)

Definition SubRel (Delta Gamma : LCtx) (sigma : Lang.Sub)
                  (rho : SemEnv (length Gamma)) : Prop :=
  forall (v : Var), (v < length Gamma)%N ->
    exists d : VInf,
      rho !! v =-= eta d /\
      @TermRel Delta (sigma v) d (Gamma ∋ v).

Arguments SubRel : clear implicits.

(** *Basic properties [ISSUE-015d] *)

Lemma TermRel_typed : forall (Gamma : LCtx) (t : Term) (d : VInf) (theta : LType),
    Gamma ⊩ t ∼ d ⦂ theta -> inhabited (Gamma ⊢ t ⦂ theta).
Proof. Admitted.

Lemma TermRel_reify : forall (Gamma : LCtx) (t : Term) (d : VInf) (theta : LType),
    Gamma ⊩ t ∼ d ⦂ theta -> ReifRel Gamma t d theta.
Proof. Admitted.

Lemma TermRel_eq : forall (Gamma : LCtx) (t t' : Term) (d : VInf) (theta : LType),
    Gamma ⊩ t ∼ d ⦂ theta ->
    Gamma ⊢ t ≡ t' ⦂ theta ->
    Gamma ⊩ t' ∼ d ⦂ theta.
Proof. Admitted.

Lemma TermRel_weaken : forall (Theta Gamma : LCtx) (t : Term) (d : VInf)
                              (theta : LType),
    Gamma ⊩ t ∼ d ⦂ theta ->
    (Theta ++ Gamma) ⊩ wk (length Theta) t ∼ d ⦂ theta.
Proof. Admitted.

(** *Reflection and the identity substitution [ISSUE-015e] *)

Lemma TermRel_reflect : forall (Gamma : LCtx) (t : Term) (d : VInf)
                               (theta : LType),
    NeV d -> ReifRel Gamma t d theta -> Gamma ⊩ t ∼ d ⦂ theta.
Proof. Admitted.

Lemma TermRel_var : forall (Gamma : LCtx) (v : Var),
    (v < length Gamma)%N ->
    Gamma ⊩ VAR v ∼ inNat (length Gamma - v.+1) ⦂ (Gamma ∋ v).
Proof. Admitted.

Lemma SubRel_weaken : forall (Theta Delta Gamma : LCtx) (sigma : Lang.Sub)
                             (rho : SemEnv (length Gamma)),
    SubRel Delta Gamma sigma rho ->
    SubRel (Theta ++ Delta) Gamma (fun n => wk (length Theta) (sigma n)) rho.
Proof. Admitted.

Lemma SubRel_ext : forall (Delta Gamma : LCtx) (sigma : Lang.Sub)
                          (rho : SemEnv (length Gamma)) (s : Term) (a : VInf)
                          (theta : LType),
    SubRel Delta Gamma sigma rho ->
    Delta ⊩ s ∼ a ⦂ theta ->
    SubRel Delta (theta × Gamma) (consMap s sigma) (rho, eta a).
Proof. Admitted.

Lemma SubRel_id : forall (Gamma : LCtx),
    SubRel Gamma Gamma idSub (id_env (length Gamma)).
Proof. Admitted.

(** *Fundamental theorem (paper Thm 2) [ISSUE-015f] *)

Theorem Fundamental : forall (Gamma : LCtx) (t : Term) (theta : LType),
    (Gamma ⊢ t ⦂ theta) ->
    forall (Delta : LCtx) (sigma : Lang.Sub) (rho : SemEnv (length Gamma)),
      SubRel Delta Gamma sigma rho ->
      exists d : VInf,
        ⟦ t ⟧ rho =-= eta d /\
        Delta ⊩ subT sigma t ∼ d ⦂ theta.
Proof. Admitted.
