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
Require Import LogicalRel.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
(*end hide*)

(** *)
(*** Correctness of NbE (paper Thm 3) — statement ***)
(** *)

(* ADMITTED sentence in this module (filled in by ISSUE-016b):
     - Correctness

   `Correctness_sem` below is *proved* from the two 015a sentences; the `ρ_Γ`
   statement `Correctness` uses `nbe` (hence the canonical environment) and is
   pending ISSUE-020. *)

(** *Semantic (env-parametrised) correctness *)

(* Every well-typed term is equal (in the typed equality judgement) to the
   readback of its value.  PROVED from `Fundamental` + `TermRel_readback`. *)
Lemma Correctness_sem :
  forall (Γ : LCtx) (t : Term) (θ : LType),
    (Γ ⊢ t ⦂ θ) -> 0 < length Γ ->
    forall (η : SemEnv (length Γ)), Γ ⊨ η ->
      exists t' : Term, Γ ⊢ t ≡ t' ⦂ θ.
Proof.
  move => Γ t θ Ht Hpos η Hη.
  case: (Fundamental Ht Hpos Hη) => d Hd.
  case: (TermRel_readback Hpos Hd) => t' [_ HE].
  by exists t'.
Qed.

(** *Correctness of NbE at the canonical environment (paper Thm 3) *)

(* ADMITTED — this is the `ρ_Γ` instance (via `nbe`); it is expected to need
   ISSUE-020 (`SemCtx_id_env`).  `t'` is the normal form read back from
   `nbe |Γ| t`.  No `0 < length Γ` hypothesis: `R 0` is the paper's `R_0`
   (ISSUE-022), so closed terms are covered. *)
Theorem Correctness :
  forall (Γ : LCtx) (t : Term) (θ : LType),
    (Γ ⊢ t ⦂ θ) ->
    exists t' : Term, nbe (length Γ) t =-= eta t' /\ Γ ⊢ t ≡ t' ⦂ θ.
Proof. Admitted.
