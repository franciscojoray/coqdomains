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
Require Import LogicalRel.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
(*end hide*)

(** *)
(*** Correctness of NbE (paper Thm 3) — statement ***)
(** *)

(* ISSUE-016b: `Correctness` is PROVED.  This is the `ρ_Γ` instance (via
   `nbe`); `t'` is the normal form read back from `nbe |Γ| t`.  No
   `0 < length Γ` hypothesis: `R 0` is the paper's `R_0` (ISSUE-022), so
   closed terms are covered. *)

(** *Correctness of NbE at the canonical environment (paper Thm 3) *)
Theorem Correctness :
  forall (Γ : LCtx) (t : Term) (θ : LType),
    (Γ ⊢ t ⦂ θ) ->
    exists t' : Term, nbe (length Γ) t =-= eta t' /\ Γ ⊢ t ≡ t' ⦂ θ.
Proof.
  move => Γ t θ Ht.
  case: (@Fundamental Γ t θ Ht Γ idSub (id_env (length Γ))
            (@SubRel_id Γ)) => d [Hden Hrel].
  rewrite subT_id in Hrel.
  case: (TermRel_reify Hrel nil) => t' [Hread HEq].
  simpl in HEq. rewrite wk_0 in HEq.
  exists t'. split => //.
  unfold nbe.
  apply Oeq_trans with (y := KLEISLI (R (length Γ)) (eta d)).
  - apply: KLEISLI_eq_arg. exact Hden.
  - rewrite (KLEISLI_etaVal (R (length Γ)) d). exact Hread.
Qed.
