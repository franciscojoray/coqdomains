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

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
(*end hide*)

(** *)
(*** Logical relations (paper Defs 8–9, Thm 2) — statements ***)
(** *)

(* ADMITTED sentences in this module (filled in by ISSUE-015b):
     - TermRel_readback
     - Fundamental

   The relations are stated *relative to a valid environment* `η` (the
   "option 1" of the roadmap discussion): this is the paper's general form and
   avoids the canonical-environment (`ρ_Γ`) gap, which is ISSUE-020.  The `ρ_Γ`
   specialisation is kept commented out at the bottom of this file.

   The paper's weakening/monotonicity lemmas (Lemmas 9, 15) use syntactic
   substitutions `tπ`, which are out of scope for the simple language (see
   ISSUE-009); they are therefore omitted here. *)

(** *Type relation *)

(* The type relation is trivial: `SemType θ = True` for every simple type
   (there are no type-level values in `VInf`).  Recorded as a deviation from
   the paper in ISSUE-018. *)
Definition TypeRel (Γ : LCtx) (θ : LType) : Prop := SemType θ.

(** *Term relation *)

(* Term relation  Γ ⊢ t ∼ d ∈ [θ]  (paper Def. 8, simple-language fragment),
   relative to a valid environment `η`:
   - at `★`: `t` denotes `d` and is equal (in `EqTm`) to the readback of `d`;
   - at `θ1 ⇥ θ2`: `t` denotes `d`, `d` is a semantic function `f`, and the
     applicative closure holds on related arguments.

   The paper's *neutral* branch of the function clause (used to read variables
   back at higher types) is deferred to ISSUE-020. *)
Fixpoint TermRel (Γ : LCtx) (η : SemEnv (length Γ))
                 (t : Term) (d : VInf) (θ : LType) : Prop :=
  match θ with
  | UnitTy =>
      ⟦ t ⟧ η =-= eta d /\
      (exists t' : Term, R (length Γ) d =-= eta t' /\ EqTm Γ t t' UnitTy)
  | FunTy θ1 θ2 =>
      ⟦ t ⟧ η =-= eta d /\
      (exists f : DInf _BOT -=> DInf _BOT,
         d = inFun f /\
         (forall (s : Term) (e : VInf), @TermRel Γ η s e θ1 ->
            exists w : VInf,
              f (eta (Roll e)) =-= Val (Roll w) /\ @TermRel Γ η (APP t s) w θ2))
  end.

Arguments TermRel : clear implicits.

(* Pretty notation for the term relation (paper `Γ ⊢ t ∼ d ∈ [X]`).  The
   environment `η` is shown explicitly, since our relation is env-parametrised.
   We use `⊩` (not `⊢`) and `⦂` (not `∈ ⟨·⟩`) to avoid collisions with the
   typing/equality notations and with `SemTm`'s `d ∈ ⟨θ⟩`. *)
Notation "Γ ; η ⊩ t ∼ d ⦂ θ" := (TermRel Γ η t d θ)
  (at level 1, no associativity).

(** *Readback of related terms (paper Lemma 11.2) *)

(* ADMITTED — the function-type case is expected to need ISSUE-020 (the
   neutral branch).  The `0 < length Γ` hypothesis is a leftover from the old
   `R 0 = ⊥` stub (fixed by ISSUE-022); it is dropped when this sentence is
   restated (ISSUE-015a). *)
Lemma TermRel_readback :
  forall (Γ : LCtx) (η : SemEnv (length Γ)) (t : Term) (d : VInf) (θ : LType),
    0 < length Γ -> Γ ; η ⊩ t ∼ d ⦂ θ ->
    exists t' : Term, R (length Γ) d =-= eta t' /\ Γ ⊢ t ≡ t' ⦂ θ.
Proof. Admitted.

(** *Fundamental theorem of logical relations (paper Thm 2) *)

(* ADMITTED — proof deferred to ISSUE-015b.  Env-parametrised form: every
   well-typed term is logically related to its denotation. *)
Theorem Fundamental :
  forall (Γ : LCtx) (t : Term) (θ : LType),
    (Γ ⊢ t ⦂ θ) -> 0 < length Γ ->
    forall (η : SemEnv (length Γ)), Γ ⊨ η ->
      exists d : VInf, Γ ; η ⊩ t ∼ d ⦂ θ.
Proof. Admitted.

(* REMOVED (kept commented, pending ISSUE-020): the `ρ_Γ` specialisation of the
   fundamental theorem uses the canonical environment, whose validity
   (`SemCtx_id_env`) is false in the present encoding.  Restore it together
   with `SemCtx_id_env` once `VInf` gains neutral values:

Theorem Fundamental_id_env :
  forall (Γ : LCtx) (t : Term) (θ : LType),
    (Γ ⊢ t ⦂ θ) -> 0 < length Γ ->
    exists d : VInf, Γ ; (id_env (length Γ)) ⊩ t ∼ d ⦂ θ.
Proof. Admitted.
*)
