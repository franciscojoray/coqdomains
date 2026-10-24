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
Require Import Weakening.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
(*end hide*)

(** *)
(*** Typed equality under renaming and substitution (ISSUE-021, step C) ***)
(** *)

(* The β case rests on `subT_single_comm` (`Weakening.v`); renaming is
   obtained from substitution through `renT_as_subT` / `SubOK_ofRen`. *)

(** *Equality is stable under substitution *)

Lemma EqTm_sub : forall (Γ : LCtx) (t t' : Term) (θ : LType),
    Γ ⊢ t ≡ t' ⦂ θ ->
    forall (Δ : LCtx) (σ : Lang.Sub), SubOK Δ Γ σ ->
      Δ ⊢ (subT σ t) ≡ (subT σ t') ⦂ θ.
Proof.
  move => Γ t t' θ H. elim: H.
  - (* refl *) move => Γ0 t0 θ0 Ht Δ σ Hσ.
    apply: Eq_refl. exact: (TypeJudge_sub Ht Hσ).
  - (* sym *) move => Γ0 t0 t0' θ0 _ IH Δ σ Hσ.
    apply: Eq_sym. exact: (IH Δ σ Hσ).
  - (* trans *) move => Γ0 t0 t0' t0'' θ0 _ IH1 _ IH2 Δ σ Hσ.
    apply: Eq_trans; [ exact: (IH1 Δ σ Hσ) | exact: (IH2 Δ σ Hσ) ].
  - (* xi *) move => Γ0 e e' θ' θ0 _ IH Δ σ Hσ.
    unfold subT. rewrite -> !mapFUN.
    apply: Eq_xi.
    apply: (IH (θ' × Δ) (liftSub σ)).
    exact: SubOK_lift.
  - (* app *) move => Γ0 t1 t1' t2 t2' θ' θ0 _ IH1 _ IH2 Δ σ Hσ.
    unfold subT. rewrite -> !mapAPP.
    apply: Eq_app; [ exact: (IH1 Δ σ Hσ) | exact: (IH2 Δ σ Hσ) ].
  - (* beta *) move => Γ0 e r θ' θ0 He Hr Δ σ Hσ.
    rewrite -> subT_single_comm.
    have -> : subT σ (APP (FUN e) r) = APP (FUN (subT (liftSub σ) e)) (subT σ r)
      by reflexivity.
    apply: Eq_beta.
    + apply: (TypeJudge_sub He). exact: SubOK_lift.
    + exact: (TypeJudge_sub Hr Hσ).
Qed.

(** *Equality is stable under renaming (corollary) *)

Lemma EqTm_ren : forall (Γ : LCtx) (t t' : Term) (θ : LType),
    Γ ⊢ t ≡ t' ⦂ θ ->
    forall (Δ : LCtx) (π : Ren), RenOK Δ Γ π ->
      Δ ⊢ (renT π t) ≡ (renT π t') ⦂ θ.
Proof.
  move => Γ t t' θ H Δ π Hπ.
  rewrite -> !renT_as_subT.
  apply: (EqTm_sub H). exact: SubOK_ofRen.
Qed.

(* weakening by one fresh variable (paper `t p = t' p`) *)
Lemma EqTm_weaken : forall (θ' : LType) (Γ : LCtx) (t t' : Term) (θ : LType),
    Γ ⊢ t ≡ t' ⦂ θ ->
    (θ' × Γ) ⊢ (renT (fun n => S n) t) ≡ (renT (fun n => S n) t') ⦂ θ.
Proof.
  move => θ' Γ t t' θ H. apply: (EqTm_ren H). exact: RenOK_shift.
Qed.

(** *Sanity check *)

(* weakening a β-step: in context ★ × nil, (λ.0) 0 ≡ 0; after weakening by a
   fresh ★, the same equation holds with the outer variable shifted to 1 *)
Example weaken_beta :
  (★ × (★ × nil)) ⊢ (APP (FUN (VAR 0)) (VAR 1)) ≡ (VAR 1) ⦂ ★.
Proof.
  have H : (★ × nil) ⊢ (APP (FUN (VAR 0)) (VAR 0)) ≡ (VAR 0) ⦂ ★.
  { apply: (@Eq_beta (★ × nil) (VAR 0) (VAR 0) ★ ★).
    - by apply: (@VarRule (★ × (★ × nil)) 0).
    - by apply: (@VarRule (★ × nil) 0). }
  exact: (EqTm_weaken ★ H).
Qed.
