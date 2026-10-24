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
Require Import Weakening.
Require Import SemSubst.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
(*end hide*)

(** *)
(*** Typed-indexed equality judgements (paper Figs 2–3) — statements ***)
(** *)

(* ISSUE-014b: `EqTm_sound` is PROVED.  In the call-by-name model
   (ISSUE-023/024) its equation part holds in *every* environment — no
   validity hypothesis (the strict model refuted it, see ISSUE-023). *)

(* The single substitution `e[r]` used by the β-rule: replace the bound
   variable (index 0) by `r`, keep the rest.  Types are non-dependent, so no
   substitution in the type is needed. *)
Notation "e ⟦ r ⟧" := (subT (consMap r idSub) e) (at level 1, no associativity).

Reserved Notation "Γ ⊢ t ≡ t' ⦂ θ" (at level 1, no associativity).

(* We use `≡` rather than `=` because a literal `=` collides with Coq's
   built-in equality operator inside notations. *)
Inductive EqTm : LCtx -> Term -> Term -> LType -> Prop :=
| Eq_refl  : forall (Γ : LCtx) (t : Term) (θ : LType),
             (Γ ⊢ t ⦂ θ) -> Γ ⊢ t ≡ t ⦂ θ
| Eq_sym   : forall (Γ : LCtx) (t t' : Term) (θ : LType),
             Γ ⊢ t ≡ t' ⦂ θ -> Γ ⊢ t' ≡ t ⦂ θ
| Eq_trans : forall (Γ : LCtx) (t t' t'' : Term) (θ : LType),
             Γ ⊢ t ≡ t' ⦂ θ -> Γ ⊢ t' ≡ t'' ⦂ θ -> Γ ⊢ t ≡ t'' ⦂ θ
| Eq_xi    : forall (Γ : LCtx) (e e' : Term) (θ' θ : LType),
             (θ' × Γ) ⊢ e ≡ e' ⦂ θ -> Γ ⊢ (FUN e) ≡ (FUN e') ⦂ (θ' ⇥ θ)
| Eq_app   : forall (Γ : LCtx) (t1 t1' t2 t2' : Term) (θ' θ : LType),
             Γ ⊢ t1 ≡ t1' ⦂ (θ' ⇥ θ) -> Γ ⊢ t2 ≡ t2' ⦂ θ' ->
             Γ ⊢ (APP t1 t2) ≡ (APP t1' t2') ⦂ θ
| Eq_beta  : forall (Γ : LCtx) (e r : Term) (θ' θ : LType),
             ((θ' × Γ) ⊢ e ⦂ θ) -> (Γ ⊢ r ⦂ θ') ->
             Γ ⊢ (APP (FUN e) r) ≡ (e ⟦ r ⟧) ⦂ θ
where "Γ ⊢ t ≡ t' ⦂ θ" := (EqTm Γ t t' θ).

(** *Equality soundness (paper: equality is modelled by denotational equality) *)

(* equal terms are well typed (EqTm lives in Prop, TypeJudge in Type) *)
Lemma EqTm_typed : forall (Γ : LCtx) (t t' : Term) (θ : LType),
    Γ ⊢ t ≡ t' ⦂ θ -> inhabited (Γ ⊢ t ⦂ θ) /\ inhabited (Γ ⊢ t' ⦂ θ).
Proof.
  move => Γ t t' θ H. elim: H.
  - (* refl *) move => Γ0 t0 θ0 Ht. by split; constructor.
  - (* sym *) move => Γ0 t0 t0' θ0 _ [H1 H2]. by split.
  - (* trans *) move => Γ0 t0 t0' t0'' θ0 _ [H1 _] _ [_ H2]. by split.
  - (* xi *) move => Γ0 e e' θ' θ0 _ [[He] [He']].
    split; constructor; exact: FunRule.
  - (* app *) move => Γ0 t1 t1' t2 t2' θ' θ0 _ [[H1] [H1']] _ [[H2] [H2']].
    split; constructor; [exact: (AppRule H1 H2) | exact: (AppRule H1' H2')].
  - (* beta *) move => Γ0 e r θ' θ0 He Hr.
    split; constructor.
    + exact: (AppRule (FunRule He) Hr).
    + exact: (TypeJudge_beta He Hr).
Qed.

(* the equation part, in every environment (call-by-name) *)
Lemma EqTm_sem : forall (Γ : LCtx) (t t' : Term) (θ : LType),
    Γ ⊢ t ≡ t' ⦂ θ ->
    forall (η : SemEnv (length Γ)), ⟦ t ⟧ η =-= ⟦ t' ⟧ η.
Proof.
  move => Γ t t' θ H. elim: H.
  - (* refl *) move => Γ0 t0 θ0 _ η. exact: tset_refl.
  - (* sym *) move => Γ0 t0 t0' θ0 _ IH η. exact: (Oeq_sym (IH η)).
  - (* trans *) move => Γ0 t0 t0' t0'' θ0 _ IH1 _ IH2 η.
    exact: (Oeq_trans (IH1 η) (IH2 η)).
  - (* xi *) move => Γ0 e e' θ' θ0 _ IH η.
    apply: SemT_FUN_cong => d. exact: (IH (η, d)).
  - (* app *) move => Γ0 t1 t1' t2 t2' θ' θ0 _ IH1 _ IH2 η.
    apply: AppOp_cong; [exact: (IH1 η) | exact: (IH2 η)].
  - (* beta *) move => Γ0 e r θ' θ0 He Hr η.
    eapply Oeq_trans; first by exact: SemT_APP_FUN.
    apply: Oeq_sym. exact: (SemT_beta He Hr η).
Qed.

Theorem EqTm_sound : forall (Γ : LCtx) (t t' : Term) (θ : LType),
    Γ ⊢ t ≡ t' ⦂ θ ->
    Γ ⊨ t ⦂ θ /\ Γ ⊨ t' ⦂ θ /\
    (forall (η : SemEnv (length Γ)), ⟦ t ⟧ η =-= ⟦ t' ⟧ η).
Proof.
  move => Γ t t' θ H.
  case: (EqTm_typed H) => [[Ht] [Ht']].
  split; [exact: (TypeJudge_sound Ht) | split].
  - exact: (TypeJudge_sound Ht').
  - exact: (EqTm_sem H).
Qed.
