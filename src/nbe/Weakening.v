(*begin hide*)

Require Import Utils.
Require Import Program.
Require Import Lang.

(** new in 8.4! *)
Set Automatic Coercions Import.
Unset Automatic Introduction.
(** endof new in 8.4 *)

Require Import Types.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
(*end hide*)

(** *)
(*** Renamings and substitutions on typed terms (ISSUE-021) ***)
(** *)

(* Step A: typing is stable under (typed) renamings.
   Step B: typing is stable under (typed) substitutions.
   Step C (syntax part): renaming as substitution; β-commutation.
   Step E: scoping (free variables below the context length).  The syntax side —
   `renT`, `liftRen`, `composeRen`, `applyComposeRen` — lives in `Lang.v`;
   here we only relate it to the typing judgement `Γ ⊢ t ⦂ θ`. *)

(** *Typed renamings *)

(* `π : Δ ≤ Γ`: every in-scope variable of `Γ` is sent to an in-scope
   variable of `Δ` carrying the same type. *)
Definition RenOK (Δ Γ : LCtx) (π : Ren) : Prop :=
  forall (v : Var), v < length Γ ->
    π v < length Δ /\ Δ ∋ (π v) = Γ ∋ v.

(* going under a binder *)
Lemma RenOK_lift : forall (θ : LType) (Δ Γ : LCtx) (π : Ren),
    RenOK Δ Γ π -> RenOK (θ × Δ) (θ × Γ) (liftRen π).
Proof.
  move => θ Δ Γ π H v. case: v => [ | v'] Hv.
  - by rewrite -> liftRen_O.
  - rewrite -> liftRen_S.
    case: (H v' Hv) => [Hlt Heq].
    by split.
Qed.

(* weakening ↑ : Γ is included in θ × Γ, shifting every index by one *)
Lemma RenOK_shift : forall (θ : LType) (Γ : LCtx),
    RenOK (θ × Γ) Γ (fun n => S n).
Proof. move => θ Γ v Hv. by split. Qed.

(* the identity renaming *)
Lemma RenOK_id : forall (Γ : LCtx), RenOK Γ Γ (idRen).
Proof. move => Γ v Hv. by split. Qed.

(** *Typing is stable under renaming *)

Lemma TypeJudge_ren : forall (Γ : LCtx) (t : Term) (θ : LType),
    (Γ ⊢ t ⦂ θ) ->
    forall (Δ : LCtx) (π : Ren), RenOK Δ Γ π -> (Δ ⊢ (renT π t) ⦂ θ).
Proof.
  move => Γ t θ H. elim: H.
  - (* VarRule *) move => Γ0 v Hv Δ π Hπ.
    case: (Hπ v Hv) => [Hlt Heq].
    unfold renT. rewrite -> mapVAR. cbn.
    rewrite <- Heq. by apply: VarRule.
  - (* FunRule *) move => Γ0 e θ' θ0 He IH Δ π Hπ.
    unfold renT. rewrite -> mapFUN.
    apply: FunRule.
    apply: (IH (θ' × Δ) (liftRen π)).
    exact: RenOK_lift.
  - (* AppRule *) move => Γ0 t1 t2 θ0 θ' H1 IH1 H2 IH2 Δ π Hπ.
    unfold renT. rewrite -> mapAPP.
    apply: AppRule.
    + exact: (IH1 Δ π Hπ).
    + exact: (IH2 Δ π Hπ).
Qed.

(* weakening by one fresh variable (paper `t p`) *)
Lemma TypeJudge_weaken : forall (θ' : LType) (Γ : LCtx) (t : Term) (θ : LType),
    (Γ ⊢ t ⦂ θ) -> ((θ' × Γ) ⊢ (renT (fun n => S n) t) ⦂ θ).
Proof.
  move => θ' Γ t θ H. apply: (TypeJudge_ren H). exact: RenOK_shift.
Qed.

(** *Typed substitutions (step B) *)

(* `σ : Δ → Γ`: every in-scope variable of `Γ` is sent to a term typed in
   `Δ` with the variable's type.  (`TypeJudge` lives in `Type`, so this is a
   `Type`-valued family too.) *)
Definition SubOK (Δ Γ : LCtx) (σ : Sub) : Type :=
  forall (v : Var), v < length Γ -> (Δ ⊢ (σ v) ⦂ (Γ ∋ v)).

(* going under a binder: the old terms are weakened, the new slot is VAR 0 *)
Lemma SubOK_lift : forall (θ : LType) (Δ Γ : LCtx) (σ : Sub),
    SubOK Δ Γ σ -> SubOK (θ × Δ) (θ × Γ) (liftSub σ).
Proof.
  move => θ Δ Γ σ H v. case: v => [ | v'] Hv.
  - rewrite -> liftSub_O. by apply: (@VarRule (θ × Δ) 0).
  - rewrite -> liftSub_S. apply: TypeJudge_weaken. exact: (H v' Hv).
Qed.

(* the identity substitution *)
Lemma SubOK_id : forall (Γ : LCtx), SubOK Γ Γ (idSub).
Proof. move => Γ v Hv. by apply: VarRule. Qed.

(* single substitution `e⟦r⟧ = subT (consMap r idSub) e` (the β-rule's) *)
Lemma SubOK_single : forall (θ' : LType) (Γ : LCtx) (r : Term),
    (Γ ⊢ r ⦂ θ') -> SubOK Γ (θ' × Γ) (consMap r (idSub)).
Proof.
  move => θ' Γ r Hr v. case: v => [ | v'] Hv.
  - exact Hr.
  - by apply: VarRule.
Qed.

(** *Typing is stable under substitution *)

Lemma TypeJudge_sub : forall (Γ : LCtx) (t : Term) (θ : LType),
    (Γ ⊢ t ⦂ θ) ->
    forall (Δ : LCtx) (σ : Sub), SubOK Δ Γ σ -> (Δ ⊢ (subT σ t) ⦂ θ).
Proof.
  move => Γ t θ H. elim: H.
  - (* VarRule *) move => Γ0 v Hv Δ σ Hσ.
    unfold subT. rewrite -> mapVAR. cbn.
    exact: (Hσ v Hv).
  - (* FunRule *) move => Γ0 e θ' θ0 He IH Δ σ Hσ.
    unfold subT. rewrite -> mapFUN.
    apply: FunRule.
    apply: (IH (θ' × Δ) (liftSub σ)).
    exact: SubOK_lift.
  - (* AppRule *) move => Γ0 t1 t2 θ0 θ' H1 IH1 H2 IH2 Δ σ Hσ.
    unfold subT. rewrite -> mapAPP.
    apply: AppRule.
    + exact: (IH1 Δ σ Hσ).
    + exact: (IH2 Δ σ Hσ).
Qed.

(* the β-rule's right-hand side is well typed (needed by `Eq_beta`) *)
Lemma TypeJudge_beta : forall (Γ : LCtx) (e r : Term) (θ' θ : LType),
    ((θ' × Γ) ⊢ e ⦂ θ) -> (Γ ⊢ r ⦂ θ') ->
    (Γ ⊢ (subT (consMap r (idSub)) e) ⦂ θ).
Proof.
  move => Γ e r θ' θ He Hr. apply: (TypeJudge_sub He).
  exact: SubOK_single.
Qed.

(** *Renaming as substitution, and β-commutation (step C, syntax part) *)

(* every renaming is the substitution of variables `VAR ∘ π` *)
Lemma renT_as_subT : forall (π : Ren) (t : Term),
    renT π t = subT (fun n => VAR (π n)) t.
Proof.
  move => π t.
  change (fun n => VAR (π n)) with (composeRen (idSub) π).
  unfold subT. rewrite -> (applyComposeRen t SubMapOps (idSub) π).
  symmetry. apply: (applyIdMap SubMapOps).
Qed.

(* a typed renaming gives a typed substitution *)
Lemma SubOK_ofRen : forall (Δ Γ : LCtx) (π : Ren),
    RenOK Δ Γ π -> SubOK Δ Γ (fun n => VAR (π n)).
Proof.
  move => Δ Γ π H v Hv. case: (H v Hv) => [Hlt Heq].
  rewrite <- Heq. by apply: VarRule.
Qed.

(* substitution commutes with the single substitution of the β-rule:
     (e⟦r⟧)σ = (e (σ↑))⟦r σ⟧                                              *)
Lemma subT_single_comm : forall (σ : Sub) (e r : Term),
    subT σ (subT (consMap r (idSub)) e) =
    subT (consMap (subT σ r) (idSub)) (subT (liftSub σ) e).
Proof.
  move => σ e r.
  rewrite <- !substComposeSub.
  rewrite -> composeCons. rewrite -> composeSubIdLeft.
  f_equal. apply: MapExtensional. move => n. case: n => [ | n']; reflexivity.
Qed.

(** *Scoping (step E) *)

(* `Scoped n t`: every free variable of `t` is below `n` (de Bruijn indices;
   going under a binder raises the bound).  Needed because the readback `R`
   reads variables with truncated subtraction (ISSUE-017b, `Lemma8_typed`). *)
Fixpoint Scoped (n : nat) (t : Term) : Prop :=
  match t with
  | VAR v     => v < n
  | FUN e     => Scoped n.+1 e
  | APP t1 t2 => Scoped n t1 /\ Scoped n t2
  end.

(* a well-typed term is scoped by the length of its context *)
Lemma TypeJudge_scoped : forall (Γ : LCtx) (t : Term) (θ : LType),
    (Γ ⊢ t ⦂ θ) -> Scoped (length Γ) t.
Proof.
  move => Γ t θ H. elim: H.
  - (* VarRule *) move => Γ0 v Hv. exact: Hv.
  - (* FunRule *) move => Γ0 e θ' θ0 _ IH. exact: IH.
  - (* AppRule *) move => Γ0 t1 t2 θ0 θ' _ IH1 _ IH2. by split.
Qed.

(* scoping is monotone in the bound *)
Lemma Scoped_mono : forall (t : Term) (n m : nat),
    n <= m -> Scoped n t -> Scoped m t.
Proof.
  move => t. elim: t => [v | e IH | t1 IH1 t2 IH2] n m Hnm /=.
  - move => Hv. exact: (leq_trans Hv Hnm).
  - apply: IH. by rewrite ltnS.
  - case => [H1 H2]. split; [exact: (IH1 n m Hnm H1) | exact: (IH2 n m Hnm H2)].
Qed.

(** *Sanity checks *)

(* weakening a variable shifts its index *)
Example weaken_var :
  ((★ ⇥ ★) × (★ × nil)) ⊢ (renT (fun n => S n) (VAR 0)) ⦂ ★.
Proof. apply: TypeJudge_weaken. by apply: VarRule. Qed.

Example weaken_var_computes : renT (fun n => S n) (VAR 0) = VAR 1.
Proof. reflexivity. Qed.

(* a closed abstraction is unaffected by weakening, and keeps its type *)
Example weaken_id :
  (★ × nil) ⊢ (renT (fun n => S n) (FUN (VAR 0))) ⦂ (★ ⇥ ★).
Proof. apply: TypeJudge_weaken. exact: typing_id. Qed.

Example weaken_id_computes : renT (fun n => S n) (FUN (VAR 0)) = FUN (VAR 0).
Proof. reflexivity. Qed.

(* β on an open term: substituting VAR 0 for the bound variable of the body
   VAR 1 (which refers to the outer variable) yields VAR 0, still at ★ *)
Example beta_var :
  (★ × nil) ⊢ (subT (consMap (VAR 0) (idSub)) (VAR 1)) ⦂ ★.
Proof.
  apply: (@TypeJudge_beta (★ × nil) (VAR 1) (VAR 0) ★ ★).
  - by apply: (@VarRule (★ × (★ × nil)) 1).
  - by apply: (@VarRule (★ × nil) 0).
Qed.

Example beta_var_computes : subT (consMap (VAR 0) (idSub)) (VAR 1) = VAR 0.
Proof. reflexivity. Qed.

(* λ.1 has one free variable (index 0 outside the binder) *)
Example scoped_fun1 : Scoped 1 (FUN (VAR 1)).
Proof. reflexivity. Qed.

Example not_scoped_var0 : ~ Scoped 0 (VAR 0).
Proof. done. Qed.
