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

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
(*end hide*)

(** *)
(*** Semantic types and semantic terms (paper Def. 4, simple-language instance) ***)
(** *)

(* Our domain `VInf` carries no type-level values (no `Ul`/`Fun X F`), so the
   paper's `Types ⊆ D` subset collapses: every simple type is a semantic type.
   This is recorded as a deviation from the paper in ISSUE-018. *)
Definition SemType (θ : LType) : Prop := True.

(** *Neutral values (paper §3, `Ne ⊆ D`) — ISSUE-020 *)

(* Variables `x_n` (encoded `inNat n`, a de Bruijn level) are neutral, and a
   neutral applied to *any* value is neutral again (`App k e`, encoded
   `inPair (Roll k, Roll e)`). *)
Inductive NeV : VInf -> Prop :=
| NeV_var : forall n : nat, NeV (inNat n)
| NeV_app : forall k e : VInf, NeV k -> NeV (inPair (Roll k, Roll e)).

(* neutrals are closed under semantic application: k · e = App k e *)
Lemma NeV_AppV : forall (k e : VInf),
    NeV k -> AppV (k, eta e) =-= eta (inPair (Roll k, Roll e)).
Proof.
  move => k e H. case: H => [n | k' e' _].
  - exact: AppV_nat.
  - exact: AppV_pair.
Qed.

Lemma NeV_AppOp : forall (E : Env) (d1 d2 : SemEnv E =-> VInf _BOT)
    (η : SemEnv E) (k e : VInf),
    d1 η =-= eta k -> d2 η =-= eta e -> NeV k ->
    AppOp d1 d2 η =-= eta (inPair (Roll k, Roll e)) /\
    NeV (inPair (Roll k, Roll e)).
Proof.
  move => E d1 d2 η k e H1 H2 Hk. split.
  - rewrite -> (AppOp_eval d2 H1). rewrite -> H2. exact: NeV_AppV.
  - exact: NeV_app.
Qed.

(* The semantic terms of type θ: a family of subsets of the (raw) value
   domain, by recursion on the meta-level type.
   - At `★` there are no constants: the values are exactly the neutrals.
   - At `θ1 ⇥ θ2` a value is either a semantic function `inFun f` (applied
     to a semantic argument it yields a semantic result — the paper's
     `d · e ∈ [F e]`, adapted to our untyped domain: `f` acts on `DInf` and
     the result is read back via `Val`/`Roll`), or a neutral (paper
     Lemma 6.1, `Ne ⊆ [X]`). *)
Fixpoint SemTm (θ : LType) (d : VInf) : Prop :=
  match θ with
  | UnitTy => NeV d
  | FunTy θ1 θ2 =>
      (exists f : DInf _BOT -=> DInf _BOT,
        d = inFun f /\
        (forall e : VInf, SemTm θ1 e ->
           exists w : VInf, f (eta (Roll e)) =-= Val (Roll w) /\ SemTm θ2 w))
      \/ NeV d
  end.

(* Pretty notation for semantic-term membership: `d ∈ ⟨θ⟩` (paper `[θ]`).
   Angle brackets avoid a clash with `⟦ t ⟧` (`SemT`). *)
Notation "d ∈ ⟨ θ ⟩" := (SemTm θ d) (at level 1, no associativity).

(* closure of the base type (paper Lemma 6, base-case fragment):
   every `inNat n` is a semantic normal form at any non-zero level. *)
Lemma SemTm_star_NfD : forall (E n : nat), NfD E.+1 (inNat n).
Proof.
  move => E n. exists (VAR (E - n)). split.
  - by rewrite -> R_roundtrip.
  - apply Nf_ne, Ne_var.
Qed.

(* paper Lemma 6.1: every neutral is a semantic term of every type *)
Lemma NeV_SemTm : forall (θ : LType) (d : VInf), NeV d -> SemTm θ d.
Proof. move => θ d H. case: θ => [θ1 θ2 | ] /=; [right | ]; exact: H. Qed.

(* unpacking / closure for the function type: a semantic function value is
   either a semantic function, which applied to a semantic argument yields a
   semantic result (the "β" behaviour), or a neutral. *)
Lemma SemTm_fun_elim : forall (θ1 θ2 : LType) (d e : VInf),
    d ∈ ⟨ (θ1 ⇥ θ2) ⟩ -> e ∈ ⟨ θ1 ⟩ ->
    (exists f : DInf _BOT -=> DInf _BOT,
      d = inFun f /\
      exists w : VInf, f (eta (Roll e)) =-= Val (Roll w) /\ w ∈ ⟨ θ2 ⟩)
    \/ NeV d.
Proof.
  move => θ1 θ2 d e [[f [Hd Hf]] | Hne] He.
  - left. exists f. split => //. exact (Hf e He).
  - by right.
Qed.
