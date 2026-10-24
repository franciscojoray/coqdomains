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
Require Import Correctness.
Require Import Weakening.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
(*end hide*)

(** *)
(*** Completeness of NbE (paper Cor. 1, Lemma 8) ***)
(** *)

(* ISSUE-017b: all three sentences are PROVED.
     - Completeness  — closed (from `EqTm_sem` at `id_env`, CBN model)
     - Lemma8_typed  — closed (via `nf_readback`)
     - Reflection    — proved from `Correctness`, hence depends on it until
                       ISSUE-016b closes (`Print Assumptions` lists it)
   They carry no `0 < length Γ` hypothesis: `R 0` is the paper's `R_0`
   (ISSUE-022). *)

(** *Completeness (paper Cor. 1) *)

(* Equal terms normalise to equal normal forms. *)
Theorem Completeness :
  forall (Γ : LCtx) (t t' : Term) (θ : LType),
    Γ ⊢ t ≡ t' ⦂ θ ->
    nbe (length Γ) t =-= nbe (length Γ) t'.
Proof.
  move => Γ t t' θ H.
  unfold nbe. apply: KLEISLI_eq_arg.
  exact: (EqTm_sem H (id_env (length Γ))).
Qed.

(** *Readback of scoped normal forms at the canonical environment *)

Scheme Ne_mut := Induction for Ne Sort Prop
  with Nf_mut := Induction for Nf Sort Prop.
Combined Scheme NeNf_mut from Ne_mut, Nf_mut.

(* Readback of normal forms (the core of paper Lemma 8).

   Statement.  For every level `L` (number of variables in scope):
   - a scoped neutral `k` denotes, at the canonical environment `id_env L`,
     a *neutral* value `v` that reads back to `k`;
   - a scoped normal form `t` denotes a value `v` that reads back to `t`.
   The neutral half also records `NeV v`: the `Ne_app` case needs the head's
   value to be neutral, so that application builds `App` instead of β.

   Why generalise over `L`.  Going under a binder raises the level by one, so
   the induction hypothesis must hold at `L.+1`, not only at `|Γ|`.

   Why `Scoped L`.  `R L (inNat n) = VAR (L - n.+1)` uses truncated
   subtraction; the bound `n < L` is what makes it read back the right index
   (`subn_round`).  Typing provides it (`TypeJudge_scoped`).

   Proof, by mutual induction on `Ne`/`Nf` (`NeNf_mut`):
   - `Ne_var n` (n < L, so L = E.+1):
     `⟦VAR n⟧(id_env E.+1) = eta (inNat (E - n))` (`SemVar_id_env`), a
     neutral (`NeV_var`), and `R E.+1 (inNat (E - n)) = VAR (E - (E - n))
     = VAR n` (`R_roundtrip`, `subn_round`).
   - `Ne_app k v`: by the IHs, `k ↦ vk` (neutral) and `v ↦ vv`.  Applying a
     neutral gives `App vk vv = inPair (Roll vk, Roll vv)`, again neutral
     (`NeV_AppOp`), and it reads back to `APP k v` (`R_neutral_app`).
   - `Nf_fun e` (Scoped L (FUN e) = Scoped L.+1 e): `⟦FUN e⟧(id_env L)
     = eta (inFun f)` with `f = F ⟦e⟧ (id_env L)`.  Readback applies `f` to
     the fresh variable `eta (Roll (inNat L))` (`R_FUN`, `FunCase_eval`):
       f (eta (Roll (inNat L)))
         = KR (⟦e⟧ (id_env L, KUR (eta (Roll (inNat L)))))   (F_body)
         = KR (⟦e⟧ (id_env L, eta (inNat L)))                (Unroll_Roll)
         = KR (⟦e⟧ (id_env L.+1))                            (definition)
         = eta (Roll v')                                     (IH at L.+1)
     So the body is read at level L.+1 to `e` (IH), and the result is
     `FUN e`.  The key point is that `id_env L.+1 = (id_env L, eta (inNat
     L))`: the readback's fresh variable *is* the next slot of the canonical
     environment.
   - `Nf_ne k`: the neutral IH, forgetting `NeV`. *)
Lemma nf_readback :
  (forall k : Term, Ne k -> forall L : nat, Scoped L k ->
     exists v : VInf, ⟦ k ⟧ (id_env L) =-= eta v /\ NeV v /\ R L v =-= eta k) /\
  (forall t : Term, Nf t -> forall L : nat, Scoped L t ->
     exists v : VInf, ⟦ t ⟧ (id_env L) =-= eta v /\ R L v =-= eta t).
Proof.
  apply: NeNf_mut.
  - (* Ne_var *) move => n L Hs.
    case: L Hs => [ | E] Hs; first done.
    have Hn : (n <= E)%N := Hs.
    exists (inNat (E - n)). split; [ | split].
    + rewrite -> SemT_VAR_equation. apply: SemVar_id_env.
      by rewrite natO_le.
    + exact: NeV_var.
    + rewrite -> R_roundtrip. by rewrite (subn_round Hn).
  - (* Ne_app *) move => k v Hk IHk Hv IHv L [Hsk Hsv].
    case: (IHk L Hsk) => [vk [Hvk [Hnk HRk]]].
    case: (IHv L Hsv) => [vv [Hvv HRv]].
    case: (NeV_AppOp Hvk Hvv Hnk) => [Happ Hne].
    (* App vk vv: neutral, read back to APP k v *)
    exists (inPair (Roll vk, Roll vv)). split; [ | split].
    + exact: Happ.
    + exact: Hne.
    + exact: (R_neutral_app HRk HRv).
  - (* Nf_fun *) move => e He IH L Hs.
    case: (IH L.+1 Hs) => [v' [Hv' HR']].
    exists (inFun (F (@SemT L.+1 e) (id_env L))). split.
    + exact: SemT_FUN_equation2.
    + rewrite -> (R_FUN L (F (@SemT L.+1 e) (id_env L))).
      (* the body at the fresh variable is the body at id_env L.+1 *)
      have Hf : F (@SemT L.+1 e) (id_env L) (eta (Roll (inNat L)))
                =-= eta (Roll v').
      { apply Oeq_trans with
            (y := kleisli (eta << Roll)
                    (@SemT L.+1 e (id_env L,
                                   kleisli (eta << Unroll) (eta (Roll (inNat L)))))).
        { exact: (@F_body L e (id_env L) (eta (Roll (inNat L)))). }
        apply Oeq_trans with
            (y := kleisli (eta << Roll) (@SemT L.+1 e (id_env L, eta (inNat L)))).
        { apply: kleisli_eq_arg. apply: SemT_eq_env.
          apply: pair_Oeq.
          - apply: tset_refl.
          - rewrite -> kleisli_eta. rewrite -> comp_simpl.
            apply: StreamVal_eq. exact: Unroll_Roll. }
        apply Oeq_trans with (y := kleisli (eta << Roll) (eta v')).
        { apply: kleisli_eq_arg. exact: Hv'. }
        rewrite -> kleisli_eta. rewrite -> comp_simpl. apply: tset_refl. }
      rewrite -> (FunCase_eval (R L.+1) Hf).
      rewrite -> (KLEISLI_etaVal (R L.+1) v').
      rewrite -> HR'.
      rewrite -> kleisli_eta. rewrite -> comp_simpl. apply: tset_refl.
  - (* Nf_ne *) move => k Hk IHk L Hs.
    case: (IHk L Hs) => [v [Hv [_ HR]]].
    by exists v.
Qed.

(** *Typed Lemma 8: `nbe` is the identity on normal forms *)

(* `nbe` is the identity on well-typed normal forms (typing gives scoping). *)
Lemma Lemma8_typed :
  forall (Γ : LCtx) (t : Term) (θ : LType),
    Nf t -> (Γ ⊢ t ⦂ θ) ->
    nbe (length Γ) t =-= eta t.
Proof.
  move => Γ t θ Hnf Ht.
  case: ((proj2 nf_readback) t Hnf (length Γ) (TypeJudge_scoped Ht))
    => [v [Hv HR]].
  unfold nbe. rewrite -> Hv.
  rewrite -> (KLEISLI_etaVal (R (length Γ)) v). exact: HR.
Qed.

(** *Reflection (converse direction) *)

(* Normalisation reflects equality (converse of Completeness).

   Proof.  Apply `Correctness` (paper Thm 3) to both terms:
     nbe t  = eta t1  with  Γ ⊢ t  ≡ t1,
     nbe t' = eta t2  with  Γ ⊢ t' ≡ t2.
   From `nbe t = nbe t'` we get `eta t1 =-= eta t2` in the lifted discrete
   cpo of terms.  `eta` is injective (`vinj`), and equality in a discrete cpo
   is Leibniz equality (`discrete_eq`), so `t1 = t2`.  Then
     Γ ⊢ t ≡ t1 ≡ t'       (Eq_trans, Eq_sym).

   Typing hypotheses are needed only to apply `Correctness`.

   Dependency.  The proof is complete, but `Correctness` is still admitted
   (ISSUE-016b, which depends on the logical relation of ISSUE-015), so
   `Print Assumptions Reflection` lists it.  Once 016b is proved,
   `Reflection` becomes closed with no change here. *)
Theorem Reflection :
  forall (Γ : LCtx) (t t' : Term) (θ : LType),
    (Γ ⊢ t ⦂ θ) -> (Γ ⊢ t' ⦂ θ) ->
    nbe (length Γ) t =-= nbe (length Γ) t' -> Γ ⊢ t ≡ t' ⦂ θ.
Proof.
  move => Γ t t' θ Ht Ht' H.
  case: (Correctness Ht) => [t1 [Hn1 He1]].
  case: (Correctness Ht') => [t2 [Hn2 He2]].
  have E12 : (eta t1 : discrete_cpoType Term _BOT) =-= eta t2.
  { apply Oeq_trans with (y := nbe (length Γ) t).
    - apply: Oeq_sym. exact: Hn1.
    - apply Oeq_trans with (y := nbe (length Γ) t').
      + exact: H.
      + exact: Hn2. }
  (* eta is injective; equality in a discrete cpo is Leibniz *)
  have Heq : t1 = t2.
  { apply: discrete_eq. apply: vinj. exact: E12. }
  subst t2.
  apply: (Eq_trans He1). apply: Eq_sym. exact: He2.
Qed.
