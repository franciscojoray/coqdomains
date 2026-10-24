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
Require Import DomainLemmas.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
(*end hide*)

(** *)
(*** Validity and soundness (paper Def. 6, Thm 1) — statements ***)
(** *)

(* ISSUE-013b: both sentences below are now PROVED.
     - SemCtx_ext
     - TypeJudge_sound

   ISSUE-020: with application on neutrals and `SemTm` admitting neutrals,
   `TypeJudge_sound` has a neutral branch in its App case, and the
   canonical-environment validity `SemCtx_id_env` (needed by ISSUE-016/017)
   is restored and PROVED.                                                  *)

(** *Context interpretation *)

(* Every in-scope slot holds a semantic term of its declared type. *)
Definition SemCtx (Γ : LCtx) (η : SemEnv (length Γ)) : Prop :=
  forall (n : nat), n < length Γ ->
    exists d : VInf, η !! n =-= eta d /\ d ∈ ⟨ (Γ ∋ n) ⟩.

(* Pretty notation: context validity `Γ ⊨ η`. *)
Notation "Γ ⊨ η" := (@SemCtx Γ η) (at level 1, no associativity).

(** *Validity of terms *)

Definition ValidTm (Γ : LCtx) (t : Term) (θ : LType) : Prop :=
  forall (η : SemEnv (length Γ)), Γ ⊨ η ->
    exists d : VInf, ⟦ t ⟧ η =-= eta d /\ d ∈ ⟨ θ ⟩.

(* Pretty notation: term validity `Γ ⊨ t ⦂ θ`. *)
Notation "Γ ⊨ t ⦂ θ" := (ValidTm Γ t θ) (at level 1, no associativity).

(** *Helper sentences *)

(* context rewriting on list cons (needed by the soundness proof) *)
Lemma length_cons : forall (θ : LType) (Γ : LCtx), length (θ × Γ) = (length Γ).+1.
Proof. done. Qed.

Lemma lookupType_cons_0 : forall (θ : LType) (Γ : LCtx), (θ × Γ) ∋ 0 = θ.
Proof. done. Qed.

Lemma lookupType_cons_S : forall (θ : LType) (Γ : LCtx) (n : nat),
    (θ × Γ) ∋ (S n) = Γ ∋ n.
Proof. done. Qed.

(* extending a valid context by one semantic term *)
Lemma SemCtx_ext : forall (θ : LType) (Γ : LCtx) (η : SemEnv (length Γ)) (d : VInf),
    Γ ⊨ η -> d ∈ ⟨ θ ⟩ -> (θ × Γ) ⊨ (η, eta d).
Proof.
  move => θ Γ η d Hη Hd n Hn.
  case: n Hn => [ | m] Hn.
  - exists d. split.
    + apply: SemVar0.
    + rewrite -> lookupType_cons_0. exact Hd.
  - have Hm : m < length Γ.
    { rewrite -ltnS -(length_cons θ Γ). exact Hn. }
    case: (Hη m Hm) => [d0 [Hd0 Hsd0]].
    exists d0. split.
    + eapply Oeq_trans; [ apply: SemVarS | exact Hd0 ].
    + rewrite -> lookupType_cons_S. exact Hsd0.
Qed.

(* The canonical environment (paper `ρ_Γ`, Def. 7) is valid for every
   context (ISSUE-020).  Every slot of `id_env` holds a variable `x_n`
   (`inNat n`), which is neutral, and neutrals inhabit every semantic type
   (paper Lemma 6.1, `NeV_SemTm`).  This sentence was false (and commented
   out) while `AppOp` sent neutrals to ⊥. *)

Lemma id_env_NeV : forall (L n : nat), n < L ->
    exists d : VInf, (id_env L) !! n =-= eta d /\ NeV d.
Proof.
  move => L n. case: L => [ | E] Hn; first done.
  exists (inNat (E - n)). split.
  - apply: SemVar_id_env. by rewrite natO_le -ltnS.
  - exact: NeV_var.
Qed.

Lemma SemCtx_id_env : forall (Γ : LCtx), @SemCtx Γ (id_env (length Γ)).
Proof.
  move => Γ n Hn.
  case: (id_env_NeV Hn) => [d [Hd Hne]].
  exists d. split; [exact Hd | exact: NeV_SemTm].
Qed.

(** *Domain helpers used by the soundness proof *)

(* `Unroll` is a left inverse of `Roll`. *)
Lemma Unroll_Roll : forall (v : VInf), Unroll (Roll v) =-= v.
Proof. move => v. have X := fmon_eq_elim UR_id v. exact X. Qed.

(* Componentwise equality of pairs (explicit product ordType: the library
   registers no canonical Setoid instance for products). *)
Lemma pair_Oeq : forall (A B : cpoType) (a a' : A) (b b' : B),
    a =-= a' -> b =-= b' -> @tset_eq (@prod_ordType A B) (a, b) (a', b').
Proof.
  move => A B a a' b b' H1 H2. apply: Ole_antisym; split.
  - exact (proj1 H1).
  - exact (proj1 H2).
  - exact (proj2 H1).
  - exact (proj2 H2).
Qed.

(* `SemT` is a morphism, hence monotone in the environment. *)
Lemma SemT_eq_env : forall (E : Env) (t : Term) (η η' : SemEnv E),
    η =-= η' -> ⟦ t ⟧ η =-= ⟦ t ⟧ η'.
Proof.
  move => E t η η' H. split.
  - apply: (fmonotonic (@SemT E t) (proj1 H)).
  - apply: (fmonotonic (@SemT E t) (proj2 H)).
Qed.

(* Application, at the value level: evaluating `AppOp` on a semantic function
   `inFun f` and an argument `e` yields `kleisli (eta << Unroll) (f (Roll e))`
   (paper: `x · e`).  This is the key computation behind rule `AppRule`. *)
Lemma AppOp_val : forall (E : Env) (d1 d2 : SemEnv E =-> VInf _BOT) (η : SemEnv E)
    (f : DInf _BOT -=> DInf _BOT) (e : VInf),
    d1 η =-= eta (inFun f) -> d2 η =-= eta e ->
    AppOp d1 d2 η =-= kleisli (eta << Unroll) (f (eta (Roll e))).
Proof.
  move => E d1 d2 η f e H1 H2.
  rewrite -> (AppOp_eval d2 H1). rewrite -> AppV_fun. rewrite -> H2.
  rewrite -> kleisli_eta. rewrite -> comp_simpl.
  by split; apply: Ole_refl.
Qed.

(** *Soundness (paper Thm 1) *)

Theorem TypeJudge_sound : forall (Γ : LCtx) (t : Term) (θ : LType),
    (Γ ⊢ t ⦂ θ) -> Γ ⊨ t ⦂ θ.
Proof.
  move => Γ t θ H. elim: H.
  - (* VarRule *) move => Γ0 v Hv η Hη.
    exact (Hη v Hv).
  - (* FunRule *) move => Γ0 e θ' θ0 H IH η Hη.
    exists (inFun (F (@SemT (length Γ0).+1 e) η)). split.
    + apply: tset_refl.
    + left. exists (F (@SemT (length Γ0).+1 e) η). split.
      * done.
      * move => e0 He0.
        have Hη' : @SemCtx (θ' × Γ0) (η, eta e0).
        { apply: SemCtx_ext Hη He0. }
        case: (IH (η, eta e0) Hη') => [d' [Hd' Hsd']].
        exists d'. split.
        { apply Oeq_trans with
              (y := kleisli (eta << Roll)
                      (⟦e⟧ ((η, kleisli (eta << Unroll) (eta (Roll e0)))
                              : SemEnv (length Γ0).+1))).
          { apply: F_body. }
          apply Oeq_trans with
              (y := kleisli (eta << Roll)
                      (⟦e⟧ ((η, eta e0) : SemEnv (length Γ0).+1))).
          { apply: kleisli_eq_arg. apply: SemT_eq_env.
            apply: pair_Oeq; first by apply: tset_refl.
            rewrite -> kleisli_eta. rewrite -> comp_simpl.
            apply: StreamVal_eq. exact: Unroll_Roll. }
          apply Oeq_trans with (y := kleisli (eta << Roll) (eta d')).
          { apply: kleisli_eq_arg. exact Hd'. }
          { rewrite -> kleisli_eta. rewrite -> comp_simpl. rewrite -> eta_val.
            by split; apply: Ole_refl. } }
        { exact Hsd'. }
  - (* AppRule *) move => Γ0 t1 t2 θ0 θ' H1 IH1 H2 IH2 η Hη.
    case: (IH1 η Hη) => [d1 [Hd1 Hsd1]].
    case: (IH2 η Hη) => [d2 [Hd2 Hsd2]].
    case: Hsd1 => [[f [Hd1' Hf]] | Hne].
    + (* semantic function: β *)
      rewrite -> Hd1' in Hd1.
      case: (Hf d2 Hsd2) => [w [Hfw Hsw]].
      exists w. split.
      * apply Oeq_trans with (y := kleisli (eta << Unroll) (f (eta (Roll d2)))).
        { apply: AppOp_val; [exact Hd1 | exact Hd2]. }
        apply Oeq_trans with (y := kleisli (eta << Unroll) (Val (Roll w))).
        { apply: kleisli_eq_arg. exact Hfw. }
        { rewrite -> kleisliVal. rewrite -> comp_simpl. rewrite -> Unroll_Roll.
          by split; apply: Ole_refl. }
      * exact Hsw.
    + (* neutral: x · e = App x e, again neutral (paper Lemma 6.1) *)
      case: (NeV_AppOp Hd1 Hd2 Hne) => [Happ Hne'].
      exists (inPair (Roll d1, Roll d2)). split.
      * exact Happ.
      * exact: NeV_SemTm.
Qed.
