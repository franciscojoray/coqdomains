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
Require Import DomainLemmas.
Require Import SemOps.
Require Import Semantics.
Require Import Types.
Require Import Weakening.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Include RD.
(*end hide*)

(** *)
(*** Semantic renaming and substitution lemmas (ISSUE-021, step D) ***)
(** *)

(* Both lemmas are stated *relationally*: instead of building the semantic
   environment `⟦σ⟧η` from a function (which would need a product Setoid
   instance the library lacks), we relate two environments slot by slot.
   They go by induction on the typing derivation, which keeps every variable
   in scope; neither depends on how `AppOp` treats non-functions, so they are
   unaffected by ISSUE-020. *)

(** *Congruences of the semantic constructors *)

(* application respects `=-=` in both arguments, across two (possibly
   different-sized) environments *)
Lemma AppOp_cong : forall (E E' : Env)
    (d1 d2 : SemEnv E =-> VInf _BOT) (d1' d2' : SemEnv E' =-> VInf _BOT)
    (η : SemEnv E) (η' : SemEnv E'),
    d1 η =-= d1' η' -> d2 η =-= d2' η' ->
    AppOp d1 d2 η =-= AppOp d1' d2' η'.
Proof.
  move => E E' d1 d2 d1' d2' η η' H1 H2.
  unfold AppOp.
  change (KLEISLIL AppV (d1 η, d2 η) =-= KLEISLIL AppV (d1' η', d2' η')).
  apply: (fmon_stable (KLEISLIL AppV)).
  apply: Ole_antisym; split.
  - exact (proj1 H1).
  - exact (proj1 H2).
  - exact (proj2 H1).
  - exact (proj2 H2).
Qed.

(* abstraction: bodies that agree on every extension of the two
   environments by the same value denote equal semantic functions *)
Lemma SemT_FUN_cong : forall (E E' : Env) (e e' : Term)
    (η : SemEnv E) (η' : SemEnv E'),
    (forall d : VInf _BOT,
        @SemT E'.+1 e' (η', d) =-= @SemT E.+1 e (η, d)) ->
    ⟦ FUN e' ⟧ η' =-= ⟦ FUN e ⟧ η.
Proof.
  move => E E' e e' η η' H.
  rewrite -> !SemT_FUN_equation2.
  have Hf : F (@SemT E'.+1 e') η' =-= F (@SemT E.+1 e) η.
  { apply: fmon_eq_intro. move => x.
    apply Oeq_trans with
        (y := kleisli (eta << Roll)
                (@SemT E'.+1 e' (η', kleisli (eta << Unroll) x))).
    { exact: (@F_body E' e' η' x). }
    apply Oeq_trans with
        (y := kleisli (eta << Roll)
                (@SemT E.+1 e (η, kleisli (eta << Unroll) x))).
    { apply: kleisli_eq_arg. exact: H. }
    apply: Oeq_sym. exact: (@F_body E e η x). }
  rewrite -> Hf. apply: tset_refl.
Qed.

(** *D1: semantic renaming *)

(* `⟦t π⟧η' = ⟦t⟧η` whenever `η'` agrees with `η` along `π` *)
Lemma SemT_ren : forall (Γ : LCtx) (t : Term) (θ : LType),
    (Γ ⊢ t ⦂ θ) ->
    forall (Δ : LCtx) (π : Ren)
           (η : SemEnv (length Γ)) (η' : SemEnv (length Δ)),
      (forall v : Var, v < length Γ -> η' !! (π v) =-= η !! v) ->
      ⟦ renT π t ⟧ η' =-= ⟦ t ⟧ η.
Proof.
  move => Γ t θ H. elim: H.
  - (* VarRule *) move => Γ0 v Hv Δ π η η' Hη.
    unfold renT. rewrite -> mapVAR. cbn.
    exact: (Hη v Hv).
  - (* FunRule *) move => Γ0 e θ' θ0 He IH Δ π η η' Hη.
    unfold renT. rewrite -> mapFUN. fold (renT (liftRen π) e).
    apply: SemT_FUN_cong. move => d.
    apply: (IH (θ' × Δ) (liftRen π) (η, d) (η', d)).
    case => [ | v'] Hv.
    + rewrite -> liftRen_O.
      eapply Oeq_trans; [ exact: (SemVar0 η' d) | ].
      apply: Oeq_sym. exact: (SemVar0 η d).
    + rewrite -> liftRen_S.
      eapply Oeq_trans; [ exact: (SemVarS (π v') η' d) | ].
      eapply Oeq_trans; [ exact: (Hη v' Hv) | ].
      apply: Oeq_sym. exact: (SemVarS v' η d).
  - (* AppRule *) move => Γ0 t1 t2 θ0 θ' H1 IH1 H2 IH2 Δ π η η' Hη.
    unfold renT. rewrite -> mapAPP. fold (renT π t1). fold (renT π t2).
    rewrite -> !SemT_APP_equation.
    apply: AppOp_cong; [ exact: (IH1 Δ π η η' Hη) | exact: (IH2 Δ π η η' Hη) ].
Qed.

(* weakening by one fresh slot does not change the denotation *)
Lemma SemT_weaken : forall (Γ : LCtx) (t : Term) (θ : LType),
    (Γ ⊢ t ⦂ θ) ->
    forall (η : SemEnv (length Γ)) (d : VInf _BOT),
      @SemT (length Γ).+1 (renT (fun n => S n) t) (η, d) =-= ⟦ t ⟧ η.
Proof.
  move => Γ t θ H η d.
  apply: (@SemT_ren Γ t θ H (★ × Γ) (fun n => S n) η (η, d)).
  move => v Hv. exact: (SemVarS v η d).
Qed.

(** *D2: semantic substitution *)

(* `⟦t σ⟧η' = ⟦t⟧η` whenever each `σ v` denotes, in `η'`, the slot `v`
   of `η` *)
Lemma SemT_sub : forall (Γ : LCtx) (t : Term) (θ : LType),
    (Γ ⊢ t ⦂ θ) ->
    forall (Δ : LCtx) (σ : Lang.Sub), SubOK Δ Γ σ ->
    forall (η : SemEnv (length Γ)) (η' : SemEnv (length Δ)),
      (forall v : Var, v < length Γ -> ⟦ σ v ⟧ η' =-= η !! v) ->
      ⟦ subT σ t ⟧ η' =-= ⟦ t ⟧ η.
Proof.
  move => Γ t θ H. elim: H.
  - (* VarRule *) move => Γ0 v Hv Δ σ Hσ η η' Hη.
    unfold subT. rewrite -> mapVAR. cbn.
    exact: (Hη v Hv).
  - (* FunRule *) move => Γ0 e θ' θ0 He IH Δ σ Hσ η η' Hη.
    unfold subT. rewrite -> mapFUN. fold (subT (liftSub σ) e).
    apply: SemT_FUN_cong. move => d.
    apply: (IH (θ' × Δ) (liftSub σ) (@SubOK_lift θ' Δ Γ0 σ Hσ) (η, d) (η', d)).
    case => [ | v'] Hv.
    + rewrite -> liftSub_O.
      eapply Oeq_trans; [ exact: (SemVar0 η' d) | ].
      apply: Oeq_sym. exact: (SemVar0 η d).
    + rewrite -> liftSub_S.
      eapply Oeq_trans; [ exact: (SemT_weaken (Hσ v' Hv) η' d) | ].
      eapply Oeq_trans; [ exact: (Hη v' Hv) | ].
      apply: Oeq_sym. exact: (SemVarS v' η d).
  - (* AppRule *) move => Γ0 t1 t2 θ0 θ' H1 IH1 H2 IH2 Δ σ Hσ η η' Hη.
    unfold subT. rewrite -> mapAPP. fold (subT σ t1). fold (subT σ t2).
    rewrite -> !SemT_APP_equation.
    apply: AppOp_cong;
      [ exact: (IH1 Δ σ Hσ η η' Hη) | exact: (IH2 Δ σ Hσ η η' Hη) ].
Qed.

(* the β instance (used by `EqTm_sound`, ISSUE-014b).  Call-by-name
   (ISSUE-024d): unconditional — `e⟦r⟧` denotes what `e` denotes with the
   (possibly divergent) denotation of `r` in slot 0. *)
Lemma SemT_beta : forall (Γ : LCtx) (e r : Term) (θ' θ : LType),
    ((θ' × Γ) ⊢ e ⦂ θ) -> (Γ ⊢ r ⦂ θ') ->
    forall (η : SemEnv (length Γ)),
      ⟦ subT (consMap r (idSub)) e ⟧ η =-= @SemT (length Γ).+1 e (η, ⟦ r ⟧ η).
Proof.
  move => Γ e r θ' θ He Hr η.
  apply: (@SemT_sub (θ' × Γ) e θ He Γ (consMap r (idSub))
            (@SubOK_single θ' Γ r Hr) (η, ⟦ r ⟧ η) η).
  case => [ | v'] Hv.
  - apply: Oeq_sym. exact: (SemVar0 η (⟦ r ⟧ η)).
  - apply: Oeq_sym. exact: (SemVarS v' η (⟦ r ⟧ η)).
Qed.

(* β in the model: application of an abstraction passes the argument's
   denotation unevaluated (call-by-name).  Holds for every environment and
   every argument, including a divergent one (cf. ISSUE-023). *)
Lemma SemT_APP_FUN : forall (E : Env) (e r : Term) (η : SemEnv E),
    ⟦ APP (FUN e) r ⟧ η =-= @SemT E.+1 e (η, ⟦ r ⟧ η).
Proof.
  move => E e r η.
  rewrite -> SemT_APP_equation.
  have Hh : ⟦ FUN e ⟧ η =-= eta (inFun (F (@SemT E.+1 e) η)).
  { exact: SemT_FUN_equation2. }
  rewrite -> (AppOp_eval ⟦ r ⟧ Hh).
  rewrite -> AppV_fun.
  apply Oeq_trans with
      (y := KUR (KR (@SemT E.+1 e (η, KUR (KR (⟦ r ⟧ η)))))).
  { unfold KUR, KR. apply: kleisli_eq_arg.
    exact: (@F_body E e η (kleisli (eta << Roll) (⟦ r ⟧ η))). }
  rewrite -> KURKR_id. rewrite -> KURKR_id.
  apply: tset_refl.
Qed.
