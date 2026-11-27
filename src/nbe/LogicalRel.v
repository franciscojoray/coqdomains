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
Require Import EqSubst.
Require Import NbE.
Require Import Weakening.
From Stdlib Require Import List.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
(*end hide*)

(** *)
(*** Logical relations (paper Defs 8–9, Thm 2) — statements ***)
(** *)

(* ISSUE-015a: the old environment-parametrised relation was false.  The
   relation below is the Kripke/readback-carrying version; the proofs are
   filled in by ISSUE-015d … 015f. *)

(** *Readback-carrying relation *)

Definition ReifRel (Gamma : LCtx) (t : Term) (d : VInf) (theta : LType) : Prop :=
  forall (Theta : LCtx),
    exists t' : Term,
      R (length Theta + length Gamma)%N d =-= eta t' /\
      (Theta ++ Gamma) ⊢ wk (length Theta) t ≡ t' ⦂ theta.

(** *Term relation (paper Def. 8) *)

Fixpoint TermRel (Gamma : LCtx) (t : Term) (d : VInf) (theta : LType) : Prop :=
  match theta with
  | UnitTy => ReifRel Gamma t d UnitTy
  | FunTy theta1 theta2 =>
      ReifRel Gamma t d (FunTy theta1 theta2) /\
      forall (Theta : LCtx) (s : Term) (a : VInf),
        @TermRel (Theta ++ Gamma) s a theta1 ->
        exists w : VInf,
          AppV (d, eta a) =-= eta w /\
          @TermRel (Theta ++ Gamma) (APP (wk (length Theta) t) s) w theta2
  end.

Arguments TermRel : clear implicits.

Notation "Gamma ⊩ t ∼ d ⦂ theta" := (TermRel Gamma t d theta)
  (at level 1, no associativity).

(** *Related substitutions (paper Def. 9) *)

Definition SubRel (Delta Gamma : LCtx) (sigma : Lang.Sub)
                  (rho : SemEnv (length Gamma)) : Prop :=
  forall (v : Var), (v < length Gamma)%N ->
    exists d : VInf,
      rho !! v =-= eta d /\
      @TermRel Delta (sigma v) d (Gamma ∋ v).

Arguments SubRel : clear implicits.

(** *Basic properties [ISSUE-015d] *)

Lemma TermRel_reify : forall (Gamma : LCtx) (t : Term) (d : VInf) (theta : LType),
    Gamma ⊩ t ∼ d ⦂ theta -> ReifRel Gamma t d theta.
Proof.
  move => Gamma t d theta H. case: theta H => [theta1 theta2 | ] /= H.
  - exact: (proj1 H).
  - exact: H.
Qed.

Lemma TermRel_typed : forall (Gamma : LCtx) (t : Term) (d : VInf) (theta : LType),
    Gamma ⊩ t ∼ d ⦂ theta -> inhabited (Gamma ⊢ t ⦂ theta).
Proof.
  move => Gamma t d theta H.
  have HR : ReifRel Gamma t d theta.
  { case: theta H => [theta1 theta2 | ] /= H; [exact: (proj1 H) | exact: H]. }
  case: (HR nil) => t' [_ HE].
  case: (EqTm_typed HE) => [[Ht] _].
  rewrite wk_0 in Ht. by constructor.
Qed.

(* the reification component is stable under typed equality *)
Lemma ReifRel_eq : forall (Gamma : LCtx) (t t' : Term) (d : VInf)
                          (theta : LType),
    ReifRel Gamma t d theta ->
    Gamma ⊢ t ≡ t' ⦂ theta ->
    ReifRel Gamma t' d theta.
Proof.
  move => Gamma t t' d theta HR Heq Theta.
  case: (HR Theta) => t'' [HRd HE].
  exists t''. split => //.
  apply: (Eq_trans _ HE).
  apply: Eq_sym. exact: (@EqTm_wk Theta Gamma t t' theta Heq).
Qed.

Lemma TermRel_eq : forall (Gamma : LCtx) (t t' : Term) (d : VInf) (theta : LType),
    Gamma ⊩ t ∼ d ⦂ theta ->
    Gamma ⊢ t ≡ t' ⦂ theta ->
    Gamma ⊩ t' ∼ d ⦂ theta.
Proof.
  move => Gamma t t' d theta.
  elim: theta Gamma t t' d => [theta1 IH1 theta2 IH2 | ] /=.
  - move => Gamma t t' d Hrel Heq. case: Hrel => [HR Hfun]. split.
    + exact: (ReifRel_eq HR Heq).
    + move => Theta s a Hsa.
      case: (Hfun Theta s a Hsa) => w [Happ Hrel2].
      exists w. split => //.
      case: (TermRel_typed Hsa) => [Hs].
      have Heqapp :
        (Theta ++ Gamma) ⊢ APP (wk (length Theta) t) s
                          ≡ APP (wk (length Theta) t') s ⦂ theta2.
      { apply: Eq_app.
        - exact: (@EqTm_wk Theta Gamma t t' (theta1 ⇥ theta2) Heq).
        - exact: (Eq_refl Hs). }
      refine (IH2 (Theta ++ Gamma) (APP (wk (length Theta) t) s)
                  (APP (wk (length Theta) t') s) w _ _).
      - exact Hrel2.
      - exact Heqapp.
  - move => Gamma t t' d Hrel Heq. exact: (ReifRel_eq Hrel Heq).
Qed.

Lemma ReifRel_weaken : forall (Theta Gamma : LCtx) (t : Term) (d : VInf)
                              (theta : LType),
    ReifRel Gamma t d theta ->
    ReifRel (Theta ++ Gamma) (wk (length Theta) t) d theta.
Proof.
  move => Theta Gamma t d theta HR Theta'.
  case: (HR (Theta' ++ Theta)) => t' [HRd HE].
  exists t'. split.
  - rewrite length_app in HRd. rewrite length_app.
    by rewrite addnA.
  - have Hterm : wk (length Theta') (wk (length Theta) t)
                 = wk (length (Theta' ++ Theta)) t.
    { rewrite length_app. by rewrite wk_wk. }
    rewrite Hterm.
    have Hassoc : (Theta' ++ (Theta ++ Gamma)) = ((Theta' ++ Theta) ++ Gamma)
      by apply: catA.
    rewrite Hassoc. exact HE.
Qed.

Lemma TermRel_weaken : forall (Theta Gamma : LCtx) (t : Term) (d : VInf)
                              (theta : LType),
    Gamma ⊩ t ∼ d ⦂ theta ->
    (Theta ++ Gamma) ⊩ wk (length Theta) t ∼ d ⦂ theta.
Proof.
  move => Theta Gamma t d theta.
  elim: theta Gamma t d => [theta1 IH1 theta2 IH2 | ] /=.
  - move => Gamma t d Hrel. case: Hrel => [HR Hfun]. split.
    + exact: (@ReifRel_weaken Theta Gamma t d (theta1 ⇥ theta2) HR).
    + move => Theta' s a Hsa.
      have Hassoc : (Theta' ++ (Theta ++ Gamma)) = ((Theta' ++ Theta) ++ Gamma)
        by apply: catA.
      have Hsa' : ((Theta' ++ Theta) ++ Gamma) ⊩ s ∼ a ⦂ theta1.
      { rewrite -Hassoc. exact Hsa. }
      case: (Hfun (Theta' ++ Theta) s a Hsa') => w [Happ Hrel2].
      exists w. split => //.
      have Hterm : wk (length Theta') (wk (length Theta) t)
                   = wk (length (Theta' ++ Theta)) t.
      { rewrite length_app. by rewrite wk_wk. }
      rewrite -Hterm in Hrel2.
      rewrite -Hassoc in Hrel2.
      exact Hrel2.
  - move => Gamma t d HR.
    exact: (@ReifRel_weaken Theta Gamma t d UnitTy HR).
Qed.

(** *Reflection and the identity substitution [ISSUE-015e] *)

Lemma TermRel_reflect : forall (Gamma : LCtx) (t : Term) (d : VInf)
                               (theta : LType),
    NeV d -> ReifRel Gamma t d theta -> Gamma ⊩ t ∼ d ⦂ theta.
Proof.
  move => Gamma t d theta.
  elim: theta Gamma t d => [theta1 IH1 theta2 IH2 | ] /=.
  - move => Gamma t d Hne HR. split.
    + exact HR.
    + move => Theta s a Hsa.
      exists (inPair (Roll d, Roll a)). split.
      * exact: (@NeV_AppV d a Hne).
      * apply: (IH2 (Theta ++ Gamma) (APP (wk (length Theta) t) s)
                  (inPair (Roll d, Roll a))).
        -- exact: (@NeV_app d a Hne).
        -- move => Theta'.
           case: (HR (Theta' ++ Theta)) => tf [HRd HEf].
           have Hsa_w : (Theta' ++ (Theta ++ Gamma)) ⊩ wk (length Theta') s ∼ a ⦂ theta1.
           { exact: (@TermRel_weaken Theta' (Theta ++ Gamma) s a theta1 Hsa). }
           case: (TermRel_reify Hsa_w nil) => sf [HRa HEs].
           simpl in HEs.
           rewrite wk_0 in HEs.
           have Hindexa : (length [::] + length (Theta' ++ Theta ++ Gamma))%N
                          = (length Theta' + length (Theta ++ Gamma))%N.
           { by rewrite !length_app. }
           rewrite Hindexa in HRa.
           have Hindex : (length (Theta' ++ Theta) + length Gamma)%N
                         = (length Theta' + length (Theta ++ Gamma))%N.
           { by rewrite !length_app addnA. }
           rewrite Hindex in HRd.
           have HRapp := @R_neutral_app (length Theta' + length (Theta ++ Gamma))%N
                                          d a tf sf HRd HRa.
           exists (APP tf sf). split => //.
           have Hassoc : (Theta' ++ (Theta ++ Gamma)) = ((Theta' ++ Theta) ++ Gamma)
             by apply: catA.
           rewrite -Hassoc in HEf.
           have Hterm : wk (length Theta') (wk (length Theta) t)
                        = wk (length (Theta' ++ Theta)) t.
           { rewrite length_app. by rewrite wk_wk. }
           rewrite -Hterm in HEf.
           rewrite wk_APP.
           apply: Eq_app.
           ++ exact HEf.
           ++ exact HEs.
  - move => Gamma t d Hne HR. exact HR.
Qed.

Lemma TermRel_var : forall (Gamma : LCtx) (v : Var),
    (v < length Gamma)%N ->
    Gamma ⊩ VAR v ∼ inNat (length Gamma - v.+1) ⦂ (Gamma ∋ v).
Proof.
  move => Gamma v Hv.
  apply: TermRel_reflect.
  - exact: NeV_var.
  - move => Theta.
    exists (VAR (v + length Theta)%N).
    split.
    + exact: (@R_var_ext Gamma (length Theta) v Hv).
    + rewrite wk_VAR.
      have Hty : (Theta ++ Gamma) ⊢ VAR (v + length Theta)%N
                   ⦂ ((Theta ++ Gamma) ∋ (v + length Theta)%N).
      { apply: VarRule. rewrite length_app. rewrite addnC.
        by rewrite ltn_add2l. }
      rewrite (lookupType_app Theta Gamma v) in Hty.
      exact: (Eq_refl Hty).
Qed.

Lemma SubRel_weaken : forall (Theta Delta Gamma : LCtx) (sigma : Lang.Sub)
                             (rho : SemEnv (length Gamma)),
    SubRel Delta Gamma sigma rho ->
    SubRel (Theta ++ Delta) Gamma (fun n => wk (length Theta) (sigma n)) rho.
Proof.
  move => Theta Delta Gamma sigma rho Hsub v Hv.
  case: (Hsub v Hv) => d [Hrho Hrel].
  exists d. split => //.
  exact: (@TermRel_weaken Theta Delta (sigma v) d (Gamma ∋ v) Hrel).
Qed.

Lemma SubRel_ext : forall (Delta Gamma : LCtx) (sigma : Lang.Sub)
                          (rho : SemEnv (length Gamma)) (s : Term) (a : VInf)
                          (theta : LType),
    SubRel Delta Gamma sigma rho ->
    Delta ⊩ s ∼ a ⦂ theta ->
    SubRel Delta (theta × Gamma) (consMap s sigma) (rho, eta a).
Proof.
  move => Delta Gamma sigma rho s a theta Hsub Hrel v Hv.
  case: v Hv => [ |v'] Hv.
  - exists a. split.
    + exact: (@SemVar0 (length Gamma) rho (eta a)).
    + rewrite lookupType_cons_0. simpl. exact Hrel.
  - rewrite length_cons ltnS in Hv.
    case: (Hsub v' Hv) => d [Hrho Hrel'].
    exists d. split.
    + rewrite -> (@SemVarS v' (length Gamma) rho (eta a)). exact Hrho.
    + rewrite lookupType_cons_S. simpl. exact Hrel'.
Qed.

(* lookup in the canonical environment at the actual context length *)
Lemma SemVar_id_env_at : forall (Gamma : LCtx) (v : Var),
    (v < length Gamma)%N ->
    (id_env (length Gamma)) !! v =-= eta (inNat (length Gamma - v.+1)).
Proof.
  move => Gamma. elim: Gamma => [ |θ Gamma IH] v Hv.
  - done.
  - simpl in Hv. case: v Hv => [ |n] Hv.
    + simpl. by rewrite subn1.
    + simpl. rewrite (IH n Hv). f_equal. by rewrite subSS.
Qed.

Lemma SubRel_id : forall (Gamma : LCtx),
    SubRel Gamma Gamma idSub (id_env (length Gamma)).
Proof.
  move => Gamma v Hv.
  exists (inNat (length Gamma - v.+1)). split.
  - exact: (SemVar_id_env_at Hv).
  - apply: TermRel_var. exact Hv.
Qed.

(** *Fundamental theorem (paper Thm 2) [ISSUE-015f] *)

Theorem Fundamental : forall (Gamma : LCtx) (t : Term) (theta : LType),
    (Gamma ⊢ t ⦂ theta) ->
    forall (Delta : LCtx) (sigma : Lang.Sub) (rho : SemEnv (length Gamma)),
      SubRel Delta Gamma sigma rho ->
      exists d : VInf,
        ⟦ t ⟧ rho =-= eta d /\
        Delta ⊩ subT sigma t ∼ d ⦂ theta.
Proof. Admitted.
