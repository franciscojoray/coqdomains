
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

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Include RD.
(*end hide*)

(** *)
(*** Chapter 4: Extended Language Semantics ***)
(** *)

(** *Environment Semantics *)
Fixpoint SemEnv E : cpoType :=
  match E with
  | O => One
  | S E => SemEnv E * VInf
  end.

(** *Variable Semantics *)
Fixpoint SemVar E (v : Var E) : SemEnv E =-> VInf :=
  match v with 
  | ZVAR _   => pi2
  | SVAR _ v => SemVar v << pi1
  end.

(** *Notation *)
Notation "η !! v" := (@SemVar _ v η) (at level 1, no associativity).
Notation "↑⊥ v" := (eta v) (at level 1, left associativity).
(* Notation "↑int n" := (inl n) (at level 1, left associativity). *)
(* Notation "↑i⊥ n" := (↑⊥ (↑int n)) (at level 1, left associativity). *)
Notation "⊥" := PBot.

(** *Auxiliar functions *)
Definition F (E : Env) (SemE : SemEnv E.+1 =-> VInf _BOT) :
  SemEnv E -=> (DInf -=> DInf _BOT)
  := exp_fun
      (kleisli (eta << Roll) <<
        SemE << (Id >< Unroll)).

Definition mod2 (n : nat) : nat_cpoType :=
  PeanoNat.Nat.modulo n 2.

Definition MOD2 : nat_cpoType =-> nat_cpoType := SimpleUOp mod2.

Definition VInfToBool : VInf -=> bool_cpoType _BOT :=
  [| [| N_to_B , const _ ⊥ |] , const _ ⊥ |].

Definition VInfToNat : VInf -=> nat_cpoType _BOT :=
  [| [| eta , const _ ⊥ |] , const _ ⊥ |].

Definition VInfToFun : VInf -=> (DInf -=> DInf _BOT) _BOT :=
  [| [| const _ ⊥, eta |] , const _ ⊥ |].

Definition VInfToPair : VInf -=> (DInf * DInf) _BOT :=
  [| const _ ⊥, eta |].

Definition GenBinOp (A B : Type) (C : cpoType) (E : Env)
           (inC  : C =-> VInf)
           (outA : VInf =-> discrete_cpoType A _BOT)
           (outB : VInf =-> discrete_cpoType B _BOT)
           (op : A -> B -> C)
           (d1 d2 : SemEnv E =-> VInf _BOT) :
  SemEnv E =-> VInf _BOT :=
  (kleisli (eta << inC << SimpleBOp op) << uncurry (Smash _ _))
    << <| kleisli outA << d1
        , kleisli outB << d2
|>.
Arguments GenBinOp [A B C E] _ _ _ _ _.

Definition GenBinOp_DInf (A B : Type) (C : cpoType) (E : Env)
           (inC  : C =-> VInf)
           (outA : VInf =-> discrete_cpoType A _BOT)
           (outB : VInf =-> discrete_cpoType B _BOT)
           (op : A -> B -> C)
           (d1 d2 : SemEnv E =-> VInf _BOT) :
  SemEnv E =-> VInf _BOT :=
  (kleisli (eta << inC << SimpleBOp op) << uncurry (Smash _ _))
    << <| kleisli (outA << Unroll) << KR << d1
  , kleisli (outB << Unroll) << KR << d2  
            |>.
Arguments GenBinOp_DInf [A B C E] _ _ _ _ _.

Definition GenOrdOp {E : Env}
           (op : nat -> nat -> bool)
           (d1 d2 : SemEnv E =-> VInf _BOT) :
  SemEnv E =-> VInf _BOT := GenBinOp (inNat << B_to_N)
                                    VInfToNat VInfToNat op d1 d2.

Definition GenBoolOp {E : Env}
           (op : bool -> bool -> bool)
           (d1 d2 : SemEnv E =-> VInf _BOT) :
  SemEnv E =-> VInf _BOT := GenBinOp (inNat << B_to_N)
                                    (VInfToBool) (VInfToBool) op d1 d2.

Definition GenNatOp {E : Env}
           (op : nat -> nat -> nat)
           (d1 d2 : SemEnv E =-> VInf _BOT) :
  SemEnv E =-> VInf _BOT := GenBinOp inNat VInfToNat VInfToNat op d1 d2.

Definition GenOrdOp_DInf {E : Env}
           (op : nat -> nat -> bool)
           (d1 d2 : SemEnv E =-> VInf _BOT) :
  SemEnv E =-> VInf _BOT := GenBinOp_DInf (inNat << B_to_N)
                                         VInfToNat VInfToNat op d1 d2.

Definition GenBoolOp_DInf {E : Env}
           (op : bool -> bool -> bool)
           (d1 d2 : SemEnv E =-> VInf _BOT) :
  SemEnv E =-> VInf _BOT := GenBinOp_DInf (inNat << B_to_N)
                                         VInfToBool VInfToBool op d1 d2.

Definition GenNatOp_DInf {E : Env}
           (op : nat -> nat -> nat)
           (d1 d2 : SemEnv E =-> VInf _BOT) :
  SemEnv E =-> VInf _BOT := GenBinOp_DInf inNat VInfToNat VInfToNat op d1 d2.

Definition LetApp {E : Env}
           (d1 : SemEnv E.+1 =-> VInf _BOT)
           (d2 : SemEnv E =-> VInf _BOT) :
  SemEnv E =-> VInf _BOT := ev << <| exp_fun (KLEISLIR d1), d2 |>
.

Definition LetAppDInf (E : Env)
           (d1 : SemEnv E.+1 =-> VInf _BOT)
           (d2 : SemEnv E =-> VInf _BOT) :=
  KR << ev << <| exp_fun (KLEISLIR (d1 << Id >< Unroll)), KR << d2 |>.


Definition AppOp {E : Env}
           (d1 : SemEnv E =-> VInf)
           (d2 : SemEnv E =-> VInf) : SemEnv E =-> VInf _BOT :=
  KLEISLI (eta << Unroll) << (KLEISLIL ev) <<
          <| VInfToFun << d1, Roll << d2 |>.

Definition IfBOp {E : Env}
           (b  : SemEnv E =-> VInf _BOT)
           (d1 : SemEnv E =-> VInf _BOT)
           (d2 : SemEnv E =-> VInf _BOT) : SemEnv E =-> VInf _BOT
  := ev
    <<
    <| pi1 << pi1 , <| pi2 << pi1 , pi2 |> |>
    <<
    <| <| const (SemEnv E)
          (KLEISLIL (UNCURRY
                 ((CCURRY (CCURRY (IfB (SemEnv E) (VInf _BOT)))) d1 d2)))
    , kleisli VInfToBool << b
        |>
    , Id
    |>
.

Definition IfZOp {E : Env}
           (b  : SemEnv E =-> VInf _BOT)
           (d1 : SemEnv E =-> VInf _BOT)
           (d2 : SemEnv E =-> VInf _BOT) : SemEnv E =-> VInf _BOT
  := ev
    <<
    <| pi1 << pi1 , <| pi2 << pi1 , pi2 |> |>
    <<
    <| <| const (SemEnv E)
          (KLEISLIL (UNCURRY
                 ((CCURRY (CCURRY (IfZ (SemEnv E) (VInf _BOT)))) d1 d2)))
    , kleisli VInfToNat << b
        |>
    , Id
    |>
.

Definition IfOneOp {E : Env}
           (b  : SemEnv E =-> VInf _BOT)
           (d1 : SemEnv E =-> VInf _BOT)
           (d2 : SemEnv E =-> VInf _BOT) : SemEnv E =-> VInf _BOT
  := IfZOp b d2 d1.

Definition PairOp {E : Env}
           (d1 : SemEnv E =-> VInf)
           (d2 : SemEnv E =-> VInf) : SemEnv E =-> VInf
  := inPair << (Roll >< Roll) << prod_morph (d1, d2) << <|Id, Id|>.

Definition FSTOp {E : Env}
           (v  : SemEnv E =-> VInf) : SemEnv E =-> VInf _BOT
  := kleisli (eta << Unroll << pi1) << VInfToPair << v.

Definition SNDOp {E : Env}
           (v  : SemEnv E =-> VInf) : SemEnv E =-> VInf _BOT
  := kleisli (eta << Unroll << pi2) << VInfToPair << v.

(** *Notation *)
Notation "'⦓' op '⦔'"    := (GenNatOp op) (at level 1, left associativity).
Infix "⊥⊥⃑" := LetApp (at level 1, no associativity) .
Infix "↓f"   := AppOp (at level 1, no associativity) .

(** Notation *)
Reserved Notation "⟦ v '⟧v'" (at level 1, no associativity).
Reserved Notation "⟦ e '⟧e'" (at level 1, no associativity).

(** *Definition 40: Extrinsic Semantics *)
Fixpoint SemV E (v:V E) : SemEnv E =-> VInf :=
  match v return SemEnv E =-> VInf with
  | VAR m        => SemVar m
  | FUN e        => inFun << (F ⟦ e ⟧e)
  end
with SemE E (e: Expr E) : SemEnv E =-> VInf _BOT :=
  match e with
  | VAL v        => eta << ⟦ v ⟧v
  | APP v1 v2    => (⟦ v1 ⟧v)↓f ⟦ v2 ⟧v
  end
where "⟦ e ⟧e" := (SemE e) and "⟦ v ⟧v" := (SemV v).

(** *Notation and properties *)
Notation "↑f f" := (inFun f) (at level 1, left associativity).
Notation "↑n n" := (inNat n) (at level 1, left associativity).
Notation "↑p p" := (inPair p) (at level 1, left associativity).
Notation "↑⊥ v"   := (eta v) (at level 1, left associativity).
Notation "↑n⊥ n"  := (↑⊥ (↑n n)) (at level 1, left associativity).
Notation "↑f⊥ f"  := (↑⊥ (↑f f)) (at level 1, left associativity).
Notation "↑p⊥ p"  := (↑⊥ (↑p p)) (at level 1, left associativity).

Lemma SmashLemmaValVal :
  forall A B (d : A _BOT) (d' : B _BOT)
    (v : A) (v' : B),
    d =-= ↑⊥ v /\ d' =-= ↑⊥ v' ->
    (((Smash A B) d) d') =-= ↑⊥ (v , v').
Proof.
  intros A B d d' v v' H.
  inversion H. unfold Smash.
  rewrite -> H0. rewrite -> H1.
  simpl. by rewrite -> Operator2_simpl.
Qed.

Lemma StepLemma :
  forall {A B C} (f : cpoCatType (A * B) C) (g : cpoCatType A B),
    (ev << <| exp_fun f , g |>) =-= f <<  <| Id , g |>.
Proof.
  intros A B C f g.
  assert (Fid : exp_fun f =-= exp_fun f << Id) by
      (rewrite -> comp_idR; reflexivity).
  assert (Gid : g =-= Id << g) by
      (rewrite -> comp_idL; reflexivity).
  rewrite -> Fid at 1 ; 
    rewrite -> Gid at 1.
  rewrite -> prod_fun_compr.
  rewrite -> comp_assoc.
    by rewrite exp_com.
Qed.

Lemma SemVal_VAR_equation : forall (E : Env) (η : SemEnv E) (v : Var E),
    SemV (VAR v) η =-= SemVar v η.
Proof.
  intros E η v. by unfold SemV.
Qed.

Lemma SemVal_FUN_equation : forall (E : Env) (η : SemEnv E) (e : Expr E.+1),
    ⟦ FUN e ⟧v η =-= ↑f ((F ⟦e ⟧e) η).
Proof.
  intros E η e.
  unfold "⟦ _ ⟧v" at 1. fold ⟦ e ⟧e.
  rewrite -> comp_simpl.
  eapply tset_trans. apply tset_refl.
  auto.
Qed.

Lemma SemExp_VAL_equation : forall (E : Env) (η : SemEnv E) (v : V E),
    ⟦ VAL v ⟧e η =-= ↑⊥ (⟦ v ⟧v η).
Proof.
  by simpl.
Qed.

Lemma SmashLemma_Bot :
  forall A B (d : A _BOT) (d' : B _BOT),
    d =-= ⊥ \/ d' =-= ⊥ ->
    (((Smash A B) d) d') =-= ⊥.
Proof.
  intros A B d d' H.
  inversion H.
  - (* Case "d =-= ⊥". *)
    unfold Smash.
    rewrite -> H0.
    by rewrite -> Operator2_strictL.
  - (* Case "d' =-= ⊥". *)
    unfold Smash.
    rewrite -> H0.
    by rewrite -> Operator2_strictR.
Qed.

Lemma VInfToBool_prop : forall (vb : VInf) (b : bool),
    VInfToBool vb =-= Val b -> vb =-= inNat (B_to_N b).
Proof.
  intros vb b H.
  destruct vb as [[n | f] | p].
  destruct n. do 2 setoid_rewrite -> SUM_fun_simplx in H.
  simpl in H. apply vinj with (D:=bool_cpoType) in H.
  rewrite <- H. by simpl.
  destruct n. do 2 setoid_rewrite -> SUM_fun_simplx in H.
  simpl in H. apply vinj with (D:=bool_cpoType) in H.
  rewrite <- H. by simpl.
  do 2 setoid_rewrite -> SUM_fun_simplx in H.
  simpl in H. symmetry in H. apply PBot_incon_eq in H. inversion H.
  do 2 setoid_rewrite -> SUM_fun_simplx in H.
  simpl in H. symmetry in H. apply PBot_incon_eq in H. inversion H.
  setoid_rewrite -> SUM_fun_simplx in H.
  simpl in H. symmetry in H. apply PBot_incon_eq in H. inversion H.
Qed.

Lemma SemVal_FUN_equation2 : forall (E : Env) (η : SemEnv E) (e : Expr E.+1),
    ⟦ λ e ⟧v η =-= inFun (F ⟦e ⟧e η).
Proof.
  intros E η e.
  auto.
Qed.

Lemma VInfToNat_Nat : (VInfToNat << inNat) =-= eta.
Proof.
  rewrite comp_assoc. by do 2 setoid_rewrite -> sum_fun_fst.
Qed.

Lemma VInfToFun_Fun : (VInfToFun << inFun) =-= eta.
Proof.
  rewrite comp_assoc. setoid_rewrite -> sum_fun_fst.
    by setoid_rewrite -> sum_fun_snd.
Qed.

(* Fixpoint R (E: Env) (v: VInf _BOT) : Expr E.
  destruct v as [[n | f] | p].
  Focus 2.
  Check f (Roll (inNat E)).
  exact (VAL (FUN (R E.+1 (f (Roll (inNat E)))))).
  (* match v with
  | inFun f => VAL (FUN (R E.+1 (f (eta (ZVAR _)))))
  | inPair p => VAL (VAR (ZVAR _))
  | PBot => VAL (VAR (ZVAR _))
  end. *) *)
