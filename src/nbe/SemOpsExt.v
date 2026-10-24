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
Require Import SemOps.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Include RD.
(*end hide*)

(** *Value-domain operators not used by the simple language (kept for extensions) *)

Definition mod2 (n : nat) : nat_cpoType :=
  PeanoNat.Nat.modulo n 2.

Definition MOD2 : nat_cpoType =-> nat_cpoType := SimpleUOp mod2.

Definition VInfToBool : VInf -=> bool_cpoType _BOT :=
  [| [| N_to_B , const _ ⊥ |] , const _ ⊥ |].

Definition VInfToNat : VInf -=> nat_cpoType _BOT :=
  [| [| eta , const _ ⊥ |] , const _ ⊥ |].

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
  SemEnv E =-> VInf _BOT := d1 << <| Id, d2 |>   (* CBN let (ISSUE-024) *)
.

Definition LetAppDInf (E : Env)
           (d1 : SemEnv E.+1 =-> VInf _BOT)
           (d2 : SemEnv E =-> VInf _BOT) :=
  KR << d1 << <| Id, d2 |>.

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

Lemma VInfToNat_Nat : (VInfToNat << inNat) =-= eta.
Proof.
  rewrite comp_assoc. by do 2 setoid_rewrite -> sum_fun_fst.
Qed.
