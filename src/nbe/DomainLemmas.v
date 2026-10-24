(*begin hide*)

Require Import Utils.
Require Import Program.

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
(*** Domain-level congruence and reduction lemmas ***)
(** *)

(* Stream-level congruence of Val *)
Lemma StreamVal_eq (D : ordType) (x y : D) :
    x =-= y -> (Val x) =-= (Val y).
Proof.
  case => [l1 l2].
  split.
  - apply (@DLleVal _ x y 0 (Val y)) => //.
  - apply (@DLleVal _ y x 0 (Val x)) => //.
Qed.

(* congruence for the locked kleisli layer *)
Lemma kleisli_eq_arg (D0 D1 : cpoType) (g : D0 =-> D1 _BOT) (x y : D0 _BOT) :
    x =-= y -> kleisli g x =-= kleisli g y.
Proof.
  move => H. split.
  - apply (fmonotonic (kleisli g) (proj1 H)).
  - apply (fmonotonic (kleisli g) (proj2 H)).
Qed.

(* congruence for the stream-kleisli extension of a thunk *)
Lemma KLEISLI_eq_arg (D0 D1 : cpoType) (r : D0 -=> D1 _BOT) (x y : D0 _BOT) :
    x =-= y -> KLEISLI r x =-= KLEISLI r y.
Proof.
  move => H. split.
  - apply (fmonotonic (KLEISLI r) (proj1 H)).
  - apply (fmonotonic (KLEISLI r) (proj2 H)).
Qed.

(* applying the stream-kleisli extension of a thunk to a value
   (generalized to arbitrary cpoTypes; no syntax dependency) *)
Lemma KLEISLI_etaVal (D0 D1 : cpoType) (r : D0 -=> D1 _BOT) (d : D0) :
    KLEISLI r (eta d) =-= r d.
Proof.
  rewrite -> eta_val.
  change (kleisli r (Val d) =-= r d).
  by rewrite -> kleisliVal.
Qed.

Lemma kleisli_eta (D0 D1 : cpoType) (f : D0 =-> D1 _BOT) (d : D0) :
    kleisli f (eta d) =-= f d.
Proof.
  rewrite -> eta_val. by rewrite -> kleisliVal.
Qed.
