(** Solutions to exercise sheet for lecture 2: Fundamentals of Coq. 

Note that these are just suggestions for solutions and many of the
problems can have different solutions. Once you know how to prove
things in Coq you can try to prove that your solutions are equivalent
to the ones in this file.

Written by Anders Mörtberg.

*)
Require Import UniMath.Foundations.Preamble.
Require Import fundamentals_lecture.

Definition idfun : forall (A : UU), A -> A := fun (A : UU) (a : A) => a.

Definition const (A B : UU) (a : A) (b : B) : A := a.

(** * Booleans *)

Definition ifbool (A : UU) (x y : A) : bool -> A :=
  bool_rect (fun _ : bool => A) x y.

Definition negbool : bool -> bool :=
  ifbool bool false true.

Definition andbool (b : bool) : bool -> bool :=
  ifbool (bool -> bool) (idfun bool) (const bool bool false) b.

(** Exercise: define boolean or: *)

Definition orbool (b : bool) : bool -> bool :=
  ifbool (bool -> bool) (const bool bool true) (idfun bool) b.

Eval compute in orbool true true.     (* true *)
Eval compute in orbool true false.    (* true *)
Eval compute in orbool false true.    (* true *)
Eval compute in orbool false false.   (* false *)

(** * Natural numbers *)

Definition nat_rec (A : UU) (a : A) (f : nat -> A -> A) : nat -> A :=
  nat_rect (fun _ : nat => A) a f.

Definition even : nat -> bool := nat_rec bool true (fun _ b => negbool b).

(** Exercise: define a function odd that tests if a number is odd *)
Definition odd : nat -> bool :=
  nat_rec bool false (fun _ b => negbool b).

Eval compute in odd 24.    (* false *)
Eval compute in odd 19.   (* true *)


(** Exercise: define a notation "myif b then x else y" for "ifbool _ x y b"
and rewrite negbool and andbool using this notation. *)

Notation "'myif' b 'then' x 'else' y" := (ifbool _ x y b) (at level 1).

Definition negbool' (b : bool) : bool := myif b then false else true.

(* Check that negbool' uses ifbool by disabling printing of notations *)
Unset Printing Notations.
Print negbool'.
Set Printing Notations.

Eval compute in negbool' true.   (* false *)
Eval compute in negbool' false.  (* true *)

Definition andbool' (b1 b2 : bool) : bool :=
  myif b1 then b2 else false.

Eval compute in andbool true true.    (* true *)
Eval compute in andbool true false.   (* false *)
Eval compute in andbool false true.   (* false *)
Eval compute in andbool false false.  (* false *)


Definition add (m : nat) : nat -> nat := nat_rec nat m (fun _ y => S y).

Definition iter (A : UU) (a : A) (f : A → A) : nat → A :=
  nat_rec A a (λ _ y, f y).

Notation "f ̂ n" := (λ x, iter _ x f n) (at level 10).

Definition sub (m n : nat) : nat := pred ̂ n m.

(** Exercise: define addition using iter and S *)
Definition add' (m : nat) : nat → nat :=
  iter nat m S.

Eval compute in add' 4 9.   (* 13 *)

Definition is_zero : nat -> bool := nat_rec bool true (fun _ _ => false).

Definition eqnat (m n : nat) : bool :=
  andbool (is_zero (sub m n)) (is_zero (sub n m)).

Notation "m == n" := (eqnat m n) (at level 30).

(** Exercises: define <, >, ≤, ≥  *)

Definition ltnat (m n : nat) : bool := is_zero (sub (S m) n).

Notation "x < y" := (ltnat x y).

Eval compute in (2 < 3). (* true *)
Eval compute in (3 < 3). (* false *)
Eval compute in (4 < 3). (* false *)


Definition gtnat (m n : nat) : bool := n < m.

Notation "x > y" := (gtnat x y).

Eval compute in (2 > 3). (* false *)
Eval compute in (3 > 3). (* false *)
Eval compute in (4 > 3). (* true *)


Definition leqnat (m n : nat) : bool := orbool (m < n) (m == n).

Notation "x ≤ y" := (leqnat x y) (at level 10).

Eval compute in (2 ≤ 3). (* true *)
Eval compute in (3 ≤ 3). (* true *)
Eval compute in (4 ≤ 3). (* false *)


Definition geqnat (m n : nat) : bool := orbool (m > n) (m == n).

Notation "x ≥ y" := (geqnat x y) (at level 10).

Eval compute in (2 ≥ 3). (* false *)
Eval compute in (3 ≥ 3). (* true *)
Eval compute in (4 ≥ 3). (* true *)


Definition coprod_rec {A B C : UU} (f : A → C) (g : B → C) : A ⨿ B → C :=
  @coprod_rect A B (λ _, C) f g.


Definition Z : UU := nat ⨿ nat.

Notation "⊹ x" := (inl x) (at level 20).
Notation "─ x" := (inr x) (at level 40).

Definition Z1 : Z := ⊹ 1.
Definition Z0 : Z := ⊹ 0.
Definition Zn3 : Z := ─ 2.

Definition Zcase (A : UU) (fpos : nat → A) (fneg : nat → A) : Z → A :=
  coprod_rec fpos fneg.

Definition negate : Z → Z :=
  Zcase Z (λ x, ifbool Z Z0 (─ pred x) (is_zero x)) (λ x, ⊹ S x).

(* Exercise (harder): define addition for Z *)

Definition Zadd : Z -> Z -> Z :=
  Zcase (Z → Z)
        (λ posn : nat,
           Zcase Z
                 (λ posm : nat, ⊹ (posn + posm))
                 (λ negm : nat,
                    myif posn ≥ negm then ⊹ (posn - negm)
                                      else (─ (negm - posn))))
        (λ negn : nat,
           Zcase Z
                 (λ posm : nat,
                    myif posm ≥ negn then ⊹ (posm - negn)
                                      else (─ (negn - posm)))
                 (λ negm : nat, ─ (S negn + negm))).

(* This should satisfy *)
Eval compute in Zadd Z0 Z0.   (* ⊹ 0 *)
Eval compute in Zadd Z1 Z1.   (* ⊹ 2 *)
Eval compute in Zadd Z1 Zn3.  (* ─ 1 *) (* recall that negative numbers are off-by-one *)
Eval compute in Zadd Zn3 Z1.  (* ─ 1 *)
Eval compute in Zadd Zn3 Zn3. (* ─ 5 *)
Eval compute in Zadd (Zadd Zn3 Zn3) Zn3. (* ─ 8 *)
Eval compute in Zadd Z0 (negate (Zn3)). (* ⊹ 3 *)

