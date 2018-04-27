(** Exercise sheet for lecture 4: Tactics in Coq.

Written by Ralph Matthes.
 *)

(** * Exercise 1
Formalize the solutions of exercise 1 of Lecture 1.

[[
For each of the following types, write down an element of that type, if it has one. If it does not have any elements, you should establish that this is the case. But first think how this can be done in type theory! It ought to be just another construction.

1.    A × (B + C) → A × B + A × C, given types A, B, C
2.    (A → A) → (A → A), given type A (for extra credit, write down five elements of this type)
3.    Id_nat (0, succ 0)
4.    ∑ (A : Universe) (A → empty) → empty
5.    ∏ (n : nat), ∑ (m : nat), (n = 2 * m) + (n = 2 * m + 1), assuming you have got arithmetic
6.    (∑ (x : A) B × P x) → B × ∑ (x : A) P x, given types A, B, and P : A → Universe
7.    B → (B → A) → A, given types A and B
8.    B → ∏ (A : Universe) (B → A) → A, given type B
9.    (∏ (A : Universe) (B → A) → A) → B, given type B
]]

For the present exercise, this means: state the formula as a lemma, give a proof interactively if there is a proof, and give a counter-example otherwise, i.e., give specific parameters and a proof of the negation of the statement.

More precise instructions and hints:

1. Use ⨿ in place of the + and pay attention to operator precedence.

2. Write a function that provides different elements for any natural number argument, not just five elements; for extra credits: state correctly that they are different - for a good choice of [A]; for more extra credits: prove that they are different.

3. An auxiliary function may be helpful - better recall the trick.

4. The symbol for Sigma-types is ∑, not Σ.

5. Same as 1; and there is need for module UniMath.Foundations.NaturalNumbers, e.g., for Lemma natpluscomm.

6.-9. no further particulars
*)

Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.NaturalNumbers.



(** * Exercise 2
Define two computable strict comparison operators for natural numbers based on the fact that m < n iff
n - m <> 0 iff (m+1) - n = 0. Prove that the two operators are equal (using function extensionality, i.e., [funextfunStatement] in the UniMath library).

It may be helpful to use the definitions of the exercises for lecture 2. The following lemmas on substraction sub in the natural numbers may be useful:

a) sub n (S m) = pred (sub n m)

b) sub 0 n = 0

c) pred (sub 1 n) = 0

d) sub (S n) (S m) = sub n m

*)


(** from exercises to Lecture 2: *)
Definition ifbool (A : UU) (x y : A) : bool -> A :=
  bool_rect (λ _ : bool, A) x y.

Definition negbool : bool -> bool := ifbool bool false true.

Definition nat_rec (A : UU) (a : A) (f : nat -> A -> A) : nat -> A :=
  nat_rect (λ _ : nat, A) a f.

Definition pred : nat -> nat := nat_rec nat 0 (fun x _ => x).

Definition is_zero : nat -> bool := nat_rec bool true (λ _ _, false).

Definition iter (A : UU) (a : A) (f : A → A) : nat → A :=
  nat_rec A a (λ _ y, f y).

Notation "f ̂ n" := (λ x, iter _ x f n) (at level 10).

Definition sub (m n : nat) : nat := pred ̂ n m.
