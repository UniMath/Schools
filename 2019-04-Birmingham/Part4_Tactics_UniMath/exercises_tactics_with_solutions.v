(** Exercise sheet for lecture 4: Tactics in Coq.

This is the material for the advisors with solutions.

Written by Ralph Matthes (CNRS, IRIT, Univ. Toulouse, France).
*)

(** * Exercise 1
Formalize the solutions of exercise 1 of Lecture 1.

[[
For each of the following types, write down an element of that type, if it has one. If it does not have any elements, you should establish that this is the case. But first think how this can be done in type theory! It ought to be just another construction.

1.    A × (B + C) → A × B + A × C, given types A, B, C
2.    (A → A) → (A → A), given type A (for extra credit, write down five elements of this type)
3.    Id_nat (0, succ 0)
4.    ∑ (A : Universe) (A → empty) → empty
5.    ∏ (n : nat), ∑ (m : nat), Id_nat n (2 * m) + Id_nat n (2 * m + 1), assuming you have got arithmetic
6.    (∑ (x : A) B × P x) → B × ∑ (x : A) P x, given types A, B, and P : A → Universe
7.    B → (B → A) → A, given types A and B
8.    B → ∏ (A : Universe) (B → A) → A, given type B
9.    (∏ (A : Universe) (B → A) → A) → B, given type B
]]

For the present exercise, this means: state the formula as a lemma, give a proof interactively if there is a proof, and give a counter-example otherwise, i.e., give specific parameters and a proof of the negation of the statement.

More precise instructions and hints:

1. Use [⨿] in place of the + and pay attention to operator precedence.

2. Write a function that provides different elements for any natural number argument, not just five elements; for extra credits: state correctly that they are different - for a good choice of [A]; for more extra credits: prove that they are different.

3. An auxiliary function may be helpful - better recall the trick.

4. The symbol for Sigma-types is [∑], not [Σ].

5. Same as 1; and there is need for module [UniMath.Foundations.NaturalNumbers], e.g., for Lemma [natpluscomm].

6.-9. no further particulars
*)

Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Foundations.PartA.

Lemma Exo1_1 (A B C: UU): A × (B ⨿ C) → (A × B) ⨿ (A × C).
Proof.
  intro H123.
  induction H123 as [H1 H23].
  induction H23 as [H2 | H3].
  - apply ii1.
    apply make_dirprod.
    + exact H1.
    + exact H2.
  - apply ii2.
    apply make_dirprod.
    + exact H1.
    + exact H3.
Defined.


Lemma Exo1_2 (A: UU)(n: nat): (A → A) → (A → A).
Proof.
  intros f a.
  induction n as [| _ IH].
  - exact a.
  - exact (f IH).
Defined.

(** of course, the iterator of lecture 2 could be used here *)

Lemma Exo1_2_bonus (n1 n2: nat): ¬ (n1 = n2) -> ¬ (Exo1_2 nat n1 = Exo1_2 nat n2).
Proof.
  intros Hypn Hyp.
  assert (H1: Exo1_2 nat n1 S 0 = Exo1_2 nat n2 S 0).
  { rewrite Hyp.
    apply idpath.
  }
  assert (H2: ∏ n:nat, Exo1_2 nat n S 0 = n).
  { induction n.
    - apply idpath.
    - cbn.
      apply maponpaths.
      exact IHn.
  }
  rewrite H2 in H1.
  rewrite H2 in H1.
  apply Hypn.
  exact H1.
Defined.


(** counter-example needed - this is difficult to invent *)
Lemma Exo1_3: ¬ (0 = S 0).
Proof.
  intro H.
  apply nopathstruetofalse.
  set (aux := nat_rect (λ _ : nat, bool) true (λ _ _, false)).
  assert (H1: aux 0 = aux 1).
  { rewrite <- H.
    reflexivity.
  }
  cbn in H1.
  exact H1.
Defined.


Lemma Exo1_4: ∑ (A: UU), ( A -> ∅ ) -> ∅.
Proof.
  use tpair.
  - exact unit.
  - cbn.
    intro H.
    apply H.
    exact tt.
Defined.

Require Import UniMath.Foundations.NaturalNumbers.

Lemma Exo1_5 (n: nat): ∑ m:nat, (n = 2 * m) ⨿ (n = 2 * m + 1).
Proof.
  induction n as [| n IHn].
  - exists 0.
    apply ii1.
    apply idpath.
  - induction IHn as [m H].
    induction H as [H1 | H2].
    + exists m.
      apply ii2.
      rewrite H1.
      rewrite natpluscomm.
      apply idpath.
    + exists (S m).
      apply ii1.
      rewrite H2.
      rewrite natpluscomm.
      rewrite natmultcomm.
      cbn.
      rewrite natpluscomm.
      cbn.
      rewrite natmultcomm.
      apply idpath.
Defined.


Lemma Exo1_6 (A B: UU)(P: A -> UU): (∑ (x : A), B × P x) → B × ∑ (x : A), P x.
Proof.
  intro H.
  induction H as [x H12].
  induction H12 as [H1 H2].
  apply make_dirprod.
  - exact H1.
  - exists x.
    exact H2.
Defined.


Lemma Exo1_7 (A B: UU): B → (B → A) → A.
Proof.
  intros b f.
  exact (f b).
Defined.


Lemma Exo1_8 (B: UU): B → ∏ (A : UU), (B → A) → A.
Proof.
  intros b ? f.
  exact (f b).
Defined.


Lemma Exo1_9 (B: UU): (∏ (A : UU), (B → A) → A) → B.
Proof.
  intro H.
  apply H.
  intro b.
  exact b.
Defined.

(** * Exercise 2
Define two computable strict comparison operators for natural numbers based on the fact
that [m < n] iff [n - m <> 0] iff [(m+1) - n = 0]. Prove that the two operators are
equal (using function extensionality, i.e., [funextfunStatement] in the UniMath library).

It may be helpful to use the definitions of the exercises for lecture 2.
The following lemmas on substraction [sub] in the natural numbers may be
useful:

a) [sub n (S m) = pred (sub n m)]

b) [sub 0 n = 0]

c) [pred (sub 1 n) = 0]

d) [sub (S n) (S m) = sub n m]

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

(** new material: *)

Definition ltnat1 (m n : nat) : bool := is_zero (sub (S m) n).
Definition ltnat2 (m n : nat) : bool := negbool (is_zero (sub n m)).

(** the helper lemmas : *)
Lemma Exo2_aux1 (n m: nat) : sub n (S m) = pred (sub n m).
Proof.
  apply idpath.
Defined.

Lemma Exo2_aux2 (n: nat) : sub 0 n = 0.
Proof.
  induction n as [| n IHn].
  + apply idpath.
  + cbn.
    change (iter nat 0 pred n) with (sub 0 n).
    rewrite IHn.
    apply idpath.
Defined.

Lemma Exo2_aux3 (n: nat) : pred (sub 1 n) = 0.
Proof.
  induction n as [| n IHn].
  + cbn.
    apply idpath.
  + cbn.
    fold (sub 1 n).
    rewrite IHn.
    cbn.
    apply idpath.
Defined.

Lemma Exo2_aux4 (n m: nat) : sub (S n) (S m) = sub n m.
Proof.
  induction m as [| m IHm].
  - apply idpath.
  - rewrite (Exo2_aux1 (S n) (S m)).
    rewrite (Exo2_aux1 n m).
    apply maponpaths.
    exact IHm.
Defined.

(** the exercise itself: *)
Lemma Exo2: ltnat1 = ltnat2.
Proof.
  apply funextfun.
  intro m.
  induction m as [| m IHm].
  - apply funextfun.
    intro n.
    induction n as [| n IHn].
    + apply idpath.
    + cbn.
      fold (sub 1 n).
      rewrite Exo2_aux3.
      apply idpath.
  - apply funextfun.
    intro n.
    induction n as [ | n1 IHn1].
    + cbn.
      unfold ltnat2.
      rewrite Exo2_aux2.
      apply idpath.
    + unfold ltnat1, ltnat2.
      rewrite Exo2_aux4.
      rewrite Exo2_aux4.
      change (ltnat1 m n1 = ltnat2 m n1).
      rewrite IHm.
      apply idpath.
Defined.
