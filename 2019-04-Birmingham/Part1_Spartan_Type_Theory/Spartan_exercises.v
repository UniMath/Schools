Require Import UniMath.Foundations.PartD.

Axiom fill_me : forall {X : UU}, X. (* Remove this line when you are finished. *)

(** Exercise 1.1. A × (B + C) → A × B + A × C, given types A, B, C *)

Definition exercise_1_1 (A B C : UU)
  : A × (B ⨿ C) → (A × B) ⨿ (A × C) := fill_me.

(** Exercise 1.2. (A → A) → (A → A), given type A

    for extra credit, write down *five* elements of this type *)

Definition exercise_1_2 (A : UU)
  : (A → A) → (A → A)
  := fill_me.

(** Exercise 1.3. Id_nat (0, succ 0) → empty *)

Theorem exercise_1_3 : (0 = 1) → empty.
Proof.
  exact fill_me.
Qed.

(** Exercise 1.4. ∑ (A : Universe) (A → empty) *)

Theorem exercise_1_4 : ∑ A:UU, (A → empty).
Proof.
  exact fill_me.
Qed.

(** Exercise 1.6. (∑ (x : A) B × P x) → B × ∑ (x : A) P x,
                  given types A, B, and P : A → Universe *)

Theorem exercise_1_6 (A B:UU) (P:A → UU) : (∑ x:A, B × P x) → B × ∑ x:A, P x.
Proof.
  exact fill_me.
Qed.

(** Exercise 1.7. B → (B → A) → A, given types A and B *)

Theorem exercise_1_7 (A B : UU) : B → (B → A) → A.
Proof. exact fill_me. Qed.

(** Exercise 1.8. B → ∏ (A : Universe) (B → A) → A, given type B *)

Theorem exercise_1_8 (B : UU) : B → ∏ A:UU, (B → A) → A.
Proof. exact fill_me. Qed.

(** Exercise 1.9. (∏ (A : Universe) (B → A) → A) → B, given type B *)

Theorem exercise_1_9 (B : UU) : (∏ A:UU, (B → A) → A) → B.
Proof. exact fill_me. Qed.

(** Exercise 2.1. Using the basic rules, construct addition on natural numbers. *)

Definition nat_plus : nat → nat → nat := fill_me.

(** Exercise 2.2. State associativity and commutativity of addition in a type-theoretic way. *)

Definition exercise_2_2_assoc : UU := fill_me.

Definition exercise_2_2_comm : UU := fill_me.

(** Exercise 2.3. Establish associativity and commutativity of addition. What does this mean in type theory? *)

Theorem nat_plus_is_assoc : exercise_2_2_assoc.
Proof.
  exact fill_me.
Qed.

Theorem nat_plus_is_comm : exercise_2_2_comm.
Proof.
  exact fill_me.
Qed.

(** Exercise 3. Write down the following types:

    1. even natural numbers *)

Definition exercise_3_1 : UU := fill_me.

(** 2. prime numbers *)

Definition nat_mult : nat → nat → nat := fill_me.

Definition exercise_3_2 : UU := fill_me.

(** 3. functions A → nat which attain zero *)

Definition exercise_3_3 (A : UU) : UU := fill_me.

(** 4. the "less than" relation on natural numbers *)

Definition exercise_3_4 (n m : nat) : UU := fill_me.
