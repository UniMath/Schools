Require Import UniMath.Foundations.PartD.

(** Exercise 1.1. A × (B + C) → A × B + A × C, given types A, B, C *)

Definition exercise_1_1 (A B C : UU)
  : A × (B ⨿ C) → (A × B) ⨿ (A × C) :=
  λ p, coprod_rect
    (λ _, (A × B) ⨿ (A × C))
    (fun b => ii1 (pr1 p,,b))
    (fun c => ii2 (pr1 p,,c))
    (pr2 p).

(** Exercise 1.2. (A → A) → (A → A), given type A

    for extra credit, write down *five* elements of this type *)

Definition exercise_1_2_def0 (A : UU)
  : (A → A) → (A → A)
  := λ _ x, x. (* 0 *)

Definition exercise_1_2_def1 (A : UU)
  : (A → A) → (A → A)
  := λ f, f ∘ f. (* 2 *)

Definition exercise_1_2_def2 (A : UU)
  : (A → A) → (A → A)
  := λ f, exercise_1_2_def1 A (f ∘ f). (* 4 *)

Definition exercise_1_2_def3 (A : UU)
  : (A → A) → (A → A)
  := λ f, f ∘ exercise_1_2_def2 A f ∘ f. (* 6 *)

Definition exercise_1_2_def4 (A : UU)
  : (A → A) → (A → A)
  := exercise_1_2_def3 A ∘ exercise_1_2_def2 A ∘ exercise_1_2_def1 A. (* 48 *)

(** Exercise 1.3. Id_nat (0, succ 0) → empty *)

Theorem exercise_1_3 : (0 = 1) → empty.
Proof.
  exact (λ p, transportf (nat_rect (λ _, UU) unit (λ _ _, empty)) p tt).
Qed.

(** Exercise 1.4. ∑ (A : Universe) (A → empty) *)

Theorem exercise_1_4 : ∑ A:UU, (A → empty).
Proof.
  exact (empty ,, λ x, x).
Qed.

(** Exercise 1.6. (∑ (x : A) B × P x) → B × ∑ (x : A) P x,
                  given types A, B, and P : A → Universe *)

Theorem exercise_1_6 (A B:UU) (P:A → UU) : (∑ x:A, B × P x) → B × ∑ x:A, P x.
Proof.
  exact (λ p, (pr1 (pr2 p) ,, (pr1 p ,, pr2 (pr2 p)))).
Qed.

(** Exercise 1.7. B → (B → A) → A, given types A and B *)

Theorem exercise_1_7 (A B : UU) : B → (B → A) → A.
Proof. exact (λ b f, f b). Qed.

(** Exercise 1.8. B → ∏ (A : Universe) (B → A) → A, given type B *)

Theorem exercise_1_8 (B : UU) : B → ∏ A:UU, (B → A) → A.
Proof. exact (λ b A f, f b). Qed.

(** Exercise 1.9. (∏ (A : Universe) (B → A) → A) → B, given type B *)

Theorem exercise_1_9 (B : UU) : (∏ A:UU, (B → A) → A) → B.
Proof. exact (λ f, f B (λ a, a)). Qed.

(** Exercise 2.1. Using the basic rules, construct addition on natural numbers. *)

Definition nat_plus : nat → nat → nat :=
  nat_rect (λ _, nat → nat) (λ n, n) (λ _ p n, S (p n)).

(** Exercise 2.2. State associativity and commutativity of addition in a type-theoretic way. *)

Definition exercise_2_2_assoc : UU :=
  forall m n o, nat_plus (nat_plus m n) o = nat_plus m (nat_plus n o).

Definition exercise_2_2_comm : UU :=
  forall m n, nat_plus m n = nat_plus n m.

(** Exercise 2.3. Establish associativity and commutativity of addition. What does this mean in type theory? *)

Theorem nat_plus_is_assoc : exercise_2_2_assoc.
Proof.
  exact
    (nat_rec
       (λ m, forall n o,
           nat_plus (nat_plus m n) o
         = nat_plus m (nat_plus n o))
       (λ _ _, idpath _)
       (λ m IHm n o, maponpaths S (IHm n o))).
Qed.

Theorem nat_plus_S : forall m n, nat_plus m (S n) = S (nat_plus m n).
Proof.
  exact
    (nat_rect
       (λ m, forall n, nat_plus m (S n) = S (nat_plus m n))
       (λ _, idpath _)
       (λ _ IHm n, maponpaths S (IHm _))).
Qed.

Theorem nat_plus_is_comm : exercise_2_2_comm.
Proof.
  exact
    (nat_rec
       (λ m, forall n, nat_plus m n = nat_plus n m)
       (nat_rec
          (λ n, n = nat_plus n 0)
          (idpath 0)
          (λ n IHn, maponpaths S IHn))
       (λ m IHm n, maponpaths S (IHm n) @ ! nat_plus_S n m)).
Qed.

(** Exercise 3. Write down the following types:

    1. even natural numbers *)

Definition bool_to_rel (b : bool) := if b then unit else empty.

Definition evenb : nat → bool := nat_rect (λ _, bool) true (λ _ b, if b then false else true).

Definition exercise_3_1 : UU := ∑ n, bool_to_rel (evenb n).

(** 2. prime numbers *)

Definition nat_mult : nat → nat → nat :=
  nat_rec (λ _, nat → nat) (λ _, 0) (λ _ IHm n, nat_plus n (IHm n)).

Definition is_prime : nat → UU :=
  λ n, ∑ _:((n = 1) → empty), (∏ m1 m2, nat_mult m1 m2 = n → (m1 = 1) ⨿ (m2 = 1)).

Definition exercise_3_2 : UU := ∑ n, is_prime n.

(** 3. functions A → nat which attain zero *)

Definition exercise_3_3 (A : UU) : UU := ∑ f:A → nat, ∑ a, f a = 0.

(** 4. the "less than" relation on natural numbers *)

Definition lessb : nat → nat → bool :=
  nat_rect
    (λ _, nat → bool)
    (nat_rect (λ _, bool) false (λ _ _, true))
    (λ n IHn,
       nat_rect (λ _, bool) false
                (λ m _, IHn m)).

Definition exercise_3_4 (n m : nat) : UU := bool_to_rel (lessb n m).
