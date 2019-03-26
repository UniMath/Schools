(* Exercises on Category Theory in UniMath *)
(* for lecture by Peter LeFanu Lumsdaine, Thu 2017-12-14 *)
(* School and Workshop on Univalent Maths, Birmingham 2017 *)
(* https://unimath.github.io/bham2017/ *)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.FinOrdProducts.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Monads.Monads.


(* NOTE: some of these exercises (or parts of them) are straightforward, while other parts are intended to be quite difficult.  So I don’t recomment aiming to complete them in order — if stuck on a difficult part, move on and come back for another attempt later!

Skeleton solutions and hints are provided, to exhibit good tools and techniques for working with categories.  However, you may well want to add extra definitions/lemmas besides the ones suggested in the skeleton. *)

Section Exercise_0.
(** Univalent categories

  Show that in any univalent category, the type of objects has h-level 3 *)

  Proposition isofhlevel3_ob_of_univalent_cat (C : category) (H : is_univalent C)
    : isofhlevel 3 (ob C).
  Proof.
  Admitted.

End Exercise_0.

Section Exercise_1.
(** Non-univalent categories

  Problem: Construct the category with objects the natural numbers, and with maps m->n all functions {1,…,m}->{1,…,n}.  Show that this is a set-category, and that it is NOT univalent.

  Hint: for defining categories (and other large multi-component structures), it’s usually better to define them a few components at a time, following the structure of the definition, as the following skeleton suggests.

  An alternative approach is to go directly for the total structure [Definition nat_category : category], then begin with [use makecategory.] and construct the whole thing in a single interactive proof.  This approach can be good for first finding a proof/construction; but it often causes speed issues down the line, because the resulting term is very large. *)

  Definition nat_category_ob_mor : precategory_ob_mor.
  Proof.
  Admitted.

  Definition nat_category_data : precategory_data.
  Proof.
  Admitted.

  Definition nat_category_is_precategory : is_precategory nat_category_data.
  Proof.
  Admitted.

  Definition nat_category : category.
  Proof.
  Admitted.

  Definition nat_setcategory : setcategory.
  Proof.
  Admitted.

  Proposition nat_category_not_univalent : ¬ (is_univalent nat_category).
  Proof.
  Admitted.

End Exercise_1.

Section Exercise_2.
  (* Exercise 2.1: Define `pointed_disp_cat` with `disp_struct`. *)
  Definition pointed_disp_cat
  : disp_cat SET.
  Proof.
  Admitted.

  (** Exercise 2.2: Define a displayed category on sets of a binary operation on them.
      The displayed objects over `X` are maps `X × X → X` and the displayed morphisms over `f` are proofs that `f` preserves the operation.
   *)
  Definition operation_disp_cat
    : disp_cat SET.
  Proof.
  Admitted.

  (** Using the product of displayed categories, we now define *)
  Definition pointed_operation_disp_cat
    : disp_cat SET.
  Proof.
    use dirprod_disp_cat.
    - exact pointed_disp_cat.
    - exact operation_disp_cat.
  Defined.

  (** This gives rise to a total category *)
  Definition pointed_operation_set
    : category
    := total_category pointed_operation_disp_cat.

  (** For convenience, we define some projection to access the structure *)
  Definition carrier
             (X : pointed_operation_set)
    : hSet
    := pr1 X.

  Definition unit_el
             (X : pointed_operation_set)
    : carrier X
    := pr12 X.

  Definition mul
             (X : pointed_operation_set)
    : carrier X → carrier X → carrier X
    := λ x y, pr22 X (x ,, y).

  (** Exercise 2.3: Define the category of monoid displayed category.
      Hint: use `disp_full_sub`.
   *)
  Definition monoid_laws_disp_cat
    : disp_cat pointed_operation_set.
  Proof.
  Admitted.

  Definition monoids
    : category
    := total_category monoid_laws_disp_cat.

  (** During the lecture, we already showed that pointed sets are univalent. We used this proof. *)
  Definition pointed_is_univalent_disp
    : is_univalent_disp pointed_disp_cat.
  Proof.
    apply is_univalent_disp_from_fibers.
    intros X x₁ x₂.
    use isweqimplimpl.
    - intros f.
      apply f.
    - apply X.
    - apply isaproptotal2.
      + intro.
        apply isaprop_is_iso_disp.
      + intros p q r₁ r₂.
        apply X.
  Defined.

  (* Exercise 2.4: Show that each part gives rise to a displayed univalent category and conclude that the total category is univalent.
     Hint: adapt the proof from the lecture notes.
   *)
  Definition operation_is_univalent_disp
    : is_univalent_disp operation_disp_cat.
  Proof.
    apply is_univalent_disp_from_fibers.
  Admitted.

  (** Now we conclude *)
  Definition pointed_operation_is_univalent_disp
    : is_univalent_disp pointed_operation_disp_cat.
  Proof.
    use dirprod_disp_cat_is_univalent.
    - exact pointed_is_univalent_disp.
    - exact operation_is_univalent_disp.
  Defined.

  Definition pointed_operation_is_univalent
    : is_univalent pointed_operation_set.
  Proof.
    apply is_univalent_total_category.
    - exact is_univalent_HSET.
    - exact pointed_operation_is_univalent_disp.
  Defined.

  (** Exercise 2.5: conclude that the category of monoids is univalent. *)
  Definition monoid_is_univalent_disp
    : is_univalent_disp monoid_laws_disp_cat.
  Proof.
    apply disp_full_sub_univalent.
  Admitted.

  Definition monoids_is_univalent
    : is_univalent monoids.
  Proof.
    apply is_univalent_total_category.
    - exact pointed_operation_is_univalent.
    - exact monoid_is_univalent_disp.
  Defined.
End Exercise_2.


Section Exercise_3.
(** Limits and colimits.

  1. Define the empty graph and empty diagram, and show that any limit of the empty diagram is a terminal object in the directly-defined sense.
*)

  Definition empty_graph : graph.
  Proof.
  Admitted.

  Definition empty_diagram (C : category) : diagram empty_graph C.
  Proof.
  Admitted.

  Definition isTerminal_limit_of_empty_diagram
      {C} (L : LimCone (empty_diagram C))
    : isTerminal _ (lim L).
  Proof.
  Admitted.

  (* 2. Show that for a univalent category, “having an initial object” is a property. *)
  Definition isaprop_initial_obs_of_univalent_category
      {C : univalent_category}
    : isaprop (Initial C).
  Proof.
  Admitted.

  (* 3. Show that if a category has equalisers and finite products, then it has pullbacks *)
  Definition pullbacks_from_equalizers_and_products {C : category}
    : Equalizers C -> FinOrdProducts C -> Pullbacks C.
  Proof.
  Admitted.

End Exercise_3.

Section Exercise_4.
(** Functors and natural transformations / monads and adjunctions

Prove that an adjunction induces a monad.  Construct the Kleisli category of a monad.  Show that the Kleisli construction does not preserve univalence: that is, give an example of a monad on a univalent category whose Kleisli category is not univalent. *)

  (* Hint: as usual, it may be helpful to break out parts of these multi-component structures as separate definitions. *)

  Definition monad_from_adjunction {C D : category}
      (F : functor C D) (G : functor D C) (A : are_adjoints F G)
    : Monad C.
  Proof.
  Admitted.

  Definition kleisli_cat {C : category} (T : Monad C) : category.
  Proof.
    (* see <https://en.wikipedia.org/wiki/Kleisli_category> *)
  Admitted.

  Theorem kleisli_breaks_univalence
    : ∑ (C : univalent_category) (T : Monad C), ¬ is_univalent (kleisli_cat T).
  Proof.
  Admitted.

End Exercise_4.
