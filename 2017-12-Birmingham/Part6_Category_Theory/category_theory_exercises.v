(* Exercises on Category Theory in UniMath *)
(* for lecture by Peter LeFanu Lumsdaine, Thu 2017-12-14 *)
(* School and Workshop on Univalent Maths, Birmingham 2017 *)
(* https://unimath.github.io/bham2017/ *)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

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
(** Displayed categories and displayed univalence.

Define the category of pointed sets, as the total category of a displayed category over sets.  Show it’s univalent as a displayed category, and conclude that it’s univalent as a category.  Alternatively, show directly that the total category is univalent.
*)
  Require Import UniMath.CategoryTheory.categories.category_hset.
  Require Import UniMath.CategoryTheory.DisplayedCats.Core.

  Definition point_disp_cat : disp_cat hset_category.
  Proof.
    (* Hint: Remember, this is to be the displayed category whose *total* category is pointed sets. So the objects and morphisms of this are just the extra data needed to give a pointed set or map of pointed sets, compared to a set or map of sets.

     As in Exercise 1, it may help to give the various components of this as separate lemmas. *)
  Admitted.

  Definition pointed_hset : category.
  Proof.
  Admitted.

  Definition is_univalent_point_disp_cat : is_univalent_disp point_disp_cat.
  Proof.
    (* Hint: use [is_univalent_disp_from_fibers]. *)
  Admitted.

  Definition isunivalent_pointed_hset : is_univalent pointed_hset.
  Proof.
    (* Use [is_univalent_point_disp_cat] *)
  Admitted.

  Definition isunivalent_pointed_hset_proof_2 : is_univalent pointed_hset.
  Proof.
    (* Alternatively, prove this directly without using displayed univalence. *)
  Admitted.
End Exercise_2.


Section Exercise_3.
(** Limits and colimits.

  1. Define the empty graph and empty diagram, and show that any limit of the empty diagram is a terminal object in the directly-defined sense.
*)

  Require Import UniMath.CategoryTheory.limits.graphs.colimits.
  Require Import UniMath.CategoryTheory.limits.graphs.limits.
  Require Import UniMath.CategoryTheory.limits.terminal.

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

  Require Import UniMath.CategoryTheory.limits.initial.

  Definition isaprop_initial_obs_of_univalent_category
      {C : univalent_category}
    : isaprop (Initial C).
  Proof.
  Admitted.

  (* 3. Show that if a category has equalisers and finite products, then it has pullbacks *)
  Require Import UniMath.CategoryTheory.limits.FinOrdProducts.
  Require Import UniMath.CategoryTheory.limits.equalizers.
  Require Import UniMath.CategoryTheory.limits.pullbacks.

  Definition pullbacks_from_equalizers_and_products {C : category}
    : Equalizers C -> FinOrdProducts C -> Pullbacks C.
  Proof.
  Admitted.

End Exercise_3.

Section Exercise_4.
(** Functors and natural transformations / monads and adjunctions

Prove that an adjunction induces a monad.  Construct the Kleisli category of a monad.  Show that the Kleisli construction does not preserve univalence: that is, give an example of a monad on a univalent category whose Kleisli category is not univalent. *)

  Require Import UniMath.CategoryTheory.functor_categories.
  Require Import UniMath.CategoryTheory.Adjunctions.
  Require Import UniMath.CategoryTheory.Monads.Monads.

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
