(* Exercises on Category Theory in UniMath *)
(*   plus partial solutions (currently just sketches for the hardest exercises) *)
(* for lecture by Peter LeFanu Lumsdaine, Thu 2017-12-14 *)
(* School and Workshop on Univalent Maths, Birmingham 2017 *)
(* https://unimath.github.io/bham2017/ *)

(* 27 March 2019:                         *)
(* Tom de Jong                            *)
(* Added solutions to Exercises 0,1 and 3 *)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.FinOrdProducts.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.CategoryTheory.limits.binproducts.


(* NOTE: some of these exercises (or parts of them) are straightforward, while other parts are intended to be quite difficult.  So I don’t recomment aiming to complete them in order — if stuck on a difficult part, move on and come back for another attempt later!

Skeleton solutions and hints are provided, to exhibit good tools and techniques for working with categories.  However, you may well want to add extra definitions/lemmas besides the ones suggested in the skeleton. *)

Section Exercise_0.
(** Univalent categories

  Show that in any univalent category, the type of objects has h-level 3 *)

  Proposition isofhlevel3_ob_of_univalent_cat (C : category) (univ : is_univalent C)
    : isofhlevel 3 (ob C).
  Proof.
    intros a b.
    apply (isofhlevelweqb 2 (make_weq idtoiso (univ a b))).
    unfold iso.
    apply isofhleveltotal2.
    - apply homset_property.
    - intro f.
      apply isasetaprop.
      apply isaprop_is_iso.
  Qed.
End Exercise_0.

Section Exercise_1.
(** Non-univalent categories

  Problem: Construct the category with objects the natural numbers, and with maps m->n all functions {1,…,m}->{1,…,n}.  Show that this is a set-category, and that it is NOT univalent.

  Hint: for defining categories (and other large multi-component structures), it’s usually better to define them a few components at a time, following the structure of the definition, as the following skeleton suggests.

  An alternative approach is to go directly for the total structure [Definition nat_category : category], then begin with [use makecategory.] and construct the whole thing in a single interactive proof.  This approach can be good for first finding a proof/construction; but it often causes speed issues down the line, because the resulting term is very large. *)

  Definition nat_category_ob_mor : precategory_ob_mor.
  Proof.
    unfold precategory_ob_mor.
    exists nat.
    intros m n.
    (* Rather than functions {1,…,m}->{1,…,n} we consider functions {0,…,m-1}->{0,…,n-1},
       so that we can use stnset from the Combinatorics package. *)
    exact (stnset m → stnset n).
  Defined.

  Definition nat_category_data : precategory_data.
  Proof.
    unfold precategory_data.
    exists nat_category_ob_mor.
    split.
    - intro n. exact (idfun (stnset n)).
    - intros k l m f g.
      exact (g ∘ f).
  Defined.

  Definition nat_category_is_precategory : is_precategory nat_category_data.
  Proof.
    apply make_is_precategory.
    - intros m n f; apply idpath.
    - intros m n f; apply idpath.
    - intros k l m n f g h; apply idpath.
    - intros k l m n f g h; apply idpath.
  Defined.

  Definition nat_category : category.
  Proof.
    unfold category.
    exists (make_precategory nat_category_data nat_category_is_precategory).
    unfold has_homsets. cbn.
    intros m n.
    apply impred_isaset.
    intro sm.
    apply isasetstn.
  Defined.

  Definition nat_setcategory : setcategory.
  Proof.
    unfold setcategory.
    exists nat_category.
    unfold is_setcategory.
    unfold object_homtype_hlevel.
    split.
    - apply isasetnat.
    - intros m n f g.
      cbn in f, g.
      assert (helper : isaset (stn m → stn n)).
      { change isaset with (isofhlevel 2).
        apply impredfun.
        apply isasetstn.
      }
      apply helper.
  Defined.

  Proposition nat_category_not_univalent : ¬ (is_univalent nat_category).
  Proof.
    intro univ_nat.
    set (equiv22 := univ_nat 2 2).
    assert (isaprop_id : isaprop (2 = 2)).
    { apply isasetnat. }
    set (isaprop_iso := isofhlevelweqf 1 (make_weq idtoiso equiv22) isaprop_id).
    set (zero := stnel (2,0)).
    set (one := stnel (2,1)).
    set (f := @identity nat_category_data 2).
    set (g := two_rec one zero : (nat_category_data ⟦ 2, 2 ⟧)%Cat).
    set (fiso := identity_is_iso nat_category 2).
    assert (giso : is_iso g).
    {
      apply (@is_iso_from_is_z_iso nat_category 2 2).
      exists g.
      unfold is_inverse_in_precat. split.
      - apply funextfun.
        unfold homot.
        apply two_rec_dep.
        + apply idpath.
        + apply idpath.
      - apply funextfun.
        unfold homot.
        apply two_rec_dep.
        + apply idpath.
        + apply idpath.
    }
    set (f' := make_iso _ fiso).
    set (g' := @make_iso nat_category 2 2 g giso).
    set (proofirr_iso := proofirrelevance _ isaprop_iso).
    set (f'eqg' := proofirr_iso f' g').
    assert (nonsense : stnel (2,0) = stnel (2,1)).
    {
      change (stnpr 0) with (f (stnpr 0)).
      change (stnpr 1) with (g (stnpr 0)).
      apply (@eqtohomot _ _ f g).
      exact (maponpaths pr1 f'eqg').
    }
    apply (negpaths0sx 0).
    apply (maponpaths pr1 nonsense).
  Defined.

End Exercise_1.

Section Exercise_2.
  Local Open Scope cat.
  (* Exercise 2.1: Define `pointed_disp_cat` with `disp_struct`. *)
  Definition pointed_disp_cat
  : disp_cat SET.
  Proof.
    use disp_struct.
    - intros X.
      apply X.
    - intros X Y x y f ; simpl in *.
      exact (f x = y).
    - intros X Y x y f ; simpl in *.
      apply Y.
    - intros X x ; simpl in *.
      apply idpath.
    - intros X Y Z x y z f g p q ; simpl in *.
      exact (maponpaths g p @ q).
  Defined.

  (* Exercise 2.2: Define a displayed category on sets of a binary operation on them.
     The displayed objects over `X` are maps `X × X → X` and the displayed morphisms over `f` are proofs that `f` preserves the operation.
   *)
  Definition operation_disp_cat
    : disp_cat SET.
  Proof.
    use disp_struct.
    - intros X.
      simpl in *.
      exact (X × X → X).
    - intros X Y mX mY f.
      simpl in *.
      exact (∏ (z : X × X), f (mX z) = mY (f (pr1 z) ,, f (pr2 z))).
    - intros X Y mX mY f ; simpl.
      apply impred ; intro.
      apply Y.
    - intros X mX z ; simpl.
      apply idpath.
    - intros X Y Z mX mY mZ f g p q z ; cbn in *.
      rewrite (p z), q.
      apply idpath.
  Defined.

  (* Using the product of displayed categories, we now define *)
  Definition pointed_operation_disp_cat
    : disp_cat SET.
  Proof.
    use dirprod_disp_cat.
    - exact pointed_disp_cat.
    - exact operation_disp_cat.
  Defined.

  (* This gives rise to a total category *)
  Definition pointed_operation_set
    : category
    := total_category pointed_operation_disp_cat.

  (* For convenience, we define some projection to access the structure *)
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

  (* Exercise 2.3: Define the category of monoid displayed category.
     Hint: use `disp_full_sub`.
   *)
  Definition monoid_laws_disp_cat
    : disp_cat pointed_operation_set.
  Proof.
    use disp_full_sub.
    intros X.
    refine (_ × _ × _).
    - exact (∏ (x : carrier X), mul X x (unit_el X) = x).
    - exact (∏ (x : carrier X), mul X (unit_el X) x = x).
    - exact (∏ (x y z : carrier X), mul X (mul X x y) z = mul X x (mul X y z)).
  Defined.

  Definition monoids
    : category
    := total_category monoid_laws_disp_cat.

  (* During the lecture, we already showed that pointed sets are univalent as follows *)
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
     Hint: adapt the proof from the lecture.
   *)
  Definition operation_is_univalent_disp
    : is_univalent_disp operation_disp_cat.
  Proof.
    apply is_univalent_disp_from_fibers.
    intros X x₁ x₂.
    use isweqimplimpl.
    - intros f.
      simpl in *.
      use funextsec.
      apply f.
    - cbn in x₁, x₂.
      apply isaset_set_fun_space.
    - apply isaproptotal2.
      + intro.
        apply isaprop_is_iso_disp.
      + intros p q r₁ r₂.
        simpl in p, q.
        use funextsec.
        intro z.
        apply X.
  Defined.

  (* Now we conclude *)
  Definition pointed_operation_is_univalent_disp
    : is_univalent_disp pointed_operation_disp_cat.
  Proof.
    use dirprod_disp_cat_is_univalent.
    - exact pointed_is_univalent_disp.
    - exact operation_is_univalent_disp.
  Defined.

  (* Exercise 2.5: conclude that the category of monoids is univalent. *)
  Definition pointed_operation_is_univalent
    : is_univalent pointed_operation_set.
  Proof.
    apply is_univalent_total_category.
    - Search HSET.
      exact is_univalent_HSET.
    - exact pointed_operation_is_univalent_disp.
  Defined.

  Definition monoid_is_univalent_disp
    : is_univalent_disp monoid_laws_disp_cat.
  Proof.
    apply disp_full_sub_univalent.
    intro X.
    use isapropdirprod.
    - apply impred ; intro.
      apply (carrier X).
    - use isapropdirprod.
      + apply impred ; intro.
        apply (carrier X).
      + repeat (apply impred ; intro).
        apply (carrier X).
  Defined.

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
    unfold graph.
    exists empty.
    exact fromempty.
  Defined.

  Definition empty_diagram (C : category) : diagram empty_graph C.
  Proof.
    unfold diagram. cbn.
    exists fromempty.
    intro a; induction a.
  Defined.

  Definition isTerminal_limit_of_empty_diagram
      {C} (L : LimCone (empty_diagram C))
    : isTerminal _ (lim L).
  Proof.
    unfold isTerminal.
    intro a.
    assert (acone : cone (empty_diagram C) a).
    {
      unfold cone. cbn.
      exists (λ v, fromempty v).
      intro u; induction u.
    }
    set (univprop := limUnivProp L a acone).
    simple refine (iscontrretract _ _ _ univprop).
    - exact pr1.
    - intro f.
      exists f.
      intro v; induction v.
    - cbn. apply idpath.
  Defined.

  (* 2. Show that for a univalent category, “having an initial object” is a property. *)
  Definition isaprop_initial_obs_of_univalent_category
      {C : univalent_category}
    : isaprop (Initial C).
  Proof.
    apply invproofirrelevance.
    intros aInit bInit.
    unfold Initial in aInit, bInit.
    use total2_paths_f.
    - apply isotoid.
      + apply univalent_category_is_univalent.
      + exact (iso_Initials aInit bInit).
    - apply proofirrelevance.
      unfold isInitial.
      apply impred_isaprop.
      intro b.
      apply isapropiscontr.
  Defined.

  Local Open Scope cat.
  (* 3. Show that if a category has equalisers and binary products, then it has pullbacks *)
  Definition pullbacks_from_equalizers_and_products {C : category}
    : Equalizers C -> BinProducts C -> Pullbacks C.
  Proof.
    intros Eqs Prods.
    unfold Pullbacks.
    intros a b c f g.
    set (prodbc := Prods b c).
    set (btimesc := BinProductObject C prodbc).
    set (projb := BinProductPr1 C prodbc).
    set (projc := BinProductPr2 C prodbc).
    set (e := Eqs btimesc a (projb · f) (projc · g)).
    use make_Pullback.
    - exact e.
    - exact (EqualizerArrow e · projb).
    - exact (EqualizerArrow e · projc).
    - rewrite assoc'.
      rewrite assoc'.
      apply EqualizerEqAr.
    - use make_isPullback.
      intros d h k comm.
      set (hk := BinProductArrow C prodbc h k).
      assert (hkequalizes : hk · (projb · f) = hk · (projc · g)).
      {
        do 2 (rewrite assoc).
        unfold hk.
        rewrite BinProductPr1Commutes.
        rewrite BinProductPr2Commutes.
        exact comm.
      }
      set (j := EqualizerIn e d hk hkequalizes).
      assert (jeq1 : j · (EqualizerArrow e · projb) = h).
      {
        rewrite assoc.
        unfold j.
        rewrite EqualizerCommutes.
        unfold hk.
        apply BinProductPr1Commutes.
      }
      assert (jeq2 : j · (EqualizerArrow e · projc) = k).
      {
        rewrite assoc.
        unfold j.
        rewrite EqualizerCommutes.
        unfold hk.
        apply BinProductPr2Commutes.
      }
      exists (j,,jeq1,,jeq2).
      intros [j' eqs].
      use total2_paths_f.
      + cbn.
        apply EqualizerInsEq.
        apply BinProductArrowsEq.
        * rewrite assoc'.
          change (BinProductPr1 C prodbc) with projb.
          rewrite (pr1 eqs).
          rewrite assoc'.
          exact (!jeq1).
        * rewrite assoc'.
          change (BinProductPr2 C prodbc) with projc.
          rewrite assoc'.
          rewrite (pr2 eqs).
          exact (!jeq2).
      + apply proofirrelevance.
        cbn.
        apply isapropdirprod.
        * apply homset_property.
        * apply homset_property.
  Defined.

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
    (* One possible example:
    - take [C := hset_category]
    - take [T] to be the monad sending every set to [1].
    - then in [kleisli_cat T], [iso X X] is contractible for any set [X]; in particular, for [bool].  But [bool = bool] is not contractible, by univalence.
     *)
  Admitted.

End Exercise_4.
