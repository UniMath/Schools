(**
Lecture 6: Category Theory
School and Workshop on Univalent Mathematics
Organisers: Benedikt Ahrens, Marco Maggesi
Lecturer: Niels van der Weide
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.categories.HSET.All.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.

Open Scope cat.

(**
We start with a simple example on how to define functors.
These definition are done in multiple steps. First we, define the data and then we prove this constitutes a functor.
 *)
Definition maybe_data : functor_data SET SET.
Proof.
  use make_functor_data.
  - exact (λ X, setcoprod X unitset).
  - intros X Y f x.
    induction x as [x | y].
    + exact (inl (f x)).
    + exact (inr tt).
Defined.

(**
Note that this definition ends with `Qed` rather than `Defined`.
A definition that ends with `Qed` is opaque and cannot be unfolded, while a definition that ends with `Defined` is transparent and can be unfolded.
By making proofs which are irrelevant for the computation, opaque, efficiency is improved.
 *)
Definition maybe_is_functor
  : is_functor maybe_data.
Proof.
  split.
  - intro X.
    use funextsec.
    intro x.
    induction x as [x | x].
    + apply idpath.
    + induction x.
      apply idpath.
  - intros X Y Z f g.
    use funextsec.
    intro x.
    induction x as [x | x].
    + apply idpath.
    + induction x.
      apply idpath.
Qed.

(**
By combining these two, we get an actual functor from `SET` to `SET`.
 *)
Definition maybe : SET ⟶ SET.
Proof.
  use make_functor.
  - exact maybe_data.
  - exact maybe_is_functor.
Defined.

(**
Next we show how to define natural transformations.
Again the definition is done in several steps.
We first define the data and then we prove it actually gives rise to natural transfomation.
 *)
Definition pure_data
  : nat_trans_data (functor_identity SET) maybe
  := λ X, inl.

Definition pure_is_nat_trans
  : is_nat_trans (functor_identity SET) maybe pure_data.
Proof.
  intros X Y f.
  apply idpath.
Qed.
  
Definition pure : functor_identity SET ⟹ maybe.
Proof.
  use make_nat_trans.
  - exact pure_data.
  - exact pure_is_nat_trans.
Defined.

(**
The second part of this code shows how to use displayed categories to modularly construct univalent categories.
To this end, we consider the example of pointed sets.
 *)
Open Scope mor_disp.

(**
We start by defining the displayed objects and displayed morphisms.
A displayed object over a set `X` is just a point of `X`.
A displayed morphism over `f : X → Y` from `x` to `y` is a path `f x = y`.
 *)
Definition pointed_disp_ob_mor
  : disp_cat_ob_mor SET.
Proof.
  use make_disp_cat_ob_mor.
  - intro X.
    apply X.
  - exact (λ X Y x y f, f x = y).
Defined.

(**
Next we show that we have the identity and composition of morphisms.
 *)
Definition pointed_disp_cat_id_comp
  : disp_cat_id_comp SET pointed_disp_ob_mor.
Proof.
  use tpair.
  - intros X x.
    simpl.
    apply idpath.
  - intros X Y Z f g x y z p q.
    cbn in *.
    exact (maponpaths g p @ q).
Defined.

(**
This way we get the data of a displayed category.
 *)
Definition pointed_disp_cat_data
  : disp_cat_data SET.
Proof.
  use tpair.
  - exact pointed_disp_ob_mor.
  - exact pointed_disp_cat_id_comp.
Defined.

(**
To finish, we also need to show the axioms of displayed categories.
Since these are transported equalities, we need to use transport lemmata to prove them.
The core idea is to use `transportf_comp_lemma_hset`.
 *)
Check transportf_comp_lemma_hset.

Definition pointed_disp_cat_axioms
  : disp_cat_axioms SET pointed_disp_cat_data.
Proof.
  repeat split.
  - intros X Y f x y p.
    use transportb_transpose_right.
    apply transportf_comp_lemma_hset.
    { apply homset_property. }
    cbn in *.
    apply idpath.
  - intros X Y f x y p.
    unfold transportb.
    symmetry.
    apply transportf_comp_lemma_hset.
    { apply homset_property. }
    cbn in *.
    induction p.
    apply idpath.
  - intros X Y Z W f g h x y z w p q r.
    unfold transportb.
    symmetry.
    apply transportf_comp_lemma_hset.
    { apply homset_property. }
    cbn in *.
    induction p, q, r.
    simpl.
    apply idpath.
  - intros X Y f x y.
    simpl in *.
    apply isasetaprop.
    apply Y.
Qed.

(**
In conclusion, we get a displayed category on `SET`.
 *)
Definition pointed_disp_cat
  : disp_cat SET.
Proof.
  use tpair.
  - exact pointed_disp_cat_data.
  - exact pointed_disp_cat_axioms.
Defined.

(**
This displayed category gives rise to a total category.
 *)
Definition pointed_sets
  : category
  := total_category pointed_disp_cat.

(**
Now we show that pointed sets form a univalent category.
To do so, we use that `SET` is univalent.
Furthermore, we must show that `pointed_disp_cat` is displayed univalent.
 *)
Definition is_univalent_pointed_disp_cat
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

(**
All in all, pointed sets form a univalent category.
 *)
Definition is_univalent_pointed_sets
  : is_univalent pointed_sets.
Proof.
  apply is_univalent_total_category.
  - exact is_univalent_HSET.
  - exact is_univalent_pointed_disp_cat.
Defined.
