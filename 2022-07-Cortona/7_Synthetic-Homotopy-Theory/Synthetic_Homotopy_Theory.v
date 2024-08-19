(* -*- coq-prog-args: ("-type-in-type"); -*- *)

(** * Exercises on Synthetic Homotopy Theory

Peter LeFanu Lumsdaine
School on Univalent Mathematics, Cortona, July 2022
https://unimath.github.io/cortona2022/

The goal is to remove as many “Admitted” as possible in the code below.  The exercises should range from straightforward to very challenging.

The exercises are divided into 8 groups, each forming a roughly self-contained story.  In earlier groups, all statements and most definitions are given, only proofs are missing; in later groups, less is given, and more is left for the student.  Apart from the core definitions in group 0, most later groups don’t depend essentially on earlier groups.

The biggest and most interesting part is group 4 — showing the fundamental group of the circle is the integers.  Groups 1–3 can largely be seen as warm-up exercises for this.  Depending on taste, I recommend either tackling the file roughly in order, or jumping straight to group 4 and looking back to earlier exercises as necessary.

A few exercises are marked “off-topic”, when their difficulty is not really related to synthetic homotopy theory.  They’re included either because their statements are good to see, or because they’re needed in later exercises; they can all safely be left as “admitted”.  They may be good exercises on other topics — mostly on working with UniMath’s integers — but insofar as you want exercises on synthetic homotopy theory, I recommend skipping them to avoid getting bogged down.

- Group 0: Circle structure
- Group 1: Basics
- Group 2: The circle is unique
- Group 3: The circle is non-trivial
- Group 4: Fundamental group of the circle
- Group 5: Being a circle is a proposition
- Group 6: The recursor is equivalent to the universal mapping property.
- Group 7: Is the circle’s computation rule necessary?
- Group 8: Implementing the circle using Z-torsors

*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.NumberSystems.Integers.


(** * Auxiliary functions

Almost every development ends up needing a few “auxiliary” definitions that don’t really belong in the development itself, but don’t exist upstream.  There are various ways to deal with this; I like to put them in an “auxiliary” file or section, and then upstream them later when there’s a suitable moment.  *)
Section Auxiliary.

  (** Generalisation of [maponpaths] to dependent functions. *)
  Definition maponpaths_dep {X:UU} {Y : X -> UU}
      (f : ∏ x:X, Y x) {x1 x2} (e : x1 = x2)
    : transportf _ e (f x1) = f x2.
  Proof.
    destruct e. apply idpath.
  Defined.

End Auxiliary.

(** * Group 0: Circle structure

Definition of circles, as their universal property. *)

Section Circle_Structure.

  (** This axiomatises the recursor on a type that shows it is “the” circle. *)
  Definition circle_rec_structure {S : UU} {b : S} (l : b = b) : UU
  := ∏ (Y : S -> UU) (y_b : Y b) (y_l : transportf _ l y_b = y_b),
     ∑ (f : ∏ x:S, Y x)
       (e_b : f b = y_b),
         maponpaths_dep f l
       = maponpaths _ e_b @ y_l @ !e_b.
  (** The third component (the “computation rule” on the loop) is a bit complicated: the idea is just [maponpaths_dep f l = y_l], but that is only well-typed modulo via the “computation rule” for the basepoint, [e_b : f b = y_b]. *)

  (* With any multiple-component definition, it’s good practice to provide named access functions.  (Compared to accessing via lots of [pr1], [pr2], this is both more readable, and more robust for refactoring.) *)
  Definition circle_rec
      {S : UU} {b : S} {l : b = b} (H : circle_rec_structure l)
      {Y : S -> UU} {y_b : Y b} (y_l : transportf _ l y_b = y_b)
    : ∏ x:S, Y x.
  Proof.
  Admitted.

  Definition circle_rec_comp_base
      {S : UU} {b : S} {l : b = b} (H : circle_rec_structure l)
      {Y : S -> UU} {y_b : Y b} (y_l : transportf _ l y_b = y_b)
    : circle_rec H y_l b = y_b.
  Proof.
  Admitted.

  Definition circle_rec_comp_loop
      {S : UU} {b : S} {l : b = b} (H : circle_rec_structure l)
      {Y : S -> UU} {y_b : Y b} (y_l : transportf _ l y_b = y_b)
    : maponpaths_dep (circle_rec H y_l) l
    = maponpaths _ (circle_rec_comp_base _ _)
      @ y_l @ ! (circle_rec_comp_base _ _).
  Proof.
  Admitted.

  (** An alternative formulation of the universal property of the circle:
  maps out of it correspond to loops.

  “UMP” stands for the “universal mapping property” (a term category theorists love) *)
  Definition circle_ump_structure {S : UU} {b : S} (l : b = b) : UU
  := ∏ (Y : UU),
       isweq ((fun f => (f b,, maponpaths f l)) : (S -> Y) -> (∑ y:Y, y = y)).

  (* Later, when you need to use [circle_ump_structure], come back here and write access functions for it. *)

End Circle_Structure.

(** * Group 1: Basics

Various fairly straightforward exercises: some that we will need later, others that are warmups for harder things later. *)
Section Basics.

  (* Section contexts are the Coq equivalent of writing “Fix some choice of circle (S,b,l)…”  Within the section, these variables are fixed parameters that are available for all results/constructions.  After the section, all results/constructions get generalised over whichever of the variables they used: see the “Check” commands below to demonstrate this. *)
  Context {S : UU} {b : S} (l : b = b).

  Proposition isaprop_circle_ump_structure : isaprop (circle_ump_structure l).
  (* TODO: suggest some useful lemmas, or the search command to search for them *)
  Admitted.

  Definition loop_pos_power : nat -> (b = b).
  Admitted.

  (* off-topic *)
  Definition loop_power : hz -> (b = b).
  (* Use [Search hz] to find general results about hz. *)
  Admitted.
  (* Eventually, we want to show [(b = b) ≃ hz]. *)

  (* Within the section, the variables [S] etc are a fixed context, not shown explicitly in the individual types: *)
  Check loop_power.
End Basics.
(* After closing the section, the section variables are generalised: *)
Check loop_power.
(* In actual developments, it’s usually considered bad practice to leave “noisy” commands like “Check”, “Search” etc. in finished proof scripts — better to just issue them as queries in your IDE. *)

(** * Group 2: the circle is unique

Goal of this group: any two circles are canonically equivalent. *)
Section Circle_Unique.

  Context {S : UU} {b : S} {l : b = b} (is_circ : circle_rec_structure l).
  Context {S' : UU} {b' : S'} {l' : b' = b'} (is_circ' : circle_rec_structure l').

  (* It’s often helpful to make auxiliary definitions _local_ to their section or file.  This means that in later files, this can only be accessed as [Circle_Unique.S_to_S'].  If this definition was not marked “local”, then we should give it a more carefully considered name. *)
  Local Definition S_to_S' : S -> S'.
  Admitted.

  (* This definition could be copy-pasted from [S_to_S'] above; or to avoid code-duplication, you could generalise the variables in that (either by closing the section and opening a new one, or by moving the section variables explicitly to its hypotheses) and then taking this just as an instance of that. *)
  Local Definition S'_to_S : S' -> S.
  Admitted.

  Local Definition S_to_S'_to_S : S'_to_S ∘ S_to_S' = idfun S.
  Admitted.

  Local Definition S'_to_S_to_S' : S_to_S' ∘ S'_to_S = idfun S'.
  Admitted.

  Proposition weq_circle_unique : S ≃ S'.
  Proof.
    (* the lemma [gradth] is often useful for constructing equivalences *)
  Admitted.

  (** Optional extra: State and prove the fact that this equivalence is “canonical” — it’s the unique equivalence between [S] and [S'] mapping [l] to [l']. *)

End Circle_Unique.

(** * Group 3: The circle is non-trivial

Using univalence, we can show that the circle is non-trivial. *)
Section Circle_non_trivial.

  (** Outline:
     - if the circle was trivial, then every type would be a set
     - the universe is not a set, since [bool] has a non-trivial automorphism
  *)

  Context {S : UU} {b : S} {l : b = b} (S_circ : circle_rec_structure l).

  Proposition circle_trivial_implies_loops_trivial
    : iscontr S -> ∏ (X:UU) (x:X) (l : x=x), l = idpath x.
  Admitted.

  Proposition loops_trivial_implies_isaset {X:UU}
    : (∏ (x:X) (l : x=x), l = idpath x) -> isaset X.
  Admitted.

  Proposition circle_trivial_implies_isaset
    : iscontr S -> ∏ (X:UU), isaset X.
  Admitted.

  Definition flip : bool ≃ bool.
  (* You can either write this yourself, or look for it in [UniMath] iwth [Search (bool ≃ bool)], or [Search (weq bool bool)] if your command prompt makes unicode entry difficult. *)
  Admitted.

  Proposition flip_neq_idweq : flip != idweq bool.
    (* this uses the fact that [false != true];
     you can either prove this yourself or search for it in [UniMath] *)
  Admitted.

  Definition flip_path : bool = bool.
    (* this is of univalence; specifically, [weqtopaths] *)
  Admitted.

  Proposition flip_path_neq_idpath : flip_path != idpath bool.
    (* hints: [Search weqtopaths], [Search eqweqmap], [maponpaths] *)
  Admitted.

  Proposition not_isaset_uu : ¬ isaset UU.
  Admitted.

  Proposition not_iscontr_circle : ¬ iscontr S.
  Admitted.

  (** Optional extra: can you strengthen the conclusion of this section? *)
End Circle_non_trivial.

(** * Group 4: Fundamental group of the circle

In this sequence, we show that the fundamental group of the circle is the integers.

Indeed, we show the slightly stronger statement that the _loop space_ of the circle is equivalent to the integers.  (The fundamental group is the set-truncation of the loop space.) *)
Section Fundamental_Group.

  (** Fix a circle type throughout this sequence. *)
  Context {Circle : UU} {base : Circle} (loop : base = base).

  (** Outline:
  - (1) the identity-types Id_A(a,x) form the free A-indexed family generated by a single element at a; in particular, Id_S(b,x) are the free S-indexed family generated by an element at b
  - (2) by univalence, a family over a circle (S,b,l) corresponds to a single type equipped with an auto-equivalence
  - (3) so Id_S(b,b) is the free type-with-auto-equivalence generated by a single element
  - (4) (Z,succ) is the free type-with-auto-equivalence generated by a single element
  - (5) so they have the same universal peroperty, so are equivalent.

  We do not attempt to make all these results fully precise (especially (1), (2)); but they motivate the steps we use, which are just as much of the above results as are needed to make this argument go through. *)

  (** Step (1) is nothing specifically to do with the circle,
  just a particular formulation of the universal property of path-types *)

  Section Family_Maps_From_Path_Types.

    Context {X:UU} (x0:X).

    Proposition unique_family_map_from_paths {Y : X -> UU} (y0 : Y x0)
      : iscontr (∑ (f : ∏ x:X, x0 = x -> Y x), f x0 (idpath _) = y0).
    Admitted.

  End Family_Maps_From_Path_Types.

  Section Auto_Types.
  (** In the rest of the proof, we work with types equipped with with an auto-equivalence, and sometimes also with a distinguished element.  For conciseness, call these *auto-types* and *pointed auto-types*.

  We set these up explicitly as bundled structures, with access functions and a constructor function. *)

    Definition auto_type : UU := ∑ (X:UU), X ≃ X.

    Definition auto_type_pr1 : auto_type -> UU := pr1.
    Coercion auto_type_pr1 : auto_type >-> UU.

    Definition auto_type_auto { X : auto_type } : X ≃ X
      := pr2 X.

    (* a constructor function is good practice in general,
  but especially necessary in this case since Coq doesn’t generally accept [(X,,e)] for an auto-type: it de-sugars this to [tpair _ X e] and fails to infer the implicit argument correctly *)
    Definition make_auto_type {X:UU} (e : X ≃ X) : auto_type
      := tpair (fun Y => Y ≃ Y) X e.

    Definition ptd_auto_type : UU := ∑ (X:auto_type), X.

    Definition ptd_auto_type_pr1 : ptd_auto_type -> auto_type := pr1.
    Coercion ptd_auto_type_pr1 : ptd_auto_type >-> auto_type.

    Definition ptd_auto_type_pt ( X : ptd_auto_type ) : X
      := pr2 X.

    Definition make_ptd_auto_type {X:UU} (e : X ≃ X) (x0 : X) : ptd_auto_type
      := (make_auto_type e ,, x0).
  End Auto_Types.

  (* we give more concise names, but keep them local *)
  Local Definition s {X : auto_type} := @auto_type_auto X.
  Local Definition pt {X : ptd_auto_type} := @ptd_auto_type_pt X.

  (** We define “freeness” in a category-theoretic style, using a universal mapping property: *)
  Definition free_ptd_auto_type_ump_structure (X : ptd_auto_type) : UU
  := ∏ (Y : ptd_auto_type),
      iscontr (∑ (f : ∑ (f : X -> Y), f ∘ s = s ∘ f), (pr1 f pt = pt)).
  (** a more natural and readable phrasing would be
     [ ∑ (f : X -> Y), (f ∘ s = s ∘ f) × (f pt = pt) ]
  but associating the first two components together fits much better with the ways we’ll use it below *)

  (* When you use this below, you’ll probably want to come back and write access functions! *)

  (* It might be helpful to bundle “ptd-auto-preserving maps” as a structure following how we bundled ptd-auto-types. *)

  (** Step (2): families over circle correspond to types-with-automorphisms.

  We don’t give a very complete form of this “correspondence” — just as is needed in later steps of the proof. *)

  Section Families_Over_Circle.

    Definition circle_family_of_auto_type
      : auto_type -> (Circle -> UU).
    Admitted.

    Definition auto_type_of_circle_family
      : (Circle -> UU) -> auto_type.
    Admitted.

    (** The above two functions should form an equivalence; but we need only one direction of their inverse-ness. *)
    Definition auto_type_of_circle_family_of_auto_type
        (X : auto_type)
      : auto_type_of_circle_family (circle_family_of_auto_type X)
      = X.
    (* In this kind of situation, it’s often helpful to give a general lemma for building paths of auto-types, named e.g. [auto_type_path],
      saying that to show two auto-types equal, it suffices to give an equality [e] between their types, and show their automorphisms commute with the equivalence [eqweqmap e] *)
    Admitted.

    Definition weq_family_maps_auto_type_maps {X Y : Circle -> UU}
      : (∏ p:Circle, X p -> Y p)
        ≃ (∑ (f : auto_type_of_circle_family X
                  -> auto_type_of_circle_family Y),
            (f ∘ s = s ∘ f)).
    Proof.
      (* look for library lemmas for building equivalences between dependent sum types,
       e.g. [Search ((∑ (x:_), _) ≃ (∑ (x:_), _))] *)
    Admitted.

  End Families_Over_Circle.

  (** Step (3): [ loop = loop ] is a _free_ pointed-type-with-auto-equivalence.  *)
  Section Circle_Loops_Free.

    Definition circle_ptd_auto : ptd_auto_type.
    Proof.
      refine (@make_ptd_auto_type (base = base) _ _).
      - admit.
      - admit.
    Admitted.

    Definition circle_is_free_ptd_auto_type
      : free_ptd_auto_type_ump_structure circle_ptd_auto.
    (* Need to show: for any other ptd-auto-type, there’s a unique structure-preserving map to it.
    By results above, we know:
    - every ptd-auto-type arises from a family over S;
    - in that case, auto-preserving maps to it correspond to family-maps to it;
    - and then tre’s a unique point-preserving family-map to it.

    This proof is where it should be helpful that in the definition of [free_ptd_auto_type_ump_structure], we grouped “auto-preserving-map” together inside “point-preserving, auto-preserving map. *)
    Admitted.

  End Circle_Loops_Free.

  (** Step (4): the integers (with successor and zero) are also a free pointed-auto-type.

  This section involves no homotopy theory — it’s almost entirely old-fashioned set-level mathematics.  The “almost” is because the universal property we want involves mapping into arbitrary _types_, not just sets. *)

  Section Integers_Free.

    (* off-topic *)
    (* [hz] is UniMath’s integers *)
    Definition hz_ptd_auto : ptd_auto_type.
    Proof.
      refine (@make_ptd_auto_type hz _ _).
      - admit.
      - admit.
    Admitted.

    (* off-topic *)
    Definition hz_is_free_ptd_auto_type
      : free_ptd_auto_type_ump_structure hz_ptd_auto.
    (* One possible approach: show that the integers are equivalent to the coproduct of two copies of the naturals (viewed as e.g. the positive and strictly-negative integers); then give the required map (and its uniqueness) by induction over each copy of the naturals separately. *)
    Admitted.

  End Integers_Free.

  (** Step (5): we’ve shown that the integers and the loop space of the circle are each a “free pointed auto-type”. Now we use that to show they’re equivalent. *)
  Section Free_Ptd_Auto_Type_Unique.

    Definition weq_free_ptd_auto_type_unique
        {X : ptd_auto_type} (X_free : free_ptd_auto_type_ump_structure X)
        {X' : ptd_auto_type} (X'_free : free_ptd_auto_type_ump_structure X')
      : X ≃ X'.
    Admitted.

  End Free_Ptd_Auto_Type_Unique.

  Theorem weq_circle_loops_hz : (base = base) ≃ hz.
  Proof.
    (* now this should be just putting together earlier results, as sketched at the start! *)
  Admitted.

  (** Optional extra: we could instead define “freeness” in a more type-theoretic style, as a dependent recursion principle.  Using that approach in the proof would be an interesting extra challenge; if you do that, I’d be very interested to see it! *)
  Definition free_pointed_auto_type_rec_structure {X:UU} (s:X ≃ X) (x0:X) : UU
  := ∏ (Y : X -> UU) (s_y : ∏ x:X, Y x ≃ Y (s x)) (y0 : Y x0),
      ∑ (f : ∏ x:X, Y x) (_ : ∏ x, s_y x (f x) = f (s x)), (f x0 = y0).

End Fundamental_Group.

(** * Group 5: being a circle is a proposition

Precisely: for a given type, basepoint, and loop [l], [circle_rec_structure l] is a proposition. *)
Section Circle_Rec_Structure_Unique.

  Context {S : UU} {b : S} (l : b = b).

  Definition isaprop_circle_rec_conclusion
    : circle_rec_structure l
    -> ∏ (Y : S -> UU) (y_b : Y b) (y_l : transportf _ l y_b = y_b),
      isaprop
      ( ∑ (f : ∏ x:S, Y x)
        (e_b : f b = y_b),
          maponpaths_dep f l
        = maponpaths _ e_b @ y_l @ !e_b).
  (* hint: if you attack this directly by hand, it’s quite nasty;
    you will probably want lemmas about how to construct paths in sigma-types, which are available in the library,
    and also about lemmas about how [maponpaths_dep] interacts with path-composition, etc, which you will have to prove yourself *)
  Admitted.

  Definition isaprop_circle_rec_structure
    : isaprop (circle_rec_structure l).
  (* hint: look for a general result in the library to deduce this from the preceding result *)
  Admitted.

End Circle_Rec_Structure_Unique.

(** * Group 6: the recursor is equivalent to the universal mapping property. *)

Section Circle_Rec_Equiv_UMP.

  Context {S : UU} {b : S} (l : b = b).

  Definition circle_ump_from_rec
    : circle_rec_structure l -> circle_ump_structure l.
  Admitted.

  Definition circle_rec_from_ump
    : circle_ump_structure l -> circle_rec_structure l.
  Admitted.

  Definition weq_circle_rec_circle_ump
    : circle_ump_structure l ≃ circle_rec_structure l.
  (* we’ve shown both sides are propositions, and they imply each other;
  now look for a general result in the library to put these together *)
  Admitted.

End Circle_Rec_Equiv_UMP.

(** * Group 7: is the circle’s computation rule necessary?

Are the “computation rules” in the universal property of the circle really required, or are then unnecessary?  Prove or disprove! *)
Section Comp_Rule_Redundant.

  (** A weakened form of [circle_rec_structure], omitting the “computation rules” *)
  Definition weak_circle_rec_structure {S : UU} {b : S} (l : b = b) : UU
  := ∏ (Y : S -> UU) (y_b : Y b) (y_l : transportf _ l y_b = y_b),
     ∏ x:S, Y x.

  Definition comp_rule_redundant : UU
  := ∏ (X:UU) (b:X) (l:b=b),
      weak_circle_rec_structure l -> circle_rec_structure l.

  Theorem comp_rule_redundant_or_necessary
    : comp_rule_redundant ∨ ¬ comp_rule_redundant.
  Proof.
  (** Are the computation rules redundant?  Either prove they are, or disprove by giving a counterexample! *)
  Admitted.

End Comp_Rule_Redundant.

(** * Group 8: Implementing the circle using Z-torsors

The goal of the type is to give an implementation of the circle: we define “Z-torsors”, and show that the type of Z-torsors is a circle.

The proof is only very roughly outlined — fleshing out the structure of the section is entirely left for the student. *)
Section Z_torsors.

  Definition hz_auto : auto_type.
  (* probably better to define this not here, but upstream as a component of the definition of [hz_ptd_auto] *)
  Admitted.

  (** There is a general definition of “G-torsor” for an arbitrary group G.

  We don’t give the general definition, but a simplified definition for the special case where G is the integers. *)
  Definition Z_torsor : UU
  := ∑ (X : auto_type), ∥ X = hz_auto ∥.

  Local Definition base : Z_torsor.
  Admitted.

  Local Definition loop : base = base.
  Admitted.

  Theorem Z_torsors_circle : circle_rec_structure loop.
  Proof.
  (* quite long, and quite mathematically substantial! *)
  Admitted.

End Z_torsors.

(*
*** Local Variables: ***
*** coq-prog-args: ("-type-in-type") ***
*** End: ***
*)
