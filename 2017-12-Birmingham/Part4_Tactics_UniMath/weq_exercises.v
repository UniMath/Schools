(* Some exercises about equivalences *)
Require Import UniMath.Foundations.PartA.

(* Prove that the identity function is an equivalence *)
Lemma idisweq (T : UU) : isweq (idfun T).
Admitted.

(* Package this up as an equivalence *)
Definition idweq (X : UU) : X ≃ X.
Admitted.

(* Prove that any map to empty is an equivalence *)
Lemma isweqtoempty {X : UU} (f : X -> ∅) : isweq f.
Admitted.

(* Package this up as an equivalence *)
Definition weqtoempty {X : UU} (f : X -> ∅) : X ≃ ∅.
Admitted.

(* Prove that the composition of equivalences is an equivalence *)
Theorem compisweq {X Y Z : UU} (f : X -> Y) (g : Y -> Z)
        (isf : isweq f) (isg : isweq g) : isweq (g ∘ f).
Admitted.

(* Package this up as an equivalence *)
Definition weqcomp {X Y Z : UU} (w1 : X ≃ Y) (w2 : Y ≃ Z) : X ≃ Z.
Admitted.
