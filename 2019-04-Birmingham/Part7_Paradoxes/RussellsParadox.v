(** Unimath 2019
    Thorsten Altenkirch

    Russell's paradox

    The material in this file contains coq proofs
    which can be read and animated with coqide or xemacs+proofgeneral.

**)

Require Import UniMath.Foundations.All.

Section russell.

Set Implicit Arguments.

(** We simulate Set : Set by stating that there is a Set set:Set
    which contains names for all sets.
*)

Variable set : hSet.
Variable name : hSet → set.
Variable El : set → hSet.
Axiom reflect : ∏ A:hSet, A = El (name A).

Lemma paradox : ∅.
Abort.

End russell.

