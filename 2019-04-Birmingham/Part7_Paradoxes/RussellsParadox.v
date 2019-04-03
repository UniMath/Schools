(** Unimath 2019
    Thorsten Altenkirch

    Russell's paradox

    The material in this file contains coq proofs
    which can be read and animated with coqide or xemacs+proofgeneral.

**)

Section russell.

Set Implicit Arguments.

(** We simulate Set : Set by stating that there is a Set set:Set
    which contains names for all sets.
*)

Variable set : Set.
Variable name : Set -> set.
Variable El : set -> Set.
Axiom reflect : forall A:Set,A = El (name A).


Lemma paradox : False.


End russell.

