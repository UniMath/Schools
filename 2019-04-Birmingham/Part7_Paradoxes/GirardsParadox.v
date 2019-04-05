(** In this file, you will fill in the details in the proof of *Girard's paradox*, as described in
Martin-Lof's 1972 "An intuitionistic theory of types", which thwarted Martin-Lof's original plan
for a type theory having "Type-in-Type".

The proof is a replication of the classic "Burali-Forti" paradox showing (like Russell's paradox)
the problem with a naive theory of sets in which one does not distinguish between "set" and
"proper class"; it shows that the set of all ordinals cannot itself be a set. The idea is to show
that the set of all ordinals would itself be an ordinal, and from this to derive a contradiction.

Here, an *ordinal* is the "order-type" (i.e. equivalence class under order-preserving isomorphisms)
of a *well-order*, where a *well-order* is a linear order having no infinite descending sequences of
elements.

One simplification in Girard's paradox is that "well-ordering" is replaced by "well-founded relation".
Here is the classical Burali-Forti paradox, with this simplification.

A *well-founded relation* on a set A is defined to be a binary relation <⊆A×A such that there does
not exist a sequence aₙ∈A such that aₙ₊₁<aₙ for all n∈ℕ. Given any two sets A and B with well-founded
relations <₁ and <₂, we say that (A,<₁) is *less than* (B,<₂), and write (A,<₁)<(B,<₂), if there is
a mapping f:A→B which is order-preserving and which is *dominated* by some element b∈B, i.e.,
the image of f lies in the "initial segement" {x∈B:x<₂b} of B.

This puts a binary relation <⊆W×W on the set W of all sets with a well-founded relation. We can see
that it is well-founded as follows. Given a sequence (Aₙ,<ₙ) with (Aₙ₊₁,<ₙ₊₁)<(Aₙ,<ₙ) for all n∈ℕ,
we can use the associated mappings Aₙ₊₁→Aₙ to construct a sequence of elements aₙ of A₁ -- namely,
the images of the "dominating elements" of the various Aₙ -- which is descending with respect to <₁,
thus contradicting the well-foundedness of <₁.

We conclude that < is a well-founded relation on W, so (W,<)∈W. Next, for any (A,≼)∈W, we show that
(A,≼)<(W,<). Indeed, we have the function A→W which sends a∈A to the set a↓={x∈A:x≼a}⊆A with the
relation given by restricting ≼ to a↓. This function is order-preserving since if a≼b, then the
inclusion a↓↪b↓ is order-preserving and is dominated by a∈b↓; and it is dominated by (A,≼), since
for each a∈A, the inclusion a↓↪A is order-preserving and dominated by a∈A.

Finally, we arrive at a contradiction; since (A,≼)<(W,<) for every (A,≼)∈W, we in particular have
(W,<)<(W,<). But no well-founded relation can have an element which is related to itself, since then
the constant sequence is an infinite descending sequence. Q.E.A.

The corresponding proof in type theory proceeds along the same lines, making the usual modifications
according to the "propositions-as-types" philosophy. For example "binary relation" is replaced by
"binary type-valued function", and "there exists order-preserving mapping f:A→B which is dominated
by some element b∈B" is replaced by "the type of mappings f:A→B together with an element b:B,
a proof that f is order preserving, and a proof that f is dominated by b", and so on.

The details are given (by you!) below.
**)

Require Import UniMath.Foundations.All.

Axiom fill_me : forall {X : UU}, X. (* Remove this line when you are finished. *)

(** Exercise: define the type of *well-founded relations* on a type T.
    This should be a triple consisting of
     - a binary relation (i.e. binary type-valued function) on T,
     - a proof that the relation is transitive,
     - and a proof that there are no infinite descending chains. (I.e., a function
       which takes a function f:nat→T and a proof that f(n+1)<f(n) for all n,
       and returns an element of the empty type)
*)
Definition wf_rel (T : UU) : UU
  := fill_me.

(* A wf_type ("well-founded type") is a type with a well-founded relation. *)
Definition wf_type : UU := total2 wf_rel.

(* The underyling type of a wf_type. *)
Definition uset (w : wf_type) : UU := pr1 w.
(* Exercise: define the underlying relation of a wf_type. *)
Definition urel (w : wf_type) : uset w → uset w → UU := fill_me.

(* Exercise: define a binary relation on well-ordered types as follows. The type wf_type_lt A B
   should be the type of functions f:A→B together with a proof that f is order preserving, an,
   element b:B, and a proof that for each a:A, f(a)<b. *)
Definition wf_type_lt (A : wf_type) (B : wf_type) : UU
  := fill_me.

(* Prove that wf_type_lt is transitive. *)
Definition wf_type_lt_trans : ∏ x y z : wf_type,
    wf_type_lt x y → wf_type_lt y z → wf_type_lt x z.
Proof.
  exact fill_me.
Defined.

(** Next, you will show that wf_type_lt is well-founded. **)

(* Exercise: given a descending sequence f : nat → wf_type, define a map from each
   f(n) to f(0) by composing all the intermediate maps. *)
Definition wf_type_seq_shift
             (f : nat → wf_type)
             (b : ∏ n : nat, wf_type_lt (f (S n)) (f n))
           : ∏ (n : nat), (uset (f n) → uset (f 0)).
Proof.
  exact fill_me.
Defined.

(* Exercise: now use this to obtain a sequence in f(0) *)
Definition wf_type_shifted_seq
             (f : nat → wf_type)
             (b : ∏ n : nat, wf_type_lt (f (S n)) (f n))
           : nat → uset (f 0).
Proof.
  exact fill_me.
Defined.

(* Exercise: prove that in the resulting sequence in f(0), each element is less than the last. *)
Definition wf_type_seq_comp
             (f : nat → wf_type)
             (b : ∏ n : nat, wf_type_lt (f (S n)) (f n))
           : ∏ (n : nat) {x y : uset (f n)},
             urel (f n) x y →
             urel (f 0) (wf_type_seq_shift f b n x) (wf_type_seq_shift f b n y).
Proof.
  exact fill_me.
Qed.

(* Exercise: show that the resulting sequence on f(0) is descending. *)
Lemma wf_type_seq_desc
        (f : nat → wf_type)
        (b : ∏ n : nat, wf_type_lt (f (S n)) (f n))
      : ∏ n : nat, urel (f 0) (wf_type_shifted_seq f b (S n)) (wf_type_shifted_seq f b n).
Proof.
  exact fill_me.
Defined.

(* Exercise: define the wf_rel on wf_type with underlying relation wf_type_lt. *)
Definition wfs_wf : wf_rel wf_type.
Proof.
  exact fill_me.
Defined.

(* We now define wf_type_lt as an element of wf_type. *)
Definition wf_type_of_wf_types : wf_type := (wf_type,, (wfs_wf)).

(** Next, you will show that wf_type_of_wf_types is a maximal element with respect to
    wf_type_lt. **)

(* Exercise: for each wf_type w, define a function from w to wf_type
   by sending each element x to the initial segment "{y:y<x}". *)
Definition maxi_fun (w : wf_type) : uset w → wf_type.
Proof.
  exact fill_me.
Defined.

(* Exercise: prove that maxi_fun is order-preserving. *)
Lemma maxi_homo (w : wf_type) : ∏ (x y : uset w),
    urel w x y → wf_type_lt (maxi_fun w x) (maxi_fun w y).
Proof.
  exact fill_me.
Defined.

(* Exercise: prove that w itself dominates the image of w under maxi_fun. *)
Lemma maxi_dom (w : wf_type) : ∏ (x : uset w), wf_type_lt (maxi_fun w x) w.
Proof.
  exact fill_me.
Defined.

(* Exercise: prove that wf_type_of_wf_types is maximal with respect to wf_type_lt *)
Lemma maxi (w : wf_type) : wf_type_lt w wf_type_of_wf_types.
Proof.
  exact fill_me.
Defined.

(** We now come to the part where you make the universe explode. **)

(* Exercise: prove that wf_type_of_wf_types is greater than itself with respect to wf_type_lt. *)
Proposition uh_oh : urel wf_type_of_wf_types wf_type_of_wf_types wf_type_of_wf_types.
Proof.
  exact fill_me.
Defined.

(* Exercise: prove that every wf_type is irreflexive by producing an infinite descending chain. *)
Proposition irref (w : wf_type) : ∏ (x : uset w), (urel w) x x → empty.
Proof.
  exact fill_me.
Defined.

(* Exercise: conclude that the universe explodes. *)
Proposition the_universe_explodes : empty.
Proof.
  exact fill_me.
Defined.
