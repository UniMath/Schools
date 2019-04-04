(* Exercices on propositional truncation. *)
Require Import UniMath.Foundations.PartD.

Axiom insert_solution_here : forall {A : UU}, A.


(* Consider a map f : A → B. An element y from B is in its image if there is x in A such
   that f x = y. Under the Curry-Howard correspondence one would therefore define the
   (Curry-Howard) image of f as follows. *)

Definition CH_image {A B : UU} (f : A → B) :=
  ∑ (y : B),  ∑ (x : A), f x = y.

(* However, this is a faulty definition: we certainly do not want the image to always
   be equivalent to the domain, but this is precisely what happens, as witnessed by
   the first exercise. *)

Lemma CH_image_equiv_domain {A B : UU} (f : A → B) :
  A ≃ CH_image f.
Proof.
  apply insert_solution_here.
Defined.

(* We might similarly use ∑ in place of existence in the definition of surjectivity. *)

Definition CH_surjective {A B : UU} (f : A → B) :=
  ∏ (y : B), ∑ (x : A), f x = y.

(* Recall that a map f : A → B is split when it has a right inverse. *)

Definition CH_split {A B : UU} (f : A → B) :=
  ∑ (g : B → A), f ∘ g = idfun B.

(* Now, the Curry-Howard definition of surjectivity implies that a surjective
   map is split, i.e, it has a section. (This shows that the Curry-Howard formulation
   of surjectivity is too strong.) *)
Lemma CH_surjective_if_split {A B : UU} (f : A → B) :
  CH_surjective f → CH_split f.
Proof.
  apply insert_solution_here.
Defined.

(* The converse holds as well. *)
Lemma CH_split_if_surjective {A B : UU} (f : A → B) :
  CH_split f → CH_surjective f.
Proof.
  apply insert_solution_here.
Defined.

(* In Univalent mathematics, and type theory in general, we should ask for _more_ than
   just "every split map is surjective, and vice versa". We should compare the space
   of "splitness of f" with the space of "surjectivity of f". And it turns out, that
   these are equivalent: *)
Theorem CH_surjective_equiv_split {A B : UU} (f : A → B) :
  CH_surjective f ≃ CH_split f.
Proof.
  apply insert_solution_here.
Defined.

(* Next we define a parity function which takes a number and returns the remainder modulo 2. *)

(* Map 0 to 1 and everyone else to 0. *)
Definition flip (k : nat) := nat_rect (fun _ => nat) 1 (fun _ _ => 0) k.

Definition parity (n : nat) := nat_rect (fun _ => nat) 0 (fun _ b => flip b) n.

(* The CH-image of the parity map is nat according to the above, but it should be equivalent to bool.
   We have a very strange definition of surjectivity, which we now rectify by defining a univalent
   notion of image in which we replace ∑ with ∃. *)
Require Import UniMath.Foundations.Propositions.

Definition image {A B : UU} (f : A → B) :
  ∑ (y : B), ∃ (x : A), f x = y.

(* Prove that the (univalent) image of partiy is equivalent to Bool. *)
Theorem image_parity_equiv_bool :
  image parity ≃ bool.
Proof.
  apply insert_solution_here.
Defined.
