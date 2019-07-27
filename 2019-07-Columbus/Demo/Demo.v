Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.PartB.


(* First, we define addition on the natural numbers and its associativity, commutativity.*)

Definition nat_rec (A : UU) (a : A) (f : nat → A → A) : nat → A :=
  nat_rect (λ _, A) a f.

Definition add (m : nat) : nat → nat := nat_rec nat m (λ _ y, S y).

(* We've defined the function (i.e. program) add. Now we can run it. *)

Eval compute in add 11 4.

Notation "m ∔ n" := (add m n) (at level 50).

Eval compute in 11 ∔ 4.

(* There's no difference in writing Definition, Lemma, Theorem...

In the following results, we're *interactively* proving our theorem.
 *)

Lemma plus0 (n : nat): 0 ∔ n = n.
Proof.
  induction n as [| n IHn].
  - cbn.
    exact (idpath 0).
  - cbn.
    apply maponpaths.
    exact IHn.
Defined.

(*
- Induction applies the elimination principle of nat.
- idpath 0 is r_0.
- exact x is used to supply x as the 'answer'.
- cbn stands for "call by name". This reduces the expression in the goal.
- maponpaths is a function that applies a function, here S, to a path, here 0 ∔ n = n.
- apply maponpaths uses this function to reduce the goal.
*)

(* We can print plus0 to inspect the lambda term that we just constructed. *)

Print plus0.

Lemma plus1 (m n: nat): S m ∔ n = S (m ∔ n).
  Proof.
    induction n as [| n IHn].
    - cbn.
      apply (idpath (S m)).
    - cbn.
      apply maponpaths.
      exact IHn.
  Defined.

Proposition comm (m n: nat): m ∔ n = n ∔ m.
  Proof.
    induction n as [| n IHn].
    - cbn.
      rewrite (plus0 m).
      exact (idpath m).
    - cbn.
      rewrite plus1.
      exact (maponpaths S IHn).
  Defined.

(* rewrite takes an equality, say x = y, looks for an occurence of x in the goal, and changes it to y. *)

Proposition ass (m n o : nat): (m ∔ n) ∔ o = m ∔ (n ∔ o).
  Proof.
    induction o as [| o IHo].
    - cbn.
      exact (idpath (m ∔ n)).
    - cbn.
    apply maponpaths.
    exact IHo.
  Defined.


(* Characterization of paths in Sigma types. *)

Definition tr {B: UU} {E: B → UU} {a b: B} (p : a = b) (e: E a): E b.
  Proof.
    induction p.
    exact e.
  Defined.

(* Induction here refers to path induction. *)

Definition EQ (X Y : UU) : UU := ∑ (f : X -> Y), (∑ (g : Y -> X), (∑ (egf: ∏ x : X, g (f x) = x),  ∏ y : Y, f (g y) = y)).

Notation "X ≂ Y" := (EQ X Y) (at level 50).


Proposition SigmaPaths (B: UU) (E: B → UU) (s t: ∑ (x: B), (E x)): (s = t) ≂ ( ∑ (p: pr1 s = pr1 t), ((tr p (pr2 s)) = pr2 t)).
Proof.
  use tpair.
  - intro p.
    induction p.
    use tpair.
    + apply (idpath (pr1 s)).
    + cbn.
      apply (idpath (pr2 s)).
  - use tpair.
    + induction s as [b1 e1].
      induction t as [b2 e2].
      cbn.
      intro s.
      induction s as [p q].
      induction p.
      cbn in q.
      induction q.
      apply (idpath (b1,, e1)).
    + use tpair.
      -- intro p.
         induction p.
         cbn.
         induction s as [b e].
         exact (idpath (idpath (b,, e))).
      -- intro r.
         induction r as [p q].
         induction s as [b1 e1].
         induction t as [b2 e2].
         cbn in p.
         induction p.
         cbn in q.
         induction q.
         cbn.
         exact (idpath (idpath b1,, idpath e1)).
Defined.

(*
- 'use tpair' splits the ∑ type in the goal into two subgoals.
- 'intro' is used when the goal is a function. It turns the domain of the goal into a hypothesis, and the codomain into the new goal.
- 'induction s as [b1 e1]' applies elimination rule of Σ types so that we only have consider pairs b1 ,, e1.
 *)


(* We can print the λ term we just constructed. *)

Print SigmaPaths.


(* Now we show that the space of based paths is contractible. *)


Proposition basedpathscontractible {A: UU} (a: A) :  iscontr(∑ (b: A), (a = b)).
  unfold iscontr.
  use tpair.
  - use tpair.
    + exact a.
    + cbn.
      exact (idpath a).
  - cbn.
    intro t.
    induction t as [b p].
    induction p.
    apply (idpath (a,, idpath a)).
Defined.

(*
- Here ∃! is an abbreviation for iscontr.
- 'unfold iscontr' unfolds the definition of iscontr for us.
*)