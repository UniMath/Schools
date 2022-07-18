(**

<<
                   Lecture 2: Fundamentals of Coq
      -------------------------------------------------------------
        Anders Mörtberg (Carnegie Mellon and Stockholm University)
        Minor modifications made by Marco Maggesi (Univesity of Florence).
>>

The Coq proof assistant is a programming language for writing
proofs: https://coq.inria.fr/

It has been around since 1984 and was initially implemented by Thierry
Coquand and his PhD supervisor Gérard Huet. The first version, called
CoC, implemented the Calculus of Constructions as presented in:

"The Calculus of Constructions"
Thierry Coquand and Gérard Huet
Information and Computation 76(2–3): 95–120. 1988.

It was later extended to the Calculus of Inductive Constructions and
the name changed to Coq. These type theories are similar to Martin-Löf
type theory. As Coq is supposed to be a programming language for
developing proofs all programs have to be terminating, so it can be
seen as a "total" programming language.

The Coq system has a very long and detailed reference manual:

https://coq.inria.fr/distrib/current/refman/

However, UniMath is only using a small subset of Coq, so there is a
lot of information that is not relevant for UniMath development in
there. The fragment of Coq that UniMath uses consists of:

- Pi-types (with judgmental eta)
- Sigma-types (with judgmental eta)
- The inductive types of natural numbers, booleans, unit and empty
- Coproduct types
- A universe UU

The reason we only have one universe is that there is no support for
universe resizing axioms in Coq yet. Because of this we assume the
inconsistent rule UU : UU, but we are working on improving this so
that we can make use of Coq's universe consistency checker.
Furthermore, the reason UniMath only relies on this subset is that
everything in UniMath has to be motivated by the model in simplicial
sets:

https://arxiv.org/abs/1211.2851

In this lecture I will show some things than can be done in UniMath as
a programming language. In the later lectures we will also see how to
prove properties about the programs that we can write in UniMath.

The UniMath library can be found at:

https://github.com/UniMath/UniMath

This whole file is a Coq file and it hence has the file ending ".v" (v
for "vernacular") and can be processed using:

- emacs with proof-general: https://proofgeneral.github.io/

- Coq IDE

I use emacs as it is also an extremely powerful text editor, but if
you never saw emacs before it might be quite overwhelming. An
alternative that might be easier for newcomers is Coq IDE (interactive
development environment). It also has some features that emacs doesn't
have so some Coq experts use it as well, but in this talk I will use
emacs.

In order to make emacs interact with Coq one should install Proof
General. This is an extension to emacs that enables it to interact
with a range of proof assistants, including Coq. For UniMath
development one should also install agda-mode in order to be able to
properly insert unicode characters.

The basic keybinding that I use when working in Proof General are:
<<
C-c C-n      -- Process one line
C-c C-u      -- Unprocess a line
C-c C-ENTER  -- Process the whole buffer up until the cursor
C-c C-b      -- Process the whole file
C-c C-r      -- Unprocess (retract) the whole file
C-x C-c      -- Kill the Coq process
>>
For more commands see:

https://proofgeneral.github.io/doc/master/userman/Basic-Script-Management/#Script-processing-commands
https://proofgeneral.github.io/doc/master/userman/Coq-Proof-General/#Coq_002dspecific-commands

Here C = CTRL and M = ALT on a standard emacs setup, so "C-c C-n"
means "press c while holding CTRL and then press n while still holding
CTRL" (note that the keybindings are case sensitive). ENTER is the
"return" key on my keyboard.

Various basic emacs commands:
<<
C-x C-f      -- Find file
C-x C-s      -- Save file
C-x C-x      -- Exit emacs
C-x b        -- Kill buffer
C-_          -- Undo
C-x 1        -- Maximize buffer
C-x 2        -- Split buffer horizontally
C-x 3        -- Split buffer vertically
M-%          -- Search-and-replace
M-;          -- Comment region
>>
For more commands see: https://www.gnu.org/software/emacs/ (or just
Google "emacs tutorial")

*)

(** To import a file write:
<<
Require Import Dir.Filename.
>>
*)

(**

This will import the file Filename in the directory Dir. This assumes
that directory Dir is visible to Coq, that is, in the list of
directories in which Coq looks for files to import. If you are working
in the UniMath directory then Coq will be able to find all of the
files in the UniMath library, but if you are in another directory you
need to the update your LoadPath by running
<<
Add LoadPath "/path/to/UniMath".
>>
(where "/path/to/UniMath/" is replaced to the path where UniMath is
located on your computer).

Coq has a fancy module system which allows you to import and export
definitions in various complicated ways. We extremely rarely use
this in UniMath so you can safely ignore it for now. The only thing
you need to know is that there is an alternative to Require Import:
<<
Require Export Dir.Filename.
>>
that is used in some files. This will make the file you are working
on import all of the definitions in Dir.Filename and then export
them again so that any file that imports this file also gets the
definitions in Dir.Filename. I personally only use Require Import.

*)

(* Let's import one of the most basic UniMath file: *)
Require Import UniMath.Foundations.Preamble.
(* This file contains definition of the inductive types of UniMath,
makes UU the name for the universe and various other basic things. *)

(** * Definitions, lambda terms *)

(** The polymorphic identity function *)
Definition idfun : forall (A : UU), A -> A := fun (A : UU) (a : A) => a.

(** forall = Pi *)
(** fun = lambda *)

Check idfun.  (* Or use Ctrl-Alt-C or Ctrl-Cmd-C on idfun. *)
Print idfun.  (* Or use Ctrl-Alt-P or Ctrl-Cmd-P on idfun. *)

Definition idfun' (A : UU) (a : A) : A := a.

Check idfun'.
Print idfun'.

(** The constant function that returns its first argument *)
Definition const (A B : UU) (a : A) (b : B) : A := a.

(** The booleans are defined in UniMath.Foundations.Preamble *)
About bool.
Print bool.

(** These are generated by true and false *)
Check true.
Check false.

(** They also come with an induction principle *)
About bool_rect.

(** Using this we can define a "recursion" principle *)
Definition ifbool (A : UU) (x y : A) : bool -> A :=
  bool_rect (fun _ : bool => A) x y.

(** We can define boolean negation: *)
Definition negbool : bool -> bool :=
  ifbool bool false true.

(** and compute with it *)
Eval compute in negbool true.

(** Coq supports many evaluation strategies, like cbn and cbv, for
details see:

https://coq.inria.fr/refman/tactics.html#Conversion-tactics

*)

(** boolean and *)
Definition andbool (b : bool) : bool -> bool :=
  ifbool (bool -> bool) (idfun bool) (const bool bool false) b.

Eval compute in andbool true true.
Eval compute in andbool true false.
Eval compute in andbool false true.
Eval compute in andbool false false.

(** The natural numbers are defined in UniMath.Foundations.Preamble *)
About nat.
Print nat.

(** They are defined as Peano numbers, but we can use numerals *)
Check 3.

(** This type also comes with an induction principle *)
Check nat_rect.

(** We can define the recursor: *)
Definition nat_rec (A : UU) (a : A) (f : nat -> A -> A) : nat -> A :=
  nat_rect (fun _ : nat => A) a f.

(**

This can be understood as a function defined by the following clauses:
<<
nat_rec m f 0 = m
nat_rec m f (S n) = f n (nat_rec m f n)
>>
*)

(** We can look at the normal form of the recursor by *)
Eval compute in nat_rec.

(** This contains a both a "fix" and "match _ with _". These primitives
of Coq are not allowed in UniMath. Instead we write everything using
recursors. The reason is that everything we write in UniMath has to be
justified by the simplicial set model and the situation for general
inductive types with match is not spelled out in detail. *)

(** If you are used to regular programming languages it might seem very
strange to only program with the recursors, but it's actually not too
bad and we can do many programs quite directly. *)

(** Truncated predecessor function *)
Definition pred : nat -> nat := nat_rec nat 0 (const nat nat).

Eval compute in pred 3.
Eval compute in pred 1.
Eval compute in pred 0.

(** We can test if a number is even by: *)
Definition even : nat -> bool := nat_rec bool true (fun _ b => negbool b).

Eval compute in even 3.
Eval compute in even 4.

(** Addition *)
Definition add (m : nat) : nat -> nat := nat_rec nat m (fun _ y => S y).

Eval compute in add 2 3.

(** We can define a nice notation for addition by: *)
Notation "x + y" := (add x y).

Eval compute in 4 + 9.

(* Use command palette "Coq: Display All Basic Low-level Contents" to
   enable/disable printing notations. *)

Check (add 3 4).  (* 3 + 4 : nat *)
(* Use command palette "Coq: Display All Basic Low-level Contents" *)
Check (add 3 4). (* add (S (S (S O))) (S (S (S (S O)))) : nat *)
(* Use command palette "Coq: Display All Basic Low-level Contents" *)
Check (add 3 4).  (* 3 + 4 : nat *)

(** To find information about a notation we can write: *)
Locate "+".

(** Coq allows us to write very sophisticated notations, for details
see: https://coq.inria.fr/refman/syntax-extensions.html *)

(** In UniMath we use a lot of unicode symbols. To input a unicode
symbol type \ and then the name of the symbol. For example \alpha
gives α. To get information about a unicode character, including
how to write it, put the cursor on top of the symbol and type:
M-x describe-char

We can write:
<<
  λ x, e        instead of   fun x => e
  ∏ (x : A), T  instead of   forall (x : A), T
  A → B         instead of   A -> B
>>
*)

(** Iterate a function n times *)
Definition iter (A : UU) (a : A) (f : A → A) (n : nat) : A :=
  nat_rec A a (λ _ y, f y) n.

Notation "f ^ n" := (λ x, iter _ x f n).

Eval compute in (pred ^ 2) 5.

Definition sub (m n : nat) : nat := (pred ^ n) m.

Eval compute in sub 15 4.
Eval compute in sub 11 15.

Definition is_zero : nat → bool := nat_rec bool true (λ _ _, false).

Eval compute in is_zero 3.
Eval compute in is_zero 0.

Definition eqnat (m n : nat) : bool :=
  andbool (is_zero (sub m n)) (is_zero (sub n m)).

Notation "m == n" := (eqnat m n) (at level 50).

Eval compute in 1 + 1 == 2.
Eval compute in 5 == 3.
Eval compute in 9 == 5.

(** Note that I could omit the A from the definition of f ̂ n and just
replace it by _. The reason is that Coq very often can infer what
arguments are so that we can omit them. *)

(** For example if I omit nat in *)
Check idfun _ 3.
(** Coq will figure it out for us. *)

(** We can tell Coq to always put _ for an argument by using curly
braces in the definition: *)

Definition idfun'' {A : UU} (a : A) : A := a.

Check idfun'' 3.
Check idfun'' true.

(** Such an argument is called an "implicit" and these are very useful
to get definitions that don't take too many arguments. However, it is
sometimes necessary to be able to give some of the arguments
explicitly, this is using "@". *)

Check @idfun'' nat 3.


(** * More inductive types *)

(** The inductive types we have seen so far come from the standard
library, but Coq allows us to define any inductive types we want. In
UniMath we don't allow this and the additional inductive types we have
are defined in Foundations. *)

(** One of these is the coproduct (disjoint union) of types *)
About coprod.
Print coprod.
Check ii1.
Check ii2.
Print inl.
Print inr.

Check (λ A B C : UU, @coprod_rect A B (λ _, C)).

Definition coprod_rec {A B C : UU} (f : A → C) (g : B → C) : coprod A B → C :=
  @coprod_rect A B (λ _, C) f g.

(** We can define integers as a coproduct of nat with itself *)

Definition Z : UU := coprod nat nat.

(* NB: Use \hermitconjmatrix to type the symbol ⊹.
       Use \minus to type the symbol − *)
Notation "⊹ x" := (inl x) (at level 20).
Notation "─ x" := (inr x) (at level 40).

(** +1 = inl 1 *)
(** 0 = inl 0 *)
(** -1 = inr 0 *)
(** Note that we get the negative numbers "off-by-one". *)


Definition Z1 : Z := ⊹ 1.
Definition Z0 : Z := ⊹ 0.
Definition Zn3 : Z := ─ 2.

(** We can define a function by case on whether the number is ⊹ n or ─ n *)
Definition Zcase (A : UU) (fpos : nat → A) (fneg : nat → A) : Z → A :=
  coprod_rec fpos fneg.

Definition negate : Z → Z :=
  Zcase Z (λ x, ifbool Z Z0 (─ pred x) (is_zero x)) (λ x, ⊹ S x).

Eval compute in negate Z0.
Eval compute in negate Z1.
Eval compute in negate Zn3.

(** We also have two more inductive types: *)

(** The unit type with one inhabitant tt *)
About unit.
Print unit.

(** The empty type with no inhabitants *)
About empty.
Print empty.


(** * Sigma types *)

(** Sigma types are called total2 and this is the only example of a
Record in the whole UniMath library. The reason we use a record is so
that we can get the eta principle definitionally. *)

About total2.
Print total2.

(** We have a notation ∑ (x : A), B for Sigma types *)

(** To form a pair use *)
Check tpair.
Locate ",,".

(** and to project out of a pair use *)
Check pr1.
Check pr2.

(** In PartA.v we define the direct product as a Sigma type *)
Definition dirprod (X Y : UU) : UU := ∑ x : X, Y.

Notation "A × B" := (dirprod A B) (at level 75, right associativity) : type_scope.

Definition dirprod_pr1 {X Y : UU} : X × Y → X := pr1.
Definition dirprod_pr2 {X Y : UU} : X × Y → Y := pr2.

Definition dirprodf {X Y X' Y' : UU} (f : X → Y) (f' : X' → Y')
  (xx' : X × X') : Y × Y' := (f (pr1 xx'),,f' (pr2 xx')).

Definition swap {X Y : UU} (xy : X × Y) : Y × X :=
  dirprodf dirprod_pr2 dirprod_pr1 (xy,,xy).

(** We can define the type of even numbers as a Sigma-type: *)
Definition even_nat : UU := ∑ (n : nat), ifbool _ unit empty (even n).

Definition test20 : even_nat := (20,,tt).

(** This Definition does not work *)
Fail Definition test3 : even_nat := (3,,tt).

(** Section's can be very useful to only write parameters that are used
many times once and for all. They are also useful for organizing your
files into logical sections. *)
Section curry.

Variables A B C : UU.

(** To make these arguments implicit use:
<<
Context {A B C : UU}.
>>
*)

Definition curry : (A × B → C) → (A → B → C) :=
  λ (f : A × B → C) (a : A) (b : B), f (a,,b).

Definition uncurry : (A → B → C) → (A × B → C) :=
  λ (f : A → B → C) (ab : A × B), f (pr1 ab) (pr2 ab).

End curry.

Check curry.
Print curry.
Check uncurry.
Print uncurry.


(** These were all the basics for interacting with Coq in this
lecture. The UniMath library is a very large library and so far we
have only seen parts of Preamble.v. When writing programs and proofs
in UniMath it is very important to be able to search the library so
that you don't do something someone else has already done. *)

(** To find everything about nat type: *)
Search nat.

(** To search for all lemmas involving the pattern *)
(* Search _ (_ -> _ -> _). *)

(** To find information about a notation *)
Locate "+".

(** More information about searching can be found in the reference
manual:

https://coq.inria.fr/distrib/current/refman/proof-engine/vernacular-commands.html?highlight=search#coq:cmd.search
*)

(**

One can also generate HTML documentation for UniMath that is a bit
easier to browse than reading text files. This is done by typing:
<<
> make html
>>
You can then open this documentation in your browser:
<<
> firefox html/toc.html
>>
In order to have your comments display properly in the HTML use the
following format:

(** This comment will be displayed *)
(** * This will be displayed as a section header *)
(** ** This will be a subsection *)

For more details see:

https://coq.inria.fr/distrib/current/refman/tools.html#coqdoc

*)

(**

The UniMath library is organized into a collection of packages that
can be found in the UniMath folder. The library is then compiled using
a Makefile which specifies in which order things has to be compiled
and how they should be compiled.

In order to have your file get compiled when you type "make" add it to
the .package/files file of the package where it belongs. See for
example: UniMath/UniMath/Foundations/.package/files

If you're working on a new package then you need to add it to the
Makefile by writing:

PACKAGES += MyPackage

*)

               (*⋆⋆⋆⋆⋆⋆ THE END ⋆⋆⋆⋆⋆⋆*)
