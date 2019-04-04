(** Imports *)

Require Export UniMath.Foundations.Propositions.

Axiom fill_me : forall {X : UU}, X. (* Remove this line when you are finished. *)

(** * The type of sets i.e. of types of h-level 2 in [UU] *)

Definition hSet : UU := ∑ X : UU, isaset X.
Definition hSetpair (X : UU) (i : isaset X) := tpair isaset X i : hSet.
Definition pr1hSet : hSet -> UU := @pr1 UU (λ X : UU, isaset X).
Coercion pr1hSet: hSet >-> UU.

Definition setproperty (X : hSet) := pr2 X.

(** * Applications of Hedberg's theorem *)

(** Define a map from [bool] to [UU] that maps
    [true] to [unit] (the one-element type) and
    [false] to [empty] (the empty type).
*)
Definition bool_to_type : bool -> UU
  := bool_rect (λ _ : bool, UU) unit empty.

(** Show that there is no path from [true] to [false]. *)
Theorem no_path_from_true_to_false : true != false.
Proof.
  apply fill_me.
Defined.

(** Show that there is no path from [false] to [true]. *)
Theorem no_path_from_false_to_true : false != true.
Proof.
  apply fill_me.
Defined.

(** Construct decidable equality on [bool]. *)
Theorem isdeceqbool : isdeceq bool.
Proof.
  unfold isdeceq. intros x' x. induction x.
  - induction x'.
    + unfold decidable.
      apply fill_me.
    + apply fill_me.
  - induction x'.
    + apply fill_me.
    + apply fill_me.
Defined.

Check isasetifdeceq.

Theorem isaset_bool : isaset bool.
Proof.
  apply fill_me.
Defined.

(** * [nat] is a set *)

(** Define a map from [nat] to [UU] that maps
    [0] to the singleton type and
    [S n] to the empty type for any [n].
*)
Definition nat_to_type : nat -> UU
  := nat_rect _ unit (fun _ _ => empty).

Lemma no_path_from_zero_to_successor (x : nat) : 0 != S x.
Proof.
  apply fill_me.
Defined.

Lemma no_path_from_successor_to_zero (x : nat) : S x != 0.
Proof.
  apply fill_me.
Defined.

(** Define a predecessor function on [nat]:
    [0] is mapped to [0]
    [S m] is mapped to [m]
 *)
Definition predecessor : nat -> nat
  := nat_rect _ 0 (fun m (r : nat) => m).

Lemma invmaponpathsS (n m : nat) : S n = S m -> n = m.
Proof.
  apply fill_me.
Defined.

(** The following constant will be useful for the next lemma. *)
Check @negf.

Lemma noeqinjS (x x' : nat) : x != x' -> S x != S x'.
Proof.
  apply fill_me.
Defined.

Theorem isdeceqnat : isdeceq nat.
Proof.
  apply fill_me.
Defined.

Lemma isasetnat : isaset nat.
Proof.
  apply fill_me.
Defined.

(** * Functions in sets *)

Definition is_injective {X Y : hSet} (f : X -> Y) : UU
  := ∏ (x x': X), f x = f x' -> x = x'.

(* This is a useful lemma for checking that dependent function types are propositions or sets *)
Check impred.

Lemma isaprop_is_injective {X Y : hSet} (f : X -> Y)
  : isaprop (is_injective f).
Proof.
  apply fill_me.
Defined.
(** Question: does the above proof need both X and Y to be sets? *)

(** * The universe is not a set *)
(** The next result requires univalence *)

Require Import UniMath.Foundations.UnivalenceAxiom.

Module universe_is_not_a_set.

  (* We will show that bool has a weak equivalence besides the identity. *)

  Lemma isweq_negb : isweq negb.
  Proof.
    use gradth.
    - exact negb.
    - intro x. induction x; apply idpath.
    - intro x; induction x; apply idpath.
  Defined.

  Definition weq_negb : bool ≃ bool := weqpair negb isweq_negb.

  (* Show that negb is not equal to the identity.
     It suffices, using toforallpaths, to show that they differ on some element. *)
  Check toforallpaths.

  Lemma no_path_weq_negb_idweq : weq_negb != idweq bool.
  Proof.
    apply fill_me.
  Defined.

  (* Using Univalence, we can show that if the universe were a set, then
     negb would have to be equal to the identity. *)

  Definition isaset_UU_gives_path_weq_negb_idweq
    : isaset UU → weq_negb = idweq bool.
  Proof.
    intro H.
    set (H':= H bool bool).
    set (T:= invmaponpathsweq (invweq (weqpair _ (univalenceAxiom bool bool)))).
    apply T.
    apply H'.
  Defined.

  Definition not_isaset_UU : ¬ isaset UU.
  Proof.
    apply fill_me.
  Defined.

End universe_is_not_a_set.

(** * Relations *)

(** ** Definitions *)

Definition hrel (X : UU) : UU := X -> X -> hProp.

Definition isrefl {X : UU} (R : hrel X) : UU
  := ∏ x : X, R x x.
Definition istrans {X : UU} (R : hrel X) : UU := fill_me.
Definition issymm {X : UU} (R : hrel X) : UU := fill_me.

Definition ispreorder {X : UU} (R : hrel X) : UU := istrans R × isrefl R.

Definition iseqrel {X : UU} (R : hrel X) : UU := ispreorder R × issymm R.

Definition iseqrelconstr {X : UU} {R : hrel X}
           (trans0 : istrans R)
           (refl0 : isrefl R)
           (symm0 : issymm R)
  : iseqrel R
  := dirprodpair (dirprodpair trans0 refl0) symm0.

(** ** Eqivalence relations *)

Definition eqrel (X : UU) : UU
  := ∑ R : hrel X, iseqrel R.
Definition eqrelpair {X : UU} (R : hrel X) (is : iseqrel R)
  : eqrel X
  := tpair (λ R : hrel X, iseqrel R) R is.
Definition eqrelconstr {X : UU} (R : hrel X)
           (is1 : istrans R) (is2 : isrefl R) (is3 : issymm R) : eqrel X
  := eqrelpair R (dirprodpair (dirprodpair is1 is2) is3).

Definition pr1eqrel (X : UU) : eqrel X -> (X -> (X -> hProp)) := @pr1 _ _.
Coercion pr1eqrel : eqrel >-> Funclass.

Definition eqreltrans {X : UU} (R : eqrel X) : istrans R := pr1 (pr1 (pr2 R)).
Definition eqrelrefl {X : UU} (R : eqrel X) : isrefl R := pr2 (pr1 (pr2 R)).
Definition eqrelsymm {X : UU} (R : eqrel X) : issymm R := pr2 (pr2 R).

(** * The type of subtypes of a given type *)

Definition hsubtype (X : UU) : UU := X -> hProp.

(** The carrier of a subtype *)
Definition carrier {X : UU} (A : hsubtype X) : UU := ∑ x : X, A x.

Check isasethProp.
Check (impred 2).

Lemma isasethsubtype (X : UU) : isaset (hsubtype X).
Proof.
  apply fill_me.
Defined.

(** ** A subtype with paths between any two elements is an [hProp]. *)

Lemma isapropsubtype {X : UU} (A : hsubtype X)
      (is : ∏ (x1 x2 : X), A x1 -> A x2 -> x1 = x2)
  : isaprop (carrier A).
Proof.
  apply invproofirrelevance.
  intros x x'.
  assert (X0 : isincl (@pr1 _ A)).
  {
    apply isinclpr1.
    intro x0.
    apply (pr2 (A x0)).
  }
  apply (invmaponpathsincl (@pr1 _ A) X0).
  induction x as [ x0 is0 ].
  induction x' as [ x0' is0' ].
  simpl.
  apply (is x0 x0' is0 is0').
Defined.

(** ** Equivalence classes with respect to a given relation *)

Definition iseqclass {X : UU} (R : hrel X) (A : hsubtype X) : UU
  :=
    ∥ carrier A ∥ (* is non-empty *)
      ×
      ((∏ x1 x2 : X, R x1 x2 -> A x1 -> A x2)
         ×
         (∏ x1 x2 : X, A x1 -> A x2 -> R x1 x2)).

Definition iseqclassconstr {X : UU} (R : hrel X) {A : hsubtype X}
           (ax0 : ishinh (carrier A))
           (ax1 : ∏ x1 x2 : X, R x1 x2 -> A x1 -> A x2)
           (ax2 : ∏ x1 x2 : X, A x1 ->  A x2 -> R x1 x2)
  : iseqclass R A
  := dirprodpair ax0 (dirprodpair ax1 ax2).

Definition eqax0 {X : UU} {R : hrel X} {A : hsubtype X}
  : iseqclass R A -> ishinh (carrier A)
  := λ is : iseqclass R A, pr1 is.
Definition eqax1 {X : UU} {R : hrel X} {A : hsubtype X}
  : iseqclass R A -> ∏ x1 x2 : X, R x1 x2 -> A x1 -> A x2
  := λ is : iseqclass R A, pr1 (pr2 is).
Definition eqax2 {X : UU} {R : hrel X} {A : hsubtype X}
  : iseqclass R A -> ∏ x1 x2 : X, A x1 -> A x2 -> R x1 x2
  := λ is : iseqclass R A, pr2 (pr2 is).

Lemma isapropiseqclass {X : UU} (R : hrel X) (A : hsubtype X)
  : isaprop (iseqclass R A).
Proof.
  apply isofhleveldirprod.
  - apply propproperty.
  - apply fill_me.
Defined.

(** ** Setquotient defined in terms of equivalence classes *)

Definition setquot {X : UU} (R : hrel X) : UU
  := ∑ A : hsubtype X, iseqclass R A.

Definition setquotpair {X : UU} (R : hrel X) (A : hsubtype X)
           (is : iseqclass R A)
  : setquot R
  := A ,, is.

Definition pr1setquot {X : UU} (R : hrel X)
  : setquot R -> hsubtype X
  := @pr1 _ (λ A : _, iseqclass R A).
Coercion pr1setquot : setquot >-> hsubtype.

Lemma isinclpr1setquot {X : UU} (R : hrel X) : isincl (pr1setquot R).
Proof.
  apply isinclpr1.
  intro x0.
  apply isapropiseqclass.
Defined.

Definition setquottouu0 {X : UU} (R : hrel X) (a : setquot R)
  := carrier (pr1 a).
Coercion setquottouu0 : setquot >-> UU.

Theorem isasetsetquot {X : UU} (R : hrel X) : isaset (setquot R).
Proof.
  apply (isasetsubset (@pr1 _ _) (isasethsubtype X)).
  apply isinclpr1setquot.
Defined.

Theorem setquotpr {X : UU} (R : eqrel X) : X -> setquot R.
Proof.
  intro x.
  set (rax := eqrelrefl R).
  set (sax := eqrelsymm R).
  set (tax := eqreltrans R).
  apply (tpair _ (λ x0 : X, R x x0)).
  split.
  - exact (hinhpr (tpair _ x (rax x))).
  - split; intros x1 x2 X1 X2.
    + exact fill_me.
    + exact fill_me.
Defined.

Lemma setquotl0 {X : UU} (R : eqrel X) (c : setquot R) (x : c) :
  setquotpr R (pr1 x) = c.
Proof.
  Set Printing Coercions.
  apply (invmaponpathsincl _ (isinclpr1setquot R)).
  Unset Printing Coercions.
  apply funextsec; intro x0.
  apply hPropUnivalence; intro r.
  - exact fill_me.
  - exact fill_me.
Defined.

Theorem issurjsetquotpr {X : UU} (R : eqrel X) : issurjective (setquotpr R).
Proof.
  unfold issurjective.
  intro c. apply (@hinhuniv (carrier c)).
  - intro x. apply hinhpr.
    use tpair.
    + exact (pr1 x).
    + apply setquotl0.
  - apply (eqax0 (pr2 c)).
Defined.

Lemma iscompsetquotpr {X : UU} (R : eqrel X) (x x' : X)
  : R x x' -> setquotpr R x = setquotpr R x'.
Proof.
  intro r.
  Set Printing Coercions.
  apply (invmaponpathsincl _ (isinclpr1setquot R)).
  Unset Printing Coercions.
  simpl. apply funextsec.
  intro x0. apply hPropUnivalence.
  - intro r0. exact fill_me.
  - intro x0'. exact fill_me.
Defined.

(** *** Universal property of [seqtquot R] for functions to sets satisfying compatibility condition [iscomprelfun] *)

Definition iscomprelfun {X Y : UU} (R : hrel X) (f : X -> Y) : UU
  := ∏ x x' : X, R x x' -> f x = f x'.

Lemma isapropimeqclass {X : UU} (R : hrel X) (Y : hSet) (f : X -> Y)
      (is : iscomprelfun R f) (c : setquot R) :
  isaprop (image (λ x : c, f (pr1 x))).
Proof.
  apply isapropsubtype.
  intros y1 y2. simpl.
  apply (@hinhuniv2 _ _ (hProppair (y1 = y2) (pr2 Y y1 y2))).
  intros x1 x2. simpl.
  destruct c as [ A iseq ].
  destruct x1 as [ x1 is1 ]. destruct x2 as [ x2 is2 ].
  destruct x1 as [ x1 is1' ]. destruct x2 as [ x2 is2' ].
  simpl in is1. simpl in is2. simpl in is1'. simpl in is2'.
  assert (r : R x1 x2) by apply (eqax2 iseq _ _ is1' is2').
  apply ( !is1 @  (is _ _ r) @ is2).
Defined.

Definition setquotuniv {X : UU} (R : hrel X) (Y : hSet) (f : X -> Y)
        (is : iscomprelfun R f) (c : setquot R) : Y.
Proof.
  apply (pr1image (λ x : c, f (pr1 x))).
  apply (@squash_to_prop (carrier c)).
  - apply (eqax0 (pr2 c)).
  - apply isapropimeqclass. apply is.
  - unfold carrier. apply prtoimage.
Defined.

(** Note : the axioms rax, sax and trans are not used in the proof of
  setquotuniv. If we consider a relation which is not an equivalence relation
  then setquot will still be the set of subsets which are equivalence classes.
  Now however such subsets need not to cover all of the type. In fact their set
  can be empty. Nevertheless setquotuniv will apply. *)

Theorem setquotunivcomm {X : UU} (R : eqrel X) (Y : hSet) (f : X -> Y)
        (is : iscomprelfun R f) :
  ∏ x : X, setquotuniv R Y f is (setquotpr R x) = f x.
Proof.
  intros.
  apply idpath.
Defined.

Lemma setquotpr_eq_eqrel {X : UU} (R : eqrel X) (x x' : X)
  : setquotpr R x = setquotpr R x' → R x x'.
Proof.
  intro e.
  set (e' := maponpaths (pr1setquot R) e). simpl in e'.
  set (e'' := maponpaths (λ f : _, f x') e'). simpl in e''.
  rewrite e''.
  apply eqrelrefl.
Defined.

Theorem weqpathsinsetquot {X : UU} (R : eqrel X) (x x' : X) :
  R x x' ≃ setquotpr R x = setquotpr R x'.
Proof.
  intros.
  exists (iscompsetquotpr R x x').
  apply isweqimplimpl.
  - intro e.
    set (e' := maponpaths (pr1setquot R) e). simpl in e'.
    set (e'' := maponpaths (λ f : _, f x') e'). simpl in e''.
    rewrite e''.
    apply eqrelrefl.
  - apply propproperty.
  - apply isasetsetquot.
Defined.

(* End of file *)
