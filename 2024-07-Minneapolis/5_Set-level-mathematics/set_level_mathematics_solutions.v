(** Imports *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Algebra.BinaryOperations.
Require Import UniMath.Algebra.Monoids.


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
  intro X. apply (transportf bool_to_type X tt).
Defined.

(** Show that there is no path from [false] to [true]. *)
Theorem no_path_from_false_to_true : false != true.
Proof.
  intro X. apply (transportb bool_to_type X tt).
Defined.

(** Construct decidable equality on [bool]. *)
Theorem isdeceqbool : isdeceq bool.
Proof.
  unfold isdeceq. intros x' x. induction x.
  - induction x'.
    + unfold decidable.
      apply ii1.
      apply idpath.
    + apply ii2.
      exact no_path_from_false_to_true.
  - induction x'.
    + apply ii2.
      exact no_path_from_true_to_false.
    + apply ii1.
      apply idpath.
Defined.

Check isasetifdeceq.

Theorem isaset_bool : isaset bool.
Proof.
  apply isasetifdeceq.
  apply isdeceqbool.
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
  intro F.
  exact (transportf nat_to_type F tt).
Defined.

Lemma no_path_from_successor_to_zero (x : nat) : S x != 0.
Proof.
  intro X. apply (no_path_from_zero_to_successor x (pathsinv0 X)).
Defined.

(** Define a predecessor function on [nat]:
    [0] is mapped to [0]
    [S m] is mapped to [m]
 *)
Definition predecessor : nat -> nat
  := nat_rect _ 0 (fun m (r : nat) => m).

Lemma invmaponpathsS (n m : nat) : S n = S m -> n = m.
Proof.
  intro e.
  apply (maponpaths predecessor e).
Defined.

(** The following constant will be useful for the next lemma. *)
Check @negf.

Lemma noeqinjS (x x' : nat) : x != x' -> S x != S x'.
Proof.
  apply (negf (invmaponpathsS x x')).
Defined.

Theorem isdeceqnat : isdeceq nat.
Proof.
  intros m.
  induction m as [ | m].
  - intro n.
    induction n as [ | n].
    + apply ii1. apply idpath.
    + apply ii2.  apply no_path_from_zero_to_successor.
  - intro n.
    induction n as [ | n].
    + apply ii2. apply no_path_from_successor_to_zero.
    + set (IHm_n := IHm n).
      induction IHm_n as [eq_m_n | not_eq_m_n ].
      * apply ii1. apply (maponpaths S eq_m_n).
      * apply ii2. apply noeqinjS. apply not_eq_m_n.
Defined.

Lemma isasetnat : isaset nat.
Proof.
  apply isasetifdeceq.
  apply isdeceqnat.
Defined.

(** * Functions in sets *)

Definition is_injective {X Y : hSet} (f : X -> Y) : UU
  := ∏ (x x': X), f x = f x' -> x = x'.

(* This is a useful lemma for checking that dependent function types are propositions or sets *)
Check impred.

Lemma isaprop_is_injective {X Y : hSet} (f : X -> Y)
  : isaprop (is_injective f).
Proof.
  unfold is_injective.
  apply impred. intro x.
  apply impred. intro y.
  apply impred. intro e.
  apply setproperty.
Defined.
(** Question: does the above proof need both X and Y to be sets? *)

(** * The universe is not a set *)
(** The next result requires univalence *)

Require Import UniMath.Foundations.UnivalenceAxiom.

Module universe_is_not_a_set.

  (* We will show that bool has a weak equivalence besides the identity. *)

  Lemma isweq_negb : isweq negb.
  Proof.
    use isweq_iso.
    - exact negb.
    - intro x. induction x; apply idpath.
    - intro x; induction x; apply idpath.
  Defined.

  Definition weq_negb : bool ≃ bool := make_weq negb isweq_negb.

  (* Show that negb is not equal to the identity.
     It suffices, using toforallpaths, to show that they differ on some element. *)
  Check toforallpaths.

  Lemma no_path_weq_negb_idweq : weq_negb != idweq bool.
  Proof.
    intro H.
    set (H':= toforallpaths _ _ _ (maponpaths pr1 H) true).
    cbn in H'.
    exact (no_path_from_false_to_true H').
  Defined.

  (* Using Univalence, we can show that if the universe were a set, then
     negb would have to be equal to the identity. *)

  Definition isaset_UU_gives_path_weq_negb_idweq
    : isaset UU → weq_negb = idweq bool.
  Proof.
    intro H.
    set (H':= H bool bool).
    set (T:= invmaponpathsweq (invweq (make_weq _ (univalenceAxiom bool bool)))).
    apply T.
    apply H'.
  Defined.

  Definition not_isaset_UU : ¬ isaset UU.
  Proof.
    exact (funcomp isaset_UU_gives_path_weq_negb_idweq no_path_weq_negb_idweq).
  Defined.

End universe_is_not_a_set.








Section Pointed.

Definition ptdset : UU := ∑ A : hSet, A.
Coercion ptdset_to_set (X : ptdset) : hSet := pr1 X.
Definition ptd (X : ptdset) : X := pr2 X.
Definition ptdset_iso (X Y : ptdset) : UU := ∑ f : X ≃ Y, f (ptd X) = ptd Y.

Definition id_weq (X Y : ptdset) : (X = Y) ≃ (X ╝ Y).
Proof.
  apply total2_paths_equiv.
Defined.

Definition ptdset_iso_weq (X Y : ptdset) : (X ╝ Y) ≃ (ptdset_iso X Y).
Proof.
  use weqtotal2.
  + Search ( (_ = _) ≃ ( _ ≃ _)).
    use hSet_univalence.
  + intro p.
    induction X as [X x].
    induction Y as [Y y].
    cbn in p.
    induction p. cbn.
    apply idweq.
Defined.

Definition sip_for_ptdset : ∏ (X Y : ptdset), (X = Y) ≃ ptdset_iso X Y.
Proof.
  intros X Y.
  eapply weqcomp.
  - apply id_weq.
  - apply ptdset_iso_weq.
Defined.

Definition transportf_ptdset :
  ∏ (P : ptdset → UU) (X Y : ptdset), ptdset_iso X Y → P X → P Y.
Proof.
  intros P X Y f.
  apply sip_for_ptdset in f.
  exact (transportf P f).
Defined.


End Pointed.



Section Monoid.

(* see Algebra/Monoids2.v, monoid_univalence *)

Local Open Scope multmonoid.

Notation "x * y" := (op x y) : multmonoid.
Notation "1" := (unel _) : multmonoid.

Search monoid.

(*
  Construct the following chain of equivalences
                           (X = Y) ≃ (X ╝ Y)
                                   ≃ (monoidiso' X Y)
                                   ≃ (monoidiso X Y).
 *)


Definition monoidiso' (X Y : monoid) : UU :=
  ∑ g : (∑ f : X ≃ Y, isbinopfun f), (pr1 g) 1 = 1.

Definition monoid_univalence_weq1 (X Y : monoid) : (X = Y) ≃ (X ╝ Y) :=
  total2_paths_equiv _ X Y.

Definition monoid_univalence_weq2 (X Y : monoid) : (X ╝ Y) ≃ (monoidiso' X Y).
Proof.
  use weqbandf.
  - exact (setwithbinop_univalence X Y).
  - intros e. cbn. use invweq. induction X as [X Xop]. induction Y as [Y Yop]. cbn in e.
    cbn. induction e. use weqimplimpl.
    + intros i. use proofirrelevance. use isapropismonoidop.
    + intros i. induction i. use idpath.
    + use setproperty.
    + use isapropifcontr. exact (@isapropismonoidop (pr1setwithbinop X) (pr2 X) Xop Yop).
Defined.
Opaque monoid_univalence_weq2.

Definition monoid_univalence_weq3 (X Y : monoid) : (monoidiso' X Y) ≃ (monoidiso X Y) :=
  weqtotal2asstor (λ w : X ≃ Y, isbinopfun w)
                  (λ y : (∑ w : weq X Y, isbinopfun w), (pr1 y) 1 = 1).

Definition monoid_univalence_map (X Y : monoid) : X = Y → monoidiso X Y.
Proof.
  intro e. induction e. exact (idmonoidiso X).
Defined.

Lemma monoid_univalence_isweq (X Y : monoid) :
  isweq (monoid_univalence_map X Y).
Proof.
  use isweqhomot.
  - exact (weqcomp (monoid_univalence_weq1 X Y)
                   (weqcomp (monoid_univalence_weq2 X Y) (monoid_univalence_weq3 X Y))).
  - intros e. induction e.
    refine (weqcomp_to_funcomp_app @ _).
    use weqcomp_to_funcomp_app.
  - use weqproperty.
Defined.


Definition monoid_univalence (X Y : monoid) : (X = Y) ≃ (monoidiso X Y)
  := make_weq
    (monoid_univalence_map X Y)
    (monoid_univalence_isweq X Y).



End Monoid.







(** * Relations *)

(** ** Definitions *)

Definition hrel (X : UU) : UU := X -> X -> hProp.

Definition istrans {X : UU} (R : hrel X) : UU
  := ∏ (x1 x2 x3 : X), R x1 x2 -> R x2 x3 -> R x1 x3.
Definition isrefl {X : UU} (R : hrel X) : UU
  := ∏ x : X, R x x.
Definition issymm {X : UU} (R : hrel X) : UU
  := ∏ (x1 x2 : X), R x1 x2 -> R x2 x1.

Definition ispreorder {X : UU} (R : hrel X) : UU := istrans R × isrefl R.

Definition iseqrel {X : UU} (R : hrel X) : UU := ispreorder R × issymm R.

Definition iseqrelconstr {X : UU} {R : hrel X}
           (trans0 : istrans R)
           (refl0 : isrefl R)
           (symm0 : issymm R)
  : iseqrel R
  := make_dirprod (make_dirprod trans0 refl0) symm0.

(** ** Eqivalence relations *)

Definition eqrel (X : UU) : UU
  := ∑ R : hrel X, iseqrel R.
Definition eqrelpair {X : UU} (R : hrel X) (is : iseqrel R)
  : eqrel X
  := tpair (λ R : hrel X, iseqrel R) R is.
Definition eqrelconstr {X : UU} (R : hrel X)
           (is1 : istrans R) (is2 : isrefl R) (is3 : issymm R) : eqrel X
  := eqrelpair R (make_dirprod (make_dirprod is1 is2) is3).

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
  apply (impred 2).
  intro x.
  exact isasethProp.
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
  := make_dirprod ax0 (make_dirprod ax1 ax2).

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
  - apply isofhleveldirprod.
    + apply impred.
      intro x.
      apply impred.
      intro x'.
      apply impred.
      intro r.
      apply impred.
      intro a.
      apply propproperty.
    + repeat (apply impred; intro).
      exact (pr2 (R t t0)).
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
    + exact (tax x x1 x2 X2 X1).
    + exact (tax x1 x x2 (sax x x1 X1) X2).
Defined.

Lemma setquotl0 {X : UU} (R : eqrel X) (c : setquot R) (x : c) :
  setquotpr R (pr1 x) = c.
Proof.
  Set Printing Coercions.
  apply (invmaponpathsincl _ (isinclpr1setquot R)).
  Unset Printing Coercions.
  apply funextsec; intro x0.
  apply hPropUnivalence; intro r.
  - exact (eqax1 (pr2 c) (pr1 x) x0 r (pr2 x)).
  - exact (eqax2 (pr2 c) (pr1 x) x0 (pr2 x) r).
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
  - intro r0. apply (eqreltrans R _ _ _ (eqrelsymm R _ _ r) r0).
  - intro x0'. apply (eqreltrans R _ _ _ r x0').
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
  apply (@hinhuniv2 _ _ (make_hProp (y1 = y2) (pr2 Y y1 y2))).
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
  intros. apply idpath.
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
