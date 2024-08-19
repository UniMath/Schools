(** *** Advanced exercise sheet for lecture 4: Tactics in Coq. *)

(**
    This is the material for the advisors with solutions.
*)

(** Some exercises about equivalences - recall from the course that associativity
    for products of types is not available "on the nose", i.e., just with equality.

    Exercises originally suggested by Benedikt Ahrens and Anders Mörtberg
    (for UniMath school 2017) and elaborated by Ralph Matthes (CNRS, IRIT,
    Univ. Toulouse, France)
*)
Require Import UniMath.Foundations.PartA.

Locate "≃". (** typed in as [\simeq] *)
Print weq.
Print isweq.
Print hfiber.

Section weqdef.

Parameters (X Y: UU).
Eval compute in (X ≃ Y).
(** there is a function [f] so that for given image [y] one can find the preimage [x] uniquely,
    but not only as element of [X] but even the pair consisting of the preimage and the proof
    that it is the preimage is unique. *)
End weqdef.

(** Prove that the identity function is an equivalence *)
Lemma idisweq (X : UU) : isweq (idfun X).
Proof.
  unfold isweq.
  intro y.
  unfold iscontr.
  unfold hfiber.
  use tpair.
  - exists y.
    apply idpath.
  - cbn.
    intro p.
    induction p as [x H].
    (* rewrite H. *)
    induction H.
    apply idpath.
Defined.

(** Package this up as an equivalence *)
Definition idweq (X : UU) : X ≃ X.
Proof.
  exists (idfun X).
  apply idisweq.
Defined.

(** alternative proof with [isweq_iso] that is extremely useful *)
Lemma idisweq_alt (X : UU) : isweq (idfun X).
Proof.
  use isweq_iso.
  - exact (fun x => x).
  - cbn. intros x. apply idpath.
  - cbn. intros x. apply idpath.
Defined.

(** Prove that any map to empty is an equivalence *)
Lemma isweqtoempty {X : UU} (f : X -> ∅) : isweq f.
Proof.
  unfold isweq.
  intro y.
  induction y.
Defined.

(** Package this up as an equivalence *)
Definition weqtoempty {X : UU} (f : X -> ∅) : X ≃ ∅.
Proof.
  use tpair.
  - exact f.
  - cbn. apply isweqtoempty.
Defined.


(** Prove that the composition of equivalences is an equivalence.

This is rather difficult to do directly from the definition. Important lemmas
to reason on equality of pairs in a sigma type are given by [base_paths] and
[fiber_paths] that are elimination rules (that use given equality of pairs)
and [total2_paths2_f] that is an introduction rule allowing to establish an
equation between pairs. There, transport arises, but transport along the
identity path is always the identity, and this already computationally, which
means that [cbn] gets rid of it. *)
Theorem compisweq {X Y Z : UU} (f : X -> Y) (g : Y -> Z)
        (isf : isweq f) (isg : isweq g) : isweq (g ∘ f).
Proof.
  unfold isweq.
  intro z.
  unfold iscontr.
  unfold hfiber.
  set (isginst := isg z).
  induction isginst as [cntrg Hg].
  induction cntrg as [y yeq].
  induction yeq. (** do this as early as possible *)
  set (isfinst := isf y).
  induction isfinst as [cntrf Hf].
  induction cntrf as [x xeq].
  induction xeq. (** again an early induction on an equation *)
  use tpair.
  - exists x.
    apply idpath. (** thanks to the induction on equations, this is trivial *)
  - cbn.
    intro p.
    induction p as [x' Hx'].
    set (hfg := (f x',, Hx'): hfiber g (g (f x))).
    set (Hginst := Hg hfg).
    set (x'eq := base_paths _ _ Hginst).
    cbn in x'eq.
    set (hff := (x',,x'eq): hfiber f (f x)).
    set (Hfinst := Hf hff).
    set (x'eq' := base_paths _ _ Hfinst).
    cbn in x'eq'.
    assert (Hypg := fiber_paths Hginst). (** use [assert] to forget the definition *)
    cbn in Hypg.
    change (base_paths hfg (f x,, idpath (g (f x))) Hginst) with x'eq in Hypg.
    assert (Hypf := fiber_paths Hfinst).
    cbn in Hypf.
    change (base_paths hff (x,, idpath (f x)) Hfinst) with x'eq' in Hypf.
    induction x'eq'. (** this is now possible, after sufficient abstraction *)
    use total2_paths2_f. (** a rather trivial instance *)
    + apply idpath.
    + cbn.
      cbn in Hypf.
      rewrite Hypf in Hypg.
      cbn in Hypg.
      exact Hypg.
Defined.

(** a proof that is less aggressive on induction on identities - not completed *)
Lemma compisweq_alt_incomplete {X Y Z : UU} (f : X -> Y) (g : Y -> Z)
        (isf : isweq f) (isg : isweq g) : isweq (g ∘ f).
Proof.
  unfold isweq.
  intro z.
  unfold iscontr.
  unfold hfiber.
  set (isginst := isg z).
  induction isginst as [cntrg Hg].
  induction cntrg as [y yeq].
  set (isfinst := isf y).
  induction isfinst as [cntrf Hf].
  induction cntrf as [x xeq].
  use tpair.
  - exists x.
    unfold funcomp.
    intermediate_path (g y).
    + apply maponpaths.
      apply xeq.
    + apply yeq.
  - cbn.
    intro p.
    induction p as [x' Hx'].
    set (hfg := (f x',, Hx'): hfiber g z).
    set (Hginst := Hg hfg).
    set (x'eq := base_paths _ _ Hginst).
    cbn in x'eq.
    set (hff := (x',,x'eq): hfiber f y).
    set (Hfinst := Hf hff).
    set (x'eq' := base_paths _ _ Hfinst).
    cbn in x'eq'.
    set (Hypg := fiber_paths Hginst).
    cbn in Hypg.
    change (base_paths hfg (y,, yeq) Hginst) with x'eq in Hypg.
    set (Hypf := fiber_paths Hfinst).
    cbn in Hypf.
    change (base_paths hff (x,, xeq) Hfinst) with x'eq' in Hypf.
    use total2_paths2_f.
    + exact x'eq'.
    +

      intermediate_path (transportf (λ x0 : hfiber f y, (g ∘ f) (pr1 x0) = z) Hfinst Hx').
      { apply pathsinv0. unfold x'eq'. unfold base_paths. use functtransportf. }

      assert (Hypg' : transportf (λ y0 : hfiber g z, g (pr1 y0) = z) Hginst Hx' = yeq).
      { rewrite <- Hypg. unfold x'eq. unfold base_paths. use functtransportf. }

      (** Who is willing to complete this proof? *)
Abort.

(** Package this up as an equivalence *)
Definition weqcomp {X Y Z : UU} (w1 : X ≃ Y) (w2 : Y ≃ Z) : X ≃ Z.
Proof.
  induction w1 as [f isf].
  induction w2 as [g isg].
  use tpair.
  - exact (g ∘ f).
  - cbn.
    exact (compisweq _ _ isf isg).
Defined.
