Require Export UniMath.Foundations.All.
Require Export UniMath.MoreFoundations.All.

(** Start of the emulated S1. Don't touch!!! *)
Module Export S1.
  Private Inductive S1 : UU := base : S1.
  Axiom loop : base = base.
  Definition S1_ind (P : S1 -> UU) (b : P base) (l : PathOver loop b b) (x : S1) : P x :=
    match x with base => b end.
  Definition S1_rec (A : UU) (b : A) (l : b = b) : S1 -> A :=
    S1_ind (λ _, A) b (PathOverConstant_map1 loop l).
  Axiom S1_ind_beta_loop : forall (P : S1 -> UU) (b : P base) (l : PathOver loop b b), apd (S1_ind P b l) loop = l.
  Axiom S1_rec_beta_loop : forall (A : UU) (b : A) (l : b = b), maponpaths (S1_rec A b l) loop = l.
End S1.
(** End of the emulated S1. Don't touch!!! *)

(** The definition of Z we will use. It is essentially `coprod nat nat`, but
  * with more memorable names `Pos` and `NegS` instead of `inl` and `inr`.
  * `NegS 1` means -2. *)
Inductive Z : UU :=
  | Pos : nat -> Z
  | NegS : nat -> Z.

(** We define the `succ` function that increment integers by 1. *)
Definition succ (i : Z) : Z :=
  match i with
    | Pos n => Pos (S n)
    | NegS 0 => Pos 0
    | NegS (S n) => NegS n
  end.

(** [Exercise] We then define the `pred` function that decrement
  * integers by 1. *)
Definition pred (i : Z) : Z. (* Change the dot `.` to `:=` *)
Proof. Admitted.

(** [Exercise] `pred` is a left inverse of `succ` *)
Lemma pred_succ (i : Z) : pred (succ i) = i.
Proof. Admitted.

(** [Exercise] `pred` is a right inverse of `succ` *)
Lemma succ_pred (i : Z) : succ (pred i) = i.
Proof. Admitted.

(** Therefore, `succ` is an equivalence! *)
Definition succ_equiv : Z ≃ Z :=
  make_weq succ (isweq_iso succ pred pred_succ succ_pred).

(** Decoding: from numbers to paths *)

(** The definition for non-negative numbers `Pos n`. *)
Fixpoint loopexpPos (n : nat) : base = base :=
  match n with
    | 0 => idpath base
    | S n => loopexpPos n @ loop
  end.

(** The definition for negative numbers `NegS n`. *)
Fixpoint loopexpNegS (n : nat) : base = base :=
  match n with
    | 0 => ! loop
    | S n => loopexpNegS n @ ! loop
  end.

(** The conversion from loops to numbers. Think about the numbers as
  * an "encoding" of loops. In the case of the circle, this is also
  * called "winding numbers". *)
Definition loopexp (x : Z) : base = base :=
  match x with
    | Pos n => loopexpPos n
    | NegS n => loopexpNegS n
  end.

(** Encoding: from paths to numbers. This is not trivial at all,
  * as it seems we have no way to recover the number from seemingly
  * "unstructured" paths. We summon covering spaces to help us. *)

(** The (universal) covering space of the circle. *)
Definition Cover : S1 -> UU :=
  S1_rec UU Z (weqtopaths succ_equiv).

(** Transporting along `loop` is the same as applying `succ`.
  * (We will not use this lemma in the final theorems.) *)
Lemma loop_transport (x : Z) : transportf Cover loop x = succ x.
Proof.
  etrans.
  - exact (functtransportf Cover (idfun UU) loop x).
  - unfold Cover. rewrite S1_rec_beta_loop.
    refine (toforallpaths _ _ _ _ x).
    apply weqpath_transport.
Defined.

(** A very useful lemma that mimics the existing lemma `weqpath_transport` *)
Lemma invweqpath_transport {A B : UU} (e : A ≃ B)
  : transportf (λ A, A) (! (weqtopaths e)) = pr1 (invweq e).
Proof.
  etrans.
  - symmetry. refine (pr1_eqweqmap2 _).
  - rewrite eqweqmap_pathsinv0.
    rewrite eqweqmap_weqtopaths.
    reflexivity.
Defined.

(** [Exercise] prove that transporting along the inverse of
  * `loop` is the same as applying `pred`. *)
Lemma invloop_transport (x : Z) : transportf Cover (! loop) x = pred x.
Proof. Admitted.

(** Now we are ready to define the encoding function.*)

Definition encode' {x : S1} (p : base = x) (start : Z) : Cover x :=
  transportf Cover p start.

Definition encode {x : S1} (p : base = x) : Cover x :=
  encode' p (Pos 0).

(** This section proves that `encode` is the right inverse of `loopexp`.
  * That is, we can encode a loop back to its representing number. *)

(** [Exercise] A useful lemma.
  *
  * Hint: `Search (transportf _ _ (transportf _ _ _)).` *)
Lemma encode'_encode (p : base = base) (q : base = base)
  : encode' q (encode p) = encode (p @ q).
Proof. Admitted.

(** [Exercise] Another lemma. *)
Lemma encode'_loop (i : Z) : encode' loop i = succ i.
Proof. Admitted.

(** [Exercise] Yet another lemma. *)
Lemma encode'_invloop (i : Z) : encode' (! loop) i = pred i.
Proof. Admitted.

(** [Exercise, difficult] Putting all these lemmas together... *)
Lemma encode_loopexp (i : Z) : encode (loopexp i) = i.
Proof. Admitted.

(** Now, we wish to prove that `encode` is also the right inverse of
   `loopexp` as follows: *)

Lemma loopexp_encode (p : base = base): (loopexp (encode p)) = p.

(** However, this is incredibly hard because we cannot do induction
  * on `p` (why?). To overcome the difficulty, we have to loose at least
  * one end point of `p` to an arbitrary point in `S1`. While `encode`
  * can handle arbitrary path from `base` to an arbitrary point, `loopexp`
  * needs to be generalized to handle such a free end point. We will call
  * the generalized `loopexp` as `decode`, and revisit the lemma later. *)

Abort. (* We will prove this lemma after a long journey. *)

(** [Exercise] prove how `loopexp` and `succ` work with each other.
  *
  * Hint: `Search (_ @ _ @ _ = _).` *)
Lemma loopexp_succ (i : Z) : loopexp (succ i) = loopexp i @ loop.
Proof. Admitted.

(** [Exercise, optional] You can also prove the opposite case,
  * though we will not use this lemma. *)
Lemma loopexp_pred (i : Z) : loopexp (pred i) = loopexp i @ ! loop.
Proof. Admitted.

(** [Exercise] A very useful lemma that can be proved in 2 tactics. *)
Lemma transportf_arrow {A : Type} {B C : A -> Type}
  {x y : A} (p : x = y) (f : B x -> C x) (b' : B y)
  : (transportf (λ x, B x -> C x) p f) b'
  = transportf C p (f (transportf B (! p) b')).
Proof. Admitted.

(** [Exercise, very difficult] This is the generalized `loopexp` that
  * works for all elements of type `Cover x`, not just `Cover base`
  * which is `Z`. *)
Definition decode {x : S1} : Cover x -> base = x.
Proof.
  refine (S1_ind (λ x, Cover x -> base = x) loopexp _ x).
  apply transportf_to_pathover.
  apply funextsec. intro i.
  (** [Exercise] Finish the rest of the definition. *)
Admitted.

(** [Exercise] After all the preparation, this is a one-liner. *)
Lemma decode_encode {x : S1} (p : base = x): (decode (encode p)) = p.
Proof. Admitted.

(** [Exercise] Finally... *)
Lemma loopexp_encode (p : base = base): (loopexp (encode p)) = p.
Proof. Admitted.

(** [Exercise] We proved it! *)
Theorem Omega1S1 : (base = base) ≃ Z.
Proof. Admitted.

(** BONUS: We can prove that S1 has h-level 3 but not 2, thanks
  * to the constructions and the theorem we just established. *)

Lemma invmaponpathsPos {n m : nat} : Pos n = Pos m -> n = m.
Proof.
  intro p.
  set (f := λ n, match n with Pos n => n | _ => 0 end).
  exact (maponpaths f p).
Defined.

Lemma invmaponpathsNegS {n m : nat} : NegS n = NegS m -> n = m.
Proof.
  intro p.
  set (f := λ n, match n with NegS n => n | _ => 0 end).
  exact (maponpaths f p).
Defined.

Lemma negpathPosNegS {n m : nat} : ¬ (Pos n = NegS m).
Proof.
  intro p.
  set (f := λ i, match i with Pos _ => true | NegS _ => false end).
  exact (nopathstruetofalse (maponpaths f p)).
Defined.

(** [Exercise, difficult] Prove that `Z` has decidable equality. *)
Theorem isdeceqZ : isdeceq Z.
Proof. Admitted.

(** Okay, `Z` is a set. *)
Theorem isasetZ : isaset Z.
Proof. exact (isasetifdeceq _ isdeceqZ). Defined.

(** Therefore, `base = base` is also a set. *)
Lemma isasetOmega1S1 : isaset (base = base).
Proof. exact (isofhlevelweqb 2 Omega1S1 isasetZ). Defined.

(** [Exercise, extremely difficult] Prove that S1 has h-level 3. *)
Theorem isagroupoidS1 : isofhlevel 3 S1.
Proof. Admitted.

(** [Exercise] Prove that `loop` is not the constant path. *)
Lemma negpathsloopidpath : ¬ (loop = idpath base).
Proof. Admitted.

(** [Exercise] Prove that `S1` is not a set. *)
Theorem negisasetS1 : ¬ isaset S1.
Proof. Admitted.
