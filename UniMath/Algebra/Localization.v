Require Import UniMath.Algebra.Monoids.
Require Import UniMath.Algebra.RigsAndRings.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Foundations.All.
Require Import UniMath.Algebra.RigsAndRings.Ideals.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Combinatorics.StandardFiniteSets.

(* Coercing ideals *)
Definition lideal_to_subabmonoid {X : rig} : lideal X → subabmonoid (rigaddabmonoid X) := pr1.
Coercion lideal_to_subabmonoid : lideal >-> subabmonoid.

Definition the_intersection_submonoid
           {X : monoid} {I : UU} (S : I -> submonoid X) : submonoid X
  := (subtype_intersection S,, intersection_submonoid S (λ x, pr2 (S x))).

(* Monoid generated by a subset *)
Definition monoid_gen (X : monoid) (S : hsubtype X) : submonoid X :=
  the_intersection_submonoid (λ (B : ∑ (C : submonoid X), ∏ (x : X), C x), pr1 B).

(* Localization at a subset *)
Definition abmonoid_loc (X : abmonoid) (S : hsubtype X) : abmonoid :=
  abmonoidfrac X (monoid_gen X S).

Open Scope ring.

Lemma intersection_lideal
      {R : rig} {I : UU} (S : I -> lideal R):
  is_lideal (the_intersection_submonoid S).
Proof.
  intros r s.
  intro p.
  intro x.
  apply (pr2 (S x) r s (p x)).
Qed.

Definition the_intersection_lideal
           {R : rig} {I : UU} (S : I -> lideal R): lideal R
  := (the_intersection_submonoid S,, intersection_lideal S).

Definition ideal_gen {X : rig} (S : hsubtype X) : lideal X :=
  the_intersection_lideal (λ (B : ∑ (C : lideal X), ∏ (x : X), pr1 C x), pr1 B).

Open Scope rig_scope.

Definition lideal_is_everything {X : rig} (l : lideal X) : UU := ∏ x : X, l x.
Definition lideal_has_one {X : rig} (l : lideal X) : UU := l 1.


(*-- idea of the following def.: a family of localizations R-->R[S_i^{-1}] is completely determined by the S_i. Whether it is a covering can also be determined purely in terms of the S_i. --*)
Definition zariski_cover (X : rig) := ∑ I : UU, ∑ S : I → hsubtype X, lideal_has_one (ideal_gen (subtype_union S)).
(*-- for testing the sheaf condition later on we will need the localization morphisms...  --*)

Definition generated_twobinopeqrel_hrel {X : setwith2binop} (R : hrel X) : hrel X :=
  λ x x', ∀ (R' : twobinopeqrel X), himpl (∏ y z, R y z → R' y z) (R' x x').

Lemma istwobinophrel_generated_binopeqrel {X : setwith2binop} (R : hrel X) :
  is2binophrel (generated_twobinopeqrel_hrel R).
Proof.
  apply dirprodpair.
  - apply dirprodpair.
    + intros a b c genRab R' RimpR'.
      apply (pr1 (pr1 (pr2 R'))).
      exact (genRab R' RimpR').
    + intros a b c genRab R' RimpR'.
      apply (pr2 (pr1 (pr2 R'))).
      exact (genRab R' RimpR').
  - apply dirprodpair.
    + intros a b c genRab R' RimpR'.
      apply (pr1 (pr2 (pr2 R'))).
      exact (genRab R' RimpR').
    + intros a b c genRab R' RimpR'.
      apply (pr2 (pr2 (pr2 R'))).
      exact (genRab R' RimpR').
Defined.

Lemma iseqrel_generated_twobinopeqrel {X : setwith2binop} (R : hrel X) :
  iseqrel (generated_twobinopeqrel_hrel R).
Proof.
  use iseqrelconstr.
  - intros x1 x2 x3 H1 H2 R' HR. eapply eqreltrans.
    + exact (H1 R' HR).
    + exact (H2 R' HR).
  - intros x R' HR. apply eqrelrefl.
  - intros x1 x2 H R' HR. apply eqrelsymm. exact (H R' HR).
Defined.

Print twobinopeqrel.
Print eqrelpair.

Definition generated_twobinopeqrel {X : setwith2binop} (R : hrel X) : twobinopeqrel X :=
  twobinopeqrelpair (eqrelpair (generated_twobinopeqrel_hrel R) (iseqrel_generated_twobinopeqrel R))
                    (istwobinophrel_generated_binopeqrel R).

(*-- polynomial rings --*)

Section Poly.

  Context {R : commring}.

  Definition Polynomial_Type : UU := ∑ (a:nat → R) , ∃ n, ∏ k, k>n → a k = 0%ring.

  Definition zero_function : (nat → R) := (λ n, 0%ring).

  Lemma witness_that_zero_function_is_eventually_zero : ∑ n, ∏ k, k>n → zero_function k = 0%ring.
  Proof.
    exists 0%nat.
    intros.
    reflexivity. (* or apply idpath *)
  Defined.

  Definition zero_Polynomial : Polynomial_Type :=
    (zero_function,, hinhpr  witness_that_zero_function_is_eventually_zero).


  (*-- alternative version --*)
  Definition zero_Polynomial_bis : Polynomial_Type.
  Proof.
    unfold Polynomial_Type.
    use tpair.
    - exact (λ n, 0%ring).
    - cbn.
      apply hinhpr.
      exists 0%nat.
      intros.
      reflexivity. (* or "apply idpath" *)
  Defined.


  Lemma max_gt1 (m n k:nat) : natgth k (max m n) → natgth k m.
  Admitted.

  Lemma max_gt2 (m n k:nat) : natgth k (max m n) → natgth k n.
  Admitted.

  Definition sequence_sum (a b : nat → R) : nat → R := λ n, a n + b n.

  Definition Eventually_zero_proof_addition (a b : nat → R) :  (∑ n:nat, ∏ k:nat, k>n → a k = 0%ring) → (∑ n:nat, ∏ k:nat, k>n → b k = 0%ring) → (∑ n:nat, ∏ k:nat, k>n → sequence_sum a b k = 0%ring).
  Proof.
    intros p q.
    exists (max (pr1 p) (pr1 q)).
    intros k X.
    induction p as (s, hs).
    induction q as (t, ht).
    change (hProptoType (k > max s t)) in X.
    change (a k + b k = 0%ring).
    rewrite (hs k (max_gt1 s t k X)).
    rewrite (ht k (max_gt2 s t k X)).
    apply ringlunax1.
  Defined.

  Definition Polynomial_addition : Polynomial_Type → Polynomial_Type → Polynomial_Type.
  Proof.
    intros p q.
    unfold Polynomial_Type.
    use tpair.
    - exact (sequence_sum (pr1 p) (pr1 q)).
    - simpl.
      apply (hinhfun2 (Eventually_zero_proof_addition (pr1 p) (pr1 q)) (pr2 p) (pr2 q)).
  Defined.

  Definition sequence_product (a b : nat → R) : nat → R :=
    (λ n, foldleft 0%ring op1%ring (λ kp: stn n, (a (pr1 kp) * (b (n - pr1 kp)%nat))%ring)).

  Lemma sum_gt1 (m n k:nat) : natgth k (m + n) → natgth k m.
  Admitted.

  Lemma sum_gt2 (m n k:nat) : natgth k (m + n) → natgth k n.
  Admitted.

  Lemma gt_or_lt_lem (m n r k : nat) (p : r > m + n) (q : k < r) : (k > m) ⨿ (r - k > n).
  Admitted.

  Lemma sum_of_zeros (n : nat) (s : stn n → R) (allz : ∏ k : stn n, s k = 0%ring) :
    foldleft 0%ring op1%ring s = 0%ring.
  Admitted.

  Definition Eventually_zero_proof_multiplication (a b : nat → R) : (∑ n:nat, ∏ k:nat, k>n → a k = 0%ring) → (∑ n:nat, ∏ k:nat, k>n → b k = 0%ring) → (∑ n:nat, ∏ k:nat, k>n → sequence_product a b k = 0%ring).
  Proof.
    intros p q.
    exists (pr1 p + pr1 q)%nat.
    intros k X.
    induction p as (s, hs).
    induction q as (t, ht).
    change (hProptoType (k > s + t)) in X.
    unfold sequence_product.
    assert (allzero : ∏ kp : stn k, (a (pr1 kp) * b (k - pr1 kp)%nat) = 0%ring).
    {
      intro lp.
      induction lp as (l, lpf).
      induction (gt_or_lt_lem s t k l X lpf).
      - change ((a l * b (k - l)%nat)%ring = 0%ring).
        rewrite (hs l a0).
        rewrite ringmult0x.
        apply idpath.
      - change ((a l * b (k - l)%nat)%ring = 0%ring).
        rewrite (ht (k - l)%nat b0).
        rewrite ringmultx0.
        apply idpath.
    }
    rewrite (sum_of_zeros k (λ kp : (⟦ k ⟧)%stn, (a (pr1 kp) * b (k - pr1 kp)%nat)%ring) allzero).
    apply idpath.
  Defined.

  Definition Polynomial_multiplication : Polynomial_Type → Polynomial_Type → Polynomial_Type.
  Proof.
    intros p q.
    unfold Polynomial_Type.
    use tpair.
    - exact (sequence_product (pr1 p) (pr1 q)).
    - simpl.
      apply (hinhfun2 (Eventually_zero_proof_multiplication (pr1 p) (pr1 q)) (pr2 p) (pr2 q)).
  Defined.


  (* To do: Polynomial_Multiplication, R[x] as a commring, iterating this to get R[x_1,...,x_n]   *)

End Poly.

(* To do: fin. gen. ideals, fin. pres. rings (better: R-algebras...)  *)