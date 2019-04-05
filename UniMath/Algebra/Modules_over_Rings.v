(** Definition of morphisms between arbitrary modules *)

Require Import UniMath.Algebra.Groups.
Require Import UniMath.Algebra.RigsAndRings.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.Algebra.Modules.
Require Import UniMath.Algebra.Modules.Examples.
Require Import UniMath.Algebra.Monoids.

Section AMod.

  Local Open Scope module.

  (** Morphism between R-module to S-module *)

  Definition isslinear {R S : ring} {M : module R} {N : module S} (s : R → S) (f : M → N) := ∏ r : R, ∏ x : M, f(r * x) = s(r) * f(x).

(*  Definition slinearfun {R S : ring} {M : module R} {N : module S} : UU := ∑ s : R → S, isringfun s × ∑ f : M → N, isslinear s f. *)

  Definition slinearfun {R S : ring} (M : module R) (N : module S) : UU := ∑ sf : (R → S) × (M → N), isringfun (pr1 sf) × isslinear (pr1 sf) (pr2 sf).

  Definition slinearfunpair {R S : ring} {M : module R} {N : module S} (sf : (R → S) × (M → N)) (is : isringfun (pr1 sf) × isslinear (pr1 sf) (pr2 sf)) :
                                                                          slinearfun M N := tpair _ sf is.

  Definition pr1slinearfun {R S : ring} {M : module R} {N : module S} (sf : slinearfun M N) : (R → S) × (M → N) := pr1 sf.

  Definition pr11slinearfun {R S : ring} {M : module R} {N : module S} (sf : slinearfun M N) : R → S := pr1 (pr1 sf).

  Definition pr12slinearfun {R S : ring} {M : module R} {N : module S} (sf : slinearfun M N) : M → N := pr2 (pr1 sf).

  Definition spart {R S : ring} {M : module R} {N : module S} (sf : slinearfun M N) : R → S := pr11slinearfun sf.

  Definition fpart {R S : ring} {M : module R} {N : module S} (sf : slinearfun M N) : M → N := pr12slinearfun sf.

Definition pr2slinearfun {R S : ring} {M : module R} {N : module S} (sf : slinearfun M N) : (isringfun (spart sf)) × (isslinear (spart sf) (fpart sf)) := pr2 sf.

Definition pr21slinearfun {R S : ring} {M : module R} {N : module S} (sf : slinearfun M N) : (isringfun (spart sf)) := pr1 (pr2 sf).

Definition pr22slinearfun {R S : ring} {M : module R} {N : module S} (sf : slinearfun M N) : (isslinear (spart sf) (fpart sf)) := pr2 (pr2 sf).

Definition ringpart {R S : ring} {M : module R} {N : module S} (sf : slinearfun M N) : ringfun R S := ringfunconstr (pr21slinearfun sf).

Definition slinearfun_isringfunisslinear {R S : ring} {M : module R} {N : module S} (sf : slinearfun M N) : isringfun (pr11slinearfun sf) × isslinear (pr11slinearfun sf) (pr12slinearfun sf) := pr2 sf.

Definition slinearfun_isringfun {R S : ring} {M : module R} {N : module S} (sf : slinearfun M N) : isringfun (pr11slinearfun sf) := pr1 (pr2 sf).

Definition slinearfun_isslinear {R S : ring} {M : module R} {N : module S} (sf : slinearfun M N) : isslinear (pr11slinearfun sf) (pr12slinearfun sf) := pr2 (pr2 sf).

Lemma isslinearfuncomp {R S T : ring} {M : module R} {N : module S} {P : module T} (sf : slinearfun M N) (tg : slinearfun N P) : isslinear (funcomp (spart sf) (spart tg)) (funcomp (fpart sf) (fpart tg)).
Proof.
  intros r x.
  unfold funcomp.
  rewrite (slinearfun_isslinear sf).
  rewrite (slinearfun_isslinear tg).
  apply idpath.
Defined.

Lemma isringfuncomp {R S T : ring} (s : ringfun R S) (t : ringfun S T)  : isringfun (funcomp s t).
Proof.
  apply mk_isrigfun.
  - change (ismonoidfun (funcomp (ringaddfun s) (ringaddfun t))).
     apply ismonoidfuncomp.
  - change (ismonoidfun (funcomp (ringmultfun s) (ringmultfun t))).
    apply ismonoidfuncomp.
Defined.

Definition linearfuncomp {R S T : ring} {M : module R} {N : module S} {P : module T} (sf : slinearfun M N) (tg : slinearfun N P) :
  slinearfun M P := tpair _ (funcomp (spart sf) (spart tg),,funcomp (fpart sf) (fpart tg)) (isringfuncomp (ringpart sf) (ringpart tg),, isslinearfuncomp sf tg).

Lemma isapropisslinear {R S : ring} {M : module R} {N : module S} (s : R → S) (f : M → N) : isaprop (isslinear s f).
Proof.
  apply (impred 1 _). intro r.
  apply (impred 1 _). intro x.
  apply (setproperty N).
Defined.

Lemma isasetslinearfun {R S : ring} (M : module R) (N : module S) : isaset (slinearfun M N).
Proof.
  intros sf s'f'.
  apply (isasetsubset (@pr1slinearfun R S M N)).
  - change (isofhlevel 2 ((R → S)×(M → N))).
    apply isofhleveltotal2.
    + apply impred.
      exact (fun x => setproperty S).
    + intro s.
      apply impred.
      exact (fun x => setproperty N).
  - refine (isinclpr1 _ _).
    intro x.
    apply isofhleveltotal2.
    + apply isapropisrigfun.
    + intro t; apply isapropisslinear.
Defined.

Definition isamodulefun {R S : ring} {M : module R} {N : module S} (sf : (R → S) × (M → N)) : UU := (isbinopfun (pr2 sf)) × (isslinear (pr1 sf) (pr2 sf)).

Definition isamodulefunpair {R S : ring} {M : module R} {N : module S} (sf : (R → S) × (M → N)) (isb : isbinopfun (pr2 sf)) (issl : isslinear (pr1 sf) (pr2 sf)) := tpair _ isb issl.

Lemma isapropisamodulefun {R S : ring} {M : module R} {N : module S} (sf : (R → S) × (M → N)) : isaprop (isamodulefun sf).
Proof.

  exact (@isofhleveldirprod 1 (isbinopfun (pr2 sf)) (isslinear (pr1 sf) (pr2 sf))
                            (isapropisbinopfun (pr2 sf)) (isapropisslinear (pr1 sf) (pr2 sf))).
Defined.

Definition amodulefun {R S : ring} (M : module R) (N : module S) : UU := ∑ sf : (R → S) × (M → N), isringfun (pr1 sf) ×  isamodulefun sf.

Definition amodulefunpair {R S : ring} {M : module R} {N : module S} (sf : (R → S) × (M → N)) (isr : isringfun (pr1 sf)) (ism : isamodulefun sf) :
  amodulefun M N := tpair _ sf (tpair _ isr ism).

Local Notation "mod( M , N )" := (amodulefun M N) : module_scope.

Section accessors.
  Context {R S : ring} {M : module R} {N : module S} (sf : mod(M,N)).

  Definition pr1amodulefun : (R → S) × (M → N) := pr1 sf.
  Definition spartamodulefun : R → S := pr1 (pr1 sf).
  Definition fpartamodulefun : M → N := pr2 (pr1 sf).

  Definition amodulefun_isringfun : isringfun spartamodulefun := pr1 (pr2 sf).

  Definition amodulefun_to_ringfun : ringfun R S :=
    ringfunconstr amodulefun_isringfun.

  Definition amodulefun_isamodulefun : isamodulefun pr1amodulefun := pr2 (pr2 sf).

  Definition amodulefun_to_isbinopfun : isbinopfun fpartamodulefun :=
    pr1 amodulefun_isamodulefun.

  Definition amodulefun_to_binopfun : binopfun M N :=
    binopfunpair fpartamodulefun amodulefun_to_isbinopfun.

  Definition amodulefun_to_isslinear : isslinear spartamodulefun fpartamodulefun :=
    pr2 amodulefun_isamodulefun.

  Definition amodulefun_to_slinearfun : slinearfun M N :=
    slinearfunpair pr1amodulefun (tpair _ amodulefun_isringfun amodulefun_to_isslinear).

End accessors.


Definition pairfuncomp {A B C A' B' C' : UU} (ff' : (A → B) × (A' → B')) (gg' : (B → C) × (B' → C')) : (A → C) × (A' → C') := tpair _ (funcomp (pr1 ff') (pr1 gg')) (funcomp (pr2 ff') (pr2 gg')).

Local Notation "ff' ∘ gg'" := (pairfuncomp gg' ff') : module_scope.

Lemma isamodulefun_comp {R S T : ring} {M : module R} {N : module S} {P : module T} (sf : mod(M,N)) (tg : mod(N,P)) :
  isamodulefun ((pr1 tg) ∘ (pr1 sf)).
Proof.
  exact (dirprodpair (isbinopfuncomp (amodulefun_to_binopfun sf)
                                     (amodulefun_to_binopfun tg))
                     (isslinearfuncomp (amodulefun_to_slinearfun sf)
                                      (amodulefun_to_slinearfun tg))).
Defined.

Definition amodulefun_comp {R S T : ring} {M : module R} {N : module S} {P : module T} (sf : mod(M,N)) (tg : mod(N,P)) : mod(M,P) :=
  tpair _ ((pr1 tg) ∘ (pr1 sf)) (tpair _ (isringfuncomp (ringpart (amodulefun_to_slinearfun sf)) (ringpart (amodulefun_to_slinearfun tg))) (isamodulefun_comp sf tg)).

Lemma amodulefun_unel {R S : ring} {M : module R} {N : module S} (sf : mod(M,N)) : (fpartamodulefun  sf)(unel M) = unel N.
Proof.
  rewrite <- (module_mult_0_to_0 (unel M)).
  rewrite ((amodulefun_to_isslinear sf) ringunel1 (unel M)).
  change  ((ringpart (amodulefun_to_slinearfun sf)) 0%rig * fpartamodulefun sf 1%multmonoid =
  1%multmonoid).
  rewrite (rigfun_to_unel_rigaddmonoid (ringpart (amodulefun_to_slinearfun sf))).
  change (0%ring * fpartamodulefun sf 1%multmonoid = 1%multmonoid).
  rewrite (module_mult_0_to_0 _).
  apply idpath.
Defined.

Definition amodulefun_to_monoidfun {R S : ring} {M : module R} {N : module S} (sf : mod(M,N)) :
  monoidfun (moduletomonoid M) (moduletomonoid N) :=
  tpair _ (pr2 (pr1 sf)) (tpair _ (pr1 (pr2 (pr2  sf))) (amodulefun_unel sf)).

Lemma linearfun_isslinear {R : ring} {M N : module R} (f : linearfun M N) : isslinear (idfun R) (pr1 f).
Proof.
  intro r.
  change ( ∏ x : M, pr1 f (r * x) = r * pr1 f x).
  apply (pr2 f).
Defined.

Lemma idmodulefun_isamodulefun {R : ring} {M N : module R} (f : modulefun M N) : isamodulefun  (idfun R,, pr1 f).
Proof.
  split.
  - cbn.
    apply modulefun_to_isbinopfun.
  - cbn.
    apply (linearfun_isslinear (modulefun_to_linearfun f)).
Defined.

Lemma idfun_isringfun {R : ring} : isringfun (idfun R).
Proof.
  split.
  - split.
    + intros x y.
      apply idpath.
    + apply idpath.
  - split.
    + intros x y.
      apply idpath.
    + apply idpath.
Defined.

Lemma id_amodulefun {R : ring} {M : module R} : isamodulefun (idfun R,,idfun M).
Proof.
  apply (idmodulefun_isamodulefun (modulefunpair (idfun M) (id_modulefun M))).
Defined.

Definition idmodulefun_to_amodulefun {R : ring} {M N : module R} (f : modulefun M N) : mod(M,N) := amodulefunpair (idfun R,,pr1 f) (idfun_isringfun) (idmodulefun_isamodulefun f).

Definition amodule_idfun {R : ring} {M : module R} : amodulefun M M :=
  amodulefunpair (idfun R,, idfun M) idfun_isringfun id_amodulefun.

Lemma amodulefun_paths {R S : ring} {M : module R} {N : module S} {sf tg : mod(M,N)} (p : pr1 sf = pr1 tg) : sf = tg.
Proof.
  use total2_paths_f.
  - exact p.
  - use proofirrelevance.
    apply isofhleveldirprod.
    + apply isapropisrigfun.
    + apply isapropisamodulefun.
Defined.

Lemma amodulefun_paths2 {R S : ring} {M : module R} {N : module S} {sf tg : mod(M,N)} (p1 : (pr1 (pr1 sf)) ~ (pr1 (pr1 tg))) (p2 : (pr2 (pr1 sf)) ~ (pr2 (pr1 tg))) : sf = tg.
Proof.
  apply amodulefun_paths.
  apply dirprod_paths; apply funextfun; [exact p1 | exact p2].
Defined.

Lemma isasetamodulefun {R S : ring} {M : module R} {N : module S} : isaset (mod(M,N)).
Proof.
  intros x y.
  apply (isasetsubset (@pr1amodulefun R S M N)).
  - apply isasetdirprod;apply impred;intro; [apply (setproperty S) | apply (setproperty N)].
  - refine (isinclpr1 _ _).
    intro.
    apply isapropdirprod; [apply isapropisrigfun | apply isapropisamodulefun].
Defined.

End AMod.