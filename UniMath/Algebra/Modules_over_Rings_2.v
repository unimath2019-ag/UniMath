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

  Definition isslinear' {R S : ring} {M : module R} {N : module S} (s : R → S) (f : M → N) := ∏ r : R, ∏ x : M, f(r * x) = s(r) * f(x).

(*  Definition slinearfun {R S : ring} {M : module R} {N : module S} : UU := ∑ s : R → S, isringfun s × ∑ f : M → N, isslinear s f. *)

  Definition slinearfun' {R S : ring} (s : ringfun R S) (M : module R) (N : module S) : UU := ∑ f : (M → N), isslinear' s f.

  Definition slinearfunpair' {R S : ring} {s : ringfun R S} {M : module R} {N : module S} (f : M → N) (is : isslinear' s f) :
                                                                          slinearfun' s M N := tpair _ f is.

  Definition pr1slinearfun' {R S : ring} {s : ringfun R S} {M : module R} {N : module S} (f : slinearfun' s M N) : M → N := pr1 f.

  Definition pr2slinearfun' {R S : ring} {s : ringfun R S} {M : module R} {N : module S} (f : slinearfun' s M N) : (isslinear' s (pr1slinearfun' f) ) := pr2 f.

  Definition slinearfun_isslinear' {R S : ring} {s : ringfun R S} {M : module R} {N : module S} (f : slinearfun' s M N) :isslinear' s (pr1slinearfun' f) := pr2 f.

Lemma isslinearfuncomp' {R S T : ring} {s : ringfun R S} {t : ringfun S T} {M : module R} {N : module S} {P : module T} (f : slinearfun' s M N) (g : slinearfun' t N P) : isslinear' (funcomp s t) (funcomp (pr1slinearfun' f) (pr1slinearfun' g)).
Proof.
  intros r x.
  unfold funcomp.
  rewrite (slinearfun_isslinear' f).
  rewrite (slinearfun_isslinear' g).
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



Definition linearfuncomp' {R S T : ring} {s : ringfun R S} {t : ringfun S T} {M : module R} {N : module S} {P : module T} (f : slinearfun' s M N) (g : slinearfun' t N P) :
  slinearfun'(ringfunconstr (isringfuncomp s t)) M P := tpair _ (funcomp (pr1slinearfun' f) (pr1slinearfun' g)) (isslinearfuncomp' f g).

Lemma isapropisslinear' {R S : ring} {s : ringfun R S} {M : module R} {N : module S} (f : M → N) : isaprop (isslinear' s f).
Proof.
  apply (impred 1 _). intro r.
  apply (impred 1 _). intro x.
  apply (setproperty N).
Defined.

Lemma isasetslinearfun' {R S : ring} {s : ringfun R S} (M : module R) (N : module S) : isaset (slinearfun' s M N).
Proof.
  intros f f'.
  apply (isasetsubset (@pr1slinearfun' R S s M N)).
  - apply Propositions.funspace_isaset.
    apply isasetmodule.
  - refine (isinclpr1 _ _).
    intro x.
    apply isapropisslinear'.
Defined.

Definition isamodulefun' {R S : ring} {s : ringfun R S} {M : module R} {N : module S} (f : M → N) : UU := (isbinopfun f) × (isslinear' s f).

Definition isamodulefunpair' {R S : ring} {s : ringfun R S} {M : module R} {N : module S} (f : M → N) (isb : isbinopfun f) (issl : isslinear' s f) := tpair _ isb issl.

Lemma isapropisamodulefun' {R S : ring} {s : ringfun R S} {M : module R} {N : module S} (f : M → N) : isaprop (@isamodulefun' _ _ s _ _ f).
Proof.

  exact (@isofhleveldirprod 1 (isbinopfun f) (isslinear' s f)
                            (isapropisbinopfun f) (isapropisslinear' f)).
Defined.

Definition amodulefun' {R S : ring} (s : ringfun R S) (M : module R) (N : module S) : UU := ∑ f : (M → N),  @isamodulefun' _ _ s _ _ f.

Definition amodulefunpair' {R S : ring} {s : ringfun R S} {M : module R} {N : module S} (f : M → N) (is : isamodulefun' f) :
  @amodulefun' _ _ s M N := tpair _ f is.

Local Notation "mod( s , M , N )" := (amodulefun' s M N) : module_scope.

Section accessors.
  Context {R S : ring} {s : ringfun R S} {M : module R} {N : module S} (f : mod(s,M,N)).

  Definition pr1amodulefun' : M → N := pr1 f.

  Definition amodulefun_isamodulefun' : isamodulefun' pr1amodulefun' := pr2 f.

  Definition amodulefun_to_isbinopfun' : isbinopfun pr1amodulefun' :=
    pr1 amodulefun_isamodulefun'.

  Definition amodulefun_to_binopfun' : binopfun M N :=
    binopfunpair pr1amodulefun' amodulefun_to_isbinopfun'.

  Definition amodulefun_to_isslinear' : isslinear' (pr1 s) pr1amodulefun' :=
    pr2 amodulefun_isamodulefun'.

  Definition amodulefun_to_slinearfun' : slinearfun' s M N :=
    slinearfunpair' pr1amodulefun' amodulefun_to_isslinear'.

End accessors.

Definition ringfun_comp {R S T : ring} (s : ringfun R S) (t : ringfun S T) := ringfunconstr (isringfuncomp s t).

Notation "t ∘ s" := (ringfun_comp s t).

Lemma isamodulefun_comp' {R S T : ring} {s : ringfun R S} {t : ringfun S T} {M : module R} {N : module S} {P : module T} (f : mod(s,M,N)) (g : mod(t,N,P)) :
  @isamodulefun' _ _ (t ∘ s) _ _ (funcomp (pr1amodulefun' f) (pr1amodulefun' g)).
Proof.
  exact (dirprodpair (isbinopfuncomp (amodulefun_to_binopfun' f)
                                     (amodulefun_to_binopfun' g))
                     (isslinearfuncomp' (amodulefun_to_slinearfun' f)
                                      (amodulefun_to_slinearfun' g))).
Defined.

Definition amodulefun_comp' {R S T : ring} {s : ringfun R S} {t : ringfun S T} {M : module R} {N : module S} {P : module T} (f : mod(s,M,N)) (g : mod(t,N,P)) : mod(t∘s,M,P) :=
  tpair _ (funcomp (pr1 f) (pr1 g)) (isamodulefun_comp' f g).

Lemma amodulefun_unel' {R S : ring} {s : ringfun R S} {M : module R} {N : module S} (f : mod(s,M,N)) : (pr1amodulefun'  f)(unel M) = unel N.
Proof.
  rewrite <- (module_mult_0_to_0 (unel M)).
  rewrite ((amodulefun_to_isslinear' f) ringunel1 (unel M)).
  change  (s 0%rig * pr1amodulefun' f 1%multmonoid =
  1%multmonoid).
  rewrite (rigfun_to_unel_rigaddmonoid s).
  change (0%ring * pr1amodulefun' f 1%multmonoid = 1%multmonoid).
  rewrite (module_mult_0_to_0 _).
  apply idpath.
Defined.

Definition amodulefun_to_monoidfun' {R S : ring} {s : ringfun R S} {M : module R} {N : module S} (f : mod(s,M,N)) :
  monoidfun (moduletomonoid M) (moduletomonoid N) :=
  tpair _ (pr1 f) (tpair _ (pr1 (pr2  f)) (amodulefun_unel' f)).

Lemma linearfun_isslinear' {R : ring} {M N : module R} (f : linearfun M N) : isslinear' (idfun R) (pr1 f).
Proof.
  intro r.
  change ( ∏ x : M, pr1 f (r * x) = r * pr1 f x).
  apply (pr2 f).
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

Definition idringfun {R : ring} : ringfun R R :=  ringfunconstr idfun_isringfun.

Lemma idmodulefun_isamodulefun' {R : ring} {M N : module R} (f : modulefun M N) : @isamodulefun' _ _ idringfun _ _ (pr1 f).
Proof.
  split.
  - cbn.
    apply modulefun_to_isbinopfun.
  - cbn.
    apply (linearfun_isslinear' (modulefun_to_linearfun f)).
Defined.

Lemma id_amodulefun' {R : ring} {M : module R} : @isamodulefun' _ _ idringfun _ _ (idfun M).
Proof.
  apply (idmodulefun_isamodulefun' (modulefunpair (idfun M) (id_modulefun M))).
Defined.

Definition idmodulefun_to_amodulefun' {R : ring} {M N : module R} (f : modulefun M N) : mod(idringfun,M,N) := amodulefunpair' f (idmodulefun_isamodulefun' f).

Definition amodule_idfun' {R : ring} {M : module R} : amodulefun' idringfun M M :=
  amodulefunpair' (idfun M) id_amodulefun'.

Lemma amodulefun_paths' {R S : ring} {s: ringfun R S} {M : module R} {N : module S} {f : mod(s,M,N)} {g : mod(s,M,N)} (p : pr1 f = pr1 g) : f = g.
Proof.
  use total2_paths_f.
  - exact p.
  - use proofirrelevance.
    apply isapropisamodulefun'.
Defined.

Lemma amodulefun_paths2' {R S : ring} {s : ringfun R S} {M : module R} {N : module S} {f g : mod(s,M,N)} (p : (pr1 f) ~ (pr1 g)) : f = g.
Proof.
  apply amodulefun_paths'.
  apply funextfun.
  exact p.
Defined.

Lemma isasetamodulefun' {R S : ring} {s : ringfun R S} {M : module R} {N : module S} : isaset (mod(s,M,N)).
Proof.
  intros x y.
  apply (isasetsubset (@pr1amodulefun' R S s M N)).
  - apply Propositions.funspace_isaset.
    apply isasetmodule.
  - refine (isinclpr1 _ _).
    intro.
    apply isapropisamodulefun'.
Defined.

End AMod.