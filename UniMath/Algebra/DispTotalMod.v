Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.All.
Require Import UniMath.Algebra.All.
Require Import UniMath.Algebra.Modules_over_Rings_2.

Definition totalmod_ob_mor :disp_cat_ob_mor ring_category :=
mk_disp_cat_ob_mor ring_category (λ R : ring_category, module R)
  (λ (R S : ring) (M : module R) (N : module S)
   (s : ringfun R S), amodulefun' s M N).

Definition totalmod_id_comp : disp_cat_id_comp ring_category totalmod_ob_mor.
Proof.
  use tpair.
  - intros R M.
    apply (amodule_idfun').
  - cbn.
    intros R S T s t M N P f g.
    induction f as (f,pf).
    induction g as (g,pg).
    exists (g ∘ f).
    induction s as (s,ps).
    induction t as (t,pt).
    apply dirprodpair.
    + cbn.
      apply (isbinopfuncomp (binopfunpair f (pr1 pf)) (binopfunpair g (pr1 pg))).
    + cbn.
      exact (isslinearfuncomp (slinearfunpair (s,,f) (ps,,(pr2 pf))) (slinearfunpair (t,,g) (pt,,(pr2 pg)))).
Defined.

Print totalmod_id_comp.

Definition totalmod_data : disp_cat_data ring_category :=
  (totalmod_ob_mor,,totalmod_id_comp).

Lemma totalmod_axioms : disp_cat_axioms ring_category totalmod_data.
Proof.
  apply tpair.
  - intros R S s M N f.
    use total2_paths_f.
    + cbn.
      cbn.
      apply pathsinv0.
      etrans.
      * unfold mor_disp.
        cbn.
        unfold amodulefun'.
        apply (pr1_transportf (P := (λ _, isamodulefun'))).
      * induction f as (f,pf).
        cbn.
        change (transportf (λ _ : ringfun R S, pr1 M → pr1 N) (! id_left s) f = f).
        unfold id_left.
        cbn.
        unfold is_precategory_ring_precategory_data.
        Search transportf
        Search id_left.
        Check (id_left s).
        apply subtypeEquality.
        SearchAbout (transportf ).
        Search transportf total2 tpair.
        Search (transportf) (paths (total2 _)).

        change (transportf (λ _ : ringfun R S, pr1 M → pr1 N) (idpath s) f =
                f).
    + apply proofirrelevance.
      apply isapropisamodulefun'.

Defined.