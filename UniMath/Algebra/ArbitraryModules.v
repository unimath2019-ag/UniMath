(** The category of modules over arbitrary rings *)

Require Import UniMath.Algebra.Groups.
Require Import UniMath.Algebra.RigsAndRings.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.Algebra.Modules.
Require Import UniMath.Algebra.Modules.Examples.
Require Import UniMath.Algebra.Monoids.
Require Import UniMath.Algebra.Modules_over_Rings.

Section AMod.

Local Open Scope module.
Local Open Scope cat.

(** Precategory of arbitrary modules *)

Definition amod_precategory_ob_mor : precategory_ob_mor :=
  precategory_ob_mor_pair (∑ R : ring, module R) (λ M N, amodulefun (pr2 M) (pr2 N)).

Definition amod_precategory_data : precategory_data :=
  precategory_data_pair amod_precategory_ob_mor
  (λ RM : amod_precategory_ob_mor, amodule_idfun)
  (λ RM SN TP : amod_precategory_ob_mor, amodulefun_comp).

Lemma is_precategory_amod_precategory_data :
  is_precategory (amod_precategory_data).
Proof.
  apply is_precategory_one_assoc_to_two.
  apply dirprodpair.
  - apply dirprodpair; intros M N f; use total2_paths_f.
    + apply idpath.
    + induction f as((s,f),(ps,pf)). cbn.
      apply pathsdirprod.
      * apply isapropisrigfun.
      * apply isapropisamodulefun.
    + apply idpath.
    + induction f as((s,f),(ps,pf)). cbn.
      apply pathsdirprod.
      * apply isapropisrigfun.
      * apply isapropisamodulefun.
  - intros M N P Q (f,pf) (g,pg) (h,ph).
    apply amodulefun_paths.
    cbn.
    apply idpath.
Defined.

Definition amod_precategory : precategory :=
  mk_precategory (amod_precategory_data) (is_precategory_amod_precategory_data).

Definition has_homsets_amod : has_homsets amod_precategory :=
  λ _ _, isasetamodulefun.

Definition amod_category : category :=
  category_pair amod_precategory has_homsets_amod.

Definition mor_to_amodulefun {RM SN : ob amod_category} : amod_category⟦RM, SN⟧ → amodulefun (pr2 RM) (pr2 SN) := idfun _.

End AMod.