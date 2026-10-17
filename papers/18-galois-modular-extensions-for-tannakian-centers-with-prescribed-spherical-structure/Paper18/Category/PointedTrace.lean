import Paper18.Category.PointedFusion
import Paper18.Category.PointedBraiding
import Paper18.Category.PivotalBalancingInvertible

noncomputable section

open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators

namespace Paper18.Category.PointedVec

attribute [local instance 2000] RightRigidCategory.rightDual

/-- The ordinary vector-space cup, flip and cap compute the vector-space
dimension, using an actual basis of the finite-dimensional component. -/
@[reassoc]
lemma vector_braidedDimension (V : FGModuleCat ℂ) :
    η_ V Vᘁ ≫ (β_ V Vᘁ).hom ≫ ε_ V Vᘁ =
      (Module.finrank ℂ V : ℂ) • 𝟙 (𝟙_ (FGModuleCat ℂ)) := by
  have flip (v : V) (f : Module.Dual ℂ V) :
      (β_ V Vᘁ).hom.hom (v ⊗ₜ[ℂ] f) = f ⊗ₜ[ℂ] v := rfl
  apply FGModuleCat.hom_ext
  apply LinearMap.ext_ring
  change (FGModuleCat.FGModuleCatEvaluation ℂ V).hom
      ((β_ V Vᘁ).hom.hom ((FGModuleCat.FGModuleCatCoevaluation ℂ V).hom (1 : ℂ))) = _
  rw [FGModuleCat.FGModuleCatCoevaluation_apply_one]
  simp only [map_sum, flip]
  change (∑ x, (Module.Basis.ofVectorSpace ℂ V).coord x
    ((Module.Basis.ofVectorSpace ℂ V) x)) = _
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_eq_same, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]
  rw [ModuleCat.hom_smul, FGModuleCat.hom_id]
  rw [Module.finrank_eq_card_basis (Module.Basis.ofVectorSpace ℂ V)]
  change (Fintype.card (Module.Basis.ofVectorSpaceIndex ℂ V) : ℂ) =
    (Fintype.card (Module.Basis.ofVectorSpaceIndex ℂ V) : ℂ) * (1 : ℂ)
  exact (mul_one _).symm

variable {A : Type} [Fintype A] [AddCommGroup A]

open GradedObject.Monoidal

local instance traceGradedMonoidal : MonoidalCategory (GradedObject A (FGModuleCat ℂ)) :=
  GradedObject.monoidalCategory

lemma closure_summand (c : ComplexBicharacter A) (X : PointedVec A) (a : A) :
    η_ (X a) (X a)ᘁ ≫ (X a) ◁ (dualFiberIso X a).inv ≫
      ιTensorObj X (gradedDual X) a (-a) 0 (add_neg_cancel a) ≫
      (bicharacterBraiding c X (gradedDual X)).hom 0 ≫ gradedEvaluation X 0 =
      ((c.val a (-a) : ℂ) * (Module.finrank ℂ (X a) : ℂ)) • unitFiberIso.inv := by
  rw [inclusion_bicharacterBraiding_assoc]
  rw [Linear.smul_comp]
  rw [Linear.comp_smul]
  simp only [Category.assoc]
  rw [inclusion_evaluation_zero, dualPairIso_canonical]
  rw [← BraidedCategory.braiding_naturality_right_assoc]
  simp only [← whiskerLeft_comp_assoc, Iso.inv_hom_id, whiskerLeft_id, Category.id_comp]
  simp only [Linear.comp_smul]
  rw [vector_braidedDimension_assoc]
  simp only [Linear.smul_comp, Category.id_comp, smul_smul]

lemma graded_closure_zero (c : ComplexBicharacter A) (X : PointedVec A) :
    gradedCoevaluation X 0 ≫ (bicharacterBraiding c X (gradedDual X)).hom 0 ≫
        gradedEvaluation X 0 =
      (∑ a, (c.val a (-a) : ℂ) * (Module.finrank ℂ (X a) : ℂ)) •
        𝟙 ((𝟙_ (PointedVec A)) 0) := by
  calc
    _ = unitFiberIso.hom ≫ ∑ a,
        (η_ (X a) (X a)ᘁ ≫ (X a) ◁ (dualFiberIso X a).inv ≫
          ιTensorObj X (gradedDual X) a (-a) 0 (add_neg_cancel a) ≫
          (bicharacterBraiding c X (gradedDual X)).hom 0 ≫ gradedEvaluation X 0) := by
      simp only [gradedCoevaluation, mapFromUnit_zero, gradedCoevaluationZero,
        Category.assoc, Preadditive.sum_comp, Preadditive.comp_sum]
    _ = unitFiberIso.hom ≫ ∑ a,
        ((c.val a (-a) : ℂ) * (Module.finrank ℂ (X a) : ℂ)) • unitFiberIso.inv := by
      simp only [closure_summand]
    _ = _ := by
      rw [← Finset.sum_smul]
      simp only [Linear.comp_smul, Iso.hom_inv_id]

/-- The categorical braided closure is the weighted sum of the actual
vector-space dimensions of the homogeneous components. -/
lemma graded_braidedDimension (c : ComplexBicharacter A) (X : PointedVec A) :
    gradedCoevaluation X ≫ (bicharacterBraiding c X (gradedDual X)).hom ≫
        gradedEvaluation X =
      (∑ a, (c.val a (-a) : ℂ) * (Module.finrank ℂ (X a) : ℂ)) •
        𝟙 (𝟙_ (PointedVec A)) := by
  funext k
  by_cases hk : k = 0
  · subst k
    exact graded_closure_zero c X
  · have hz : IsZero ((𝟙_ (PointedVec A)) k) :=
      (GradedObject.Monoidal.isInitialTensorUnitApply k hk).isZero
    exact hz.eq_of_src _ _

lemma simpleFiber_finrank (a k : A) :
    Module.finrank ℂ (simpleObject A a k) = if k = a then 1 else 0 := by
  by_cases hk : k = a
  · subst k
    rw [if_pos rfl, ← LinearEquiv.finrank_eq
      (FGModuleCat.isoToLinearEquiv (simpleFiberIso A a)).symm]
    exact Module.finrank_self ℂ
  · rw [if_neg hk]
    have hz := simpleFiber_isZero A a k hk
    have hz' : IsZero ((simpleObject A a k).obj) :=
      (forget₂ (FGModuleCat ℂ) (ModuleCat ℂ)).map_isZero hz
    letI : Subsingleton (simpleObject A a k) := ModuleCat.isZero_iff_subsingleton.mp hz'
    exact Module.finrank_zero_of_subsingleton

/-- A concentrated complex line has braided closure exactly the
bicharacter value on its degree and inverse degree. -/
lemma simple_braidedDimension (c : ComplexBicharacter A) (a : A) :
    gradedCoevaluation (simpleObject A a) ≫
        (bicharacterBraiding c (simpleObject A a) (gradedDual (simpleObject A a))).hom ≫
        gradedEvaluation (simpleObject A a) =
      (c.val a (-a) : ℂ) • 𝟙 (𝟙_ (PointedVec A)) := by
  rw [graded_braidedDimension]
  simp [simpleFiber_finrank]

end Paper18.Category.PointedVec
