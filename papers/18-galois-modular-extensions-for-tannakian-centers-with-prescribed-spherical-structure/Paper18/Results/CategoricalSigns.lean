import Paper18.Category.ENOPseudounitary
import Paper18.Category.InvertibleObjectsDimensions

/-! # The actual negative-generator sign in equation (3.5) -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (J K : PivotalStructure C)

include S in
/-- Comparison with any actual positive pivotal structure takes value
minus one on an actual invertible of prescribed dimension minus one. -/
lemma comparison_negative_invertible {e : C} (E : TensorInverse e)
    (hK : K.Positive) (he : J.rightDim e = -1) :
    (J.ratio K).hom.app e = (-1 : ℂ) • 𝟙 e := by
  letI := E.simple S
  rw [← TensorAutomorphism.scalar_spec]
  change J.comparisonScalar K e • 𝟙 e = _
  rw [J.comparisonScalar_eq_dimension_ratio K S,
    E.rightDim_eq_one_of_positive S K hK, he, div_one]

include S in
/-- Equations (3.4) and (3.5) for the actual canonical positive structure,
constructed from weak integrality. -/
lemma canonicalPositive_comparison_negative {e : C} (E : TensorInverse e)
    (hJ : J.Spherical) (hB : S.fusionBasis.WeaklyIntegral) (he : J.rightDim e = -1) :
    (J.ratio (J.canonicalPositive S hJ hB)).hom.app e = (-1 : ℂ) • 𝟙 e :=
  comparison_negative_invertible S J (J.canonicalPositive S hJ hB) E
    (J.canonicalPositive_positive S hJ hB) he

include S in
/-- The comparison of two actual spherical structures is involutive on
every object, rather than just on chosen simple representatives. -/
lemma comparison_involutive (hJ : J.Spherical) (hK : K.Spherical) (X : C) :
    (J.ratio K).hom.app X ≫ (J.ratio K).hom.app X = 𝟙 X := by
  let χ := J.ratio K
  have hi (i : ι) : χ.hom.app (S.simpleObject i) ≫ χ.hom.app (S.simpleObject i) =
      𝟙 (S.simpleObject i) := by
    rw [← TensorAutomorphism.scalar_spec χ (S.simpleObject i)]
    change (J.comparisonScalar K (S.simpleObject i) • 𝟙 _) ≫
      (J.comparisonScalar K (S.simpleObject i) • 𝟙 _) = _
    rcases J.comparisonScalar_sign K S hJ hK (S.simpleObject i) with h | h <;> rw [h] <;> simp
  apply S.hom_ext_simples
  intro i f
  have hn := χ.hom.naturality f
  change f ≫ χ.hom.app X = χ.hom.app (S.simpleObject i) ≫ f at hn
  change f ≫ (χ.hom.app X ≫ χ.hom.app X) = f ≫ 𝟙 X
  calc
    _ = (f ≫ χ.hom.app X) ≫ χ.hom.app X := (Category.assoc _ _ _).symm
    _ = (χ.hom.app (S.simpleObject i) ≫ f) ≫ χ.hom.app X :=
      congrArg (fun k => k ≫ χ.hom.app X) hn
    _ = χ.hom.app (S.simpleObject i) ≫
        (χ.hom.app (S.simpleObject i) ≫ f) := by rw [Category.assoc, hn]
    _ = f ≫ 𝟙 X := by rw [← Category.assoc, hi]; simp

end Paper18.Category
