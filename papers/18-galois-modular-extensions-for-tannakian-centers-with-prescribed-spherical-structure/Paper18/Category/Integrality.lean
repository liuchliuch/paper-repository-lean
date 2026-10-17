import Paper18.Category.FusionCategory
import Paper18.Results.Integrality

/-! # Integrality transfer for actual fusion categories

The declarations state Lemma 3.1 using actual simple objects, Hom spaces,
tensor functors and categorical retracts. The numerical multiplicity map is
constructed by `FusionCategory`, and all dimension laws are proved there.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe v u w v' u' w'
namespace Paper18.Category.FiniteSemisimpleSkeleton

attribute [local instance 2000] RightRigidCategory.rightDual

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [RightRigidCategory D] [Simple (𝟙_ D)]
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)
  (F : C ⥤ D) [F.Additive] [F.Monoidal]

/-- The dominant-functor assertion of Lemma 3.1 for actual categories. -/
theorem integral_of_dominant
    (hF : ∀ Y : D, ∃ X : C, Nonempty (Retract Y (F.obj X)))
    (hS : S.Integral) : T.Integral := by
  apply T.integral_iff_basis.mpr
  exact Paper18.lemma3_1_dominant (S.fusionMap T F hF) (S.integral_iff_basis.mp hS)

include F in
/-- Integrality reflects along every tensor functor, using FP dimension
preservation on actual objects. -/
theorem integral_of_integral_target (hT : T.Integral) : S.Integral := by
  apply S.integral_iff_basis.mpr
  exact (S.fusionRuleMap T F).integral_of_target_integral (T.integral_iff_basis.mp hT)

/-- Integrality is equivalent along a dominant tensor functor. -/
theorem integral_iff_of_dominant
    (hF : ∀ Y : D, ∃ X : C, Nonempty (Retract Y (F.obj X))) :
    S.Integral ↔ T.Integral :=
  ⟨S.integral_of_dominant T F hF, S.integral_of_integral_target T F⟩

/-- Lemma 3.1 with the paper's dominance condition on actual simple objects. -/
theorem lemma3_1_dominant (hF : Dominant F) (hS : S.Integral) : T.Integral :=
  S.integral_of_dominant T F ((S.dominant_iff_retracts T F).mp hF) hS

end Paper18.Category.FiniteSemisimpleSkeleton
