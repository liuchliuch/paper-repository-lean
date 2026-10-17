import Paper18.Category.FixedBoundaryDescentBasic
import Paper18.Category.RepresentationFunctionAverage
import Paper18.Category.FixedBoundaryRegularFaithful

/-! # Actual regular descent without a transparency hypothesis -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators MonObj Obj
universe v u
namespace Paper18.Category.FixedBoundary
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [CategoryTheory.Limits.HasCoequalizers C]
  {G : Type} [Group G] [Fintype G]
  (F : FDRep ℂ G ⥤ C) [F.Braided] [F.Additive] [F.Linear ℂ]

omit [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
/-- The actual mean of the regular translation automorphisms is precisely
the projector onto the actual algebra unit. -/
theorem regular_average_translation :
    (Fintype.card G : ℂ)⁻¹ • (∑ g : G, (regularTranslation F) g) =
      (regularAugmentation F) ≫ η[(regularAlgebra F)] := by
  have h := congrArg F.map (Representation.average_rightTranslation (G := G))
  simp only [Functor.map_smul, Functor.map_sum, Functor.map_comp] at h
  change (Fintype.card G : ℂ)⁻¹ • (∑ g : G, F.map (Representation.rightTranslation g)) =
    (F.map Representation.functionsAverage ≫
      (Functor.Monoidal.εIso F).inv) ≫
        (Functor.Monoidal.εIso F).hom ≫ F.map Representation.functionsOne
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h

omit [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
@[reassoc (attr := simp)]
theorem freeUnit_translation (X : C) (g : G) :
    RelativeTensor.freeUnit (A := (regularAlgebra F)) X ≫ ((regularTranslation F) g ▷ X) =
      RelativeTensor.freeUnit X := by
  unfold RelativeTensor.freeUnit
  rw [Category.assoc, ← comp_whiskerRight, IsMonHom.one_hom]

/-- A map fixed by the actual finite-group translations factors through
the actual constant-function summand of the regular algebra. -/
theorem invariant_factors_unit {X Y : C}
    (k : X ⟶ (regularAlgebra F) ⊗ Y)
    (hk : ∀ g : G, k ≫ ((regularTranslation F) g ▷ Y) = k) :
    k ≫ ((regularAugmentation F) ▷ Y) ≫ (η[(regularAlgebra F)] ▷ Y) = k := by
  rw [← comp_whiskerRight, ← (regular_average_translation F)]
  rw [MonoidalLinear.smul_whiskerRight, Linear.comp_smul,
    sum_whiskerRight, Preadditive.comp_sum]
  simp only [hk, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast Fintype.card_ne_zero


end Paper18.Category.FixedBoundary
