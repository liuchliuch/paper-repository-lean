import Paper18.Category.TannakianDescent
import Paper18.Category.RepresentationFunctionAverage
import Paper18.Category.RelativeTensorFree

/-! # Actual regular-algebra averaging for Tannakian descent -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators MonObj
universe v u
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  {G : Type} [Group G] [Fintype G] (T : TannakianCenter C G)

/-- The actual regular-algebra augmentation is the transported finite-group
mean, with the actual monoidal unit isomorphism. -/
def TannakianCenter.regularAugmentation : T.regularAlgebra ⟶ 𝟙_ C :=
  T.inclusion.map Representation.functionsAverage ≫ (Functor.Monoidal.εIso T.inclusion).inv

omit [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
@[reassoc (attr := simp)]
theorem TannakianCenter.regular_one_augmentation :
    η[T.regularAlgebra] ≫ T.regularAugmentation = 𝟙 _ := by
  change ((Functor.Monoidal.εIso T.inclusion).hom ≫
      T.inclusion.map Representation.functionsOne) ≫
        (T.inclusion.map Representation.functionsAverage ≫
          (Functor.Monoidal.εIso T.inclusion).inv) = 𝟙 _
  simp only [Category.assoc]
  rw [← T.inclusion.map_comp_assoc, Representation.functionsOne_average,
    T.inclusion.map_id, Category.id_comp, Iso.hom_inv_id]

omit [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
/-- The actual mean of the regular translation automorphisms is precisely
the projector onto the actual algebra unit. -/
theorem TannakianCenter.regular_average_translation :
    (Fintype.card G : ℂ)⁻¹ • (∑ g : G, T.regularTranslation g) =
      T.regularAugmentation ≫ η[T.regularAlgebra] := by
  have h := congrArg T.inclusion.map (Representation.average_rightTranslation (G := G))
  simp only [Functor.map_smul, Functor.map_sum, Functor.map_comp] at h
  change (Fintype.card G : ℂ)⁻¹ • (∑ g : G, T.inclusion.map (Representation.rightTranslation g)) =
    (T.inclusion.map Representation.functionsAverage ≫
      (Functor.Monoidal.εIso T.inclusion).inv) ≫
        (Functor.Monoidal.εIso T.inclusion).hom ≫ T.inclusion.map Representation.functionsOne
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h

omit [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
@[reassoc (attr := simp)]
theorem TannakianCenter.freeUnit_translation (X : C) (g : G) :
    RelativeTensor.freeUnit (A := T.regularAlgebra) X ≫ (T.regularTranslation g ▷ X) =
      RelativeTensor.freeUnit X := by
  unfold RelativeTensor.freeUnit
  rw [Category.assoc, ← comp_whiskerRight, IsMonHom.one_hom]

/-- A map fixed by the actual finite-group translations factors through
the actual constant-function summand of the regular algebra. -/
theorem TannakianCenter.invariant_factors_unit {X Y : C}
    (k : X ⟶ T.regularAlgebra ⊗ Y)
    (hk : ∀ g : G, k ≫ (T.regularTranslation g ▷ Y) = k) :
    k ≫ (T.regularAugmentation ▷ Y) ≫ (η[T.regularAlgebra] ▷ Y) = k := by
  rw [← comp_whiskerRight, ← T.regular_average_translation]
  rw [MonoidalLinear.smul_whiskerRight, Linear.comp_smul,
    sum_whiskerRight, Preadditive.comp_sum]
  simp only [hk, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast Fintype.card_ne_zero

end Paper18.Category
