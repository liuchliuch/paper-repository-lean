import Paper18.Category.RepresentationFunctionSeparable
import Paper18.Category.RepresentationRightTranslation

/-! # Actual diagonal orthogonality for the regular finite-group algebra -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct BigOperators MonObj
namespace Paper18.Category.Representation
variable {G : Type} [Group G] [Fintype G]

/-- The diagonal and a nontrivial right translation have disjoint actual
delta-function support. -/
theorem functionDelta_translation_mul (g : G) (f : G → ℂ) :
    (LinearMap.mul' ℂ (G → ℂ))
      (TensorProduct.map (LinearMap.id : (G → ℂ) →ₗ[ℂ] (G → ℂ))
        (rightTranslationLinear g) (functionDelta f)) = if g = 1 then f else 0 := by
  simp only [functionDelta_apply, map_sum, map_smul, TensorProduct.map_tmul,
    LinearMap.id_apply, LinearMap.mul'_apply]
  funext x
  simp [Finset.sum_apply, delta_apply, Pi.mul_apply, Pi.smul_apply,
    rightTranslationLinear_apply, eq_comm]
  by_cases hg : g = 1 <;> simp [hg]

/-- The actual separability element satisfies the finite-group torsor
orthogonality identity. -/
theorem functions_element_translation (g : G) :
    (functionsSeparable (G := G)).element ≫
        (functions (G := G) ◁ rightTranslation g) ≫ μ[functions (G := G)] =
      if g = 1 then η[functions (G := G)] else 0 := by
  by_cases hg : g = 1
  · subst g
    simpa only [rightTranslation_one, MonoidalCategory.whiskerLeft_id,
      Category.id_comp, if_pos rfl] using (functionsSeparable (G := G)).element_mul
  · rw [if_neg hg]
    apply Action.Hom.ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    change (LinearMap.mul' ℂ (G → ℂ))
      (TensorProduct.map (LinearMap.id : (G → ℂ) →ₗ[ℂ] (G → ℂ))
        (rightTranslationLinear g) (functionDelta (fun _ : G => (show ℂ from c)))) = 0
    rw [functionDelta_translation_mul, if_neg hg]

end Paper18.Category.Representation
