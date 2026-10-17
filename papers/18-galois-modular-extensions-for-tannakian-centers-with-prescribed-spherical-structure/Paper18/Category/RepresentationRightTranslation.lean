import Paper18.Category.RepresentationFunctionAlgebra

/-!
# Genuine algebra automorphisms by right translation

Right translation commutes with left translation and preserves pointwise
multiplication. It therefore gives actual algebra automorphisms of the
Tannakian regular algebra, rather than permutations of numerical labels.
-/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped MonObj TensorProduct
namespace Paper18.Category.Representation
variable {G : Type} [Group G] [Fintype G]

/-- Right translation as an actual complex-linear map. -/
def rightTranslationLinear (g : G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) :=
  LinearMap.pi (fun h => LinearMap.proj (h * g))

omit [Fintype G] in
@[simp] lemma rightTranslationLinear_apply (g : G) (f : G → ℂ) (h : G) :
    rightTranslationLinear g f h = f (h * g) := rfl

/-- Right translation is equivariant for the left regular action. -/
def rightTranslation (g : G) : functions (G := G) ⟶ functions (G := G) where
  hom := ModuleCat.ofHom (rightTranslationLinear g)
  comm h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    funext x
    change f (h⁻¹ * (x * g)) = f ((h⁻¹ * x) * g)
    rw [mul_assoc]

@[simp] lemma rightTranslation_one : rightTranslation (1 : G) = 𝟙 functions := by
  apply Action.Hom.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  funext x
  change f (x * 1) = f x
  rw [mul_one]

/-- Multiplication in the endomorphism algebra follows the usual group
order; categorical composition is written in the reverse order. -/
lemma rightTranslation_mul (g h : G) :
    rightTranslation (g * h) = rightTranslation h ≫ rightTranslation g := by
  apply Action.Hom.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  funext x
  change f (x * (g * h)) = f ((x * g) * h)
  rw [mul_assoc]

/-- Right translation is an actual isomorphism of representations. -/
def rightTranslationIso (g : G) : functions (G := G) ≅ functions (G := G) where
  hom := rightTranslation g
  inv := rightTranslation g⁻¹
  hom_inv_id := by rw [← rightTranslation_mul, inv_mul_cancel, rightTranslation_one]
  inv_hom_id := by rw [← rightTranslation_mul, mul_inv_cancel, rightTranslation_one]

/-- Right translation preserves the actual algebra unit and product. -/
instance rightTranslationIsMonHom (g : G) : IsMonHom (rightTranslation g) where
  one_hom := by
    apply Action.Hom.ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    funext x
    rfl
  mul_hom := by
    apply Action.Hom.ext
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro h
    change rightTranslationLinear g ((LinearMap.mul' ℂ (G → ℂ)) (f ⊗ₜ h)) =
      (LinearMap.mul' ℂ (G → ℂ))
        ((TensorProduct.map (rightTranslationLinear g) (rightTranslationLinear g)) (f ⊗ₜ h))
    simp only [LinearMap.mul'_apply, TensorProduct.map_tmul]
    rfl

end Paper18.Category.Representation
