import Paper18.Category.InvertibleObjects
import Paper18.Category.SphericalComparisonPositive

/-!
# Actual duals and dimensions of invertible objects

The inverse-to-dual isomorphism is constructed by the rigid Hom adjunction
from the actual tensor-unit isomorphism. Spherical dimensions of invertibles
are then derived to be signs; positivity fixes that sign to one.
-/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

namespace TensorInverse
variable {T : C} (A : TensorInverse T)

/-- An actual tensor inverse is actually isomorphic to the chosen rigid dual. -/
def inverseIsoDual : A.inverse ≅ dual C T := by
  letI := A.simple S
  letI := A.symm.simple S
  letI := S.simple_rightDual T
  let E := (tensorRightHomLinearEquiv A.inverse T (dual C T) (𝟙_ C)).trans
    (CategoryTheory.Linear.homCongr ℂ (Iso.refl A.inverse) (λ_ (dual C T)))
  have hl : A.left.hom ≠ 0 := by
    intro hz
    exact CategoryTheory.id_nonzero (𝟙_ C) (by
      simpa [hz] using A.left.inv_hom_id.symm)
  have hf : E A.left.hom ≠ 0 := by
    intro hz
    apply hl
    apply E.injective
    simpa only [map_zero] using hz
  letI := CategoryTheory.isIso_of_hom_simple hf
  exact asIso (E A.left.hom)

include S A in
/-- An actual spherical trace takes a sign value on any actual invertible. -/
lemma rightDim_sign (J : PivotalStructure C) (hJ : J.Spherical) :
    J.rightDim T = 1 ∨ J.rightDim T = -1 := by
  have hi : J.rightDim A.inverse = J.rightDim T := by
    rw [J.rightDim_iso (A.inverseIsoDual S), J.rightDim_dual_of_spherical hJ]
  have hm : J.rightDim T ^ 2 = 1 := by
    calc
      J.rightDim T ^ 2 = J.rightDim T * J.rightDim A.inverse := by rw [hi, pow_two]
      _ = J.rightDim (T ⊗ A.inverse) := (J.rightDim_tensor T A.inverse).symm
      _ = J.rightDim (𝟙_ C) := J.rightDim_iso A.right
      _ = 1 := J.rightDim_unit S
  exact sq_eq_one_iff.mp hm

include S A in
/-- A positive pivotal trace equals one on every actual invertible object. -/
lemma rightDim_eq_one_of_positive (J : PivotalStructure C) (hJ : J.Positive) :
    J.rightDim T = 1 := by
  rw [J.rightDim_eq_fpdim S hJ T, S.fpdim_eq_one_of_tensorInvertible ⟨A⟩]
  rfl

end TensorInverse
end Paper18.Category
