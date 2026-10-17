import Paper18.Category.RepresentationFunctionAlgebra
import Paper18.Category.SeparableModules

/-!
# The equivariant diagonal splitting of `Fun(G)`

The diagonal map sends a delta function at `g` to the tensor of that delta
function with itself. Its equivariance and algebra splitting are actual
linear-map statements, used to construct the separable algebra witness.
-/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct BigOperators
namespace Paper18.Category.Representation
variable {G : Type} [Group G] [Fintype G]

/-- The delta function supported at a specified group element. -/
def delta (g : G) : G → ℂ := Pi.single g 1

omit [Group G] [Fintype G] in
@[simp] lemma delta_apply (g x : G) : delta g x = if x = g then 1 else 0 := by
  simp [delta, Pi.single_apply, eq_comm]

omit [Fintype G] in
lemma action_delta (g h : G) : functionAction g (delta h) = delta (g * h) := by
  funext x
  simp only [functionAction_apply, delta_apply]
  rw [inv_mul_eq_iff_eq_mul]

/-- The diagonal splitting as an actual complex-linear map. -/
def functionDelta : (G → ℂ) →ₗ[ℂ] ((G → ℂ) ⊗[ℂ] (G → ℂ)) :=
  ∑ g : G, (LinearMap.proj g).smulRight (delta g ⊗ₜ delta g)

omit [Group G] in
@[simp] lemma functionDelta_apply (f : G → ℂ) :
    functionDelta f = ∑ g : G, f g • (delta g ⊗ₜ delta g) := by
  simp [functionDelta, LinearMap.sum_apply]

/-- The diagonal splitting is equivariant under actual left translation. -/
lemma functionDelta_equivariant (g : G) (f : G → ℂ) :
    functionDelta (functionAction g f) =
      TensorProduct.map (functionAction g) (functionAction g) (functionDelta f) := by
  simp only [functionDelta_apply, map_sum, map_smul, TensorProduct.map_tmul, action_delta]
  apply Fintype.sum_equiv (Equiv.mulLeft g⁻¹)
  intro x
  simp [Equiv.mulLeft, functionAction_apply]

/-- The equivariant diagonal map, as a morphism in the actual representation
category. -/
def functionsSection : functions (G := G) ⟶ functions (G := G) ⊗ functions (G := G) where
  hom := ModuleCat.ofHom functionDelta
  comm g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact functionDelta_equivariant g f

omit [Group G] in
lemma functionDelta_mul (f : G → ℂ) : (LinearMap.mul' ℂ (G → ℂ)) (functionDelta f) = f := by
  simp only [functionDelta_apply, map_sum, map_smul, LinearMap.mul'_apply]
  funext x
  simp [delta_apply, Finset.sum_apply]

/-- Multiplication composed with the actual diagonal splitting is the
identity morphism on the regular commutative algebra. -/
lemma functionsSection_mul : functionsSection (G := G) ≫ functionsMul = 𝟙 (functions (G := G)) := by
  apply Action.Hom.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  exact functionDelta_mul

end Paper18.Category.Representation

namespace Paper18.Category.Representation
variable {G : Type} [Group G] [Fintype G]

omit [Group G] [Fintype G] in
lemma mul_delta (f : G → ℂ) (g : G) : f * delta g = f g • delta g := by
  funext x
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, delta_apply]
  split_ifs with h
  · subst x; rfl
  · simp

omit [Group G] [Fintype G] in
lemma delta_mul (f : G → ℂ) (g : G) : delta g * f = f g • delta g := by
  rw [mul_comm, mul_delta]

omit [Group G] in
/-- Left module compatibility of the diagonal map, on actual tensor
vectors. -/
lemma functionDelta_left_linear (f h : G → ℂ) :
    functionDelta (f * h) =
      (LinearMap.mul' ℂ (G → ℂ)).rTensor (G → ℂ)
        ((TensorProduct.assoc ℂ (G → ℂ) (G → ℂ) (G → ℂ)).symm
          (f ⊗ₜ functionDelta h)) := by
  simp only [functionDelta_apply, Pi.mul_apply, TensorProduct.tmul_sum,
    TensorProduct.tmul_smul, map_sum, map_smul, TensorProduct.assoc_symm_tmul,
    LinearMap.rTensor_tmul, LinearMap.mul'_apply, mul_delta,
    ← TensorProduct.smul_tmul', smul_smul]
  congr 1
  funext g
  rw [mul_comm]

omit [Group G] in
/-- Right module compatibility of the diagonal map, on actual tensor
vectors. -/
lemma functionDelta_right_linear (f h : G → ℂ) :
    functionDelta (f * h) =
      (LinearMap.mul' ℂ (G → ℂ)).lTensor (G → ℂ)
        ((TensorProduct.assoc ℂ (G → ℂ) (G → ℂ) (G → ℂ))
          (functionDelta f ⊗ₜ h)) := by
  simp only [functionDelta_apply, Pi.mul_apply, TensorProduct.sum_tmul,
    TensorProduct.smul_tmul', map_sum, TensorProduct.assoc_tmul,
    LinearMap.lTensor_tmul, LinearMap.mul'_apply, delta_mul,
    TensorProduct.tmul_smul, smul_smul]
  apply Finset.sum_congr rfl
  intro g _
  rw [mul_comm]

end Paper18.Category.Representation

namespace Paper18.Category.Representation
variable {G : Type} [Group G] [Fintype G]

/-- The diagonal splitting is a left module map in the actual
representation category. -/
lemma functionsSection_left_linear :
    functionsMul (G := G) ≫ functionsSection =
      (functions ◁ functionsSection) ≫ (α_ functions functions functions).inv ≫
        (functionsMul ▷ functions) := by
  apply Action.Hom.ext
  simp only [Action.comp_hom, Action.whiskerLeft_hom, Action.whiskerRight_hom,
    Action.associator_inv_hom]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro h
  exact functionDelta_left_linear f h

/-- The diagonal splitting is a right module map in the actual
representation category. -/
lemma functionsSection_right_linear :
    functionsMul (G := G) ≫ functionsSection =
      (functionsSection ▷ functions) ≫ (α_ functions functions functions).hom ≫
        (functions ◁ functionsMul) := by
  apply Action.Hom.ext
  simp only [Action.comp_hom, Action.whiskerLeft_hom, Action.whiskerRight_hom,
    Action.associator_hom_hom]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro h
  exact functionDelta_right_linear f h

end Paper18.Category.Representation

namespace Paper18.Category.Representation
variable {G : Type} [Group G] [Fintype G]

/-- The actual regular function algebra is separable, via the equivariant
diagonal map and its proved left and right module compatibilities. -/
def functionsSeparable : SeparableAlgebra (functions (G := G)) where
  section_ := functionsSection
  section_mul := functionsSection_mul
  left_linear := functionsSection_left_linear
  right_linear := functionsSection_right_linear

end Paper18.Category.Representation
