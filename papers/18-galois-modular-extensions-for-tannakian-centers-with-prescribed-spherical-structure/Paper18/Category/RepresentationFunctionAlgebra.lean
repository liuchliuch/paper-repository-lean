import Paper18.Category.RepresentationDimension
import Mathlib.CategoryTheory.Monoidal.Internal.Module
import Mathlib.CategoryTheory.Monoidal.CommMon_
import Mathlib.CategoryTheory.Monoidal.Mod_

/-!
# The actual regular commutative algebra `Fun(G)`

Left translation on complex-valued functions is an actual finite-dimensional
representation. Its pointwise product is equivariant and gives the regular
commutative algebra used in de-equivariantization.
-/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct BigOperators
namespace Paper18.Category.Representation
variable {G : Type} [Group G] [Fintype G]

/-- Left translation of functions, as an actual representation. -/
def functionAction : _root_.Representation ℂ G (G → ℂ) where
  toFun g := LinearMap.pi (fun h => LinearMap.proj (g⁻¹ * h))
  map_one' := by
    apply LinearMap.ext
    intro f
    funext h
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro f
    funext x
    change f ((g * h)⁻¹ * x) = f (h⁻¹ * (g⁻¹ * x))
    simp [mul_inv_rev, mul_assoc]

/-- The finite representation on the regular function algebra. -/
def functions : FDRep ℂ G := FDRep.of (functionAction (G := G))

omit [Fintype G] in
@[simp] lemma functionAction_apply (g : G) (f : G → ℂ) (h : G) :
    functionAction g f h = f (g⁻¹ * h) := rfl

/-- The constant-function unit is equivariant. -/
def functionsOne : 𝟙_ (FDRep ℂ G) ⟶ functions (G := G) where
  hom := ModuleCat.ofHom (Algebra.linearMap ℂ (G → ℂ))
  comm g := by
    apply ModuleCat.hom_ext
    rfl

/-- Pointwise multiplication is equivariant under left translation. -/
def functionsMul : functions (G := G) ⊗ functions (G := G) ⟶ functions (G := G) where
  hom := ModuleCat.ofHom (LinearMap.mul' ℂ (G → ℂ))
  comm g := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro h
    change (LinearMap.mul' ℂ (G → ℂ))
      ((TensorProduct.map (functionAction g) (functionAction g)) (f ⊗ₜ h)) =
      functionAction g ((LinearMap.mul' ℂ (G → ℂ)) (f ⊗ₜ h))
    simp only [TensorProduct.map_tmul, LinearMap.mul'_apply]
    rfl

/-- The categorical algebra laws for the actual representation on `Fun(G)`.
They follow from the pointwise complex algebra laws. -/
instance functionsMonObj : MonObj (functions (G := G)) where
  one := functionsOne
  mul := functionsMul
  one_mul := by
    apply Action.Hom.ext
    letI := ModuleCat.MonModuleEquivalenceAlgebra.inverseObj (AlgCat.of ℂ (G → ℂ))
    simpa only [Action.comp_hom, Action.whiskerRight_hom, Action.leftUnitor_hom_hom,
      functionsOne, functionsMul] using MonObj.one_mul (ModuleCat.of ℂ (G → ℂ))
  mul_one := by
    apply Action.Hom.ext
    letI := ModuleCat.MonModuleEquivalenceAlgebra.inverseObj (AlgCat.of ℂ (G → ℂ))
    simpa only [Action.comp_hom, Action.whiskerLeft_hom, Action.rightUnitor_hom_hom,
      functionsOne, functionsMul] using MonObj.mul_one (ModuleCat.of ℂ (G → ℂ))
  mul_assoc := by
    apply Action.Hom.ext
    letI := ModuleCat.MonModuleEquivalenceAlgebra.inverseObj (AlgCat.of ℂ (G → ℂ))
    simpa only [Action.comp_hom, Action.whiskerLeft_hom, Action.whiskerRight_hom,
      Action.associator_hom_hom, functionsMul] using MonObj.mul_assoc (ModuleCat.of ℂ (G → ℂ))

/-- Pointwise multiplication is commutative for the actual symmetric
representation braiding. -/
instance functionsCommMonObj : IsCommMonObj (functions (G := G)) where
  mul_comm := by
    apply Action.Hom.ext
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro h
    change (LinearMap.mul' ℂ (G → ℂ))
      ((TensorProduct.comm ℂ (G → ℂ) (G → ℂ)) (f ⊗ₜ h)) =
      (LinearMap.mul' ℂ (G → ℂ)) (f ⊗ₜ h)
    simp only [TensorProduct.comm_tmul, LinearMap.mul'_apply]
    exact @mul_comm (G → ℂ) inferInstance h f

end Paper18.Category.Representation

namespace Paper18.Category.Representation
variable {G : Type} [Group G] [Fintype G]

/-- Equivariance forces the invariant vector in the regular function
representation to be a constant function. -/
lemma unit_hom_constant (p : 𝟙_ (FDRep ℂ G) ⟶ functions (G := G)) (g : G) :
    p.hom.hom (1 : ℂ) g = p.hom.hom (1 : ℂ) 1 := by
  have h := congrArg
    (fun q : FGModuleCat.of ℂ ℂ ⟶ FGModuleCat.of ℂ (G → ℂ) => q.hom 1 g) (p.comm g)
  change p.hom.hom (1 : ℂ) g = p.hom.hom (1 : ℂ) (g⁻¹ * g) at h
  simpa using h

/-- Evaluation identifies the invariant Hom space of `Fun(G)` with the
complex scalars, as an actual linear equivalence. -/
def functionsUnitHomEquiv :
    (𝟙_ (FDRep ℂ G) ⟶ functions (G := G)) ≃ₗ[ℂ] ℂ where
  toFun p := p.hom.hom (1 : ℂ) 1
  invFun c := c • functionsOne
  left_inv p := by
    apply Action.Hom.ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    funext g
    change p.hom.hom (1 : ℂ) 1 * (1 : ℂ) = p.hom.hom (1 : ℂ) g
    simpa using (unit_hom_constant p g).symm
  right_inv c := by
    change c * (1 : ℂ) = c
    exact mul_one c
  map_add' p q := rfl
  map_smul' c p := rfl

/-- The actual regular commutative algebra is connected. -/
theorem functions_connected :
    Module.finrank ℂ (𝟙_ (FDRep ℂ G) ⟶ functions (G := G)) = 1 := by
  rw [functionsUnitHomEquiv.finrank_eq, Module.finrank_self]

end Paper18.Category.Representation
