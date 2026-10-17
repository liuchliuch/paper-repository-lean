import Paper18.Category.GraphLagrangianNoPivotal
import Paper18.Category.SeparableModuleOrbit

/-! # The actual nonempty simple-orbit module of a graph algebra -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped MonObj
universe v u w
namespace Paper18.Category.GraphLagrangian
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)
  (α : D ⥤ D) [α.Braided] [α.Additive] [α.Linear ℂ] [α.IsEquivalence]

/-- The normalized actual graph pairing proves the underlying algebra
nonzero; no existence of a nonzero module is assumed. -/
theorem underlying_id_ne_zero : (𝟙 (underlyingAlgebra S α) : _ ⟶ _) ≠ 0 := by
  have hc := congrArg (Center.forget D).map (pairing_one_counit S α)
  have hunit : η[underlyingAlgebra S α] ≫
      (Center.forget D).map (multiplicationPairing S α).counit = 𝟙 (𝟙_ D) := by
    change (𝟙 (𝟙_ D) ≫ (η[algebra S α]).f) ≫ (multiplicationPairing S α).counit.f = _
    change (η[algebra S α]).f ≫ (multiplicationPairing S α).counit.f = 𝟙 (𝟙_ D) at hc
    simpa only [Category.id_comp] using hc
  intro hz
  have hη : η[underlyingAlgebra S α] = 0 := by
    calc
      η[underlyingAlgebra S α] = η[underlyingAlgebra S α] ≫ 𝟙 _ := (Category.comp_id _).symm
      _ = 0 := by rw [hz, comp_zero]
  rw [hη, zero_comp] at hunit
  exact CategoryTheory.id_nonzero (𝟙_ D) hunit.symm

/-- The actual graph algebra's finite semisimple module skeleton. -/
def moduleSkeleton := (underlyingSeparableNoPivotal S α).skeleton S

/-- A chosen actual simple-orbit component of graph modules. -/
abbrev ModuleOrbit := (underlyingSeparableNoPivotal S α).OrbitComponent S
  (underlying_id_ne_zero S α)

/-- The actual chosen simple generator of the graph module component. -/
def moduleOrbitBase : ModuleOrbit S α :=
  (underlyingSeparableNoPivotal S α).orbitBase S (underlying_id_ne_zero S α)

def moduleOrbitSkeleton :=
  (underlyingSeparableNoPivotal S α).orbitSkeleton S (underlying_id_ne_zero S α)

def moduleOrbitHasKernels : HasKernels (ModuleOrbit S α) :=
  (underlyingSeparableNoPivotal S α).orbitHasKernels S (underlying_id_ne_zero S α)

end Paper18.Category.GraphLagrangian
