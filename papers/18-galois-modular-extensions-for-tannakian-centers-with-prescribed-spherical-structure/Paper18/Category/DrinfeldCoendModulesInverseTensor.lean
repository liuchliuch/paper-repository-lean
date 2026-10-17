import Paper18.Category.DrinfeldCoendModulesInverseAssociativity
import Paper18.Category.DrinfeldCoendModulesInverseGeneration
import Paper18.Category.DrinfeldCoendModulesInverseHexagon
import Paper18.Category.DrinfeldCoendModulesAssociativityCriterion

/-! # The half-braiding laws recovered from actual module associativity -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj
universe v u w
namespace Paper18.Category.DrinfeldCoendModules
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)

/-- Actual module associativity, the actual coend multiplication, and
rigid cap transposition imply the annular tensor law. -/
lemma moduleHolonomy_tensor (M : Mod_ D (algebra S)) (X Y : D) :
    moduleHolonomy S M (X ⊗ Y) =
      annularTensor X Y M.X (moduleHolonomy S M X) (moduleHolonomy S M Y) := by
  apply (cap_associativity_iff_tensor M.X (moduleHolonomy S M)
    (fun f => moduleHolonomy_naturality S M f) X Y).mp
  simpa only [productKernel, ← moduleCap_eq_capOf] using moduleCap_tensor S M X Y

/-- The recovered crossing obeys the inverse half-braiding hexagon,
with no extra coherence data supplied. -/
lemma moduleInverseCrossing_tensor (M : Mod_ D (algebra S)) (X Y : D) :
    moduleInverseCrossing S M (X ⊗ Y) =
      (α_ X Y M.X).hom ≫ X ◁ moduleInverseCrossing S M Y ≫
        (α_ X M.X Y).inv ≫ moduleInverseCrossing S M X ▷ Y ≫ (α_ M.X X Y).hom := by
  dsimp only [moduleInverseCrossing]
  rw [moduleHolonomy_tensor]
  exact inverseCrossing_tensor_word M.X X Y (moduleHolonomy S M X) (moduleHolonomy S M Y)

/-- The actual recovered crossing, with all three laws derived from the
module action, its laws, and rigid transposition. -/
def moduleRightLaxHalfBraiding (M : Mod_ D (algebra S)) : RightLaxHalfBraiding M.X where
  hom := moduleInverseCrossing S M
  naturality := moduleInverseCrossing_naturality S M
  monoidal := moduleInverseCrossing_tensor S M
  unit := moduleInverseCrossing_unit S M

/-- Every actual module yields an actual half-braiding. Rigidity proves
invertibility, while module associativity proves the hexagon. -/
def moduleHalfBraiding (M : Mod_ D (algebra S)) : HalfBraiding M.X :=
  (moduleRightLaxHalfBraiding S M).toHalfBraiding

@[simp] lemma moduleHalfBraiding_inv (M : Mod_ D (algebra S)) (T : D) :
    ((moduleHalfBraiding S M).β T).inv = moduleInverseCrossing S M T := rfl

end Paper18.Category.DrinfeldCoendModules
