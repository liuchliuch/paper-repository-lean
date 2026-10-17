import Paper18.Category.DiagonalAlgebraAdjoints
import Mathlib.CategoryTheory.Monoidal.Mon_

/-!
# The actual algebra obtained from the right-adjoint unit

The unit algebra is mapped through the constructed actual right adjoint.
Its multiplication, unit and all monoid coherence are the proved lax
monoidal image construction. Explicit adjunction transpose formulas make
the later centrality and commutativity proof concrete.
-/

noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped MonObj
universe v u v₁ u₁
namespace Paper18.Category.DiagonalAlgebra

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [LeftRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [RightRigidCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  (F : C ⥤ D) [F.Monoidal] [F.Additive] [F.Linear ℂ]
  (L : D ⥤ C) (adj : L ⊣ F)

/-- The actual right adjoint evaluated at the actual tensor unit. -/
def rightAdjointUnit : C := (rigidRightAdjoint F L adj).obj (𝟙_ D)

/-- The actual monoid structure is derived from the actual lax monoidal
functor, so associativity and both unit laws require no algebra-law input. -/
instance rightAdjointUnitMonObj : MonObj (rightAdjointUnit F L adj) :=
  Functor.monObjObj (F := rigidRightAdjoint F L adj) (𝟙_ D)

/-- The actual counit of the constructed right adjunction at the unit. -/
def rightAdjointUnitCounit : F.obj (rightAdjointUnit F L adj) ⟶ 𝟙_ D :=
  (rigidRightAdjunction F L adj).counit.app (𝟙_ D)

set_option maxRecDepth 4000 in
/-- Multiplication is the actual transpose of the product of the two
counit components, including the strong monoidal comparison of `F`. -/
theorem rightAdjointUnit_mul :
    μ[rightAdjointUnit F L adj] =
      (rigidRightAdjunction F L adj).homEquiv
        (rightAdjointUnit F L adj ⊗ rightAdjointUnit F L adj) (𝟙_ D)
        (δ F _ _ ≫ (rightAdjointUnitCounit F L adj ⊗ₘ rightAdjointUnitCounit F L adj) ≫
          (λ_ (𝟙_ D)).hom) := by
  change ((rigidRightAdjunction F L adj).homEquiv _ _
      (δ F _ _ ≫ (rightAdjointUnitCounit F L adj ⊗ₘ rightAdjointUnitCounit F L adj))) ≫
      (rigidRightAdjoint F L adj).map (λ_ (𝟙_ D)).hom = _
  simpa only [Category.assoc] using
    ((rigidRightAdjunction F L adj).homEquiv_naturality_right
      (δ F _ _ ≫ (rightAdjointUnitCounit F L adj ⊗ₘ rightAdjointUnitCounit F L adj))
      (λ_ (𝟙_ D)).hom).symm

/-- The algebra unit is the transpose of the actual unit comparison of
the strong monoidal functor. -/
theorem rightAdjointUnit_one :
    η[rightAdjointUnit F L adj] =
      (rigidRightAdjunction F L adj).homEquiv (𝟙_ C) (𝟙_ D) (Functor.OplaxMonoidal.η F) := by
  change (rigidRightAdjunction F L adj).homEquiv _ _ (Functor.OplaxMonoidal.η F) ≫
    (rigidRightAdjoint F L adj).map (𝟙 (𝟙_ D)) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

end Paper18.Category.DiagonalAlgebra
