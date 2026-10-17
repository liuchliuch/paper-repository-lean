import Paper18.Category.DiagonalAlgebraRightAdjoint
import Paper18.Category.SemisimpleSplitting
import Paper18.Category.LocalModulesPivotalFrobenius

/-! # Actual counit and rigid contractions for the canonical algebra -/
noncomputable section
set_option maxHeartbeats 1000000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped MonObj
universe v u v' u' w
namespace Paper18.Category.DiagonalAlgebra

section Contraction
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  (X Y : C) [ExactPairing X Y]

/-- The cap functional associated with an actual map into the primal object. -/
def capFunctional (q : 𝟙_ C ⟶ X) : Y ⟶ 𝟙_ C :=
  (ρ_ Y).inv ≫ (Y ◁ q) ≫ ε_ X Y

/-- Contracting an actual cup with a functional and the cap-dual of a
vector is exactly their original composite. -/
lemma cup_capFunctional (a : X ⟶ 𝟙_ C) (q : 𝟙_ C ⟶ X) :
    η_ X Y ≫ (a ⊗ₘ capFunctional X Y q) ≫ (λ_ (𝟙_ C)).hom = q ≫ a := by
  calc
    _ = η_ X Y ≫ (X ◁ (ρ_ Y).inv) ≫ (X ◁ (Y ◁ q)) ≫
        (X ◁ ε_ X Y) ≫ (ρ_ X).hom ≫ a := by
      simp only [capFunctional, MonoidalCategory.tensorHom_def', whiskerLeft_comp, assoc]
      monoidal
    _ = (λ_ (𝟙_ C)).inv ≫ η_ X Y ▷ (𝟙_ C) ≫
        (α_ X Y (𝟙_ C)).hom ≫ (X ◁ (Y ◁ q)) ≫
        (X ◁ ε_ X Y) ≫ (ρ_ X).hom ≫ a := by monoidal
    _ = q ≫ a := by
      rw [← associator_naturality_right_assoc, ← whisker_exchange_assoc]
      rw [ExactPairing.evaluation_coevaluation_assoc]
      monoidal
end Contraction

section Algebra
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [LeftRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [RightRigidCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  (F : C ⥤ D) [F.Monoidal] [F.Additive] [F.Linear ℂ]
  (L : D ⥤ C) (adj : L ⊣ F)

/-- The actual adjunction counit evaluates the canonical algebra unit to
the strong monoidal unit comparison. -/
lemma rightAdjointUnit_one_counit :
    F.map η[rightAdjointUnit F L adj] ≫ rightAdjointUnitCounit F L adj =
      Functor.OplaxMonoidal.η F := by
  unfold rightAdjointUnitCounit
  rw [rightAdjointUnit_one, ← (rigidRightAdjunction F L adj).homEquiv_counit]
  exact Equiv.symm_apply_apply _ _

/-- The actual multiplication counit equation, with all tensorators. -/
lemma rightAdjointUnit_mul_counit :
    F.map μ[rightAdjointUnit F L adj] ≫ rightAdjointUnitCounit F L adj =
      δ F _ _ ≫ (rightAdjointUnitCounit F L adj ⊗ₘ rightAdjointUnitCounit F L adj) ≫
        (λ_ (𝟙_ D)).hom := by
  unfold rightAdjointUnitCounit
  rw [rightAdjointUnit_mul, ← (rigidRightAdjunction F L adj).homEquiv_counit]
  exact Equiv.symm_apply_apply _ _

end Algebra
end Paper18.Category.DiagonalAlgebra
