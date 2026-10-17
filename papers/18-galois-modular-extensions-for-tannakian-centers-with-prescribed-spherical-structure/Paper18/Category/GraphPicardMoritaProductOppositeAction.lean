import Paper18.Category.GraphPicardMoritaProductExternal
import Paper18.Category.BimoduleRelativeTensorModuleInverse

/-! # Actual ambient-module coherence of the left/right conversion

The actual braiding hexagon identifies the two actual right algebra
actions after adding an ambient tensor factor. The resulting actual
identity-underlying isomorphisms give genuine strong module lineators.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalLeftAction MonoidalOpposite
open scoped MonObj
universe v u
namespace Paper18.Category.GraphPicard.MoritaProduct
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  (B : Mon D)
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

/-- The genuine hexagon identifies the two transported right actions. -/
theorem leftToRight_residual_action (X : Dᴹᵒᵖ) (N : LeftModules B) :
    letI := (oppositeAlgebra B).mon
    letI := rightModulesResidualAction (oppositeAlgebra B)
    (γ[mop (oppositeAlgebra B).X,(X ⊙ₗ (leftToRight B).obj N).X]).unmop =
      (γ[mop (oppositeAlgebra B).X,((leftToRight B).obj (X ⊙ₗ N)).X]).unmop := by
  letI := (oppositeAlgebra B).mon
  letI := rightModulesResidualAction (oppositeAlgebra B)
  rw [rightModulesResidualAction_action]
  rw [leftToRight_action, leftToRight_action]
  change (α_ N.X X.unmop B.X).hom ≫ N.X ◁ (β_ X.unmop B.X).hom ≫
      (α_ N.X B.X X.unmop).inv ≫ ((β_ N.X B.X).hom ≫ γ[B.X,N.X]) ▷ X.unmop =
    (β_ (N.X ⊗ X.unmop) B.X).hom ≫
      ((α_ B.X N.X X.unmop).inv ≫ γ[B.X,N.X] ▷ X.unmop)
  rw [BraidedCategory.braiding_tensor_left_hom]
  simp only [comp_whiskerRight, Category.assoc, Iso.hom_inv_id_assoc]

/-- Adding an ambient factor commutes with the actual left/right
conversion through an actual identity-underlying module isomorphism. -/
def leftToRightResidualComponent (X : Dᴹᵒᵖ) (N : LeftModules B) :
    letI := (oppositeAlgebra B).mon
    letI := rightModulesResidualAction (oppositeAlgebra B)
    X ⊙ₗ (leftToRight B).obj N ≅ (leftToRight B).obj (X ⊙ₗ N) := by
  letI := (oppositeAlgebra B).mon
  letI := rightModulesResidualAction (oppositeAlgebra B)
  refine
    { hom := Mod_.Hom.mk' (𝟙 _) ?_
      inv := Mod_.Hom.mk' (𝟙 _) ?_
      hom_inv_id := by apply Mod_.Hom.ext; exact Category.id_comp _
      inv_hom_id := by apply Mod_.Hom.ext; exact Category.id_comp _ }
  · apply Quiver.Hom.unmop_inj
    change _ ≫ 𝟙 _ = (𝟙 _) ▷ B.X ≫ _
    simpa only [Category.comp_id, id_whiskerRight, Category.id_comp] using
      leftToRight_residual_action B X N
  · apply Quiver.Hom.unmop_inj
    change _ ≫ 𝟙 _ = (𝟙 _) ▷ B.X ≫ _
    simpa only [Category.comp_id, id_whiskerRight, Category.id_comp] using
      (leftToRight_residual_action B X N).symm

/-- The actual comparison maps obey genuine native module coherence. -/
def leftToRightResidualLaxLeftLinear :
    letI := (oppositeAlgebra B).mon
    letI := rightModulesResidualAction (oppositeAlgebra B)
    (leftToRight B).LaxLeftLinear Dᴹᵒᵖ := by
  letI := (oppositeAlgebra B).mon
  letI := rightModulesResidualAction (oppositeAlgebra B)
  exact
    { μₗ X N := (leftToRightResidualComponent B X N).hom
      μₗ_naturality_left := by
        intro X Y f N
        apply Mod_.Hom.ext
        apply Quiver.Hom.unmop_inj
        change (N.X ◁ f.unmop) ≫ 𝟙 _ = 𝟙 _ ≫ (N.X ◁ f.unmop)
        simp only [Category.comp_id, Category.id_comp]
      μₗ_naturality_right := by
        intro X N N' f
        apply Mod_.Hom.ext
        apply Quiver.Hom.unmop_inj
        change f.hom ▷ X.unmop ≫ 𝟙 _ = 𝟙 _ ≫ f.hom ▷ X.unmop
        simp only [Category.comp_id, Category.id_comp]
      μₗ_associativity := by
        intro X Y N
        apply Mod_.Hom.ext
        change 𝟙 _ ≫ ((leftToRight B).map (αₗ X Y N).hom).hom =
          ((αₗ X Y ((leftToRight B).obj N)).hom).hom ≫
            (X ◁ 𝟙 _) ≫ 𝟙 _
        rw [negativeLiftedAction_associator_hom]
        apply Quiver.Hom.unmop_inj
        change 𝟙 _ ≫ (α_ N.X Y.unmop X.unmop).inv =
          (α_ N.X Y.unmop X.unmop).inv ≫ (𝟙 _ ▷ X.unmop) ≫ 𝟙 _
        simp only [Category.id_comp, id_whiskerRight, Category.comp_id]
      μₗ_unitality := by
        intro N
        apply Mod_.Hom.ext
        change ((λₗ[Dᴹᵒᵖ] ((leftToRight B).obj N)).hom).hom =
          𝟙 _ ≫ ((leftToRight B).map (λₗ[Dᴹᵒᵖ] N).hom).hom
        rw [negativeLiftedAction_unit_hom]
        apply Quiver.Hom.unmop_inj
        change (ρ_ N.X).hom = 𝟙 _ ≫ (ρ_ N.X).hom
        exact (Category.id_comp _).symm }

def leftToRightResidualLeftLinear :
    letI := (oppositeAlgebra B).mon
    letI := rightModulesResidualAction (oppositeAlgebra B)
    (leftToRight B).LeftLinear Dᴹᵒᵖ := by
  letI := (oppositeAlgebra B).mon
  letI := rightModulesResidualAction (oppositeAlgebra B)
  letI := leftToRightResidualLaxLeftLinear B
  letI (X : Dᴹᵒᵖ) (N : LeftModules B) :
      IsIso (Functor.LaxLeftLinear.μₗ (leftToRight B) X N) :=
    (leftToRightResidualComponent B X N).isIso_hom
  exact ModuleFunctor.leftLinearOfLax (C := Dᴹᵒᵖ) (leftToRight B)

variable [CategoryTheory.Limits.HasKernels D] (S : SeparableAlgebra B.X)

def leftRightEquivalence_functorLeftLinear :
    letI := (oppositeAlgebra B).mon
    letI := rightModulesResidualAction (oppositeAlgebra B)
    (leftRightEquivalence B S).functor.LeftLinear Dᴹᵒᵖ :=
  leftToRightResidualLeftLinear B

/-- The actual inverse of the actual left/right equivalence inherits a
genuine strong ambient module lineator. -/
def leftRightEquivalence_inverseLeftLinear :
    letI := (oppositeAlgebra B).mon
    letI := rightModulesResidualAction (oppositeAlgebra B)
    (leftRightEquivalence B S).inverse.LeftLinear Dᴹᵒᵖ := by
  letI := (oppositeAlgebra B).mon
  letI := rightModulesResidualAction (oppositeAlgebra B)
  letI := leftRightEquivalence_functorLeftLinear B S
  exact BimoduleRelativeTensor.ModuleInverse.inverseLeftLinear (C := Dᴹᵒᵖ) (leftRightEquivalence B S)

/-- Actual unit module naturality is derived by the actual inverse
module-functor construction. -/
def leftRightEquivalence_unit_moduleNatural :
    letI := (oppositeAlgebra B).mon
    letI := rightModulesResidualAction (oppositeAlgebra B)
    letI := leftRightEquivalence_functorLeftLinear B S
    letI := leftRightEquivalence_inverseLeftLinear B S
    ModuleFunctor.IsModuleNatural Dᴹᵒᵖ (leftRightEquivalence B S).unitIso.hom := by
  letI := (oppositeAlgebra B).mon
  letI := rightModulesResidualAction (oppositeAlgebra B)
  letI := leftRightEquivalence_functorLeftLinear B S
  letI := leftRightEquivalence_inverseLeftLinear B S
  exact BimoduleRelativeTensor.ModuleInverse.unit_moduleNatural (C := Dᴹᵒᵖ) (leftRightEquivalence B S)

def leftRightEquivalence_counit_moduleNatural :
    letI := (oppositeAlgebra B).mon
    letI := rightModulesResidualAction (oppositeAlgebra B)
    letI := leftRightEquivalence_functorLeftLinear B S
    letI := leftRightEquivalence_inverseLeftLinear B S
    ModuleFunctor.IsModuleNatural Dᴹᵒᵖ (leftRightEquivalence B S).counitIso.hom := by
  letI := (oppositeAlgebra B).mon
  letI := rightModulesResidualAction (oppositeAlgebra B)
  letI := leftRightEquivalence_functorLeftLinear B S
  letI := leftRightEquivalence_inverseLeftLinear B S
  exact BimoduleRelativeTensor.ModuleInverse.counit_moduleNatural (C := Dᴹᵒᵖ) (leftRightEquivalence B S)

end Paper18.Category.GraphPicard.MoritaProduct
