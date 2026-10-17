import Paper18.Category.BimoduleRelativeTensorProduct
import Mathlib.CategoryTheory.Limits.Shapes.SplitCoequalizer

/-! # The actual split balancing coequalizer from middle separability -/
noncomputable section
set_option maxHeartbeats 1000000
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u
namespace Paper18.Category.BimoduleRelativeTensor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  {R S T : D} [MonObj R] [MonObj S] [MonObj T]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
variable (Sep : SeparableAlgebra S) (M : Native R S) (N : Native S T)

/-- The actual separable module section inserts the middle algebra. -/
def balancingSection : M.X.X ⊗ N.X.X ⟶ (M.X.X ⊗ S) ⊗ N.X.X :=
  M.X.X ◁ Sep.moduleSection N.X ≫ (α_ M.X.X S N.X.X).inv

/-- The actual averaging projector for the balancing relation. -/
def projector : M.X.X ⊗ N.X.X ⟶ M.X.X ⊗ N.X.X :=
  balancingSection Sep M N ≫ γ[mop S,M.X].hom ▷ N.X.X

lemma balancingSection_right :
    balancingSection Sep M N ≫
      ((α_ M.X.X S N.X.X).hom ≫ M.X.X ◁ γ[S,N.X.X]) = 𝟙 _ := by
  dsimp only [balancingSection]
  rw [assoc, Iso.inv_hom_id_assoc, ← whiskerLeft_comp, Sep.moduleSection_action,
    whiskerLeft_id]

/-- Actual linearity of the separable section and actual right-module
associativity prove that the averaging map is balanced. -/
lemma projector_balanced :
    γ[mop S,M.X].hom ▷ N.X.X ≫ projector Sep M N =
      (α_ M.X.X S N.X.X).hom ≫ M.X.X ◁ γ[S,N.X.X] ≫ projector Sep M N := by
  have hs : γ[S,N.X.X] ≫ Sep.moduleSection N.X =
      S ◁ Sep.moduleSection N.X ≫ (α_ S S N.X.X).inv ≫ μ[S] ▷ N.X.X := by
    simpa only [InternalModule.free_smul, assoc] using
      (Sep.moduleSectionHom N.X).isMod_Hom.smul_hom
  have hp : γ[mop S,M.X].hom ▷ S ≫ γ[mop S,M.X].hom =
      (α_ M.X.X S S).hom ≫ M.X.X ◁ μ[S] ≫ γ[mop S,M.X].hom := by
    have hh := (toBimodObj R S M).right_assoc
    apply (cancel_epi (α_ M.X.X S S).inv).mp
    simpa only [assoc, Iso.inv_hom_id_assoc] using hh.symm
  dsimp only [projector, balancingSection]
  simp only [assoc]
  rw [← whisker_exchange_assoc, associator_inv_naturality_left_assoc,
    ← comp_whiskerRight, hp]
  rw [← whiskerLeft_comp_assoc, hs]
  monoidal

variable [HasCoequalizers D] [LeftRigidCategory D] [RightRigidCategory D]

lemma projector_π : projector Sep M N ≫ π M N = π M N := by
  dsimp only [projector, balancingSection]
  simp only [assoc]
  rw [condition, Iso.inv_hom_id_assoc, ← whiskerLeft_comp_assoc,
    Sep.moduleSection_action, whiskerLeft_id, id_comp]

/-- The actual averaging projector descends to a section of the actual
balancing quotient. -/
def quotientSection : (tensor M N).X.X ⟶ M.X.X ⊗ N.X.X :=
  desc M N (projector Sep M N) (projector_balanced Sep M N)

@[reassoc (attr := simp)]
lemma π_section : π M N ≫ quotientSection Sep M N = projector Sep M N := π_desc _ _ _ _

@[reassoc (attr := simp)]
lemma section_π : quotientSection Sep M N ≫ π M N = 𝟙 _ := by
  apply (cancel_epi (π M N)).mp
  rw [π_section_assoc, projector_π, comp_id]

/-- The middle algebra's actual bimodule splitting constructs all the
maps of an actual split coequalizer, so this balancing quotient is absolute. -/
def splitCoequalizer : IsSplitCoequalizer
    (γ[mop S,M.X].hom ▷ N.X.X)
    ((α_ M.X.X S N.X.X).hom ≫ M.X.X ◁ γ[S,N.X.X]) (π M N) where
  rightSection := quotientSection Sep M N
  leftSection := balancingSection Sep M N
  condition := by simpa only [assoc] using condition M N
  rightSection_π := section_π Sep M N
  leftSection_bottom := balancingSection_right Sep M N
  leftSection_top := (π_section Sep M N).symm

end Paper18.Category.BimoduleRelativeTensor
