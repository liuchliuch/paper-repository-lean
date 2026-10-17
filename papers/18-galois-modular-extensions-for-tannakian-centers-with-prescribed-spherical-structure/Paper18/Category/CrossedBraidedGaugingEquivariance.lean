import Paper18.Category.CrossedBraidedGaugingHexagons
import Paper18.Category.CrossedBraidedGaugingAction

/-! # Actual equivariance of the assembled crossed braiding -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits Functor.LaxMonoidal Functor.OplaxMonoidal
universe v u w
namespace Paper18.Category.CrossedBraidedGauging.CrossedBraiding
variable {G : Type w} [Group G] [Fintype G]
  {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasKernels C] [HasFiniteBiproducts C]
  {P : Grading G C} {A : WeakAction G C}
  [∀ g : G, (A.ρ g).Monoidal] [A.IsMonoidal]
  [∀ g : G, (A.ρ g).Additive]
  {Q : GradedAction P A} (B : CrossedBraiding P A Q)

/-- Closing actual crossed isomorphisms commutes with every actual weak
translate, proved on the complete translated degree inclusions. -/
@[reassoc] theorem halfSwapIso_action (a : G) (X : C) (Y : A.Equivariant) :
    μ (A.ρ a) X Y.obj ≫ (A.ρ a).map (B.halfSwapIso X Y).hom ≫
        δ (A.ρ a) Y.obj X ≫ ((Y.structureIso a).hom ▷ (A.ρ a).obj X) =
      ((A.ρ a).obj X ◁ (Y.structureIso a).hom) ≫
        (B.halfSwapIso ((A.ρ a).obj X) Y).hom := by
  apply P.map_component_hom_ext ((A.ρ a) ⋙ (tensoringRight C).obj ((A.ρ a).obj Y.obj))
  intro g
  change ((A.ρ a).map (P.componentInclusion g X) ▷ (A.ρ a).obj Y.obj) ≫ _ =
    ((A.ρ a).map (P.componentInclusion g X) ▷ (A.ρ a).obj Y.obj) ≫ _
  rw [μ_natural_left_assoc]
  rw [← (A.ρ a).map_comp_assoc, B.halfSwapIso_component]
  simp only [Functor.map_comp, Category.assoc]
  rw [← δ_natural_right_assoc]
  rw [whisker_exchange]
  rw [B.blockIso_action_assoc a g (P.component g X) (P.component_homogeneous g X)]
  rw [← whisker_exchange_assoc, B.halfSwapIso_naturality_left]
  rw [B.halfSwapIso_homogeneous (a * g * a⁻¹) _
    (Q.homogeneous_map a (P.component_homogeneous g X))]

end Paper18.Category.CrossedBraidedGauging.CrossedBraiding
