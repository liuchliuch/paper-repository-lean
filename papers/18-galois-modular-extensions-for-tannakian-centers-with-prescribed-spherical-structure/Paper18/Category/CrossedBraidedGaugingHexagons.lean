import Paper18.Category.CrossedBraidedGaugingBraidingNaturality
import Paper18.Category.CrossedBraidedGaugingHexagonBlocks

/-! # The actual assembled gauging hexagons -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.CrossedBraidedGauging
variable {G : Type w} [Group G] [Fintype G]
  {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasKernels C] [HasFiniteBiproducts C]
  {P : Grading G C} {A : WeakAction G C}
  [∀ g : G, (A.ρ g).Monoidal] [A.IsMonoidal]

namespace Grading
variable (P)

/-- Every actual additive functor preserves the complete family of split
degree inclusions. This uses their actual total projector identity. -/
theorem map_component_hom_ext (F : C ⥤ C) [F.Additive]
    {X Z : C} {f h : F.obj X ⟶ Z}
    (hh : ∀ g : G, F.map (P.componentInclusion g X) ≫ f =
      F.map (P.componentInclusion g X) ≫ h) : f = h := by
  have ht : ∑ g : G, F.map (P.componentProjection g X) ≫
      F.map (P.componentInclusion g X) = 𝟙 (F.obj X) := by
    simp only [← F.map_comp, P.componentProjection_inclusion]
    rw [← F.map_sum, P.total, F.map_id]
  calc
    f = (∑ g : G, F.map (P.componentProjection g X) ≫
      F.map (P.componentInclusion g X)) ≫ f := by rw [ht, Category.id_comp]
    _ = (∑ g : G, F.map (P.componentProjection g X) ≫
      F.map (P.componentInclusion g X)) ≫ h := by
        simp only [Preadditive.sum_comp, Category.assoc, hh]
    _ = h := by rw [ht, Category.id_comp]

end Grading

namespace CrossedBraiding
variable {Q : GradedAction P A} (B : CrossedBraiding P A Q)

/-- The genuine tensor hexagon holds for the assembled crossing on every
actual first object. -/
theorem halfSwapIso_tensor_right (X : C) (Y Z : A.Equivariant) :
    (B.halfSwapIso X (Y ⊗ Z)).hom =
      (α_ X Y.obj Z.obj).inv ≫ ((B.halfSwapIso X Y).hom ▷ Z.obj) ≫
        (α_ Y.obj X Z.obj).hom ≫ (Y.obj ◁ (B.halfSwapIso X Z).hom) ≫
          (α_ Y.obj Z.obj X).inv := by
  apply P.tensorRight_hom_ext
  intro g
  rw [B.halfSwapIso_component]
  change (B.blockIso g (P.component g X) (P.component_homogeneous g X) (Y ⊗ Z)).hom ≫
    ((Y.obj ⊗ Z.obj) ◁ P.componentInclusion g X) =
      (P.componentInclusion g X ▷ (Y.obj ⊗ Z.obj)) ≫ _
  rw [associator_inv_naturality_left_assoc]
  rw [← comp_whiskerRight_assoc, B.halfSwapIso_component]
  simp only [comp_whiskerRight, Category.assoc]
  rw [associator_naturality_middle_assoc]
  rw [← whiskerLeft_comp_assoc, B.halfSwapIso_component]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [associator_inv_naturality_right]
  rw [B.blockIso_tensor_right]
  simp only [Category.assoc]

/-- The other actual tensor hexagon follows on both actual degree
decompositions, with no ordinary braiding on the original category. -/
theorem halfSwapIso_tensor_left (X Y : C) (Z : A.Equivariant) :
    (B.halfSwapIso (X ⊗ Y) Z).hom =
      (α_ X Y Z.obj).hom ≫ (X ◁ (B.halfSwapIso Y Z).hom) ≫
        (α_ X Z.obj Y).inv ≫ ((B.halfSwapIso X Z).hom ▷ Y) ≫
          (α_ Z.obj X Y).hom := by
  apply P.map_component_hom_ext
    (((tensoringRight C).obj Y) ⋙ (tensoringRight C).obj Z.obj)
  intro g
  apply P.map_component_hom_ext
    (((tensoringLeft C).obj (P.component g X)) ⋙ (tensoringRight C).obj Z.obj)
  intro h
  change ((P.component g X ◁ P.componentInclusion h Y) ▷ Z.obj) ≫
    ((P.componentInclusion g X ▷ Y) ▷ Z.obj) ≫ _ =
      ((P.component g X ◁ P.componentInclusion h Y) ▷ Z.obj) ≫
        ((P.componentInclusion g X ▷ Y) ▷ Z.obj) ≫ _
  rw [← Category.assoc, ← comp_whiskerRight, ← tensorHom_def',
    B.halfSwapIso_naturality_left]
  rw [B.halfSwapIso_homogeneous (g * h) _
    (P.homogeneous_tensor (P.component_homogeneous g X) (P.component_homogeneous h Y))]
  rw [associator_naturality_left_assoc, associator_naturality_middle_assoc]
  rw [whisker_exchange_assoc]
  rw [← whiskerLeft_comp_assoc, B.halfSwapIso_component]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [← whisker_exchange_assoc (P.componentInclusion g X)
    (B.blockIso h (P.component h Y) (P.component_homogeneous h Y) Z).hom]
  rw [associator_inv_naturality_right_assoc,
    associator_inv_naturality_left_assoc]
  rw [whisker_exchange_assoc (B.halfSwapIso X Z).hom (P.componentInclusion h Y)]
  rw [← comp_whiskerRight_assoc, B.halfSwapIso_component]
  simp only [comp_whiskerRight, Category.assoc]
  rw [associator_naturality_right, associator_naturality_middle_assoc]
  rw [B.blockIso_tensor_left g h (P.component g X) (P.component h Y)
    (P.component_homogeneous g X) (P.component_homogeneous h Y)]
  simp only [Category.assoc, tensorHom_def', whiskerLeft_comp]
  simp only [← whiskerLeft_comp, whisker_exchange]

end CrossedBraiding
end Paper18.Category.CrossedBraidedGauging
