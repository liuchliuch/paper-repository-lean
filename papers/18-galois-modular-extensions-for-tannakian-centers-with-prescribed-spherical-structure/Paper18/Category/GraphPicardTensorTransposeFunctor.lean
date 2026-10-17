import Paper18.Category.GraphPicardTensorTranspose
import Paper18.Category.RigidDoubleDual

/-! # Actual tensor transport of specified image pairings -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
universe v u v' u'
namespace Paper18.Category.GraphPicard
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {E : Type u'} [Category.{v'} E] [MonoidalCategory E]
  (F : C ⥤ E) [F.Monoidal]

/-- Strong tensor functors carry the actual nested cap to the nested
pair of actual image caps. Neither category needs a rigid structure here. -/
lemma map_nestedCap {X Xd Y Yd : C}
    (ex : Xd ⊗ X ⟶ 𝟙_ C) (ey : Yd ⊗ Y ⟶ 𝟙_ C) :
    (μ F Yd Xd ⊗ₘ μ F X Y) ≫ μ F (Yd ⊗ Xd) (X ⊗ Y) ≫
        F.map (nestedCap ex ey) ≫ η F =
      nestedCap (μ F Xd X ≫ F.map ex ≫ η F)
        (μ F Yd Y ≫ F.map ey ≫ η F) := by
  dsimp only [nestedCap]
  simp only [Functor.map_comp, Functor.Monoidal.map_associator,
    Functor.Monoidal.map_associator_inv, Functor.Monoidal.map_whiskerLeft,
    Functor.Monoidal.map_whiskerRight, Functor.Monoidal.map_leftUnitor, assoc]
  simp only [μ_δ_assoc, μ_δ, comp_id, MonoidalCategory.whiskerLeft_comp,
    comp_whiskerRight, assoc]
  rw [MonoidalCategory.tensorHom_def']
  simp only [assoc, ← comp_whiskerRight_assoc, μ_δ, id_whiskerRight, id_comp]
  rw [associator_naturality_right_assoc]
  simp only [μ_δ_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, μ_δ,
    MonoidalCategory.whiskerLeft_id, id_comp]

variable [RightRigidCategory C]
attribute [local instance 2000] RightRigidCategory.rightDual

/-- The canonical source dual-tensor comparison identifies the actual
chosen image evaluation with the nested image evaluation. No chosen
dual or pivotal structure on the target is used. -/
lemma mapped_tensor_evaluation (X Y : C) :
    (F.map (dualTensorIso X Y).hom ≫ δ F (dual C Y) (dual C X)) ▷
        (F.obj X ⊗ F.obj Y) ≫
      nestedCap (μ F (dual C X) X ≫ F.map (ε_ X (dual C X)) ≫ η F)
        (μ F (dual C Y) Y ≫ F.map (ε_ Y (dual C Y)) ≫ η F) =
    F.obj (dual C (X ⊗ Y)) ◁ μ F X Y ≫
      μ F (dual C (X ⊗ Y)) (X ⊗ Y) ≫
        F.map (ε_ (X ⊗ Y) (dual C (X ⊗ Y))) ≫ η F := by
  rw [← map_nestedCap]
  simp only [MonoidalCategory.tensorHom_def, comp_whiskerRight, assoc]
  rw [← comp_whiskerRight_assoc (δ F (dual C Y) (dual C X))
    (μ F (dual C Y) (dual C X)) (F.obj X ⊗ F.obj Y),
    δ_μ, id_whiskerRight, Category.id_comp]
  rw [← whisker_exchange_assoc, μ_natural_left_assoc]
  simp only [← F.map_comp_assoc]
  have hs : (dualTensorIso X Y).hom ▷ (X ⊗ Y) ≫
      nestedCap (ε_ X (dual C X)) (ε_ Y (dual C Y)) =
        ε_ (X ⊗ Y) (dual C (X ⊗ Y)) := dualTensorIso_evaluation X Y
  rw [hs]

/-- The source's actual dual-unit comparison normalizes the actual image
evaluation on the original strong tensor unit map. -/
lemma mapped_unit_evaluation :
    F.obj (dual C (𝟙_ C)) ◁ ε F ≫
      μ F (dual C (𝟙_ C)) (𝟙_ C) ≫
        F.map (ε_ (𝟙_ C) (dual C (𝟙_ C))) ≫ η F =
      (ρ_ (F.obj (dual C (𝟙_ C)))).hom ≫
        F.map (dualUnitIso (C := C)).hom ≫ η F := by
  rw [← dualUnitIso_evaluation, Functor.map_comp, Category.assoc,
    ← μ_natural_left_assoc, whisker_exchange_assoc,
    ← Functor.LaxMonoidal.right_unitality_assoc,
    rightUnitor_naturality_assoc]

end Paper18.Category.GraphPicard
