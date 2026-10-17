import Paper18.Category.RigidDoubleDual
import Paper18.Category.SphericalizationFunctor

/-! # Tensor-cap coherence of arbitrary strong monoidal functors -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Functor
open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
universe v u v' u'
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [RightRigidCategory D]
  (F : C ⥤ D) [F.Monoidal]

/-- The actual image of a nested tensor cap is the nested pair of image caps. -/
lemma map_tensorEval (X Y Xd Yd : C) (ex : Xd ⊗ X ⟶ 𝟙_ C) (ey : Yd ⊗ Y ⟶ 𝟙_ C) :
    (μ F Yd Xd ⊗ₘ μ F X Y) ≫ μ F (Yd ⊗ Xd) (X ⊗ Y) ≫
      F.map (tensorEval X Y Xd Yd ex ey) ≫ η F =
    tensorEval (F.obj X) (F.obj Y) (F.obj Xd) (F.obj Yd)
      (μ F Xd X ≫ F.map ex ≫ η F) (μ F Yd Y ≫ F.map ey ≫ η F) := by
  dsimp only [tensorEval]
  simp only [Functor.map_comp, Functor.Monoidal.map_associator,
    Functor.Monoidal.map_associator_inv, Functor.Monoidal.map_whiskerLeft,
    Functor.Monoidal.map_whiskerRight, Functor.Monoidal.map_leftUnitor, assoc]
  simp only [μ_δ_assoc, μ_δ, comp_id, MonoidalCategory.whiskerLeft_comp, comp_whiskerRight, assoc]
  rw [tensorHom_def']
  simp only [assoc, ← comp_whiskerRight_assoc, μ_δ, id_whiskerRight, id_comp]
  rw [associator_naturality_right_assoc]
  simp only [μ_δ_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, μ_δ,
    MonoidalCategory.whiskerLeft_id, id_comp]


end Paper18.Category
