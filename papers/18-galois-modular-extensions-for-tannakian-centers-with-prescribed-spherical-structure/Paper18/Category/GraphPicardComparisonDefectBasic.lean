import Paper18.Category.PivotalBalancingTensor
import Paper18.Category.RigidDoubleDual

/-! # Double-dual correction of an actual monodromy tensor defect

This auxiliary calculation concerns arbitrary genuine tensor functors. The
concrete graph cap will supply its tensor and unit equations separately.
No rigid structure on the target category is needed.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal
universe v u v' u'
namespace Paper18.Category.GraphPicard
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C]
  {E : Type u'} [Category.{v'} E] [MonoidalCategory E]
  {F G : C ⥤ E} [F.Monoidal] [G.Monoidal]

/-- The actual Drinfeld comparison corrects the target of an ordinary
natural transformation to the canonical double-dual tensor functor. -/
def drinfeldCorrectedNatTrans (σ : G ⟶ F) : G ⟶ doubleDualFunctor C ⋙ F where
  app X := σ.app X ≫ F.map (drinfeldIso X).hom
  naturality {X Y} f := by
    dsimp only [Functor.comp_map]
    rw [← assoc, σ.naturality, assoc, ← F.map_comp, drinfeldIso_naturality,
      F.map_comp, assoc]

/-- The actual monodromy defect is exactly canceled by the actual
Drinfeld tensor comparison, without requiring duals on the target. -/
lemma drinfeldCorrectedNatTrans_tensor (σ : G ⟶ F) (X Y : C)
    (h : μ G X Y ≫ σ.app (X ⊗ Y) =
      (σ.app X ⊗ₘ σ.app Y) ≫ μ F X Y ≫ F.map (doubleBraiding X Y).hom) :
    μ G X Y ≫ (drinfeldCorrectedNatTrans σ).app (X ⊗ Y) =
      ((drinfeldCorrectedNatTrans σ).app X ⊗ₘ
        (drinfeldCorrectedNatTrans σ).app Y) ≫ μ (doubleDualFunctor C ⋙ F) X Y := by
  dsimp only [drinfeldCorrectedNatTrans]
  rw [← assoc, h]
  simp only [assoc, ← F.map_comp]
  rw [drinfeldIso_tensor, F.map_comp]
  rw [← μ_natural_assoc]
  simp only [Functor.LaxMonoidal.comp_μ, canonicalDoubleDual_tensor,
    ← tensorHom_comp_tensorHom_assoc]

/-- The canonical unit of double dualization gives the corrected unit law. -/
lemma drinfeldCorrectedNatTrans_unit (σ : G ⟶ F)
    (h : ε G ≫ σ.app (𝟙_ C) = ε F) :
    ε G ≫ (drinfeldCorrectedNatTrans σ).app (𝟙_ C) = ε (doubleDualFunctor C ⋙ F) := by
  dsimp only [drinfeldCorrectedNatTrans]
  rw [← assoc, h, drinfeldIso_unit]
  simp only [Functor.LaxMonoidal.comp_ε, canonicalDoubleDual_unit]

/-- Genuine unit and monodromy-defect equations imply genuine monoidality
of the corrected transformation. This is only the generic correction lemma;
the graph specialization must prove both original equations. -/
def drinfeldCorrectedNatTransMonoidal (σ : G ⟶ F)
    (hu : ε G ≫ σ.app (𝟙_ C) = ε F)
    (ht : ∀ X Y : C, μ G X Y ≫ σ.app (X ⊗ Y) =
      (σ.app X ⊗ₘ σ.app Y) ≫ μ F X Y ≫ F.map (doubleBraiding X Y).hom) :
    NatTrans.IsMonoidal (drinfeldCorrectedNatTrans σ) where
  unit := drinfeldCorrectedNatTrans_unit σ hu
  tensor X Y := drinfeldCorrectedNatTrans_tensor σ X Y (ht X Y)

end Paper18.Category.GraphPicard
