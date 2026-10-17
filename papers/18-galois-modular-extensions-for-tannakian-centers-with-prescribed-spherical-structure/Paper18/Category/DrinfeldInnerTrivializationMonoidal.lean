import Paper18.Category.DrinfeldInnerTrivializationLift
import Paper18.Category.InvertibleFunctor

/-! # Actual monoidality from a tensor-conjugation intertwiner -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.Monoidal
universe v u
namespace Paper18.Category.DrinfeldInner
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Right tensoring by an actual invertible object is an actual equivalence. -/
def tensorRightEquivalence {L : C} (E : TensorInverse L) : C ≌ C :=
  CategoryTheory.Equivalence.mk (tensorRight L) (tensorRight E.inverse)
    ((rightUnitorNatIso C).symm ≪≫ (tensoringRight C).mapIso E.right.symm ≪≫
      tensorRightTensor L E.inverse)
    ((tensorRightTensor E.inverse L).symm ≪≫ (tensoringRight C).mapIso E.left ≪≫
      rightUnitorNatIso C)

lemma conjugating_tensor_slide {L X Y P Q : C}
    (p : P ⟶ X) (q : Q ⟶ Y) (g : L ⊗ X ⟶ P ⊗ L) (h : L ⊗ Y ⟶ Q ⊗ L) :
    ((α_ L X Y).inv ≫ g ▷ Y ≫ (α_ P L Y).hom ≫
      P ◁ h ≫ (α_ P Q L).inv) ≫ (p ⊗ₘ q) ▷ L =
    (α_ L X Y).inv ≫ (g ≫ p ▷ L) ▷ Y ≫ (α_ X L Y).hom ≫
      X ◁ (h ≫ q ▷ L) ≫ (α_ X Y L).inv := by
  have ha : (α_ P Q L).inv ≫ (p ⊗ₘ q) ▷ L =
      (p ⊗ₘ q ▷ L) ≫ (α_ X Y L).inv := by
    simpa only [MonoidalCategory.tensorHom_id] using
      (MonoidalCategory.associator_inv_naturality p q (𝟙 L)).symm
  simp only [Category.assoc]
  rw [ha, MonoidalCategory.tensorHom_def p (q ▷ L)]
  simp only [Category.assoc]
  rw [whisker_exchange_assoc p h, ← associator_naturality_left_assoc p L Y]
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]

variable (F : C ⥤ C) [F.Monoidal] [F.IsEquivalence] (L : C)
  (γ : tensorLeft L ≅ F ⋙ tensorRight L)

/-- The actual tensor comparison of the conjugation intertwiner before
the tensorator of `F` is applied. -/
def conjugatingTensorIso (X Y : C) : L ⊗ (X ⊗ Y) ≅ (F.obj X ⊗ F.obj Y) ⊗ L :=
  (α_ L X Y).symm ≪≫ whiskerRightIso (γ.app X) Y ≪≫ α_ (F.obj X) L Y ≪≫
    whiskerLeftIso (F.obj X) (γ.app Y) ≪≫ (α_ (F.obj X) (F.obj Y) L).symm

variable (σ : DrinfeldEquivalence.map F ⋙ Center.forget C ≅ Center.forget C)

/-- Actual intertwining with the half-braiding and actual coherence of γ
derive the tensor equation for the underlying trivialization. -/
lemma monoidal_tensor_of_intertwining (E : TensorInverse L)
    (hγ : ∀ X Y, γ.hom.app (X ⊗ Y) =
      (conjugatingTensorIso F L γ X Y).hom ≫ μ F X Y ▷ L)
    (hσ : ∀ Z : Center C, γ.hom.app Z.1 ≫ σ.hom.app Z ▷ L = (Z.2.β L).inv)
    (Z W : Center C) :
    μ F Z.1 W.1 ≫ σ.hom.app (Z ⊗ W) = σ.hom.app Z ⊗ₘ σ.hom.app W := by
  letI : (tensorRight L).IsEquivalence := (tensorRightEquivalence E).isEquivalence_functor
  apply (tensorRight L).map_injective
  change (μ F Z.1 W.1 ≫ σ.hom.app (Z ⊗ W)) ▷ L =
    (σ.hom.app Z ⊗ₘ σ.hom.app W) ▷ L
  apply (cancel_epi (conjugatingTensorIso F L γ Z.1 W.1).hom).mp
  rw [comp_whiskerRight]
  calc
    _ = γ.hom.app (Z.1 ⊗ W.1) ≫ σ.hom.app (Z ⊗ W) ▷ L := by
      rw [← Category.assoc, ← hγ]
    _ = ((Z ⊗ W).2.β L).inv := hσ (Z ⊗ W)
    _ = _ := by
      have ht := conjugating_tensor_slide (σ.hom.app Z) (σ.hom.app W)
        (γ.hom.app Z.1) (γ.hom.app W.1)
      rw [hσ Z, hσ W] at ht
      change (conjugatingTensorIso F L γ Z.1 W.1).hom ≫
          (σ.hom.app Z ⊗ₘ σ.hom.app W) ▷ L =
        (α_ L Z.1 W.1).inv ≫ (Z.2.β L).inv ▷ W.1 ≫ (α_ Z.1 L W.1).hom ≫
          Z.1 ◁ (W.2.β L).inv ≫ (α_ Z.1 W.1 L).inv at ht
      rw [ht]
      simp only [Center.tensor_β, Iso.trans_inv, Iso.symm_inv,
        whiskerLeftIso_inv, whiskerRightIso_inv, Category.assoc]

lemma monoidal_unit_of_intertwining (E : TensorInverse L)
    (hγ : γ.hom.app (𝟙_ C) =
      (ρ_ L).hom ≫ (λ_ L).inv ≫ ε F ▷ L)
    (hσ : ∀ Z : Center C, γ.hom.app Z.1 ≫ σ.hom.app Z ▷ L = (Z.2.β L).inv) :
    ε F ≫ σ.hom.app (𝟙_ (Center C)) = 𝟙 (𝟙_ C) := by
  letI : (tensorRight L).IsEquivalence := (tensorRightEquivalence E).isEquivalence_functor
  have hs := hσ (𝟙_ (Center C))
  change γ.hom.app (𝟙_ C) ≫ σ.hom.app (𝟙_ (Center C)) ▷ L =
    (ρ_ L).hom ≫ (λ_ L).inv at hs
  rw [hγ, Category.assoc, Category.assoc, ← comp_whiskerRight] at hs
  have ht : (ε F ≫ σ.hom.app (𝟙_ (Center C))) ▷ L = 𝟙 ((𝟙_ C) ⊗ L) := by
    apply (cancel_epi ((ρ_ L).hom ≫ (λ_ L).inv)).mp
    simpa only [Category.assoc, comp_id] using hs
  apply (tensorRight L).map_injective
  change (ε F ≫ σ.hom.app (𝟙_ (Center C))) ▷ L = (𝟙 (𝟙_ C)) ▷ L
  simpa only [id_whiskerRight] using ht

/-- Both monoidal laws of the actual underlying trivialization follow
from the actual tensor-line intertwiner and its proved coherence. -/
def monoidalOfIntertwining (E : TensorInverse L)
    (hγunit : γ.hom.app (𝟙_ C) =
      (ρ_ L).hom ≫ (λ_ L).inv ≫ ε F ▷ L)
    (hγtensor : ∀ X Y, γ.hom.app (X ⊗ Y) =
      (conjugatingTensorIso F L γ X Y).hom ≫ μ F X Y ▷ L)
    (hσ : ∀ Z : Center C, γ.hom.app Z.1 ≫ σ.hom.app Z ▷ L = (Z.2.β L).inv) :
    NatTrans.IsMonoidal σ.hom where
  unit := by
    simp only [Functor.LaxMonoidal.comp_ε, Center.forget_ε]
    change (𝟙 _ ≫ ε F) ≫ σ.hom.app (𝟙_ (Center C)) = 𝟙 _
    simpa only [id_comp] using monoidal_unit_of_intertwining F L γ σ E hγunit hσ
  tensor Z W := by
    simp only [Functor.LaxMonoidal.comp_μ, Center.forget_μ]
    change (𝟙 _ ≫ μ F Z.1 W.1) ≫ σ.hom.app (Z ⊗ W) =
      (σ.hom.app Z ⊗ₘ σ.hom.app W) ≫ 𝟙 _
    simpa only [id_comp, comp_id] using
      monoidal_tensor_of_intertwining F L γ σ E hγtensor hσ Z W

end Paper18.Category.DrinfeldInner
