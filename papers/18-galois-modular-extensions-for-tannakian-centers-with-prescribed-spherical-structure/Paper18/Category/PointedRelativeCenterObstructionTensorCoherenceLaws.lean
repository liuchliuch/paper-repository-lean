import Paper18.Category.PointedRelativeCenterObstructionTensorCoherence

/-! # Derived tensor laws and exact fourth-cocycle defect

All laws below are equations between actual relative-central arrows.
The global pentagon is replaced by its proved scalar defect equation.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category.PointedRelativeCenterObstruction

/-- The actual homogeneous relative center with its specified cochain and
quotient defect retained in the type. This records the tensor data for
instance selection without asserting a global pentagon. -/
def QuasiRelativeCenter {Γ G : Type} [Group Γ] [Fintype Γ] [Group G]
    (p : Γ →* G) (ψ : FiniteCohomologyKilling.ThreeCochain Γ ℂˣ)
    (ω : FiniteCohomologyKilling.FourCocycle G ℂˣ)
    (_hψ : ∀ a b c d, FiniteCohomologyKilling.dThree ψ.val a b c d =
      ω.val (p a) (p b) (p c) (p d)) := HomogeneousRelativeCenter p ψ

namespace QuasiRelativeCenter
open HomogeneousRelativeCenter
open FiniteCohomologyKilling QuasiFusion
variable {Γ G : Type} [Group Γ] [Fintype Γ] [Group G]
  (p : Γ →* G) (ψ : ThreeCochain Γ ℂˣ) (ω : FourCocycle G ℂˣ)
  (hψ : ∀ a b c d, dThree ψ.val a b c d = ω.val (p a) (p b) (p c) (p d))
local notation "HC" => QuasiRelativeCenter p ψ ω hψ
instance category : Category HC := inferInstanceAs (Category (HomogeneousRelativeCenter p ψ))
instance preadditive : Preadditive HC := inferInstanceAs (Preadditive (HomogeneousRelativeCenter p ψ))
instance linear : Linear ℂ HC := inferInstanceAs (Linear ℂ (HomogeneousRelativeCenter p ψ))
instance tensorStructure : MonoidalCategoryStruct HC :=
  HomogeneousRelativeCenter.monoidalStruct p ψ ω hψ

@[simp] lemma tensorHom_f {X X' Y Y' : HC} (f : X ⟶ X') (g : Y ⟶ Y') :
    (f ⊗ₘ g).f = f.f ⊗ₘ g.f := rfl

@[simp] lemma whiskerLeft_f (X : HC) {Y Y' : HC} (f : Y ⟶ Y') :
    (X ◁ f).f = (obj p ψ X).1 ◁ f.f := id_tensorHom _ _

@[simp] lemma whiskerRight_f {X X' : HC} (f : X ⟶ X') (Y : HC) :
    (f ▷ Y).f = f.f ▷ (obj p ψ Y).1 := tensorHom_id _ _

@[simp] lemma associator_hom_f (X Y Z : HC) :
    (α_ X Y Z).hom.f = (quasiAssociator ψ (obj p ψ X).1 (obj p ψ Y).1 (obj p ψ Z).1).hom := rfl

@[simp] lemma leftUnitor_hom_f (X : HC) :
    (λ_ X).hom.f = (λ_ (obj p ψ X).1).hom := rfl

@[simp] lemma rightUnitor_hom_f (X : HC) :
    (ρ_ X).hom.f = (ρ_ (obj p ψ X).1).hom := rfl

lemma tensorHom_def {X X' Y Y' : HC} (f : X ⟶ X') (g : Y ⟶ Y') :
    f ⊗ₘ g = f ▷ Y ≫ X' ◁ g := by
  apply RelativeObject.ext p ψ
  change f.f ⊗ₘ g.f = (f ▷ Y).f ≫ (X' ◁ g).f
  rw [whiskerLeft_f, whiskerRight_f, MonoidalCategory.tensorHom_def]
  rfl

lemma tensor_id (X Y : HC) : (𝟙 X) ⊗ₘ (𝟙 Y) = 𝟙 (X ⊗ Y) := by
  apply RelativeObject.ext p ψ
  exact MonoidalCategory.id_tensorHom_id _ _

lemma tensor_comp {X X' X'' Y Y' Y'' : HC}
    (f : X ⟶ X') (f' : X' ⟶ X'') (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    (f ⊗ₘ g) ≫ (f' ⊗ₘ g') = (f ≫ f') ⊗ₘ (g ≫ g') := by
  apply RelativeObject.ext p ψ
  exact MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _

lemma associator_naturality {X Y Z X' Y' Z' : HC}
    (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    ((f ⊗ₘ g) ⊗ₘ h) ≫ (α_ X' Y' Z').hom =
      (α_ X Y Z).hom ≫ (f ⊗ₘ (g ⊗ₘ h)) := by
  apply RelativeObject.ext p ψ
  exact quasiAssociator_naturality ψ f.f g.f h.f

lemma leftUnitor_naturality {X Y : HC} (f : X ⟶ Y) :
    (𝟙_ HC) ◁ f ≫ (λ_ Y).hom = (λ_ X).hom ≫ f := by
  apply RelativeObject.ext p ψ
  simpa only [RelativeObject.comp_f, whiskerLeft_f, leftUnitor_hom_f] using
    MonoidalCategory.leftUnitor_naturality f.f

lemma rightUnitor_naturality {X Y : HC} (f : X ⟶ Y) :
    f ▷ (𝟙_ HC) ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f := by
  apply RelativeObject.ext p ψ
  simpa only [RelativeObject.comp_f, whiskerRight_f, rightUnitor_hom_f] using
    MonoidalCategory.rightUnitor_naturality f.f

lemma triangle (X Y : HC) :
    (α_ X (𝟙_ HC) Y).hom ≫ X ◁ (λ_ Y).hom = (ρ_ X).hom ▷ Y := by
  apply RelativeObject.ext p ψ
  simpa only [RelativeObject.comp_f, associator_hom_f, whiskerLeft_f,
    leftUnitor_hom_f, whiskerRight_f, rightUnitor_hom_f] using
    scalarAssociator_triangle
      (fun a b c : Additive Γ => ψ.val a.toMul b.toMul c.toMul)
      (fun a c => ψ.one₂ a.toMul c.toMul) (obj p ψ X).1 (obj p ψ Y).1

lemma whiskerLeft_id (X Y : HC) : X ◁ 𝟙 Y = 𝟙 (X ⊗ Y) := by
  apply RelativeObject.ext p ψ
  change (𝟙 (obj p ψ X).1 ⊗ₘ 𝟙 (obj p ψ Y).1) = 𝟙 _
  exact MonoidalCategory.id_tensorHom_id _ _

lemma id_whiskerRight (X Y : HC) : 𝟙 X ▷ Y = 𝟙 (X ⊗ Y) := by
  apply RelativeObject.ext p ψ
  change (𝟙 (obj p ψ X).1 ⊗ₘ 𝟙 (obj p ψ Y).1) = 𝟙 _
  exact MonoidalCategory.id_tensorHom_id _ _

/-- The actual homogeneous tensor associator has the prescribed fourth-cocycle
pentagon defect on actual relative-central arrows. -/
lemma pentagon_defect (W X Y Z : HC) :
    (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom =
      (ω.val (degree p ψ W) (degree p ψ X) (degree p ψ Y) (degree p ψ Z) : ℂ) •
        ((α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom) := by
  apply RelativeObject.ext p ψ
  simpa only [RelativeObject.comp_f, RelativeObject.smul_f, associator_hom_f,
    whiskerLeft_f, whiskerRight_f] using
    quasiAssociator_pentagon_on_support p ψ ω hψ
      (obj p ψ W).1 (obj p ψ X).1 (obj p ψ Y).1 (obj p ψ Z).1
      W.support X.support Y.support Z.support


/-- Every actual pentagon with one neutral-degree object commutes. -/
lemma mixed_pentagon (W X Y Z : HC)
    (hn : degree p ψ W = 1 ∨ degree p ψ X = 1 ∨
      degree p ψ Y = 1 ∨ degree p ψ Z = 1) :
    MonoidalCategory.Pentagon W X Y Z := by
  apply RelativeObject.ext p ψ
  simpa only [RelativeObject.comp_f, associator_hom_f, whiskerLeft_f,
    whiskerRight_f] using
    quasiAssociator_mixed_pentagon p ψ ω hψ
      (obj p ψ W).1 (obj p ψ X).1 (obj p ψ Y).1 (obj p ψ Z).1
      W.support X.support Y.support Z.support hn

end QuasiRelativeCenter
end Paper18.Category.PointedRelativeCenterObstruction
