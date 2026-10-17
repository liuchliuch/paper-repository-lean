import Paper18.Category.PointedRelativeCenterObstructionTensorCoherenceLaws

/-! # The actual neutral component of the homogeneous quasi relative center

Its tensor operations are restrictions of the actual homogeneous operations.
Its pentagon is proved from the mixed pentagon with neutral degree.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category.PointedRelativeCenterObstruction
open FiniteCohomologyKilling
variable {Γ G : Type} [Group Γ] [Fintype Γ] [Group G]
  (p : Γ →* G) (ψ : ThreeCochain Γ ℂˣ) (ω : FourCocycle G ℂˣ)
  (hψ : ∀ a b c d, dThree ψ.val a b c d = ω.val (p a) (p b) (p c) (p d))

/-- Actual degree-one homogeneous relative-central objects. -/
def neutralDegreeProperty : ObjectProperty (QuasiRelativeCenter p ψ ω hψ) :=
  fun X => HomogeneousRelativeCenter.degree p ψ X = 1
abbrev NeutralComponent := (neutralDegreeProperty p ψ ω hψ).FullSubcategory

namespace NeutralComponent
local notation "Q" => QuasiRelativeCenter p ψ ω hψ
local notation "N" => NeutralComponent p ψ ω hψ

instance tensorStructure : MonoidalCategoryStruct N where
  tensorObj X Y := ⟨X.obj ⊗ Y.obj, by
    change HomogeneousRelativeCenter.degree p ψ X.obj *
      HomogeneousRelativeCenter.degree p ψ Y.obj = 1
    rw [X.property, Y.property, one_mul]⟩
  tensorHom {X₁ Y₁ X₂ Y₂} f g :=
    (show X₁.obj ⟶ Y₁.obj from f) ⊗ₘ (show X₂.obj ⟶ Y₂.obj from g)
  whiskerLeft X Y₁ Y₂ f := X.obj ◁ (show Y₁.obj ⟶ Y₂.obj from f)
  whiskerRight {X₁ X₂} f Y := (show X₁.obj ⟶ X₂.obj from f) ▷ Y.obj
  tensorUnit := ⟨𝟙_ Q, rfl⟩
  associator X Y Z := ObjectProperty.isoMk _ (α_ X.obj Y.obj Z.obj)
  leftUnitor X := ObjectProperty.isoMk _ (λ_ X.obj)
  rightUnitor X := ObjectProperty.isoMk _ (ρ_ X.obj)

/-- All neutral monoidal laws are inherited as actual equations; in
particular the pentagon is a derived mixed-pentagon equation. -/
instance monoidalCategory : MonoidalCategory N where
  tensorHom_def f g := QuasiRelativeCenter.tensorHom_def p ψ ω hψ f g
  id_tensorHom_id X Y := QuasiRelativeCenter.tensor_id p ψ ω hψ X.obj Y.obj
  tensorHom_comp_tensorHom f f' g g' := QuasiRelativeCenter.tensor_comp p ψ ω hψ f g f' g'
  whiskerLeft_id X Y := QuasiRelativeCenter.whiskerLeft_id p ψ ω hψ X.obj Y.obj
  id_whiskerRight X Y := QuasiRelativeCenter.id_whiskerRight p ψ ω hψ X.obj Y.obj
  associator_naturality f g h := QuasiRelativeCenter.associator_naturality p ψ ω hψ f g h
  leftUnitor_naturality f := QuasiRelativeCenter.leftUnitor_naturality p ψ ω hψ f
  rightUnitor_naturality f := QuasiRelativeCenter.rightUnitor_naturality p ψ ω hψ f
  pentagon W X Y Z := QuasiRelativeCenter.mixed_pentagon p ψ ω hψ W.obj X.obj Y.obj Z.obj
    (Or.inl W.property)
  triangle X Y := QuasiRelativeCenter.triangle p ψ ω hψ X.obj Y.obj

end NeutralComponent
end Paper18.Category.PointedRelativeCenterObstruction
