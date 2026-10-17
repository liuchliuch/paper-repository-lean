import Paper18.Category.PointedRelativeCenterObstructionNeutral
import Paper18.Category.PointedLinear

/-! # Linearity of the actual neutral cochain tensor product -/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace Paper18.Category.PointedRelativeCenterObstruction
open FiniteCohomologyKilling
variable {Γ G : Type} [Group Γ] [Fintype Γ] [Group G]
  (p : Γ →* G) (ψ : ThreeCochain Γ ℂˣ) (ω : FourCocycle G ℂˣ)
  (hψ : ∀ a b c d, dThree ψ.val a b c d = ω.val (p a) (p b) (p c) (p d))
namespace NeutralTwistedVec
instance monoidalPreadditive : MonoidalPreadditive (NeutralTwistedVec p ψ ω hψ) where
  whiskerLeft_zero {X Y Z} := by
    change X.obj ◁ (0 : Y.obj ⟶ Z.obj) = 0
    exact MonoidalPreadditive.whiskerLeft_zero
  zero_whiskerRight {X Y Z} := by
    change (0 : Y.obj ⟶ Z.obj) ▷ X.obj = 0
    exact MonoidalPreadditive.zero_whiskerRight
  whiskerLeft_add {X Y Z} f g := by
    let f' : Y.obj ⟶ Z.obj := f
    let g' : Y.obj ⟶ Z.obj := g
    change X.obj ◁ (f' + g') = X.obj ◁ f' + X.obj ◁ g'
    exact MonoidalPreadditive.whiskerLeft_add f' g' 
  add_whiskerRight {X Y Z} f g := by
    let f' : Y.obj ⟶ Z.obj := f
    let g' : Y.obj ⟶ Z.obj := g
    change (f' + g') ▷ X.obj = f' ▷ X.obj + g' ▷ X.obj
    exact MonoidalPreadditive.add_whiskerRight f' g' 
instance monoidalLinear : MonoidalLinear ℂ (NeutralTwistedVec p ψ ω hψ) where
  whiskerLeft_smul X {Y Z} c f := by
    let f' : Y.obj ⟶ Z.obj := f
    change X.obj ◁ (c • f') = c • (X.obj ◁ f')
    exact MonoidalLinear.whiskerLeft_smul X.obj c f' 
  smul_whiskerRight c {Y Z} f X := by
    let f' : Y.obj ⟶ Z.obj := f
    change (c • f') ▷ X.obj = c • (f' ▷ X.obj)
    exact MonoidalLinear.smul_whiskerRight c f' X.obj
end NeutralTwistedVec
end Paper18.Category.PointedRelativeCenterObstruction
