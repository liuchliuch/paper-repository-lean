import Paper18.Category.PointedRelativeCenterObstructionPentagon
import Mathlib.CategoryTheory.Monoidal.Subcategory

/-! # The genuine neutral monoidal category inside the quasi extension -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category.PointedRelativeCenterObstruction
open FiniteCohomologyKilling QuasiFusion
variable {Γ G : Type} [Group Γ] [Fintype Γ] [Group G] (p : Γ →* G)
local notation "V" => PointedVec (Additive Γ)

def neutralSupport : ObjectProperty V := Supported p 1
instance neutralSupport_monoidal : (neutralSupport p).IsMonoidal where
  prop_unit := supported_unit p
  prop_tensor X Y hX hY := by simpa only [one_mul] using supported_tensor p hX hY

/-- The actual full subcategory of vectors supported on the actual kernel. -/
abbrev NeutralVec := (neutralSupport p).FullSubcategory

/-- The actual scaled associator is a morphism between actual neutral objects. -/
def neutralAssociator (ψ : ThreeCochain Γ ℂˣ) (X Y Z : NeutralVec p) :
    (X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z) :=
  ObjectProperty.isoMk _ (quasiAssociator ψ X.obj Y.obj Z.obj)

/-- The neutral component is genuinely monoidal: its full pentagon is
one of the actual mixed pentagons, rather than an additional assumption. -/
def neutralMonoidalCategory (ψ : ThreeCochain Γ ℂˣ) (ω : FourCocycle G ℂˣ)
    (hψ : ∀ a b c d, dThree ψ.val a b c d = ω.val (p a) (p b) (p c) (p d)) :
    MonoidalCategory (NeutralVec p) :=
  { (inferInstance : MonoidalCategory (NeutralVec p)) with
    associator := neutralAssociator p ψ
    associator_naturality := by
      intro X Y Z X' Y' Z' f g h
      exact scalarAssociator_naturality
        (fun a b c : Additive Γ => ψ.val a.toMul b.toMul c.toMul) f g h
    pentagon := by
      intro W X Y Z
      exact quasiAssociator_mixed_pentagon p ψ ω hψ W.obj X.obj Y.obj Z.obj
        W.property X.property Y.property Z.property (Or.inl rfl)
    triangle := by
      intro X Y
      exact scalarAssociator_triangle
        (fun a b c : Additive Γ => ψ.val a.toMul b.toMul c.toMul)
        (fun a c => ψ.one₂ a.toMul c.toMul) X.obj Y.obj }

/-- The type wrapper records the actual primitive and its proved
coboundary equation so its actual neutral associator is unambiguous. -/
def NeutralTwistedVec (ψ : ThreeCochain Γ ℂˣ) (ω : FourCocycle G ℂˣ)
    (_hψ : ∀ a b c d, dThree ψ.val a b c d = ω.val (p a) (p b) (p c) (p d)) :=
  NeutralVec p

namespace NeutralTwistedVec
variable (ψ : ThreeCochain Γ ℂˣ) (ω : FourCocycle G ℂˣ)
  (hψ : ∀ a b c d, dThree ψ.val a b c d = ω.val (p a) (p b) (p c) (p d))
instance : Category (NeutralTwistedVec p ψ ω hψ) :=
  inferInstanceAs (Category (NeutralVec p))
instance : Preadditive (NeutralTwistedVec p ψ ω hψ) :=
  inferInstanceAs (Preadditive (NeutralVec p))
instance : Linear ℂ (NeutralTwistedVec p ψ ω hψ) :=
  inferInstanceAs (Linear ℂ (NeutralVec p))
instance : MonoidalCategory (NeutralTwistedVec p ψ ω hψ) :=
  neutralMonoidalCategory p ψ ω hψ
end NeutralTwistedVec

end Paper18.Category.PointedRelativeCenterObstruction
