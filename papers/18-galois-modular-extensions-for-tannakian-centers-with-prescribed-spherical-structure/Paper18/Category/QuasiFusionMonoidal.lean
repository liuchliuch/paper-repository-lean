import Paper18.Category.QuasiFusionPentagon
import Paper18.Category.QuasiFusionUnit

/-! # Actual twisted graded-vector-space monoidal categories -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
namespace Paper18.Category.QuasiFusion
variable {A : Type} [Fintype A] [AddGroup A]
local instance twistedBaseMonoidal : MonoidalCategory (GradedObject A (FGModuleCat ℂ)) :=
  GradedObject.monoidalCategory

/-- Actual convolution tensor product with the cocycle-scaled actual
associator. Every category axiom, including pentagon, is proved. -/
def scalarMonoidalCategory (r : A → A → A → ℂˣ)
    (hr : ∀ a b c d, r b c d * r a (b + c) d * r a b c =
      r (a + b) c d * r a b (c + d))
    (h₀ : ∀ a c, r a 0 c = 1) : MonoidalCategory (PointedVec A) :=
  { (inferInstance : MonoidalCategory (PointedVec A)) with
    associator := scalarAssociator r
    associator_naturality := scalarAssociator_naturality r
    pentagon := scalarAssociator_pentagon r hr
    triangle := scalarAssociator_triangle r h₀ }

variable {G : Type} [Group G] [Fintype G]

/-- The genuine monoidal category `Vec^ψ[G]` for an actual normalized third cocycle. -/
def twistedMonoidalCategory (ψ : ThreeCocycle G) : MonoidalCategory (PointedVec (Additive G)) :=
  scalarMonoidalCategory (fun a b c => ψ.val a.toMul b.toMul c.toMul)
    (fun a b c d => ψ.pentagon a.toMul b.toMul c.toMul d.toMul)
    (fun a c => ψ.one₂ a.toMul c.toMul)

end Paper18.Category.QuasiFusion
