import Paper18.Category.PointedRelativeCenterObstructionLinear
import Mathlib.CategoryTheory.InducedCategory

/-! # The actual homogeneous relative-center category -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category.PointedRelativeCenterObstruction
open FiniteCohomologyKilling
variable {Γ G : Type} [Group Γ] [Fintype Γ] [Group G] (p : Γ →* G)
  (ψ : ThreeCochain Γ ℂˣ)

/-- An actual relative-central object with its actual quotient-coset support. -/
structure HomogeneousObject where
  degree : G
  obj : RelativeObject p ψ
  support : Supported p degree obj.1

/-- Actual relative-central morphisms between actual homogeneous objects. -/
def HomogeneousRelativeCenter :=
  InducedCategory (RelativeObject p ψ) (fun X : HomogeneousObject p ψ => X.obj)

namespace HomogeneousRelativeCenter
instance : Category (HomogeneousRelativeCenter p ψ) := inferInstanceAs
  (Category (InducedCategory (RelativeObject p ψ) (fun X : HomogeneousObject p ψ => X.obj)))
instance : Preadditive (HomogeneousRelativeCenter p ψ) := inferInstanceAs
  (Preadditive (InducedCategory (RelativeObject p ψ) (fun X : HomogeneousObject p ψ => X.obj)))
instance : Linear ℂ (HomogeneousRelativeCenter p ψ) := inferInstanceAs
  (Linear ℂ (InducedCategory (RelativeObject p ψ) (fun X : HomogeneousObject p ψ => X.obj)))

def underlying (X : HomogeneousRelativeCenter p ψ) : HomogeneousObject p ψ := X
abbrev degree (X : HomogeneousRelativeCenter p ψ) : G := (underlying p ψ X).degree
abbrev obj (X : HomogeneousRelativeCenter p ψ) : RelativeObject p ψ := (underlying p ψ X).obj

def forget : HomogeneousRelativeCenter p ψ ⥤ RelativeObject p ψ := inducedFunctor _
instance forget_faithful : (forget p ψ).Faithful :=
  (fullyFaithfulInducedFunctor (fun X : HomogeneousObject p ψ => X.obj)).faithful
instance forget_full : (forget p ψ).Full :=
  (fullyFaithfulInducedFunctor (fun X : HomogeneousObject p ψ => X.obj)).full

/-- Distinct actual quotient degrees admit only the actual zero morphism. -/
lemma hom_zero {X Y : HomogeneousRelativeCenter p ψ}
    (h : degree p ψ X ≠ degree p ψ Y) (f : X ⟶ Y) : f = 0 := by
  apply RelativeObject.ext p ψ
  exact hom_zero_of_supported p (underlying p ψ X).support
    (underlying p ψ Y).support h f.f

instance hom_finiteDimensional (X Y : HomogeneousRelativeCenter p ψ) :
    FiniteDimensional ℂ (X ⟶ Y) :=
  inferInstanceAs (FiniteDimensional ℂ ((obj p ψ X) ⟶ (obj p ψ Y)))

end HomogeneousRelativeCenter
end Paper18.Category.PointedRelativeCenterObstruction
