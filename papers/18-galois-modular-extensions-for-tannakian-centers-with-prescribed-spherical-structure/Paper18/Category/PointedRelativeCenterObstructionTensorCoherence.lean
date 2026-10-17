import Paper18.Category.PointedRelativeCenterObstructionTensorCoherenceUnit
import Paper18.Category.PointedRelativeCenterObstructionGrading

/-! # The actual tensor structure on the homogeneous relative center

The specified associator is an actual relative-central isomorphism. Its
pentagon defect will be recorded explicitly rather than replaced by a
monoidal-category instance on the whole quasi extension.
-/
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category.PointedRelativeCenterObstruction
open FiniteCohomologyKilling QuasiFusion
variable {Γ G : Type} [Group Γ] [Fintype Γ] [Group G]
  (p : Γ →* G) (ψ : ThreeCochain Γ ℂˣ)
local notation "Vec" => PointedVec (Additive Γ)

namespace RelativeObject
/-- An actual ambient isomorphism intertwining all neutral crossings lifts
with its actual inverse to an isomorphism of relative-central objects. -/
def isoMk {X Y : RelativeObject p ψ} (e : X.1 ≅ Y.1)
    (he : ∀ U (hU : Supported p 1 U),
      e.hom ▷ U ≫ (Y.2.β U hU).hom = (X.2.β U hU).hom ≫ U ◁ e.hom) : X ≅ Y where
  hom := ⟨e.hom, he⟩
  inv := ⟨e.inv, by
    intro U hU
    have hh := congrArg (fun k => e.inv ▷ U ≫ k ≫ U ◁ e.inv) (he U hU)
    simpa only [assoc, ← comp_whiskerRight_assoc, Iso.inv_hom_id,
      id_whiskerRight, id_comp, ← whiskerLeft_comp, Iso.hom_inv_id,
      whiskerLeft_id, comp_id] using hh.symm⟩
  hom_inv_id := ext p ψ _ _ e.hom_inv_id
  inv_hom_id := ext p ψ _ _ e.inv_hom_id
end RelativeObject

variable (ω : FourCocycle G ℂˣ)
  (hψ : ∀ a b c d, dThree ψ.val a b c d = ω.val (p a) (p b) (p c) (p d))

namespace HomogeneousRelativeCenter
local notation "HC" => HomogeneousRelativeCenter p ψ

/-- Tensor product with the actual constructed relative half-braiding and
actual product quotient support. -/
def tensorObj (X Y : HC) : HC :=
  { degree := degree p ψ X * degree p ψ Y
    obj := ⟨(obj p ψ X).1 ⊗ (obj p ψ Y).1,
      tensorRelativeHalfBraiding p ψ ω hψ X.support Y.support
        (obj p ψ X).2 (obj p ψ Y).2⟩
    support := supported_tensor p X.support Y.support }

/-- The underlying morphism is the actual ambient tensor product. -/
def tensorHom {X X' Y Y' : HC} (f : X ⟶ X') (g : Y ⟶ Y') :
    tensorObj p ψ ω hψ X Y ⟶ tensorObj p ψ ω hψ X' Y' :=
  ⟨f.f ⊗ₘ g.f, fun U hU => tensorRelativeIso_map p ψ
    (obj p ψ X).2 (obj p ψ X').2 (obj p ψ Y).2 (obj p ψ Y').2
      f.f g.f U hU (f.comm U hU) (g.comm U hU)⟩

/-- The actual relative-central tensor unit. -/
def tensorUnit : HC :=
  { degree := 1
    obj := ⟨𝟙_ Vec, unitRelativeHalfBraiding p ψ ω hψ⟩
    support := supported_unit p }

/-- The actual quasi-associator lifts by its proved intertwining equation. -/
def associator (X Y Z : HC) :
    tensorObj p ψ ω hψ (tensorObj p ψ ω hψ X Y) Z ≅
      tensorObj p ψ ω hψ X (tensorObj p ψ ω hψ Y Z) :=
  InducedCategory.isoMk (RelativeObject.isoMk p ψ
    (X := obj p ψ (tensorObj p ψ ω hψ (tensorObj p ψ ω hψ X Y) Z))
    (Y := obj p ψ (tensorObj p ψ ω hψ X (tensorObj p ψ ω hψ Y Z)))
    (quasiAssociator ψ (obj p ψ X).1 (obj p ψ Y).1 (obj p ψ Z).1)
    (tensorRelativeIso_associator p ψ ω hψ X.support Y.support Z.support
      (obj p ψ X).2 (obj p ψ Y).2 (obj p ψ Z).2))

/-- Both unitors are actual relative-central isomorphisms. -/
def leftUnitor (X : HC) : tensorObj p ψ ω hψ (tensorUnit p ψ ω hψ) X ≅ X :=
  InducedCategory.isoMk (RelativeObject.isoMk p ψ
    (X := obj p ψ (tensorObj p ψ ω hψ (tensorUnit p ψ ω hψ) X))
    (Y := obj p ψ X) (λ_ (obj p ψ X).1)
    (tensorRelativeIso_leftUnitor p ψ ω hψ (obj p ψ X).2))

def rightUnitor (X : HC) : tensorObj p ψ ω hψ X (tensorUnit p ψ ω hψ) ≅ X :=
  InducedCategory.isoMk (RelativeObject.isoMk p ψ
    (X := obj p ψ (tensorObj p ψ ω hψ X (tensorUnit p ψ ω hψ)))
    (Y := obj p ψ X) (ρ_ (obj p ψ X).1)
    (tensorRelativeIso_rightUnitor p ψ ω hψ (obj p ψ X).2))

/-- Actual tensor/associator/unit data; no global pentagon is asserted. -/
def monoidalStruct : MonoidalCategoryStruct HC where
  tensorObj := tensorObj p ψ ω hψ
  tensorHom := tensorHom p ψ ω hψ
  whiskerLeft X _ _ f := tensorHom p ψ ω hψ (𝟙 X) f
  whiskerRight f Y := tensorHom p ψ ω hψ f (𝟙 Y)
  tensorUnit := tensorUnit p ψ ω hψ
  associator := associator p ψ ω hψ
  leftUnitor := leftUnitor p ψ ω hψ
  rightUnitor := rightUnitor p ψ ω hψ

end HomogeneousRelativeCenter
end Paper18.Category.PointedRelativeCenterObstruction
