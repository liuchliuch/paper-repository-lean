import Paper18.Category.PointedRelativeCenterObstructionNeutral
import Paper18.Category.PointedRelativeCenterObstructionLinear
import Mathlib.CategoryTheory.Monoidal.Center
import Mathlib.CategoryTheory.Equivalence

/-! # The actual neutral relative center and the ordinary neutral center -/
noncomputable section
set_option maxHeartbeats 2000000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category.PointedRelativeCenterObstruction
open FiniteCohomologyKilling
variable {Γ G : Type} [Group Γ] [Fintype Γ] [Group G] (p : Γ →* G)
  (ψ : ThreeCochain Γ ℂˣ)

def neutralRelativeProperty : ObjectProperty (RelativeObject p ψ) :=
  fun X => Supported p 1 X.1
abbrev NeutralRelativeObject := (neutralRelativeProperty p ψ).FullSubcategory

variable (ω : FourCocycle G ℂˣ)
  (hψ : ∀ a b c d, dThree ψ.val a b c d = ω.val (p a) (p b) (p c) (p d))

/-- A neutral relative half-braiding is an actual center half-braiding
on the actual neutral monoidal category. -/
def neutralRelativeToCenter : NeutralRelativeObject p ψ ⥤ Center (NeutralTwistedVec p ψ ω hψ) where
  obj X := ⟨⟨X.obj.1, X.property⟩, {
    β U := ObjectProperty.isoMk _ (X.obj.2.β U.obj U.property)
    monoidal U V := X.obj.2.monoidal U.obj V.obj U.property V.property
    naturality f := X.obj.2.naturality _ _ f }⟩
  map f := ⟨f.f, fun U => f.comm U.obj U.property⟩
  map_id X := by apply Center.Hom.ext; rfl
  map_comp f g := by apply Center.Hom.ext; rfl

instance neutralRelativeToCenter_faithful : (neutralRelativeToCenter p ψ ω hψ).Faithful where
  map_injective {X Y} f g h := by
    apply RelativeObject.ext p ψ
    exact congrArg Center.Hom.f h

instance neutralRelativeToCenter_full : (neutralRelativeToCenter p ψ ω hψ).Full where
  map_surjective f := ⟨⟨f.f, fun U hU => f.comm ⟨U,hU⟩⟩, by apply Center.Hom.ext; rfl⟩

/-- Every actual center object of the neutral category is an actual
relative-central ambient object with neutral support. -/
def neutralRelativeFromCenter (Z : Center (NeutralTwistedVec p ψ ω hψ)) : NeutralRelativeObject p ψ :=
  ⟨⟨Z.1.obj, {
    β U hU := (neutralSupport p).ι.mapIso (Z.2.β ⟨U,hU⟩)
    monoidal U V hU hV := Z.2.monoidal ⟨U,hU⟩ ⟨V,hV⟩
    naturality hU hV f := Z.2.naturality (show (⟨_,hU⟩ : NeutralTwistedVec p ψ ω hψ) ⟶ ⟨_,hV⟩ from f) }⟩,
    Z.1.property⟩

/-- The realization changes only the packaging of the actual same fibers
and the actual same half-braiding maps. -/
def neutralRelativeRealizationIso (Z : Center (NeutralTwistedVec p ψ ω hψ)) :
    (neutralRelativeToCenter p ψ ω hψ).obj (neutralRelativeFromCenter p ψ ω hψ Z) ≅ Z :=
  Center.isoMk ⟨𝟙 Z.1, fun U => by
    change (𝟙 Z.1) ▷ U ≫ (Z.2.β U).hom = (Z.2.β U).hom ≫ U ◁ (𝟙 Z.1)
    simp only [id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.comp_id]⟩

instance neutralRelativeToCenter_essSurj : (neutralRelativeToCenter p ψ ω hψ).EssSurj where
  mem_essImage Z := ⟨neutralRelativeFromCenter p ψ ω hψ Z,
    ⟨neutralRelativeRealizationIso p ψ ω hψ Z⟩⟩
instance neutralRelativeToCenter_isEquivalence :
    (neutralRelativeToCenter p ψ ω hψ).IsEquivalence := {}

/-- The genuine neutral relative-center category is actually equivalent
to the actual center of the genuine neutral graded category. -/
def neutralRelativeCenterEquivalence : NeutralRelativeObject p ψ ≌ Center (NeutralTwistedVec p ψ ω hψ) :=
  (neutralRelativeToCenter p ψ ω hψ).asEquivalence

end Paper18.Category.PointedRelativeCenterObstruction
