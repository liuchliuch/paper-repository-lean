import Paper18.Category.GraphPicardMoritaImageMonoidal
import Paper18.Category.DrinfeldLinear

/-! # Restricting a genuine central lift to its actual tensor image

Each actual half-braiding is restricted to actual image summands. The
original center tensorators supply the strong structure, and all coherence
is reflected by the actual full inclusion. No image braiding is assumed.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u v' u'
namespace Paper18.Category.GraphPicard.MoritaImage
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasFiniteBiproducts C] [MonoidalCategory C]
  {E : Type u'} [Category.{v'} E] [Preadditive E] [Linear ℂ E]
  [HasFiniteBiproducts E] [MonoidalCategory E]
  [MonoidalPreadditive E] [MonoidalLinear ℂ E]
  (K : C ⥤ Center E) [K.Monoidal] [K.Additive] [K.Linear ℂ]
local notation "U" => K ⋙ Center.forget E

/-- The actual central image object, with the actual half-braiding tested
only on actual objects of its actual tensor image. -/
def centralCoreObj (X : C) : Center (Image U) :=
  ⟨(core U).obj X,
    { β Y := (property U).isoMk ((K.obj X).2.β Y.obj)
      monoidal Y Z := (K.obj X).2.monoidal Y.obj Z.obj
      naturality f := (K.obj X).2.naturality f }⟩

/-- Actual central maps restrict to actual central image maps. -/
def centralCoreMap {X Y : C} (f : X ⟶ Y) : centralCoreObj K X ⟶ centralCoreObj K Y where
  f := (K.map f).f
  comm Z := (K.map f).comm Z.obj

/-- The actual central lift into the center of the actual tensor image. -/
def centralCore : C ⥤ Center (Image U) where
  obj := centralCoreObj K
  map f := centralCoreMap K f
  map_id X := by apply Center.ext; exact congrArg ((Center.forget E).map) (K.map_id X)
  map_comp f g := by apply Center.ext; exact congrArg ((Center.forget E).map) (K.map_comp f g)

@[simp] theorem centralCore_forget :
    centralCore K ⋙ Center.forget (Image U) = core U := rfl

/-- The actual central unit comparison is the original actual comparison. -/
def centralCoreUnitIso : 𝟙_ (Center (Image U)) ≅ (centralCore K).obj (𝟙_ C) := by
  let e : 𝟙_ (Image U) ≅ (core U).obj (𝟙_ C) :=
    (property U).isoMk ((Center.forget E).mapIso (Functor.Monoidal.εIso K))
  exact Center.isoMk { f := e.hom, comm Y := (Functor.Monoidal.εIso K).hom.comm Y.obj }

/-- The original actual central tensorator restricts to actual image
objects with its original central commutation equation. -/
def centralCoreTensorIso (X Y : C) :
    (centralCore K).obj X ⊗ (centralCore K).obj Y ≅ (centralCore K).obj (X ⊗ Y) := by
  let e : ((core U).obj X ⊗ (core U).obj Y) ≅ (core U).obj (X ⊗ Y) :=
    (property U).isoMk ((Center.forget E).mapIso (Functor.Monoidal.μIso K X Y))
  exact Center.isoMk { f := e.hom, comm Z := (Functor.Monoidal.μIso K X Y).hom.comm Z.obj }

instance centralCore_monoidal : (centralCore K).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := centralCoreUnitIso K
      μIso := centralCoreTensorIso K
      μIso_hom_natural_left f Y := by
        apply Center.ext
        exact congrArg ((Center.forget E).map) (Functor.LaxMonoidal.μ_natural_left K f Y)
      μIso_hom_natural_right X f := by
        apply Center.ext
        exact congrArg ((Center.forget E).map) (Functor.LaxMonoidal.μ_natural_right K X f)
      associativity X Y Z := by
        apply Center.ext
        exact congrArg ((Center.forget E).map) (Functor.LaxMonoidal.associativity K X Y Z)
      left_unitality X := by
        apply Center.ext
        exact congrArg ((Center.forget E).map) (Functor.LaxMonoidal.left_unitality K X)
      right_unitality X := by
        apply Center.ext
        exact congrArg ((Center.forget E).map) (Functor.LaxMonoidal.right_unitality K X) }

instance centralCore_additive : (centralCore K).Additive where
  map_add {X Y} f g := by
    apply Center.ext
    exact congrArg ((Center.forget E).map) (K.map_add (f := f) (g := g))

instance centralCore_linear : (centralCore K).Linear ℂ where
  map_smul f r := by
    apply Center.ext
    exact congrArg ((Center.forget E).map) (K.map_smul r f)

end Paper18.Category.GraphPicard.MoritaImage

namespace Paper18.Category.GraphPicard.MoritaImage
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasFiniteBiproducts C] [MonoidalCategory C] [BraidedCategory C]
  {E : Type u'} [Category.{v'} E] [Preadditive E] [Linear ℂ E]
  [HasFiniteBiproducts E] [MonoidalCategory E]
  [MonoidalPreadditive E] [MonoidalLinear ℂ E]
  (K : C ⥤ Center E) [K.Braided] [K.Additive] [K.Linear ℂ]

instance centralCore_braided : (centralCore K).Braided where
  braided X Y := by
    apply Center.ext
    exact congrArg ((Center.forget E).map) (Functor.Braided.braided (F := K) X Y)

end Paper18.Category.GraphPicard.MoritaImage
