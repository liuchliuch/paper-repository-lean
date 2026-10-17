import Paper18.Category.FusionSubcategoryBasic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # The genuine summand image of an actual additive linear functor

Membership means an actual retract of an actual image object. Finite
sums, actual kernels and an inherited actual finite simple skeleton are
derived; no image semisimplicity or dominance is assumed.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u w v' u'
namespace Paper18.Category.GraphPicard.MoritaImage
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasFiniteBiproducts C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [HasFiniteBiproducts D]
  (F : C ⥤ D) [F.Additive] [F.Linear ℂ]

/-- The actual summand closure of the actual functor image. -/
def property : ObjectProperty D := fun Y => ∃ X : C, Nonempty (Retract Y (F.obj X))

/-- The actual category of actual image summands. -/
abbrev Image := (property F).FullSubcategory

instance property_additive : IsAdditiveFullProperty (property F) where
  of_retract r := by
    rintro ⟨X, ⟨s⟩⟩
    exact ⟨X, ⟨r.trans s⟩⟩
  biproduct f hf := by
    choose X hx using hf
    let r (j) : Retract (f j) (F.obj (X j)) := Classical.choice (hx j)
    let b : Retract (⨁ f) (⨁ fun j => F.obj (X j)) :=
      { i := biproduct.map (fun j => (r j).i)
        r := biproduct.map (fun j => (r j).r)
        retract := by
          apply biproduct.hom_ext
          intro j
          rw [Category.assoc, biproduct.map_π, ← Category.assoc, biproduct.map_π,
            Category.assoc, (r j).retract, Category.comp_id, Category.id_comp] }
    exact ⟨⨁ X, ⟨b.trans (Retract.ofIso (F.mapBiproduct X).symm)⟩⟩

/-- The actual corestriction keeps the original underlying maps. -/
def core : C ⥤ Image F where
  obj X := ⟨F.obj X, X, ⟨Retract.refl _⟩⟩
  map f := F.map f
  map_id X := F.map_id X
  map_comp f g := F.map_comp f g

instance core_additive : (core F).Additive where
  map_add := F.map_add
instance core_linear : (core F).Linear ℂ where
  map_smul f r := F.map_smul r f

/-- Actual image-summand membership is genuine retract dominance of the
actual corestriction. -/
theorem core_dominant (Y : Image F) : ∃ X : C, Nonempty (Retract Y ((core F).obj X)) := by
  obtain ⟨X, ⟨r⟩⟩ := Y.property
  exact ⟨X, ⟨{ i := r.i, r := r.r, retract := r.retract }⟩⟩

variable [HasKernels D] [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  {κ : Type w} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)

/-- The actual finite image-simple classes are ambient actual classes
whose representatives are actual image summands. -/
abbrev SimpleIndex := {i : κ // property F (T.simpleObject i)}

/-- The actual target skeleton restricts to actual image summands. -/
def skeleton : FiniteSemisimpleSkeleton (Image F) (SimpleIndex F T) :=
  T.fullSubcategorySkeleton (property F)

/-- Actual image kernels are the actual ambient kernels, which split. -/
def hasKernels : HasKernels (Image F) := T.fullSubcategoryHasKernels (property F)

instance finiteHom (X Y : Image F) : FiniteDimensional ℂ (X ⟶ Y) :=
  inferInstanceAs (FiniteDimensional ℂ (X.obj ⟶ Y.obj))

end Paper18.Category.GraphPicard.MoritaImage
