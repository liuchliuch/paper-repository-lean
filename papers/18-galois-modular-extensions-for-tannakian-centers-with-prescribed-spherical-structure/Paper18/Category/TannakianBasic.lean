import Paper18.Category.Braided
import Paper18.Category.RepresentationBasic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Equivalence

/-!
# Tannakian identification of the actual Müger center

A Tannakian identification is a complex-linear fully faithful braided tensor
functor from the actual category of finite-dimensional complex representations,
whose essential image is exactly the actual Müger center. The equivalence to
the full center subcategory is derived below from these data. No spherical
positivity is included in this definition.
-/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The actual full category of transparent objects. -/
abbrev MugerCenterCategory :=
  ObjectProperty.FullSubcategory (fun X : C => X ∈ mugerCenter (C := C))

variable [Preadditive C] [Linear ℂ C]
variable (G : Type) [Group G]

/-- An actual braided tensor identification of `Rep(G)` with the Müger center.
The essential image condition is an objectwise characterization of
transparency, rather than a numerical rule on simple labels. -/
structure TannakianCenter where
  finite_group : Finite G
  inclusion : FDRep ℂ G ⥤ C
  braided : inclusion.Braided
  additive : inclusion.Additive
  linear : inclusion.Linear ℂ
  full : inclusion.Full
  faithful : inclusion.Faithful
  image_iff : ∀ X : C, inclusion.essImage X ↔ X ∈ mugerCenter (C := C)

namespace TannakianCenter
attribute [instance] braided additive linear full faithful
variable {C G} (T : TannakianCenter C G)

/-- Every representation in a Tannakian center is transparent as an actual
object of the ambient braided category. -/
lemma transparent (V : FDRep ℂ G) : T.inclusion.obj V ∈ mugerCenter (C := C) :=
  (T.image_iff _).mp (T.inclusion.obj_mem_essImage V)

lemma centralizes (V : FDRep ℂ G) (X : C) : Centralizes (T.inclusion.obj V) X :=
  T.transparent V X (Set.mem_univ X)

/-- The representation functor lifted to the full category of transparent
objects. -/
def toCenter : FDRep ℂ G ⥤ MugerCenterCategory C :=
  ObjectProperty.lift _ T.inclusion T.transparent

instance : T.toCenter.Full := by dsimp [toCenter]; infer_instance
instance : T.toCenter.Faithful := by dsimp [toCenter]; infer_instance

instance : T.toCenter.EssSurj where
  mem_essImage X := by
    obtain ⟨V, ⟨e⟩⟩ := (T.image_iff X.obj).mpr X.property
    exact ⟨V, ⟨ObjectProperty.isoMk _ e⟩⟩

instance : T.toCenter.IsEquivalence where

/-- The ordinary category equivalence underlying the specified braided
Tannakian identification. -/
def equivalence : FDRep ℂ G ≌ MugerCenterCategory C := T.toCenter.asEquivalence

@[simp] lemma equivalence_functor_obj (V : FDRep ℂ G) :
    (T.equivalence.functor.obj V).obj = T.inclusion.obj V := rfl

/-- Every transparent ambient object is isomorphic to an actual finite
representation under the specified inclusion. -/
lemma exists_representation (X : C) (hX : X ∈ mugerCenter (C := C)) :
    ∃ V : FDRep ℂ G, Nonempty (T.inclusion.obj V ≅ X) :=
  (T.image_iff X).mpr hX

end TannakianCenter
end Paper18.Category
