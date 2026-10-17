import Paper18.Category.TannakianBasic
import Paper18.Category.FusionSubcategoryFunctor

/-!
# The actual braided monoidal Müger-center subcategory

Tensor closure follows from the proved braiding hexagon calculation, so the
full category of transparent objects inherits the actual ambient tensor and
braiding. The Tannakian identification lifts as a braided strong monoidal
functor to this actual full subcategory.
-/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Transparency as an object property, for mathlib's full-subcategory
monoidal construction. -/
def transparentObjects : ObjectProperty C := fun X => X ∈ mugerCenter (C := C)

instance transparentObjectsMonoidal : (transparentObjects (C := C)).IsMonoidal where
  prop_unit := unit_mem_centralizer Set.univ
  prop_tensor _ _ hX hY := tensor_mem_centralizer hX hY

/-- The Müger-center category has the natural tensor product inherited from
actual ambient objects. -/
instance mugerCenterCategoryMonoidal : MonoidalCategory (MugerCenterCategory C) :=
  ObjectProperty.fullMonoidalSubcategory (transparentObjects (C := C))

instance mugerCenterCategoryBraided : BraidedCategory (MugerCenterCategory C) :=
  ObjectProperty.fullBraidedSubcategory (transparentObjects (C := C))

/-- The Müger-center braiding is symmetric, as a consequence of its defining
monodromy equation. -/
instance mugerCenterCategorySymmetric : SymmetricCategory (MugerCenterCategory C) where
  symmetry X Y := X.property Y.obj (Set.mem_univ Y.obj)

variable [Preadditive C] [Linear ℂ C]
variable {G : Type} [Group G] (T : TannakianCenter C G)

instance TannakianCenter.toCenterBraided : T.toCenter.Braided := by
  exact fullSubcategoryLift_braided (transparentObjects (C := C))
    T.inclusion T.transparent

end Paper18.Category
