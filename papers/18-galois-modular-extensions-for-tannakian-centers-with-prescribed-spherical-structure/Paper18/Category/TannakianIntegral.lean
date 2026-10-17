import Paper18.Category.TannakianBasic
import Paper18.Category.RepresentationDimension
import Paper18.Category.FusionSubcategoryIntegral

/-!
# Integrality of the actual Tannakian center

Tensor functor preservation of FP dimensions and the actual finite
representation dimension theorem imply integrality of every transparent
object. The inherited full-center fusion category is therefore integral.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe v u w
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {G : Type} [Group G] [Fintype G] (T : TannakianCenter C G)
include T

/-- The ambient FP dimension of an actual representation in the Tannakian
center is its ordinary vector-space dimension. -/
theorem TannakianCenter.fpdim_inclusion (V : FDRep ℂ G) :
    S.fpdim (T.inclusion.obj V) = (Representation.dimension V : ℝ) := by
  rw [(Representation.skeleton G).fpdim_map S T.inclusion V]
  exact Representation.fpdim_eq_dimension (Representation.skeleton G) V

/-- Every actual transparent object has integral FP dimension. -/
theorem TannakianCenter.transparent_fpdim_integer (X : C)
    (hX : X ∈ mugerCenter (C := C)) : ∃ n : ℤ, S.fpdim X = n := by
  obtain ⟨V, ⟨e⟩⟩ := T.exists_representation X hX
  refine ⟨(Representation.dimension V : ℤ), ?_⟩
  rw [← S.fpdim_iso e, T.fpdim_inclusion S V]
  norm_cast

/-- The inherited actual full fusion category of the Müger center is
integral when the specified center is Tannakian. -/
theorem TannakianCenter.center_integral :
    S.FullSubcategoryIntegral (centralizerProperty (Set.univ : Set C)) := by
  apply (S.fullSubcategoryIntegral_iff _).mpr
  intro i hi
  exact T.transparent_fpdim_integer S _ hi

end Paper18.Category
