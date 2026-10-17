import Paper18.Category.FusionSubcategoryFunctor
import Paper18.Category.LocalModulesNondegenerateBasic
import Paper18.Category.RelativeTensorRigid
import Paper18.Category.CentralizerFusion

/-! # The actual even centralizer under transparent condensation

Centralization against a free object is detected on the actual underlying
module. A separable module in this centralizer is a retract of a free object
from the ambient centralizer. Lemma 3.1 then gives intrinsic integrality.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj
universe v u w
namespace Paper18.Category.SeparableAlgebra
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [RightRigidCategory C] [HasCoequalizers C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {A : C} [MonObj A] [IsCommMonObj A] (R : SeparableAlgebra A)
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  [RightRigidCategory (Mod_ C A)] [Simple (𝟙_ (Mod_ C A))]

include R S in
/-- The actual centralizer of the image of `e` is integral when its
ambient centralizer is integral. No divisibility premise on module sizes
or identification of its simple objects is assumed. -/
theorem free_centralizer_integral (hA : A ∈ mugerCenter (C := C)) (e : C)
    (hI : S.CentralizerIntegral {e}) :
    letI := moduleBraidedOfTransparent hA
    (R.skeleton S).CentralizerIntegral {InternalModule.free A e} := by
  letI := moduleBraidedOfTransparent hA
  letI := RelativeTensor.freeFunctorBraidedOfTransparent hA
  let P := centralizerProperty ({e} : Set C)
  let Q := centralizerProperty ({InternalModule.free A e} : Set (Mod_ C A))
  letI : ∀ X Y : Q.FullSubcategory, FiniteDimensional ℂ (X ⟶ Y) :=
    fun X Y => inferInstanceAs (FiniteDimensional ℂ (X.obj ⟶ Y.obj))
  letI := S.fullSubcategoryHasKernels P
  letI := S.fullSubcategoryRightRigid P
  letI := S.fullSubcategorySimpleUnit P
  letI := (R.skeleton S).fullSubcategoryHasKernels Q
  letI := (R.skeleton S).fullSubcategoryRightRigid Q
  letI := (R.skeleton S).fullSubcategorySimpleUnit Q
  let hpq : ∀ X : C, P X → Q ((InternalModule.freeFunctor (A := A)).obj X) := by
    intro X hX Y hY
    rcases Set.mem_singleton_iff.mp hY with rfl
    exact (hX e (Set.mem_singleton e)).map (InternalModule.freeFunctor (A := A))
  let F := fullSubcategoryFunctor P Q (InternalModule.freeFunctor (A := A)) hpq
  have hdom : FiniteSemisimpleSkeleton.Dominant F := by
    intro M _
    have hm : Centralizes M.obj.X e :=
      (centralizes_free_iff_of_transparent hA M.obj e).mp
        (M.property (InternalModule.free A e) (Set.mem_singleton _))
    let X : P.FullSubcategory := ⟨M.obj.X, by
      intro Y hY
      rcases Set.mem_singleton_iff.mp hY with rfl
      exact hm⟩
    let r := R.freeRetract M.obj
    exact ⟨X, ⟨⟨r.i, r.r, r.retract⟩⟩⟩
  exact (S.fullSubcategorySkeleton P).lemma3_1_dominant
    ((R.skeleton S).fullSubcategorySkeleton Q) F hdom hI

end Paper18.Category.SeparableAlgebra
