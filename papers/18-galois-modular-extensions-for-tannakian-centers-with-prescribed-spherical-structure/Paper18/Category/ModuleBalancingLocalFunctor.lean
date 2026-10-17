import Paper18.Category.LocalModulesPivotalTransparent
import Paper18.Category.DrinfeldPivotalBraided
import Paper18.Category.CentralizerFusion

/-! # Actual pivotal preservation by the restricted local free functor -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj
universe v u w
namespace Paper18.Category.ModuleBalancing
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [BraidedCategory C] [HasKernels C] [HasFiniteBiproducts C]
  [HasCoequalizers C] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {A : C} [MonObj A] [IsCommMonObj A]
  [RightRigidCategory (Mod_ C A)] [RightRigidCategory (LocalModules A)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (J : PivotalStructure C) (hA : (J.twistIso A).hom = 𝟙 A)

/-- The actual strong braided local free functor preserves the actual
prescribed centralizer pivotal structure for arbitrary commutative algebras
with trivial twist. Transparency of the algebra is not required. -/
theorem localFree_preservesPivotal :
    letI := S.fullSubcategoryRightRigid (centralizerProperty ({A} : Set C))
    PreservesPivotal (localFreeFunctor (A := A))
      (S.centralizerPivotal ({A} : Set C) J) (localPivotal J hA) := by
  letI := S.fullSubcategoryRightRigid (centralizerProperty ({A} : Set C))
  have hp := S.fullSubcategory_preservesPivotal (centralizerProperty ({A} : Set C)) J
  apply preservesPivotal_of_twist
  intro X
  have hs : ((S.centralizerPivotal ({A} : Set C) J).twistIso X).hom =
      (J.twistIso X.obj).hom := hp.twist X
  change InternalModule.freeMap (C := C) (A := A) ((S.centralizerPivotal ({A} : Set C) J).twistIso X).hom =
    (localPivotal J hA).twistNatIso.hom.app ((localFreeFunctor (A := A)).obj X)
  rw [hs, localPivotal_twist]
  exact (free_twist J hA X.obj ((X.property A (Set.mem_singleton A)).symm)).symm

end Paper18.Category.ModuleBalancing
