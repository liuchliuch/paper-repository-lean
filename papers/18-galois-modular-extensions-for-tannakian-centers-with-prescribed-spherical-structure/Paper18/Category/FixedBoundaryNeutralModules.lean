import Paper18.Category.SignKernelBasic
import Paper18.Category.FixedBoundaryModuleImage
import Paper18.Category.FixedBoundaryModuleGrading
import Paper18.Category.FixedBoundaryModuleMonoidal
import Paper18.Category.FixedBoundarySemisimpleExact
import Paper18.Category.FusionSubcategoryFunctor

/-!
# The actual neutral module category is the boundary module category

When the boundary tensor image is the actual centralizer of the grading
object, actual separable modules in that image are exactly the actual
neutral modules. The resulting functor is an actual fully faithful,
essentially surjective strong tensor functor.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj Obj
universe v u w v' u'
namespace Paper18.Category.FixedBoundary
variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℂ A]
  [MonoidalCategory A] [BraidedCategory A] [MonoidalPreadditive A] [MonoidalLinear ℂ A]
  [HasKernels A]
  {N : Type u'} [Category.{v'} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N] [MonoidalPreadditive N] [MonoidalLinear ℂ N]
  [RightRigidCategory N] [HasCoequalizers N]
  (i : A ⥤ N) [i.Braided] [i.Full] [i.Faithful] [i.Additive] [i.Linear ℂ]
  (R : A) [MonObj R] [IsCommMonObj R]
  {T : N} (B : TensorInverse T)
  (himage : ∀ X : A, Centralizes T (i.obj X))

/-- The actual descended monodromy character defining the neutral modules. -/
abbrev neutralModuleCharacter : 𝟭 (Mod_ N (i.obj R)) ≅ 𝟭 (Mod_ N (i.obj R)) :=
  B.moduleMonodromyCharacter (i.obj R) (himage R)

/-- Actual module transport lifts to the actual neutral full subcategory. -/
def neutralModuleLift : Mod_ A R ⥤ SignKernel.Positive (neutralModuleCharacter i R B himage) :=
  ObjectProperty.lift _ (InternalModule.mapModules i) (fun M =>
    (B.moduleMonodromy_neutral_iff (i.obj R) (himage R) _).mpr (himage M.X))

instance neutralModuleLift_faithful : (neutralModuleLift i R B himage).Faithful := by
  dsimp only [neutralModuleLift]
  infer_instance

instance neutralModuleLift_full : (neutralModuleLift i R B himage).Full := by
  dsimp only [neutralModuleLift]
  infer_instance

variable (S : SeparableAlgebra R)
  (hfull : ∀ Y : N, Centralizes T Y → ∃ X : A, Nonempty (i.obj X ≅ Y))

include S hfull in
/-- The actual underlying centralizer equality supplies actual essential
surjectivity on modules, through separable free retracts. -/
def neutralModuleLift_essSurj : (neutralModuleLift i R B himage).EssSurj where
  mem_essImage M := by
    have hc : Centralizes T M.obj.X :=
      (B.moduleMonodromy_neutral_iff (i.obj R) (himage R) M.obj).mp M.property
    obtain ⟨X, ⟨e⟩⟩ := InternalModule.mapModules_essImage_of_underlying i S M.obj
      (hfull M.obj.X hc)
    exact ⟨X, ⟨ObjectProperty.isoMk _ e⟩⟩

/-- An actual equivalence between the boundary module category and the
actual neutral component of the de-equivariantized extension. -/
def neutralModuleEquivalence : Mod_ A R ≌ SignKernel.Positive (neutralModuleCharacter i R B himage) := by
  letI := neutralModuleLift_essSurj i R B himage S hfull
  letI : (neutralModuleLift i R B himage).IsEquivalence := {}
  exact (neutralModuleLift i R B himage).asEquivalence

section Monoidal
variable [HasFiniteBiproducts A] [RightRigidCategory A] [HasCoequalizers A]
  [∀ X Y : A, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (SA : FiniteSemisimpleSkeleton A ι)

/-- The actual neutral equivalence has the actual relative-tensor
tensorators. Preservation of ambient coequalizers is derived from SA. -/
def neutralModuleLiftMonoidal : (neutralModuleLift i R B himage).Monoidal := by
  letI : PreservesColimitsOfShape WalkingParallelPair i := SA.preservesCoequalizers i
  change (fullSubcategoryLift (SignKernel.positiveProperty (neutralModuleCharacter i R B himage))
    (InternalModule.mapModules i) _).Monoidal
  infer_instance

end Monoidal
end Paper18.Category.FixedBoundary
