import Paper18.Category.FixedBoundaryNeutralModules
import Paper18.Category.LocalModulesCenterLinear

/-!
# Actual central crossings of the neutral de-equivariant component

The actual boundary-image description of the neutral modules and the
actual transparent boundary algebra prove that each neutral module is
local. Thus the constructed local-module center functor gives an actual
central lift of the entire neutral component, with the original underlying
module object and all naturality and half-braiding coherence laws.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj Obj
universe v u v' u'
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
  (S : SeparableAlgebra R)
  (hfull : ∀ Y : N, Centralizes T Y → ∃ X : A, Nonempty (i.obj X ≅ Y))
  (hR : R ∈ mugerCenter (C := A))

include hR in
/-- Boundary modules map to actual local modules, because the boundary
algebra is actually transparent on every boundary underlying object. -/
theorem boundaryModule_local (M : Mod_ A R) :
    IsLocalModule ((InternalModule.mapModules i).obj M) := by
  rw [isLocalModule_iff]
  have hc : Centralizes (i.obj R) (i.obj M.X) := (hR M.X (Set.mem_univ _)).map i
  change (doubleBraiding (i.obj R) (i.obj M.X)).hom ≫ _ = _
  rw [hc, Category.id_comp]

include S hfull hR in
/-- Every actual neutral module is local. The proof uses the actual
module-image equivalence rather than a locality-classification premise. -/
theorem neutralModule_local
    (M : SignKernel.Positive (neutralModuleCharacter i R B himage)) : IsLocalModule M.obj := by
  have hc : Centralizes T M.obj.X :=
    (B.moduleMonodromy_neutral_iff (i.obj R) (himage R) M.obj).mp M.property
  obtain ⟨X, ⟨e⟩⟩ := InternalModule.mapModules_essImage_of_underlying i S M.obj
    (hfull M.obj.X hc)
  exact IsLocalModule.of_mono e.inv (boundaryModule_local i R hR X)

/-- The actual neutral category maps into actual local modules by the
identity on underlying modules and on all actual morphisms. -/
def neutralToLocal : SignKernel.Positive (neutralModuleCharacter i R B himage) ⥤
    LocalModules (i.obj R) :=
  ObjectProperty.lift _ (SignKernel.inclusion (neutralModuleCharacter i R B himage))
    (neutralModule_local i R B himage S hfull hR)

instance neutralToLocalFaithful : (neutralToLocal i R B himage S hfull hR).Faithful := by
  change (fullSubcategoryLift (localModuleProperty (A := i.obj R))
    (SignKernel.inclusion (neutralModuleCharacter i R B himage)) _).Faithful
  infer_instance

instance neutralToLocalFull : (neutralToLocal i R B himage S hfull hR).Full := by
  change (fullSubcategoryLift (localModuleProperty (A := i.obj R))
    (SignKernel.inclusion (neutralModuleCharacter i R B himage)) _).Full
  infer_instance

instance neutralToLocalMonoidal : (neutralToLocal i R B himage S hfull hR).Monoidal := by
  change (fullSubcategoryLift (localModuleProperty (A := i.obj R))
    (SignKernel.inclusion (neutralModuleCharacter i R B himage)) _).Monoidal
  infer_instance

instance neutralToLocalAdditive : (neutralToLocal i R B himage S hfull hR).Additive := by
  change (fullSubcategoryLift (localModuleProperty (A := i.obj R))
    (SignKernel.inclusion (neutralModuleCharacter i R B himage)) _).Additive
  infer_instance

instance neutralToLocalLinear : (neutralToLocal i R B himage S hfull hR).Linear ℂ := by
  change (fullSubcategoryLift (localModuleProperty (A := i.obj R))
    (SignKernel.inclusion (neutralModuleCharacter i R B himage)) _).Linear ℂ
  infer_instance

/-- The actual neutral central lift supplies all neutral/odd crossings,
with no braided structure assumed on the category of all modules. -/
def neutralCenterFunctor : SignKernel.Positive (neutralModuleCharacter i R B himage) ⥤
    Center (Mod_ N (i.obj R)) :=
  neutralToLocal i R B himage S hfull hR ⋙ (S.map i).localCenterFunctor

instance neutralCenterFunctorMonoidal :
    (neutralCenterFunctor i R B himage S hfull hR).Monoidal := by
  dsimp only [neutralCenterFunctor]
  infer_instance

instance neutralCenterFunctorAdditive :
    (neutralCenterFunctor i R B himage S hfull hR).Additive := by
  dsimp only [neutralCenterFunctor]
  infer_instance

instance neutralCenterFunctorLinear :
    (neutralCenterFunctor i R B himage S hfull hR).Linear ℂ := by
  dsimp only [neutralCenterFunctor]
  infer_instance

/-- Its underlying functor is precisely the actual neutral inclusion. -/
theorem neutralCenterFunctor_comp_forget :
    neutralCenterFunctor i R B himage S hfull hR ⋙ Center.forget _ =
      SignKernel.inclusion (neutralModuleCharacter i R B himage) := rfl

/-- Explicit actual half-braiding on any neutral module against every
module, including every actual odd module. -/
theorem neutralCenterFunctor_halfBraiding
    (M : SignKernel.Positive (neutralModuleCharacter i R B himage))
    (Y : Mod_ N (i.obj R)) :
    ((neutralCenterFunctor i R B himage S hfull hR).obj M).2.β Y =
      ((S.map i).localCrossingIso M.obj Y
        (neutralModule_local i R B himage S hfull hR M)).symm := rfl

end Paper18.Category.FixedBoundary
