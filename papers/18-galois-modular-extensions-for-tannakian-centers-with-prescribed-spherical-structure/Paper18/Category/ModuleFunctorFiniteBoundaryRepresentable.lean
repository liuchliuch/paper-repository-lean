import Paper18.Category.ModuleFunctorFiniteBoundaryAlpha
import Paper18.Category.ModuleFunctorFiniteRepresentable

/-! # Actual module-functor representability for the de-equivariant boundary

The actual neutral local-module central lift instantiates the constructed
alpha equivalence. No representability or alpha-equivalence certificate
is an input, and the category of all modules need not be braided.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj Obj
universe v u v' u' w
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
  (s : SeparableAlgebra R)
  (hfull : ∀ Y : N, Centralizes T Y → ∃ X : A, Nonempty (i.obj X ≅ Y))
  (hR : R ∈ mugerCenter (C := A))

section Finite
variable [HasKernels (Mod_ N (i.obj R))] [HasFiniteBiproducts (Mod_ N (i.obj R))]
  [RightRigidCategory (Mod_ N (i.obj R))] [Simple (𝟙_ (Mod_ N (i.obj R)))]
  [∀ X Y : Mod_ N (i.obj R), FiniteDimensional ℂ (X ⟶ Y)]
  {κ : Type w} [Fintype κ]
  (SD : FiniteSemisimpleSkeleton (Mod_ N (i.obj R)) κ)
  (d : ZMod 2) (j : κ)
  (hj : Homogeneous (neutralModuleCharacter i R B himage) d (SD.simpleObject j))

/-- The actual local central lift makes negative alpha induction an
actual equivalence from neutral modules to homogeneous module functors. -/
def neutralNegativeEquivalence :
    letI := neutralModuleBraided i R B himage s hfull hR
    SignKernel.Positive (neutralModuleCharacter i R B himage) ≌
      ModuleAlphaInduction.End (SignKernel.Positive (neutralModuleCharacter i R B himage))
        (HomogeneousCategory (neutralModuleCharacter i R B himage) d) := by
  letI := neutralModuleBraided i R B himage s hfull hR
  exact homogeneousNegativeEquivalence SD (neutralModuleCharacter i R B himage) d
    (neutralCenterFunctor i R B himage s hfull hR) (Iso.refl _)
    (neutralNegativeCentralCompatibility i R B himage s hfull hR) j hj

include SD j hj in
/-- Every actual homogeneous module endofunctor is represented by an
actual neutral module, with a genuine module natural isomorphism. -/
theorem neutralNegativeRepresentation
    (F : ModuleAlphaInduction.End (SignKernel.Positive (neutralModuleCharacter i R B himage))
      (HomogeneousCategory (neutralModuleCharacter i R B himage) d)) :
    letI := neutralModuleBraided i R B himage s hfull hR
    ∃ Z : SignKernel.Positive (neutralModuleCharacter i R B himage), Nonempty
      ((ModuleAlphaInduction.negative
        (SignKernel.Positive (neutralModuleCharacter i R B himage))
        (HomogeneousCategory (neutralModuleCharacter i R B himage) d)).obj Z ≅ F) := by
  letI := neutralModuleBraided i R B himage s hfull hR
  letI := homogeneousNegativeEssSurj SD (neutralModuleCharacter i R B himage) d
    (neutralCenterFunctor i R B himage s hfull hR) (Iso.refl _)
    (neutralNegativeCentralCompatibility i R B himage s hfull hR) j hj
  exact Functor.EssSurj.mem_essImage F

end Finite
end Paper18.Category.FixedBoundary
