import Paper18.Category.ModuleFunctorFiniteAlphaFull
import Paper18.Category.FixedBoundaryNeutralBraiding

/-! # Actual alpha fullness for the de-equivariant neutral component

The true local-module central lift and the true transported neutral
braiding instantiate the categorical fullness theorem. No braiding on
all modules, pivotal structure, or alpha-fullness certificate is used.
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

/-- The actual neutral center lift has exactly the negative-braiding
compatibility, after transport to the specified actual underlying objects. -/
theorem neutralNegativeCentralCompatibility :
    letI := neutralModuleBraided i R B himage s hfull hR
    NegativeCentralCompatibility (neutralModuleCharacter i R B himage)
      (neutralCenterFunctor i R B himage s hfull hR) (Iso.refl _) := by
  letI := neutralModuleBraided i R B himage s hfull hR
  intro X Y
  change ((ModuleFunctor.transportCenter
    ((neutralCenterFunctor i R B himage s hfull hR).obj X) (Iso.refl _)).2.β Y.obj).hom = _
  rw [ModuleFunctor.transportCenter_refl_β]
  exact neutralCenterFunctor_halfBraiding_neutral i R B himage s hfull hR X Y


section Finite
variable [HasKernels (Mod_ N (i.obj R))] [HasFiniteBiproducts (Mod_ N (i.obj R))]
  [RightRigidCategory (Mod_ N (i.obj R))] [Simple (𝟙_ (Mod_ N (i.obj R)))]
  [∀ X Y : Mod_ N (i.obj R), FiniteDimensional ℂ (X ⟶ Y)]
  {κ : Type w} [Fintype κ]
  (SD : FiniteSemisimpleSkeleton (Mod_ N (i.obj R)) κ)
  (d : ZMod 2) (j : κ)
  (hj : Homogeneous (neutralModuleCharacter i R B himage) d (SD.simpleObject j))

/-- Actual negative alpha induction on the actual homogeneous module
component is full. Its preimages are constructed by the proved rigid
contraction and actual one-simple module density. -/
def neutralNegativeFull :
    letI := neutralModuleBraided i R B himage s hfull hR
    (ModuleAlphaInduction.negative
      (SignKernel.Positive (neutralModuleCharacter i R B himage))
      (HomogeneousCategory (neutralModuleCharacter i R B himage) d)).Full := by
  letI := neutralModuleBraided i R B himage s hfull hR
  exact homogeneousNegativeFull SD (neutralModuleCharacter i R B himage) d
    (neutralCenterFunctor i R B himage s hfull hR) (Iso.refl _)
    (neutralNegativeCentralCompatibility i R B himage s hfull hR) j hj

end Finite
end Paper18.Category.FixedBoundary
