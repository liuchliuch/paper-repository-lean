import Paper18.Category.FixedBoundaryOddBoundaryModules
import Paper18.Category.ModuleAlphaInductionEquivalenceHomogeneous
import Paper18.Category.ModuleFunctorFiniteBoundaryRepresentable
import Paper18.Category.SignKernelDimensions

/-!
# An actual invertible representative of an arbitrary specified boundary pair

The actual odd component is nonempty because the descended monodromy is
nontrivial. The proved alpha-induction equivalence then represents the
actual odd restriction by an actual neutral object and an actual native
module natural isomorphism. There is no representability input field.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj Obj
universe v u w v' u' w'
namespace Paper18.Category.FixedBoundary
variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℂ A]
  [MonoidalCategory A] [BraidedCategory A] [MonoidalPreadditive A] [MonoidalLinear ℂ A]
  [HasKernels A] [HasFiniteBiproducts A] [RightRigidCategory A] [HasCoequalizers A]
  [∀ X Y : A, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (SA : FiniteSemisimpleSkeleton A ι)
  {N : Type u'} [Category.{v'} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N] [MonoidalPreadditive N] [MonoidalLinear ℂ N]
  [RightRigidCategory N] [HasCoequalizers N] [HasKernels N] [HasFiniteBiproducts N]
  (i : A ⥤ N) [i.Braided] [i.Full] [i.Faithful] [i.Additive] [i.Linear ℂ]
  (P : BoundaryAutoequivalence i) (R : A) [MonObj R] [IsCommMonObj R]
  {T : N} (B : TensorInverse T)
  (himage : ∀ X : A, Centralizes T (i.obj X))
  (S : SeparableAlgebra R)
  (hfull : ∀ Y : N, Centralizes T Y → ∃ X : A, Nonempty (i.obj X ≅ Y))
  (hR : R ∈ mugerCenter (C := A))
  (e : P.functor.obj T ≅ T)
  [RightRigidCategory (Mod_ N (i.obj R))] [Simple (𝟙_ (Mod_ N (i.obj R)))]
  [∀ X Y : Mod_ N (i.obj R), FiniteDimensional ℂ (X ⟶ Y)]
  {κ : Type w'} [Fintype κ]
  (SD : FiniteSemisimpleSkeleton (Mod_ N (i.obj R)) κ)

include SD in
/-- Nontrivial actual descended monodromy supplies an actual odd simple
and hence the actual alpha representative for the actual boundary pair. -/
theorem oddBoundaryInvertibleRepresentation
    (q : T ⊗ T ≅ 𝟙_ N) (M : Mod_ N (i.obj R))
    (hM : (neutralModuleCharacter i R B himage).hom.app M ≠ 𝟙 M) :
    letI := neutralModuleBraided i R B himage S hfull hR
    ∃ Z : SignKernel.Positive (neutralModuleCharacter i R B himage),
      Nonempty (TensorInverse Z) ∧ Nonempty
      ((ModuleAlphaInduction.negative
        (SignKernel.Positive (neutralModuleCharacter i R B himage))
        (HomogeneousCategory (neutralModuleCharacter i R B himage) 1)).obj Z ≅
          oddBoundaryModuleEnd SA i P R B himage S hfull e) := by
  let χ := neutralModuleCharacter i R B himage
  have hχ : ∀ X : Mod_ N (i.obj R), χ.hom.app X ≫ χ.hom.app X = 𝟙 X :=
    B.moduleMonodromy_involutive (i.obj R) (himage R) q
  obtain ⟨j, hj⟩ := SignKernel.exists_negative_label SD χ hχ M hM
  have hj' : Homogeneous χ 1 (SD.simpleObject (SD.label M j)) := by
    simpa only [Homogeneous, paritySign_one, neg_one_smul] using hj
  letI := neutralModuleBraided i R B himage S hfull hR
  let F := oddBoundaryModuleEnd SA i P R B himage S hfull e
  letI : F.toFunctor.IsEquivalence :=
    (oddBoundaryModuleEquivalence i P R B himage S hfull e).isEquivalence_functor
  exact exists_invertible_homogeneous_representer SD χ 1
    (neutralCenterFunctor i R B himage S hfull hR) (Iso.refl _)
    (neutralNegativeCentralCompatibility i R B himage S hfull hR)
    (SD.label M j) hj' F

end Paper18.Category.FixedBoundary
