import Paper18.Category.FixedBoundaryBosonGrading
import Paper18.Category.FixedBoundaryRegularFaithful
import Paper18.Category.ModuleTensorCharacters
import Paper18.Category.SeparableModulesSemisimple

/-! # Actual boson grading on the de-equivariant module category -/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped MonObj
universe v u w
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  {T : C} (B : TensorInverse T) (R : C) [MonObj R] (hR : Centralizes T R)

include hR in
/-- Centralization is exactly the condition needed to descend the
actual monodromy character to internal modules. -/
theorem TensorInverse.monodromy_algebra_identity : B.monodromyCharacter.hom.app R = 𝟙 R := by
  have h := (B.monodromy_neutral_iff R).mpr hR
  simpa only [FixedBoundary.Homogeneous, FixedBoundary.paritySign_zero, one_smul] using h

/-- The actual monodromy character on the internal module category. -/
def TensorInverse.moduleMonodromyCharacter : 𝟭 (Mod_ C R) ≅ 𝟭 (Mod_ C R) :=
  ModuleTensorCharacters.moduleCharacter B.monodromyCharacter (B.monodromy_algebra_identity R hR)

@[simp] theorem TensorInverse.moduleMonodromyCharacter_hom (M : Mod_ C R) :
    ((B.moduleMonodromyCharacter R hR).hom.app M).hom = B.monodromyCharacter.hom.app M.X := rfl

/-- The neutral actual module component consists exactly of modules
whose actual underlying object centralizes the order-two object. -/
theorem TensorInverse.moduleMonodromy_neutral_iff (M : Mod_ C R) :
    FixedBoundary.Homogeneous (B.moduleMonodromyCharacter R hR) 0 M ↔ Centralizes T M.X := by
  change (B.moduleMonodromyCharacter R hR).hom.app M =
    FixedBoundary.paritySign 0 • 𝟙 M ↔ _
  rw [FixedBoundary.paritySign_zero, one_smul]
  constructor
  · intro h
    have hh := congrArg (fun f : M ⟶ M => f.hom) h
    apply (B.monodromy_neutral_iff M.X).mp
    change B.monodromyCharacter.hom.app M.X = FixedBoundary.paritySign 0 • 𝟙 M.X
    simpa only [FixedBoundary.paritySign_zero, one_smul] using hh
  · intro h
    apply Mod_.Hom.ext
    have hh := (B.monodromy_neutral_iff M.X).mpr h
    simpa only [FixedBoundary.Homogeneous, FixedBoundary.paritySign_zero, one_smul] using hh

/-- The actual square isomorphism makes the actual module character an
involution on every module. -/
theorem TensorInverse.moduleMonodromy_involutive (q : T ⊗ T ≅ 𝟙_ C) (M : Mod_ C R) :
    (B.moduleMonodromyCharacter R hR).hom.app M ≫
      (B.moduleMonodromyCharacter R hR).hom.app M = 𝟙 M := by
  apply Mod_.Hom.ext
  exact B.monodromy_involutive_of_square q M.X

variable [RightRigidCategory C] [HasCoequalizers C] [IsCommMonObj R]

/-- The descended grading character is monoidal for the actual relative
tensor product; this uses the balancing quotient, not numerical degrees. -/
instance TensorInverse.moduleMonodromyMonoidal :
    NatTrans.IsMonoidal (B.moduleMonodromyCharacter R hR).hom := by
  dsimp only [TensorInverse.moduleMonodromyCharacter]
  infer_instance

section Faithful
variable [(InternalModule.freeFunctor (A := R)).Faithful]

/-- Faithful free extension detects nontriviality of an actual descended
tensor character. -/
theorem TensorInverse.moduleMonodromy_nontrivial
    (hn : B.monodromyCharacter ≠ Iso.refl (𝟭 C)) :
    B.moduleMonodromyCharacter R hR ≠ Iso.refl (𝟭 (Mod_ C R)) := by
  intro h
  apply hn
  ext X
  apply (InternalModule.freeFunctor (A := R)).map_injective
  change InternalModule.freeMap (B.monodromyCharacter.hom.app X) =
    (InternalModule.freeFunctor (A := R)).map (𝟙 X)
  rw [CategoryTheory.Functor.map_id, ← ModuleTensorCharacters.free_compatible
    B.monodromyCharacter (B.monodromy_algebra_identity R hR) X]
  exact congrArg (fun q : 𝟭 (Mod_ C R) ≅ 𝟭 (Mod_ C R) =>
    q.hom.app (InternalModule.free R X)) h

end Faithful

variable [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι) (s : SeparableAlgebra R)

include S s in
/-- Every actual de-equivariant module admits an actual finite biproduct
decomposition into homogeneous simples of the induced boson grading. -/
theorem TensorInverse.module_orderTwo_homogeneous_decomposition
    (q : T ⊗ T ≅ 𝟙_ C) (M : Mod_ C R) :
    ∃ (n : ℕ) (Y : Fin n → Mod_ C R) (g : Fin n → ZMod 2),
      (∀ j, Simple (Y j) ∧ FixedBoundary.Homogeneous
        (B.moduleMonodromyCharacter R hR) (g j) (Y j)) ∧ Nonempty (M ≅ ⨁ Y) :=
  FixedBoundary.exists_homogeneous_decomposition (B.moduleMonodromyCharacter R hR)
    (B.moduleMonodromy_involutive R hR q) (s.skeleton S) M

end Paper18.Category
