import Paper18.Category.DrinfeldCoendModulesInverseBasic

/-! # Naturality of annular crossings recovered from coend modules -/
noncomputable section
set_option maxHeartbeats 2000000
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj
universe v u w
namespace Paper18.Category.DrinfeldCoendModules
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D]

omit [BraidedCategory D] in
/-- Moving a map across the actual rigid transpose produces its actual
right-dual mate on the cap. -/
lemma transpose_codomain_mate (T U M : D) (f : T ⟶ U) (h : T ⊗ M ⟶ T ⊗ M) :
    (tensorLeftHomEquiv (T ⊗ M) U (dual D U) M).symm (h ≫ f ▷ M) =
      dualMap D f ▷ (T ⊗ M) ≫
        (tensorLeftHomEquiv (T ⊗ M) T (dual D T) M).symm h := by
  change dual D U ◁ (h ≫ f ▷ M) ≫ (α_ (dual D U) U M).inv ≫
      ε_ U (dual D U) ▷ M ≫ (λ_ M).hom =
    dualMap D f ▷ (T ⊗ M) ≫ dual D T ◁ h ≫
      (α_ (dual D T) T M).inv ≫ ε_ T (dual D T) ▷ M ≫ (λ_ M).hom
  simp only [whiskerLeft_comp, assoc]
  rw [associator_inv_naturality_middle_assoc,
    ← comp_whiskerRight_assoc, ← rightAdjointMate_comp_evaluation,
    comp_whiskerRight_assoc, ← associator_inv_naturality_left_assoc,
    ← whisker_exchange_assoc]

variable [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)

/-- Actual cap dinaturality implies naturality of the recovered annular
crossing in every ambient object, using the actual mate identity. -/
lemma moduleHolonomy_naturality (M : Mod_ D (algebra S)) {T U : D} (f : T ⟶ U) :
    f ▷ M.X ≫ moduleHolonomy S M U = moduleHolonomy S M T ≫ f ▷ M.X := by
  apply (tensorLeftHomEquiv (T ⊗ M.X) U (dual D U) M.X).symm.injective
  rw [tensorLeftHomEquiv_symm_naturality, moduleHolonomy, Equiv.symm_apply_apply,
    transpose_codomain_mate, moduleHolonomy, Equiv.symm_apply_apply]
  rw [associator_inv_naturality_middle_assoc, associator_inv_naturality_left_assoc,
    moduleCap_dinaturality]

omit [Simple (𝟙_ D)] in
/-- Every actual module morphism intertwines the recovered annular crossings. -/
lemma moduleHolonomy_map {M N : Mod_ D (algebra S)} (f : M ⟶ N) (T : D) :
    T ◁ f.hom ≫ moduleHolonomy S N T = moduleHolonomy S M T ≫ T ◁ f.hom := by
  apply (tensorLeftHomEquiv (T ⊗ M.X) T (dual D T) N.X).symm.injective
  simp only [moduleHolonomy]
  rw [tensorLeftHomEquiv_symm_naturality, Equiv.symm_apply_apply,
    ← tensorLeftHomEquiv_naturality, Equiv.symm_apply_apply]
  dsimp only [moduleCap]
  have hf : γ[algebra S,M.X] ≫ f.hom = algebra S ◁ f.hom ≫ γ[algebra S,N.X] :=
    IsMod_Hom.smul_hom
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc, ← hf]
  simp only [assoc]

end Paper18.Category.DrinfeldCoendModules
