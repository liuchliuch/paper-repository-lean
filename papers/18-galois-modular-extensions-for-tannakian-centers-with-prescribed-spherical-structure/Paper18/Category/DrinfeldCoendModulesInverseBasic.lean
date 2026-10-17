import Paper18.Category.DrinfeldCoendModulesUnit

/-! # Recovering actual annular crossings from actual coend modules -/
noncomputable section
set_option maxHeartbeats 2000000
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj
universe v u w
namespace Paper18.Category.DrinfeldCoendModules
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)

/-- The actual action restricted to the specified rigid cap generator. -/
def moduleCap (M : Mod_ D (algebra S)) (T : D) : (dual D T ⊗ T) ⊗ M.X ⟶ M.X :=
  injection S T ▷ M.X ≫ γ[algebra S,M.X]

/-- Cups transpose the actual action into an actual annular endomorphism.
No half-braiding or invertibility data is supplied. -/
def moduleHolonomy (M : Mod_ D (algebra S)) (T : D) : T ⊗ M.X ⟶ T ⊗ M.X :=
  tensorLeftHomEquiv (T ⊗ M.X) T (dual D T) M.X
    ((α_ (dual D T) T M.X).inv ≫ moduleCap S M T)

omit [Simple (𝟙_ D)] in
/-- The rigid transpose reconstructs the action on every cap generator. -/
lemma moduleHolonomy_cap (M : Mod_ D (algebra S)) (T : D) :
    (α_ (dual D T) T M.X).hom ≫
        (tensorLeftHomEquiv (T ⊗ M.X) T (dual D T) M.X).symm
          (moduleHolonomy S M T) = moduleCap S M T := by
  rw [moduleHolonomy, Equiv.symm_apply_apply, Iso.hom_inv_id_assoc]

/-- Dinaturality is inherited from the actual coend generators. -/
lemma moduleCap_dinaturality (M : Mod_ D (algebra S)) {T U : D} (f : T ⟶ U) :
    (dualMap D f ▷ T) ▷ M.X ≫ moduleCap S M T =
      (dual D U ◁ f) ▷ M.X ≫ moduleCap S M U := by
  dsimp only [moduleCap]
  rw [← comp_whiskerRight_assoc, injection_dinaturality, comp_whiskerRight_assoc]

instance unitInjection_isIso : IsIso (unitInjection (D := D)) := by
  dsimp only [unitInjection]
  infer_instance

/-- The cap at the tensor unit is forced by the actual module unit law. -/
lemma moduleCap_unit (M : Mod_ D (algebra S)) : moduleCap S M (𝟙_ D) =
    ε_ (𝟙_ D) (dual D (𝟙_ D)) ▷ M.X ≫ (λ_ M.X).hom := by
  apply (cancel_epi (unitInjection (D := D) ▷ M.X)).mp
  dsimp only [moduleCap]
  rw [← comp_whiskerRight_assoc, ← injection_one]
  rw [← comp_whiskerRight_assoc, unitInjection_cap, id_whiskerRight, id_comp]
  exact ModObj.one_smul (M := algebra S) M.X

/-- Transposition therefore gives the identity annular crossing at the unit. -/
lemma moduleHolonomy_unit (M : Mod_ D (algebra S)) :
    moduleHolonomy S M (𝟙_ D) = 𝟙 _ := by
  apply (tensorLeftHomEquiv ((𝟙_ D) ⊗ M.X) (𝟙_ D) (dual D (𝟙_ D)) M.X).symm.injective
  rw [moduleHolonomy, Equiv.symm_apply_apply, moduleCap_unit]
  change _ = dual D (𝟙_ D) ◁ (𝟙 ((𝟙_ D) ⊗ M.X)) ≫
    (α_ (dual D (𝟙_ D)) (𝟙_ D) M.X).inv ≫
      ε_ (𝟙_ D) (dual D (𝟙_ D)) ▷ M.X ≫ (λ_ M.X).hom
  simp only [whiskerLeft_id, id_comp]

end Paper18.Category.DrinfeldCoendModules
