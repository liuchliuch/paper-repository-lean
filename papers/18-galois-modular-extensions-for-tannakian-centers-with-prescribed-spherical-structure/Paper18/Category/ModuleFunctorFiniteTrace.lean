import Paper18.Category.PivotalDimension
import Paper18.Category.PivotalPartialTrace
import Paper18.Category.Braided

/-! # Nonzero braided contraction without a chosen pivotal structure

The cup space of an actual simple is one-dimensional. Actual
semisimplicity therefore makes its cup and braided cap compose nontrivially.
The resulting normalized actual partial contraction retracts right tensoring
on morphisms, without choosing or assuming a pivotal structure.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.ModuleFunctor
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasFiniteBiproducts C] [HasKernels C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- The actual braided cap obtained from the actual chosen right dual. -/
def braidedCap (X : C) : X ⊗ dual C X ⟶ 𝟙_ C :=
  (β_ X (dual C X)).hom ≫ ε_ X (dual C X)

/-- The actual scalar of the closed cup and braided cap. -/
def braidedClosureScalar (X : C) : ℂ :=
  unitScalarEquiv (η_ X (dual C X) ≫ braidedCap X)

include S in
theorem braidedCap_ne_zero (X : C) [Simple X] : braidedCap X ≠ 0 := by
  letI : Simple (dual C X) := S.simple_rightDual X
  have he := exactPairing_evaluation_ne_zero X (dual C X)
  intro h
  apply he
  apply (cancel_epi (β_ X (dual C X)).hom).mp
  simpa only [braidedCap, comp_zero] using h

include S in
/-- The actual braided closure is nonzero on every actual simple. -/
theorem braidedClosureScalar_ne_zero (X : C) [Simple X] : braidedClosureScalar X ≠ 0 := by
  have hc := S.comp_ne_zero_of_finrank_one (finrank_unit_to_simple_tensor_dual X)
    (η_ X (dual C X)) (braidedCap X)
    (exactPairing_coevaluation_ne_zero X (dual C X)) (braidedCap_ne_zero S X)
  intro h
  apply hc
  apply (unitScalarEquiv (C := C)).injective
  simpa only [braidedClosureScalar, map_zero] using h

/-- Contraction of a genuine right tensor map is the original map times
the actual closed-loop scalar. -/
lemma rightClosure_whiskerRight_scalar {A B X P : C}
    (cup : 𝟙_ C ⟶ X ⊗ P) (cap : X ⊗ P ⟶ 𝟙_ C) (f : A ⟶ B) :
    rightClosure cup cap (f ▷ X) = unitScalarEquiv (cup ≫ cap) • f := by
  have hc : cup ≫ cap = unitScalarEquiv (cup ≫ cap) • 𝟙 (𝟙_ C) :=
    (unitScalarEquiv_spec _).symm
  calc
    _ = f ≫ (ρ_ B).inv ≫ B ◁ (cup ≫ cap) ≫ (ρ_ B).hom := by
      simp only [rightClosure, whiskerLeft_comp, Category.assoc]
      rw [associator_naturality_left_assoc, Iso.inv_hom_id_assoc,
        whisker_exchange_assoc, ← rightUnitor_inv_naturality_assoc]
    _ = _ := by rw [hc]; simp

/-- Genuine complex-linear braided partial contraction. -/
def braidedContraction {A B : C} (X : C) : (A ⊗ X ⟶ B ⊗ X) →ₗ[ℂ] (A ⟶ B) where
  toFun f := rightClosure (η_ X (dual C X)) (braidedCap X) f
  map_add' _ _ := by simp [rightClosure]
  map_smul' _ _ := by simp [rightClosure]

@[simp] theorem braidedContraction_whiskerRight {A B : C} (X : C) (f : A ⟶ B) :
    braidedContraction X (f ▷ X) = braidedClosureScalar X • f :=
  rightClosure_whiskerRight_scalar _ _ f

/-- Normalized actual contraction is a left inverse to right tensoring
with a simple; no categorical-dimension law is a hypothesis. -/
def normalizedBraidedContraction {A B : C} (X : C) :
    (A ⊗ X ⟶ B ⊗ X) →ₗ[ℂ] (A ⟶ B) :=
  (braidedClosureScalar X)⁻¹ • braidedContraction X

include S in
theorem normalizedBraidedContraction_whiskerRight {A B : C}
    (X : C) [Simple X] (f : A ⟶ B) :
    normalizedBraidedContraction X (f ▷ X) = f := by
  simp only [normalizedBraidedContraction, LinearMap.smul_apply,
    braidedContraction_whiskerRight, smul_smul, inv_mul_cancel₀
      (braidedClosureScalar_ne_zero S X), one_smul]

end Paper18.Category.ModuleFunctor
