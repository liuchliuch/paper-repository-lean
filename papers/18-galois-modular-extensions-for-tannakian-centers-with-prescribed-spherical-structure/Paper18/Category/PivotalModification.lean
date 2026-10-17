import Paper18.Category.SphericalComparison

/-!
# Modifying actual pivotal structures by tensor automorphisms

A monoidal natural automorphism of the identity composes with a pivotal
identification. The resulting actual traces are the original traces with
the automorphism, or its inverse, inserted. Involutive automorphisms
therefore preserve sphericality on every endomorphism.
-/

noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category.PivotalStructure
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  (J : PivotalStructure C) (χ : 𝟭 C ≅ 𝟭 C) [χ.hom.IsMonoidal]

/-- Modify the actual pivotal identification by a tensor automorphism. -/
def modify : PivotalStructure C where
  j := χ ≪≫ J.j
  unit := by
    change χ.hom.app (𝟙_ C) ≫ J.j.hom.app (𝟙_ C) = _
    have h : χ.hom.app (𝟙_ C) = 𝟙 (𝟙_ C) := by
      simpa using (NatTrans.IsMonoidal.unit (τ := χ.hom))
    rw [h]
    erw [Category.id_comp]
    exact J.unit
  tensor X Y := by
    change χ.hom.app (X ⊗ Y) ≫ J.j.hom.app (X ⊗ Y) = _
    have h : χ.hom.app (X ⊗ Y) = χ.hom.app X ⊗ₘ χ.hom.app Y := by
      simpa using (NatTrans.IsMonoidal.tensor (τ := χ.hom) X Y)
    rw [h, J.tensor, ← Category.assoc, tensorHom_comp_tensorHom]
    rfl

@[simp] lemma modify_j : (J.modify χ).j = χ ≪≫ J.j := rfl

@[simp] lemma modify_hom_app (X : C) :
    (J.modify χ).j.hom.app X = χ.hom.app X ≫ J.j.hom.app X := rfl

@[simp] lemma modify_inv_app (X : C) :
    (J.modify χ).j.inv.app X = J.j.inv.app X ≫ χ.inv.app X := rfl

/-- Taking the quotient with the original pivotal structure recovers the
actual modifying automorphism. -/
@[simp] lemma modify_ratio : (J.modify χ).ratio J = χ := by
  ext X
  change (χ.hom.app X ≫ J.j.hom.app X) ≫ J.j.inv.app X = χ.hom.app X
  simp only [Category.assoc, J.j.hom_inv_id_app, Category.comp_id]

/-- The modified right trace inserts the actual automorphism component. -/
lemma modify_rightTrace {X : C} (f : X ⟶ X) :
    (J.modify χ).rightTrace f = J.rightTrace (f ≫ χ.hom.app X) := by
  simp only [rightTrace, leftEvaluation, modify_hom_app,
    comp_whiskerRight, Category.assoc]

/-- The modified left trace inserts the inverse automorphism component. -/
lemma modify_leftTrace {X : C} (f : X ⟶ X) :
    (J.modify χ).leftTrace f = J.leftTrace (χ.inv.app X ≫ f) := by
  simp only [leftTrace, leftCoevaluation, modify_inv_app,
    whiskerLeft_comp, Category.assoc]
  rfl

omit [MonoidalCategory C] [RightRigidCategory C] [χ.hom.IsMonoidal] in
/-- Componentwise involutivity identifies the inverse component with the
original component. -/
lemma inv_app_eq_hom_of_involutive
    (hχ : ∀ X : C, χ.hom.app X ≫ χ.hom.app X = 𝟙 X) (X : C) :
    χ.inv.app X = χ.hom.app X := by
  apply (cancel_epi (χ.hom.app X)).mp
  rw [χ.hom_inv_id_app, hχ]
  rfl

/-- Involutive tensor automorphisms preserve actual sphericality, without
restricting the equality to simple objects. -/
theorem modify_spherical (hJ : J.Spherical)
    (hχ : ∀ X : C, χ.hom.app X ≫ χ.hom.app X = 𝟙 X) : (J.modify χ).Spherical := by
  intro X f
  rw [J.modify_leftTrace χ, J.modify_rightTrace χ,
    inv_app_eq_hom_of_involutive χ hχ X, hJ X]
  have hn : χ.hom.app X ≫ f = f ≫ χ.hom.app X := (χ.hom.naturality f).symm
  rw [hn]

section Scalars
variable [Preadditive C] [Linear ℂ C] [CategoryTheory.Limits.HasKernels C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C]

omit [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
/-- The comparison scalar of the actual modification is its original Schur
scalar, so categorical modifications match extracted tensor characters. -/
@[simp] lemma modify_comparisonScalar (X : C) [Simple X] :
    (J.modify χ).comparisonScalar J X = TensorAutomorphism.scalar χ X := by
  unfold comparisonScalar
  rw [J.modify_ratio χ]

/-- On an actual simple object the modified right trace is multiplied by the
Schur scalar of the automorphism component. -/
lemma modify_rightTrace_scalar {X : C} [Simple X] (f : X ⟶ X) :
    (J.modify χ).rightTrace f = TensorAutomorphism.scalar χ X • J.rightTrace f := by
  rw [J.modify_rightTrace χ, ← TensorAutomorphism.scalar_spec χ X]
  simp only [Linear.comp_smul, Category.comp_id]
  simp [rightTrace, leftEvaluation]

/-- The corresponding actual left trace is multiplied by the inverse scalar. -/
lemma modify_leftTrace_scalar {X : C} [Simple X] (f : X ⟶ X) :
    (J.modify χ).leftTrace f = (TensorAutomorphism.scalar χ X)⁻¹ • J.leftTrace f := by
  rw [J.modify_leftTrace χ]
  have h : χ.inv.app X = (TensorAutomorphism.scalar χ X)⁻¹ • 𝟙 X := by
    rw [← TensorAutomorphism.inv_scalar χ X]
    exact (TensorAutomorphism.scalar_spec χ.symm X).symm
  rw [h]
  erw [Linear.smul_comp, Category.id_comp]
  simp [leftTrace, leftCoevaluation]

variable [Simple (𝟙_ C)]

lemma modify_rightDim (X : C) [Simple X] :
    (J.modify χ).rightDim X = TensorAutomorphism.scalar χ X * J.rightDim X := by
  simp only [rightDim, rightDimension, J.modify_rightTrace_scalar χ,
    map_smul, smul_eq_mul]

lemma modify_leftDim (X : C) [Simple X] :
    (J.modify χ).leftDim X = (TensorAutomorphism.scalar χ X)⁻¹ * J.leftDim X := by
  simp only [leftDim, leftDimension, J.modify_leftTrace_scalar χ,
    map_smul, smul_eq_mul]

end Scalars
end Paper18.Category.PivotalStructure
