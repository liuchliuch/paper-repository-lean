import Paper18.Category.PivotalBalancingDimensions

/-!
# Hopf links as actual pivotal traces

The Hopf-link scalar is the actual trace of the double-braiding morphism.
Its fusion expansion is derived from balancing and actual biproduct trace
resolution; no scalar-monodromy model is imposed on general simple pairs.
-/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)] [BraidedCategory C]
  {ι : Type w} [Fintype ι]

namespace PivotalStructure
variable (J : PivotalStructure C) (S : FiniteSemisimpleSkeleton C ι)

/-- The actual Hopf-link scalar, defined on actual objects. -/
def hopfLink (X Y : C) : ℂ := unitScalarEquiv (C := C)
  (J.rightTrace (doubleBraiding X Y).hom)

lemma hopfLink_symm (X Y : C) : J.hopfLink X Y = J.hopfLink Y X := by
  unfold hopfLink
  apply congrArg (unitScalarEquiv (C := C))
  exact J.rightTrace_comp (β_ X Y).hom (β_ Y X).hom

lemma hopfLink_unit_left (X : C) : J.hopfLink (𝟙_ C) X = J.rightDim X := by
  unfold hopfLink
  rw [centralizes_unit_left X]
  exact J.rightDim_iso (λ_ X)

/-- Actual trace resolution evaluates any natural endomorphism by its
Schur scalars on the actual simple constituents. -/
lemma rightTraceScalar_natIso (σ : 𝟭 C ≅ 𝟭 C) (X : C) :
    unitScalarEquiv (C := C) (J.rightTrace (σ.hom.app X)) =
      ∑ k, (S.multiplicity X k : ℂ) *
        (TensorAutomorphism.scalar σ (S.simpleObject k) * J.rightDim (S.simpleObject k)) := by
  let Y := fun a : Fin (S.length X) => S.simpleObject (S.label X a)
  let e := S.decomposition X
  let i := fun a => biproduct.ι Y a ≫ e.inv
  let p := fun a => e.hom ≫ biproduct.π Y a
  have hr : ∑ a, p a ≫ i a = 𝟙 X := by
    dsimp only [i, p]
    simp only [assoc, ← Preadditive.comp_sum]
    simp_rw [← assoc]
    rw [← Preadditive.sum_comp, biproduct.total]
    dsimp only [Y]
    rw [id_comp]
    exact e.hom_inv_id
  have hpi (a : Fin (S.length X)) : i a ≫ p a = 𝟙 (Y a) := by
    simp [i, p, assoc]
  calc
    _ = ∑ a : Fin (S.length X),
        TensorAutomorphism.scalar σ (Y a) * J.rightDim (Y a) := by
      rw [J.rightTrace_of_resolution Y i p hr, map_sum]
      apply Finset.sum_congr rfl
      intro a _
      have hn : i a ≫ σ.hom.app X = σ.hom.app (Y a) ≫ i a := σ.hom.naturality (i a)
      rw [reassoc_of% hn, hpi, comp_id, ← TensorAutomorphism.scalar_spec σ (Y a)]
      exact J.rightTrace_smul_id _ _
    _ = _ := by
      symm
      simp_rw [S.multiplicity_eq_sum, Nat.cast_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      simp [Y]

/-- The balancing formula for the actual Hopf-link matrix is derived by
taking the actual trace and resolving the tensor product into actual simples. -/
lemma hopfLink_fusion_formula (i j : ι) :
    J.hopfLink (S.simpleObject i) (S.simpleObject j) =
      (J.twistScalar (S.simpleObject i) * J.twistScalar (S.simpleObject j))⁻¹ *
        ∑ k, (S.fusionCoeff i j k : ℂ) *
          (J.twistScalar (S.simpleObject k) * J.rightDim (S.simpleObject k)) := by
  let X := S.simpleObject i
  let Y := S.simpleObject j
  have hc : J.twistScalar X * J.twistScalar Y ≠ 0 :=
    mul_ne_zero (J.twistScalar_ne_zero X) (J.twistScalar_ne_zero Y)
  have hb : (J.twistIso (X ⊗ Y)).hom =
      (J.twistScalar X * J.twistScalar Y) • (doubleBraiding X Y).hom := by
    rw [J.twist_tensor, ← J.twistScalar_spec X, ← J.twistScalar_spec Y]
    simp [tensorHom_def, smul_smul, mul_comm]
  have hm : (doubleBraiding X Y).hom =
      (J.twistScalar X * J.twistScalar Y)⁻¹ • (J.twistIso (X ⊗ Y)).hom := by
    rw [hb, smul_smul, inv_mul_cancel₀ hc, one_smul]
  change unitScalarEquiv (C := C) (J.rightTrace (doubleBraiding X Y).hom) = _
  rw [hm, J.rightTrace_smul, map_smul, smul_eq_mul]
  exact congrArg (fun z => (J.twistScalar X * J.twistScalar Y)⁻¹ * z)
    (J.rightTraceScalar_natIso S J.twistNatIso (X ⊗ Y))

end PivotalStructure
end Paper18.Category
