import Paper18.Category.ENOPseudounitaryIdempotents

/-!
# The FP projection for an actual fusion-algebra action

The construction below is on actual categorical endomorphisms. Its two
inputs are the multiplication and trace identities for those morphisms.
They are stated explicitly; this module does not assert that the central
induction loop morphisms already satisfy them.
-/

noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u w

namespace Paper18.FusionBasis

variable {ι : Type w} [Fintype ι] (B : FusionBasis ι)

theorem totalFPdim_pos : 0 < B.totalFPdim := by
  exact Finset.sum_pos' (fun i _ => sq_nonneg (B.fpdim i))
    ⟨B.one, Finset.mem_univ _, by simp⟩

/-- The coefficient of each basis vector in the square of the FP regular
element is its FP dimension times the total FP dimension. -/
theorem fpdim_regular_coefficient (k : ι) :
    (∑ i, ∑ j, B.fpdim i * B.fpdim j * (B.N i j k : ℝ)) =
      B.totalFPdim * B.fpdim k := by
  calc
    _ = ∑ i, B.fpdim i * (B.fpdim i * B.fpdim k) := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        _ = B.fpdim i * ∑ j, (B.N (B.dual i) k j : ℝ) * B.fpdim j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [← B.N_dual i j k]
          ring
        _ = _ := by rw [B.fpdim_mul, B.fpdim_dual]
    _ = _ := by simp only [totalFPdim, Finset.sum_mul]; congr 1; funext i; ring

theorem fpdim_regular_coefficient_complex (k : ι) :
    (∑ i, ∑ j, (B.fpdim i : ℂ) * (B.fpdim j : ℂ) * (B.N i j k : ℂ)) =
      (B.totalFPdim : ℂ) * (B.fpdim k : ℂ) := by
  exact_mod_cast B.fpdim_regular_coefficient k

end Paper18.FusionBasis

namespace Paper18.Category.PivotalStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (J : PivotalStructure C) (S : FiniteSemisimpleSkeleton C ι)

/-- The scalar of the actual pivotal right trace, as a linear map. -/
def scalarRightTrace (X : C) : (X ⟶ X) →ₗ[ℂ] ℂ :=
  (unitScalarEquiv (C := C)).toLinearMap.comp (J.rightTraceLinearMap X)

omit [HasFiniteBiproducts C] in
@[simp] theorem scalarRightTrace_apply {X : C} (e : X ⟶ X) :
    J.scalarRightTrace X e = unitScalarEquiv (C := C) (J.rightTrace e) := rfl

variable {X : C} (T : ι → (X ⟶ X))

/-- The normalized FP regular element of an actual fusion-algebra action. -/
def fpProjection : X ⟶ X :=
  (S.fusionBasis.totalFPdim : ℂ)⁻¹ • ∑ i, (S.fusionBasis.fpdim i : ℂ) • T i

include S in
theorem fpRegular_comp
    (hT : ∀ i j, T i ≫ T j = ∑ k, (S.fusionCoeff i j k : ℂ) • T k) :
    (∑ i, (S.fusionBasis.fpdim i : ℂ) • T i) ≫
        (∑ i, (S.fusionBasis.fpdim i : ℂ) • T i) =
      (S.fusionBasis.totalFPdim : ℂ) • ∑ i, (S.fusionBasis.fpdim i : ℂ) • T i := by
  let f : ι → ι → ι → (X ⟶ X) := fun i j k =>
    ((S.fusionBasis.fpdim i : ℂ) * (S.fusionBasis.fpdim j : ℂ) *
      (S.fusionCoeff i j k : ℂ)) • T k
  calc
    _ = ∑ i, ∑ j, ∑ k, f i j k := by
      simp only [Preadditive.sum_comp, Preadditive.comp_sum, Linear.smul_comp,
        Linear.comp_smul, hT, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      dsimp only [f]
      congr 1
      ring
    _ = ∑ k, ∑ i, ∑ j, f i j k := by
      calc
        _ = ∑ i, ∑ k, ∑ j, f i j k := by
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by
      dsimp only [f]
      simp only [← Finset.sum_smul]
      simp_rw [show ∀ k,
        (∑ i, ∑ j, (S.fusionBasis.fpdim i : ℂ) * (S.fusionBasis.fpdim j : ℂ) *
          (S.fusionCoeff i j k : ℂ)) =
        (S.fusionBasis.totalFPdim : ℂ) * (S.fusionBasis.fpdim k : ℂ) from
          S.fusionBasis.fpdim_regular_coefficient_complex]
      simp only [Finset.smul_sum, smul_smul]

include S in
theorem fpProjection_idempotent
    (hT : ∀ i j, T i ≫ T j = ∑ k, (S.fusionCoeff i j k : ℂ) • T k) :
    fpProjection S T ≫ fpProjection S T = fpProjection S T := by
  have hD : (S.fusionBasis.totalFPdim : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt S.fusionBasis.totalFPdim_pos)
  simp only [fpProjection, Linear.smul_comp, Linear.comp_smul, fpRegular_comp S T hT,
    smul_smul]
  congr 1
  field_simp

include S in
theorem scalarRightTrace_fpProjection (D : ℂ)
    (htrace : ∀ i, J.scalarRightTrace X (T i) = if i = S.unitLabel then D else 0) :
    J.scalarRightTrace X (fpProjection S T) = D / (S.fusionBasis.totalFPdim : ℂ) := by
  simp only [fpProjection, map_smul, map_sum, htrace, smul_eq_mul]
  have hunit : S.fusionBasis.fpdim S.unitLabel = 1 := S.fusionBasis.fpdim_one
  simp [hunit, mul_comm, div_eq_mul_inv]

/-- Once actual fusion-loop multiplication and its pivotal trace have been
proved, ratio integrality follows from splitting an explicit actual
idempotent in the original category. -/
theorem ratio_isIntegral_of_fusion_trace (D : ℂ)
    (hT : ∀ i j, T i ≫ T j = ∑ k, (S.fusionCoeff i j k : ℂ) • T k)
    (htrace : ∀ i, J.scalarRightTrace X (T i) = if i = S.unitLabel then D else 0) :
    IsIntegral ℤ (D / (S.fusionBasis.totalFPdim : ℂ)) := by
  rw [← J.scalarRightTrace_fpProjection S T D htrace]
  exact J.rightTrace_idempotent_isIntegral S _ (fpProjection_idempotent S T hT)

end Paper18.Category.PivotalStructure
