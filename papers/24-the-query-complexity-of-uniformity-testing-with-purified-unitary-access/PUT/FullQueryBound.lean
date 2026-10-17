import PUT.FourierPreparation
import PUT.QueryNorm
import PUT.SectorEstimates

/-!
# Finite expansion of the complete Fourier--Dirichlet query difference

The finite support of the actual adversary is enlarged by its one-coordinate
Fourier predecessors. Every operator equality below acts on the entire L²
space, including all radial complements. No decomposition equality or global
query norm bound is used as an external input.
-/
noncomputable section
namespace PUT.FullQueryBound
open MeasureTheory FourierModel FourierPreparation QueryModel
open scoped ENNReal InnerProductSpace ComplexConjugate

variable {d M : ℕ} {a : ℝ}

/-- Inverse of a single positive Fourier shift. -/
def unshift (n : PhaseIndex d M) (q : Coord d M) : PhaseIndex d M :=
  Function.update n q.1 (Function.update (n q.1) q.2 (n q.1 q.2 - 1))

@[simp] theorem shift_unshift (n : PhaseIndex d M) (q : Coord d M) :
    shift (unshift n q) q.1 q.2 = n := by
  funext i j
  by_cases hi : i = q.1 <;> by_cases hj : j = q.2 <;>
    simp [shift, unshift, hi, hj]

@[simp] theorem unshift_shift (n : PhaseIndex d M) (q : Coord d M) :
    unshift (shift n q.1 q.2) q = n := by
  funext i j
  by_cases hi : i = q.1 <;> by_cases hj : j = q.2 <;>
    simp [shift, unshift, hi, hj]

/-- The proved finite set of nonzero coefficients in the actual Γ. -/
def support (d M : ℕ) (A : ℝ) : Finset (PhaseIndex d M) :=
  (FiniteAdversary.support_finite d M A).toFinset

/-- Only the original support and its one-query predecessors can contribute
 to the two complete difference blocks. -/
def expandedSupport (d M : ℕ) (A : ℝ) : Finset (PhaseIndex d M) :=
  support d M A ∪ Finset.univ.biUnion (fun q : Coord d M =>
    (support d M A).image (fun n => unshift n q))

theorem support_subset_expanded (A : ℝ) : support d M A ⊆ expandedSupport d M A :=
  Finset.subset_union_left

theorem unshift_mem_expanded {A : ℝ} {n : PhaseIndex d M}
    (hn : n ∈ support d M A) (q : Coord d M) : unshift n q ∈ expandedSupport d M A := by
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  exact ⟨q, Finset.mem_univ _, Finset.mem_image.mpr ⟨n, hn, rfl⟩⟩

theorem support_subset_shift_expanded (A : ℝ) (q : Coord d M) :
    support d M A ⊆ (expandedSupport d M A).image (fun n => shift n q.1 q.2) := by
  intro n hn
  exact Finset.mem_image.mpr ⟨unshift n q, unshift_mem_expanded hn q, shift_unshift n q⟩

theorem weight_zero_of_not_support {A : ℝ} {n : PhaseIndex d M}
    (hn : n ∉ support d M A) : gammaWeight A n = 0 := by
  simpa only [support, Set.Finite.mem_toFinset, FiniteAdversary.support,
    Set.mem_setOf_eq, not_not] using hn

/-- Exact finite rank-one expansion on any finite superset of Γ's support. -/
theorem gamma_apply_finite (hd : 0 < d) (ha : 0 < a) (A : ℝ)
    (s : Finset (PhaseIndex d M)) (hs : support d M A ⊆ s) (x : AltL2 d M a) :
    gamma hd ha A x = ∑ n ∈ s, ((gammaWeight A n : ℂ) * inner ℂ (f hd ha n) x) • e n := by
  change FiniteAdversary.operator (support d M A) (gammaWeight A) e (f hd ha) x = _
  rw [FiniteAdversary.operator_apply]
  apply Finset.sum_subset hs
  intro n _ hn
  rw [weight_zero_of_not_support hn]
  simp

/-- Reindex the finite Γ expansion by the input frequency, including all
one-coordinate predecessor sectors required by an actual query. -/
theorem gamma_apply_shifted (hd : 0 < d) (ha : 0 < a) (A : ℝ)
    (q : Coord d M) (x : AltL2 d M a) :
    gamma hd ha A x = ∑ n ∈ expandedSupport d M A,
      ((gammaWeight A (shift n q.1 q.2) : ℂ) *
        inner ℂ (f hd ha (shift n q.1 q.2)) x) • e (shift n q.1 q.2) := by
  rw [gamma_apply_finite hd ha A _ (support_subset_shift_expanded A q)]
  rw [Finset.sum_image]
  intro n _ m _ h
  exact shift_injective q.1 q.2 h

section HilbertRegisters
variable {ι R E : Type*} [Fintype ι]
  [NormedAddCommGroup R] [InnerProductSpace ℂ R]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Coordinatewise isometry in the actual Hilbert direct-sum norm. -/
def registerIsometry (J : ι → R →ₗᵢ[ℂ] E) : Register ι R →ₗᵢ[ℂ] Register ι E where
  toFun x := WithLp.toLp 2 (fun i => J i (x i))
  map_add' x y := by apply WithLp.ofLp_injective; funext i; exact (J i).map_add _ _
  map_smul' c x := by apply WithLp.ofLp_injective; funext i; exact (J i).map_smul _ _
  norm_map' x := by
    change ‖WithLp.toLp 2 (fun i => J i (x i))‖ = ‖x‖
    have hs : ‖WithLp.toLp 2 (fun i => J i (x i))‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
      apply Finset.sum_congr rfl
      intro i _
      simp only [PiLp.toLp_apply, (J i).norm_map]
    nlinarith [norm_nonneg (WithLp.toLp 2 (fun i => J i (x i))), norm_nonneg x]

@[simp] theorem registerIsometry_apply (J : ι → R →ₗᵢ[ℂ] E) (x : Register ι R) (i : ι) :
    registerIsometry J x i = J i (x i) := rfl

variable [CompleteSpace R] [CompleteSpace E]

theorem registerIsometry_adjoint (J : ι → R →ₗᵢ[ℂ] E) (x : Register ι E) (i : ι) :
    (registerIsometry J).toContinuousLinearMap.adjoint x i =
      (J i).toContinuousLinearMap.adjoint (x i) := by
  have heq : (registerIsometry J).toContinuousLinearMap.adjoint x =
      WithLp.toLp 2 (fun i => (J i).toContinuousLinearMap.adjoint (x i)) := by
    apply ext_inner_left ℂ
    intro y
    rw [ContinuousLinearMap.adjoint_inner_right, PiLp.inner_apply, PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact ((J i).toContinuousLinearMap.adjoint_inner_right _ _).symm
  exact congrArg (fun z => z i) heq

end HilbertRegisters

section ScalarEmbedding
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def scalarEmbedding (v : E) (hv : ‖v‖ = 1) : ℂ →ₗᵢ[ℂ] E where
  toFun z := z • v
  map_add' := fun z w => add_smul z w v
  map_smul' := fun z w => mul_smul z w v
  norm_map' z := by
    change ‖z • v‖ = ‖z‖
    rw [norm_smul, hv, mul_one]

@[simp] theorem scalarEmbedding_apply (v : E) (hv : ‖v‖ = 1) (z : ℂ) :
    scalarEmbedding v hv z = z • v := rfl

variable [CompleteSpace E]

theorem scalarEmbedding_adjoint (v : E) (hv : ‖v‖ = 1) (x : E) :
    (scalarEmbedding v hv).toContinuousLinearMap.adjoint x = inner ℂ v x := by
  have h := (scalarEmbedding v hv).toContinuousLinearMap.adjoint_inner_right (1 : ℂ) x
  simpa [scalarEmbedding, RCLike.inner_apply] using h

end ScalarEmbedding

/-- Domain full radial sector of a `D₊` column. -/
abbrev plusInput (ha : 0 < a) (n : PhaseIndex d M) := sector ha n

/-- Output coordinates of a `D₊` column have the corresponding shifted
Fourier character; different columns are orthogonal in every coordinate. -/
def plusOutput (n : PhaseIndex d M) : EuclideanSpace ℂ (Coord d M) →ₗᵢ[ℂ]
    Register (Coord d M) (NullL2 d M) :=
  registerIsometry (fun q => scalarEmbedding (e (shift n q.1 q.2))
    ((e_orthonormal d M).norm_eq_one _))

/-- Domain of a `D₋` row is the full direct sum of its shifted radial sectors. -/
def minusInput (ha : 0 < a) (n : PhaseIndex d M) :
    Register (Coord d M) (RadialL2 d a) →ₗᵢ[ℂ] Register (Coord d M) (AltL2 d M a) :=
  registerIsometry (fun q => sector ha (shift n q.1 q.2))

/-- Scalar output Fourier character of a `D₋` row. -/
def minusOutput (n : PhaseIndex d M) : ℂ →ₗᵢ[ℂ] NullL2 d M :=
  scalarEmbedding (e n) ((e_orthonormal d M).norm_eq_one _)

theorem plusInput_orthogonal (ha : 0 < a) :
    OrthogonalFamily ℂ (fun _ : PhaseIndex d M => RadialL2 d a) (plusInput ha) :=
  QueryNorm.actual_fourier_orthogonal ha

theorem plusOutput_orthogonal :
    OrthogonalFamily ℂ (fun _ : PhaseIndex d M => EuclideanSpace ℂ (Coord d M)) plusOutput := by
  intro n m hnm x y
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro q _
  change inner ℂ ((x q) • e (shift n q.1 q.2)) ((y q) • e (shift m q.1 q.2)) = 0
  rw [inner_smul_left, inner_smul_right,
    orthonormal_iff_ite.mp (e_orthonormal d M) _ _,
    if_neg (fun h => hnm (shift_injective q.1 q.2 h))]
  simp

theorem minusInput_orthogonal (ha : 0 < a) :
    OrthogonalFamily ℂ (fun _ : PhaseIndex d M => Register (Coord d M) (RadialL2 d a))
      (minusInput ha) := by
  intro n m hnm x y
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro q _
  exact sector_orthogonal ha (fun h => hnm (shift_injective q.1 q.2 h)) (x q) (y q)

theorem minusOutput_orthogonal :
    OrthogonalFamily ℂ (fun _ : PhaseIndex d M => ℂ) minusOutput := by
  intro n m hnm x y
  change inner ℂ (x • e n) (y • e m) = 0
  rw [inner_smul_left, inner_smul_right,
    orthonormal_iff_ite.mp (e_orthonormal d M) n m, if_neg hnm]
  simp

/-- Inner products against every retained radial moment vector factor
through the adjoint of the entire Fourier sector, without deleting a complement. -/
theorem f_inner_factor (hd : 0 < d) (ha : 0 < a) (n : PhaseIndex d M)
    (x : AltL2 d M a) :
    inner ℂ (f hd ha n) x = inner ℂ (radial hd ha (degreeOf n))
      ((sector ha n).toContinuousLinearMap.adjoint x) := by
  rw [f_eq_sector_radial]
  exact ((sector ha n).toContinuousLinearMap.adjoint_inner_right _ _).symm

/-- The actual amplified adversary on the physical preparation coordinates. -/
def gammaH (hd : 0 < d) (ha : 0 < a) (A : ℝ) :
    Register (Coord d M) (AltL2 d M a) →L[ℂ] Register (Coord d M) (NullL2 d M) :=
  workspaceOperator (gamma hd ha A)

def actualPlus (hd : 0 < d) (ha : 0 < a) (hM : 0 < M) (A : ℝ) :
    AltL2 d M a →L[ℂ] Register (Coord d M) (NullL2 d M) :=
  OperatorBridge.dplus (gamma hd ha A) (gammaH hd ha A)
    (V0 hd hM).toContinuousLinearMap (V1 hd ha hM).toContinuousLinearMap

def actualMinus (hd : 0 < d) (ha : 0 < a) (hM : 0 < M) (A : ℝ) :
    Register (Coord d M) (AltL2 d M a) →L[ℂ] NullL2 d M :=
  OperatorBridge.dminus (gamma hd ha A) (gammaH hd ha A)
    (V0 hd hM).toContinuousLinearMap (V1 hd ha hM).toContinuousLinearMap

/-- Adjoint of a preparation column is the actual sum of its coordinate
adjoints. This algebraic identity does not assume Fourier completeness. -/
theorem preparation_adjoint {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {ι : Type*} [Fintype ι] (v : Preparation μ ι) (x : Register ι (Lp ℂ 2 μ)) :
    v.isometry.toContinuousLinearMap.adjoint x = ∑ q, (v.multiplier q).map.adjoint (x q) := by
  apply ext_inner_left ℂ
  intro h
  rw [ContinuousLinearMap.adjoint_inner_right, inner_sum, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro q _
  exact ((v.multiplier q).map.adjoint_inner_right h (x q)).symm

section RegisterSums
variable {ι κ E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

@[simp] theorem register_sum_apply (s : Finset κ) (v : κ → Register ι E) (q : ι) :
    (∑ k ∈ s, v k) q = ∑ k ∈ s, v k q :=
  map_sum (PiLp.proj (𝕜 := ℂ) 2 (fun _ : ι => E) q) v s

end RegisterSums

/-- The first term of `D₊` factors through the entire input Fourier sector,
using the actual coordinate adjoint, not only its action on selected vectors. -/
theorem V1_inner_factor (hd : 0 < d) (ha : 0 < a) (hM : 0 < M)
    (n : PhaseIndex d M) (q : Coord d M) (x : AltL2 d M a) :
    inner ℂ (f hd ha (shift n q.1 q.2)) (V1 hd ha hM x q) =
      ((1 / Real.sqrt M : ℝ) : ℂ) *
        inner ℂ (radial hd ha (degreeOf (shift n q.1 q.2)))
          (sqrtMultiply hd ha q.1 ((sector ha n).toContinuousLinearMap.adjoint x)) := by
  change inner ℂ (f hd ha (shift n q.1 q.2))
    (((alternativePreparation d M a hd ha hM).multiplier q).map x) = _
  rw [f_eq_sector_radial, ← ContinuousLinearMap.adjoint_inner_left,
    altMultiplier_adjoint_sector, inner_smul_left, Complex.conj_ofReal]
  congr 1
  calc
    _ = inner ℂ (sqrtMultiply hd ha q.1 (radial hd ha (degreeOf (shift n q.1 q.2))))
        ((sector ha n).toContinuousLinearMap.adjoint x) :=
      ((sector ha n).toContinuousLinearMap.adjoint_inner_right _ _).symm
    _ = _ := sqrtMultiply_inner hd ha q.1 _ _

/-- The second term of `D₊` is the finite shifted Γ sum, with no frequency
or radial completeness assumption. -/
theorem V0_gamma_apply (hd : 0 < d) (ha : 0 < a) (hM : 0 < M) (A : ℝ)
    (x : AltL2 d M a) (q : Coord d M) :
    V0 hd hM (gamma hd ha A x) q = ∑ n ∈ expandedSupport d M A,
      (((gammaWeight A n : ℂ) * inner ℂ (f hd ha n) x) *
        ((1 / (Real.sqrt d * Real.sqrt M) : ℝ) : ℂ)) • e (shift n q.1 q.2) := by
  rw [gamma_apply_finite hd ha A _ (support_subset_expanded A), map_sum,
    register_sum_apply]
  apply Finset.sum_congr rfl
  intro n _
  rw [map_smul, PiLp.smul_apply, V0_e, smul_smul]

/-- The complete `D₊` equals the finite direct sum of its full radial columns. -/
theorem actualPlus_eq_sectorOperator (hd : 0 < d) (ha : 0 < a) (hM : 0 < M) (A : ℝ) :
    actualPlus hd ha hM A = QueryNorm.sectorOperator (expandedSupport d M A)
      (plusInput ha) plusOutput (SectorEstimates.plusLocal hd ha A) := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro q
  change gamma hd ha A (V1 hd ha hM x q) - V0 hd hM (gamma hd ha A x) q = _
  rw [gamma_apply_shifted hd ha A q, V0_gamma_apply,
    QueryNorm.sectorOperator_apply, register_sum_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  change _ = (SectorEstimates.plusLocal hd ha A n
    ((sector ha n).toContinuousLinearMap.adjoint x) q) • e (shift n q.1 q.2)
  rw [V1_inner_factor, f_inner_factor, SectorEstimates.plusLocal_apply, ← sub_smul]
  congr 1
  simp only [gammaWeight, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_one]
  ring

/-- The finite-column identity yields the genuine global `D₊` norm bound. -/
theorem actualPlus_norm_le (moments : External.DirichletJointMomentLaw)
    (hd : 2 ≤ d) (ha : 0 < a) (A : ℝ) (hA : 0 < A) (hM : 0 < M) :
    ‖actualPlus (by omega : 0 < d) ha hM A‖ ≤ FullNorm.plusEnvelope a A d M := by
  rw [actualPlus_eq_sectorOperator]
  apply QueryNorm.sectorOperator_norm_le _ _ _ _
    (plusInput_orthogonal ha) plusOutput_orthogonal
  · unfold FullNorm.plusEnvelope etaM
    positivity
  · intro n _
    exact SectorEstimates.plusLocal_norm_le moments hd ha A hA hM n

/-- Coordinate adjoints reindex the finite Γ sum exactly; this is the
second term in the complete erasure block. -/
theorem null_adjoint_gamma (hd : 0 < d) (ha : 0 < a) (hM : 0 < M) (A : ℝ)
    (x : AltL2 d M a) (q : Coord d M) :
    ((nullPreparation d M hd hM).multiplier q).map.adjoint (gamma hd ha A x) =
      ∑ n ∈ expandedSupport d M A,
        (((gammaWeight A (shift n q.1 q.2) : ℂ) *
          inner ℂ (f hd ha (shift n q.1 q.2)) x) *
          ((1 / (Real.sqrt d * Real.sqrt M) : ℝ) : ℂ)) • e n := by
  rw [gamma_apply_shifted hd ha A q, map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [map_smul, nullMultiplier_adjoint_e, smul_smul]

/-- Exact finite row expansion of `V₀† (Γ ⊗ I)` on arbitrary query-register
inputs, including every Fourier/radial complement. -/
theorem V0_adjoint_gammaH (hd : 0 < d) (ha : 0 < a) (hM : 0 < M) (A : ℝ)
    (x : Register (Coord d M) (AltL2 d M a)) :
    (V0 hd hM).toContinuousLinearMap.adjoint (gammaH hd ha A x) =
      ∑ n ∈ expandedSupport d M A,
        (∑ q : Coord d M, ((gammaWeight A (shift n q.1 q.2) : ℂ) *
          inner ℂ (f hd ha (shift n q.1 q.2)) (x q)) *
          ((1 / (Real.sqrt d * Real.sqrt M) : ℝ) : ℂ)) • e n := by
  change (nullPreparation d M hd hM).isometry.toContinuousLinearMap.adjoint
    (gammaH hd ha A x) = _
  rw [preparation_adjoint]
  change (∑ q : Coord d M,
    ((nullPreparation d M hd hM).multiplier q).map.adjoint (gamma hd ha A (x q))) = _
  simp_rw [null_adjoint_gamma hd ha hM A]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  rw [Finset.sum_smul]

/-- The first erasure term, on the whole query-register input, factors
through its complete shifted radial input sectors. -/
theorem V1_adjoint_inner (hd : 0 < d) (ha : 0 < a) (hM : 0 < M)
    (n : PhaseIndex d M) (x : Register (Coord d M) (AltL2 d M a)) :
    inner ℂ (f hd ha n) ((V1 hd ha hM).toContinuousLinearMap.adjoint x) =
      ∑ q : Coord d M, ((1 / Real.sqrt M : ℝ) : ℂ) *
        inner ℂ (sqrtMultiply hd ha q.1 (radial hd ha (degreeOf n)))
          ((sector ha (shift n q.1 q.2)).toContinuousLinearMap.adjoint (x q)) := by
  rw [ContinuousLinearMap.adjoint_inner_right, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro q _
  change inner ℂ (V1 hd ha hM (f hd ha n) q) (x q) = _
  rw [f_eq_sector_radial, V1_sector, inner_smul_left, Complex.conj_ofReal]
  congr 1
  exact ((sector ha (shift n q.1 q.2)).toContinuousLinearMap.adjoint_inner_right _ _).symm

/-- The actual full `D₋` row applied to the sector-adjoint coordinates. -/
theorem minusLocal_factor (hd : 0 < d) (ha : 0 < a) (A : ℝ) (n : PhaseIndex d M)
    (x : Register (Coord d M) (AltL2 d M a)) :
    SectorEstimates.minusLocal hd ha A n ((minusInput ha n).toContinuousLinearMap.adjoint x) =
      ∑ q : Coord d M, ((1 / Real.sqrt M : ℝ) : ℂ) *
        ((gammaWeight A n : ℂ) *
          inner ℂ (sqrtMultiply hd ha q.1 (radial hd ha (degreeOf n)))
            ((sector ha (shift n q.1 q.2)).toContinuousLinearMap.adjoint (x q)) -
          ((gammaWeight A (shift n q.1 q.2) / Real.sqrt d : ℝ) : ℂ) *
          inner ℂ (radial hd ha (degreeOf (shift n q.1 q.2)))
            ((sector ha (shift n q.1 q.2)).toContinuousLinearMap.adjoint (x q))) := by
  change inner ℂ (SectorEstimates.minusVector hd ha A n)
    ((minusInput ha n).toContinuousLinearMap.adjoint x) = _
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro q _
  change inner ℂ (SectorEstimates.minusVector hd ha A n q)
    ((registerIsometry (fun q : Coord d M => sector ha (shift n q.1 q.2))).toContinuousLinearMap.adjoint x q) = _
  rw [registerIsometry_adjoint, SectorEstimates.minusVector_apply,
    inner_smul_left, inner_sub_left, inner_smul_left, inner_smul_left]
  simp only [Complex.conj_ofReal, gammaWeight]

/-- The entire actual `D₋` equals the finite sum of whole radial row blocks. -/
theorem actualMinus_eq_sectorOperator (hd : 0 < d) (ha : 0 < a) (hM : 0 < M) (A : ℝ) :
    actualMinus hd ha hM A = QueryNorm.sectorOperator (expandedSupport d M A)
      (minusInput ha) minusOutput (SectorEstimates.minusLocal hd ha A) := by
  apply ContinuousLinearMap.ext
  intro x
  change gamma hd ha A ((V1 hd ha hM).toContinuousLinearMap.adjoint x) -
    (V0 hd hM).toContinuousLinearMap.adjoint (gammaH hd ha A x) = _
  rw [gamma_apply_finite hd ha A _ (support_subset_expanded A), V0_adjoint_gammaH,
    QueryNorm.sectorOperator_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  change _ = (SectorEstimates.minusLocal hd ha A n
    ((minusInput ha n).toContinuousLinearMap.adjoint x)) • e n
  rw [← sub_smul, minusLocal_factor, V1_adjoint_inner]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _
  rw [f_inner_factor]
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_one]
  ring

/-- Finite row orthogonality and the proved whole-sector estimate bound the
actual complete `D₋` operator. -/
theorem actualMinus_norm_le (moments : External.DirichletJointMomentLaw)
    (hd : 2 ≤ d) (ha : 0 < a) (A : ℝ) (hA : 0 < A) (hM : 0 < M) :
    ‖actualMinus (by omega : 0 < d) ha hM A‖ ≤ FullNorm.minusEnvelope a A d M := by
  rw [actualMinus_eq_sectorOperator]
  apply QueryNorm.sectorOperator_norm_le _ _ _ _
    (minusInput_orthogonal ha) minusOutput_orthogonal
  · unfold FullNorm.minusEnvelope etaM
    positivity
  · intro n _
    exact SectorEstimates.minusLocal_norm_le moments hd ha A hA hM n

/-- Paper Lemma 1 for the actual Fourier--Dirichlet adversary and actual
reflection preparation operators on their full Hilbert spaces. The local
block identities and bounds used here are theorems, not hypotheses. -/
theorem query_norm_le_printed (moments : External.DirichletJointMomentLaw)
    (hd : 2 ≤ d) (ha : 0 < a) (A : ℝ) (hA : 1 ≤ A)
    (hM : 16 * A ^ 2 * LA A ≤ (M : ℝ)) :
    ‖OperatorBridge.liftedAdversary
        (gamma (M := M) (by omega : 0 < d) ha A)
        (gammaH (M := M) (by omega : 0 < d) ha A) ∘L
        OperatorBridge.reflectionBlock
          (V1 (M := M) (by omega : 0 < d) ha
            (by exact_mod_cast M_pos_of_param A M hA hM)).toContinuousLinearMap -
      OperatorBridge.reflectionBlock
          (V0 (M := M) (by omega : 0 < d)
            (by exact_mod_cast M_pos_of_param A M hA hM)).toContinuousLinearMap ∘L
        OperatorBridge.liftedAdversary
          (gamma (M := M) (by omega : 0 < d) ha A)
          (gammaH (M := M) (by omega : 0 < d) ha A)‖ ≤ lemma1RHS A a d := by
  have hMpos : 0 < M := by exact_mod_cast M_pos_of_param A M hA hM
  apply FullNorm.query_norm_le _ _ (V0 (by omega : 0 < d) hMpos)
    (V1 (by omega : 0 < d) ha hMpos) a A d M ha hA (by positivity) hM
  · exact actualPlus_norm_le moments hd ha A (by linarith) hMpos
  · exact actualMinus_norm_le moments hd ha A (by linarith) hMpos

end PUT.FullQueryBound
