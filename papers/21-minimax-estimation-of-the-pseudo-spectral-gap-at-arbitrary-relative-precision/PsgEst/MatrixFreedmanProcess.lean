import PsgEst.MatrixFreedmanProof
import PsgEst.EdgeBridge
import PsgEst.TraceExponential

/-! The actual matrix trace-potential process on the finite terminal path
space. Definitions use the existing prefix conditional expectation and the
actual matrix exponential. No concentration theorem is postulated here. -/

open Matrix BigOperators Real Finset
namespace PsgEst
namespace MatrixFreedman

attribute [local instance] Classical.propDecidable

/-- The actual conditional law of a terminal path on a prefix atom. -/
noncomputable def prefixWeights {d m : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (t : ℕ) (Y W : Fin (m+1) → Fin d) : ℝ :=
  if samePrefix t Y W then pathProb Q.P mu W / eventProb Q.P mu (samePrefix t Y) else 0

lemma prefixWeights_nonneg {d m : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (hmu : ∀ i, 0 ≤ mu i) (t : ℕ) (Y W : Fin (m+1) → Fin d) :
    0 ≤ prefixWeights Q mu t Y W := by
  unfold prefixWeights
  split_ifs
  · exact div_nonneg (pathProb_nonneg Q.P mu Q.nonneg hmu W)
      (pathMeasure_nonneg Q.P mu Q.nonneg hmu _)
  · exact le_rfl

lemma prefixWeights_sum {d m : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (t : ℕ) (Y : Fin (m+1) → Fin d)
    (hpos : 0 < eventProb Q.P mu (samePrefix t Y)) :
    ∑ W, prefixWeights Q mu t Y W = 1 := by
  unfold prefixWeights
  have heq : (∑ W : Fin (m+1) → Fin d,
      if samePrefix t Y W then pathProb Q.P mu W / eventProb Q.P mu (samePrefix t Y) else 0) =
      eventProb Q.P mu (samePrefix t Y) / eventProb Q.P mu (samePrefix t Y) := by
    unfold eventProb pathMeasure
    rw [sum_filter]
    simp only [ite_div, zero_div, sum_div]
  rw [heq, div_self hpos.ne']

/-- Averaging matrices against the actual prefix law gives exactly the
conditional expectation in `MatrixFreedmanInput`. -/
lemma prefixWeights_matrix_mean {d m D : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (t : ℕ) (Y : Fin (m+1) → Fin d)
    (A : (Fin (m+1) → Fin d) → Matrix (Fin D) (Fin D) ℝ) :
    (∑ W, prefixWeights Q mu t Y W • A W) = pathMatrixCondExp Q mu t A Y := by
  unfold prefixWeights pathMatrixCondExp
  rw [sum_filter, smul_sum]
  apply sum_congr rfl
  intro W _
  split_ifs
  · rw [smul_smul]
    congr 1
    ring
  · simp

lemma prefixWeights_scalar_mean {d m : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (t : ℕ) (Y : Fin (m+1) → Fin d) (f : (Fin (m+1) → Fin d) → ℝ) :
    (∑ W, prefixWeights Q mu t Y W * f W) = pathScalarCondExp Q mu t f Y := by
  unfold prefixWeights pathScalarCondExp
  rw [sum_filter, mul_sum]
  apply sum_congr rfl
  intro W _
  split_ifs <;> ring

lemma partialVariation_adapted {d m D : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (Z : Fin m → (Fin (m+1) → Fin d) → Matrix (Fin D) (Fin D) ℝ)
    (k : ℕ) (Y W : Fin (m+1) → Fin d) (h : samePrefix k Y W) :
    partialVariation Q mu Z k Y = partialVariation Q mu Z k W := by
  unfold partialVariation prefixSum
  apply sum_congr rfl
  intro t _
  split_ifs with ht
  · exact pathMatrixCondExp_adapted Q mu t.val _ Y W (fun i hi => h i (by omega))
  · rfl

/-- Compensated history before the next increment. -/
noncomputable def matrixHistory {d m D : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (Z : Fin m → (Fin (m+1) → Fin d) → Matrix (Fin D) (Fin D) ℝ)
    (θ g : ℝ) (k : ℕ) (Y : Fin (m+1) → Fin d) : Matrix (Fin D) (Fin D) ℝ :=
  θ • prefixSum Z k Y - g • partialVariation Q mu Z k Y

/-- The actual trace exponential potential `tr exp(θ S_k − g V_k)`. -/
noncomputable def matrixPotential {d m D : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (Z : Fin m → (Fin (m+1) → Fin d) → Matrix (Fin D) (Fin D) ℝ)
    (θ g : ℝ) (k : ℕ) (Y : Fin (m+1) → Fin d) : ℝ :=
  traceExp (matrixHistory Q mu Z θ g k Y)

lemma matrixHistory_isHermitian {d m D : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (hmu : ∀ i, 0 ≤ mu i)
    (Z : Fin m → (Fin (m+1) → Fin d) → Matrix (Fin D) (Fin D) ℝ)
    (hZ : ∀ t Y, (Z t Y).IsHermitian) (θ g : ℝ) (k : ℕ) (Y : Fin (m+1) → Fin d) :
    (matrixHistory Q mu Z θ g k Y).IsHermitian := by
  have hS := prefixSum_isHermitian Z hZ k Y
  have hV := (partialVariation_posSemidef Q mu hmu Z hZ k Y).isHermitian
  unfold matrixHistory
  change (θ • prefixSum Z k Y - g • partialVariation Q mu Z k Y)ᴴ = _
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, star_trivial, hS.eq, hV.eq]

lemma matrixHistory_adapted {d m D : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (Z : Fin m → (Fin (m+1) → Fin d) → Matrix (Fin D) (Fin D) ℝ)
    (hadapted : ∀ t Y W, samePrefix (t.val+1) Y W → Z t Y = Z t W)
    (θ g : ℝ) (k : ℕ) (Y W : Fin (m+1) → Fin d) (h : samePrefix k Y W) :
    matrixHistory Q mu Z θ g k Y = matrixHistory Q mu Z θ g k W := by
  unfold matrixHistory
  rw [prefixSum_adapted Z hadapted k Y W h, partialVariation_adapted Q mu Z k Y W h]

lemma matrixPotential_nonneg {d m D : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (hmu : ∀ i, 0 ≤ mu i)
    (Z : Fin m → (Fin (m+1) → Fin d) → Matrix (Fin D) (Fin D) ℝ)
    (hZ : ∀ t Y, (Z t Y).IsHermitian) (θ g : ℝ) (k : ℕ) (Y : Fin (m+1) → Fin d) :
    0 ≤ matrixPotential Q mu Z θ g k Y :=
  traceExp_nonneg (matrixHistory_isHermitian Q mu hmu Z hZ θ g k Y)

@[simp] lemma matrixPotential_zero {d m D : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (Z : Fin m → (Fin (m+1) → Fin d) → Matrix (Fin D) (Fin D) ℝ)
    (θ g : ℝ) (Y : Fin (m+1) → Fin d) : matrixPotential Q mu Z θ g 0 Y = D := by
  simp [matrixPotential, matrixHistory]

lemma matrixPotential_initial_expectation {d m D : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (hsum : ∑ i, mu i = 1)
    (Z : Fin m → (Fin (m+1) → Fin d) → Matrix (Fin D) (Fin D) ℝ) (θ g : ℝ) :
    pathExpectation Q mu (matrixPotential Q mu Z θ g 0) = D := by
  unfold pathExpectation
  simp only [matrixPotential_zero, ← sum_mul, pathProb_sum Q.P mu Q.row_stoch, hsum, one_mul]

/-- Exact recursion of the actual trace potential. -/
lemma matrixPotential_step_formula {d m D : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (Z : Fin m → (Fin (m+1) → Fin d) → Matrix (Fin D) (Fin D) ℝ)
    (θ g : ℝ) (k : ℕ) (hk : k < m) (Y : Fin (m+1) → Fin d) :
    matrixPotential Q mu Z θ g (k+1) Y = traceExp
      (matrixHistory Q mu Z θ g k Y + θ • Z ⟨k,hk⟩ Y -
        g • pathMatrixCondExp Q mu k (fun W => Z ⟨k,hk⟩ W * Z ⟨k,hk⟩ W) Y) := by
  unfold matrixPotential matrixHistory
  rw [prefixSum_succ Z k hk Y, partialVariation_succ Q mu Z k hk Y]
  congr 1
  simp only [smul_add]
  abel

/-- On a prefix atom the history and predictable increment of variation are
fixed. Only the actual martingale increment remains random. -/
theorem matrixPotential_conditional_expansion {d m D : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (Z : Fin m → (Fin (m+1) → Fin d) → Matrix (Fin D) (Fin D) ℝ)
    (hadapted : ∀ t Y W, samePrefix (t.val+1) Y W → Z t Y = Z t W)
    (θ g : ℝ) (k : ℕ) (hk : k < m) (Y : Fin (m+1) → Fin d) :
    pathScalarCondExp Q mu k (matrixPotential Q mu Z θ g (k+1)) Y =
      ∑ W, prefixWeights Q mu k Y W * traceExp
        (matrixHistory Q mu Z θ g k Y + θ • Z ⟨k,hk⟩ W -
          g • pathMatrixCondExp Q mu k (fun V => Z ⟨k,hk⟩ V * Z ⟨k,hk⟩ V) Y) := by
  rw [← prefixWeights_scalar_mean]
  apply sum_congr rfl
  intro W _
  by_cases h : samePrefix k Y W
  · rw [matrixPotential_step_formula Q mu Z θ g k hk W,
      matrixHistory_adapted Q mu Z hadapted θ g k W Y (samePrefix_symm h),
      pathMatrixCondExp_adapted Q mu k _ W Y (samePrefix_symm h)]
  · simp only [prefixWeights, if_neg h, zero_mul]

lemma prefixSum_neg {Ω A : Type*} [AddCommGroup A] {m : ℕ}
    (Z : Fin m → Ω → A) (k : ℕ) (Y : Ω) :
    prefixSum (fun t W => -Z t W) k Y = -prefixSum Z k Y := by
  unfold prefixSum
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro t _
  split_ifs <;> simp

lemma partialVariation_neg {d m D : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (Z : Fin m → (Fin (m+1) → Fin d) → Matrix (Fin D) (Fin D) ℝ)
    (k : ℕ) (Y : Fin (m+1) → Fin d) :
    partialVariation Q mu (fun t W => -Z t W) k Y = partialVariation Q mu Z k Y := by
  simp only [partialVariation, neg_mul_neg]

/-- The actual joint norm event forces one of the two signed trace
potentials above the Laplace threshold. No tail probability bound is assumed. -/
theorem matrixPotential_norm_threshold {d m D : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (hmu : ∀ i, 0 ≤ mu i)
    (Z : Fin m → (Fin (m+1) → Fin d) → Matrix (Fin D) (Fin D) ℝ)
    (hZ : ∀ t Y, (Z t Y).IsHermitian)
    (θ g u v : ℝ) (hθ : 0 ≤ θ) (hg : 0 ≤ g) (hu : 0 < u)
    (Y : Fin (m+1) → Fin d) (hS : u ≤ martingaleSumNorm Z Y)
    (hV : predictableVariationNorm Q mu Z Y ≤ v) :
    exp (θ*u-g*v) ≤ matrixPotential Q mu Z θ g m Y +
      matrixPotential Q mu (fun t W => -Z t W) θ g m Y := by
  have hSm := prefixSum_isHermitian Z hZ m Y
  have hVm := (partialVariation_posSemidef Q mu hmu Z hZ m Y).isHermitian
  have hVnorm : matrixEuclideanNorm (partialVariation Q mu Z m Y) ≤ v := by
    change euclideanMatrixNorm (partialVariation Q mu Z m Y) ≤ v
    rwa [partialVariation_terminal_norm]
  have hbound (x : Fin D → ℝ) : x ⬝ᵥ (partialVariation Q mu Z m Y *ᵥ x) ≤ v*(x⬝ᵥx) := by
    have hxx : 0 ≤ x⬝ᵥx := by unfold dotProduct; exact sum_nonneg (fun i _ => mul_self_nonneg _)
    exact (le_abs_self _).trans ((matrixEuclideanNorm_quadratic_le _ x).trans
      (mul_le_mul_of_nonneg_right hVnorm hxx))
  have hnorm : u ≤ euclideanMatrixNorm (prefixSum Z m Y) := by
    simpa only [prefixSum_terminal, martingaleSumNorm] using hS
  have hp := matrixPotential_nonneg Q mu hmu Z hZ θ g m Y
  have hn := matrixPotential_nonneg Q mu hmu (fun t W => -Z t W)
    (fun t W => (hZ t W).neg) θ g m Y
  rcases norm_event_covered_by_signed_eigenvalues _ hSm u hu hnorm with hpos | hneg
  · obtain ⟨i, hi⟩ := hpos
    have h := traceExp_joint_threshold hSm hVm θ g u v hθ hg hbound i hi
    exact h.trans (le_add_of_nonneg_right hn)
  · obtain ⟨i, hi⟩ := hneg
    have h := traceExp_joint_threshold hSm.neg hVm θ g u v hθ hg hbound i hi
    have heq : traceExp (θ • (-prefixSum Z m Y) - g • partialVariation Q mu Z m Y) =
        matrixPotential Q mu (fun t W => -Z t W) θ g m Y := by
      simp only [matrixPotential, matrixHistory, prefixSum_neg, partialVariation_neg]
    rw [heq] at h
    exact h.trans (le_add_of_nonneg_left hp)

end MatrixFreedman
end PsgEst
