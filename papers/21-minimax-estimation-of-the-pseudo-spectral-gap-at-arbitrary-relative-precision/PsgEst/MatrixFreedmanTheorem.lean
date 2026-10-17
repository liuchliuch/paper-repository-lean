import PsgEst.MatrixFreedmanProcess
import PsgEst.LiebConcavity

open Matrix BigOperators Real Finset
namespace PsgEst
namespace MatrixFreedman

/-- Actual trace potential contracts conditionally on each positive prefix
atom. The noncommutative step is the proved finite Lieb theorem. -/
theorem matrixPotential_conditional_le {d m D : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (hmu : ∀ i, 0 ≤ mu i)
    (Z : Fin m → (Fin (m+1) → Fin d) → Matrix (Fin D) (Fin D) ℝ)
    (R : ℝ) (hR : 0 < R) (hsa : ∀ t Y, (Z t Y).IsHermitian)
    (hadapted : ∀ t Y W, samePrefix (t.val+1) Y W → Z t Y = Z t W)
    (hcentered : ∀ t Y, pathMatrixCondExp Q mu t.val (Z t) Y = 0)
    (hbound : ∀ t Y, euclideanMatrixNorm (Z t Y) ≤ R)
    (θ : ℝ) (hθ : 0 ≤ θ) (k : ℕ) (hk : k < m) (Y : Fin (m+1) → Fin d)
    (hmass : 0 < eventProb Q.P mu (samePrefix k Y)) :
    pathScalarCondExp Q mu k (matrixPotential Q mu Z θ (bennettCoefficient R θ) (k+1)) Y ≤
      matrixPotential Q mu Z θ (bennettCoefficient R θ) k Y := by
  rw [matrixPotential_conditional_expansion Q mu Z hadapted θ (bennettCoefficient R θ) k hk Y]
  have hzero : (∑ W, prefixWeights Q mu k Y W • Z ⟨k,hk⟩ W) = 0 := by
    rw [prefixWeights_matrix_mean]
    exact hcentered ⟨k,hk⟩ Y
  have h := matrix_trace_potential_step (prefixWeights Q mu k Y)
    (prefixWeights_nonneg Q mu hmu k Y) (prefixWeights_sum Q mu k Y hmass)
    (matrixHistory Q mu Z θ (bennettCoefficient R θ) k Y)
    (matrixHistory_isHermitian Q mu hmu Z hsa θ (bennettCoefficient R θ) k Y)
    (Z ⟨k,hk⟩) (hsa ⟨k,hk⟩) θ R hθ hR (hbound ⟨k,hk⟩) hzero
  rw [prefixWeights_matrix_mean] at h
  exact h

/-- The actual trace potential has expectation at most the matrix dimension. -/
theorem matrixPotential_expectation_le_dim {d m D : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (hmu : ∀ i, 0 ≤ mu i) (hsum : ∑ i, mu i = 1)
    (Z : Fin m → (Fin (m+1) → Fin d) → Matrix (Fin D) (Fin D) ℝ)
    (R : ℝ) (hR : 0 < R) (hsa : ∀ t Y, (Z t Y).IsHermitian)
    (hadapted : ∀ t Y W, samePrefix (t.val+1) Y W → Z t Y = Z t W)
    (hcentered : ∀ t Y, pathMatrixCondExp Q mu t.val (Z t) Y = 0)
    (hbound : ∀ t Y, euclideanMatrixNorm (Z t Y) ≤ R) (θ : ℝ) (hθ : 0 ≤ θ) :
    pathExpectation Q mu (matrixPotential Q mu Z θ (bennettCoefficient R θ) m) ≤ D := by
  calc _ ≤ pathExpectation Q mu (matrixPotential Q mu Z θ (bennettCoefficient R θ) 0) :=
      path_potential_expectation_le Q mu hmu m _ (fun k hk Y hmass =>
        matrixPotential_conditional_le Q mu hmu Z R hR hsa hadapted hcentered hbound θ hθ k hk Y hmass)
    _ = D := matrixPotential_initial_expectation Q mu hsum Z θ (bennettCoefficient R θ)

end MatrixFreedman

/-- The original general finite-path matrix Freedman theorem, proved for all
self-adjoint adapted conditionally centered increments and their actual
predictable quadratic variation. No external concentration premise remains. -/
theorem matrixFreedman_proved {d : ℕ} (Q : Stoch d) (mu : Fin d → ℝ) : MatrixFreedmanInput Q mu := by
  intro m D R Z hmu hsum hR hsa hadapted hcentered hbound u v hu hv
  let θ := MatrixFreedman.optimalTheta R u v
  let g := MatrixFreedman.bennettCoefficient R θ
  let F : (Fin (m+1) → Fin d) → ℝ := fun Y =>
    MatrixFreedman.matrixPotential Q mu Z θ g m Y +
      MatrixFreedman.matrixPotential Q mu (fun t W => -Z t W) θ g m Y
  have hθ : 0 ≤ θ := (MatrixFreedman.optimalTheta_pos R u v hR hu hv).le
  have hg : 0 ≤ g := MatrixFreedman.bennettCoefficient_nonneg R θ
  obtain ⟨hnsa, hnadapted, hncentered, hnbound⟩ :=
    MatrixFreedman.neg_process_hypotheses Q mu Z R hsa hadapted hcentered hbound
  have hpos := MatrixFreedman.matrixPotential_expectation_le_dim Q mu hmu hsum Z R hR
    hsa hadapted hcentered hbound θ hθ
  have hneg := MatrixFreedman.matrixPotential_expectation_le_dim Q mu hmu hsum
    (fun t W => -Z t W) R hR hnsa hnadapted hncentered hnbound θ hθ
  have hmean : MatrixFreedman.pathExpectation Q mu F ≤ 2*(D:ℝ) := by
    unfold MatrixFreedman.pathExpectation
    simp only [F, mul_add, sum_add_distrib]
    change MatrixFreedman.pathExpectation Q mu (MatrixFreedman.matrixPotential Q mu Z θ g m) +
      MatrixFreedman.pathExpectation Q mu (MatrixFreedman.matrixPotential Q mu (fun t W => -Z t W) θ g m) ≤ _
    linarith
  have hF (Y : Fin (m+1) → Fin d) : 0 ≤ F Y :=
    add_nonneg (MatrixFreedman.matrixPotential_nonneg Q mu hmu Z hsa θ g m Y)
      (MatrixFreedman.matrixPotential_nonneg Q mu hmu (fun t W => -Z t W) hnsa θ g m Y)
  exact MatrixFreedman.eventProb_le_freedman_of_potential Q mu hmu F hF
    (fun Y => u ≤ martingaleSumNorm Z Y ∧ predictableVariationNorm Q mu Z Y ≤ v)
    (2*(D:ℝ)) R u v (by positivity) hR hu hv hmean
    (fun Y hY => MatrixFreedman.matrixPotential_norm_threshold Q mu hmu Z hsa θ g u v hθ hg hu Y hY.1 hY.2)

end PsgEst
