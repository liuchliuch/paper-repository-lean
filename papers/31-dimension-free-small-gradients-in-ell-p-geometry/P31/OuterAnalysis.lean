import P31.VectorTerminal
import P31.VectorPath
import P31.Schedule

/-! Composition of the actual vector terminal argument. The hypotheses below
are explicitly stage certificates. This is not stated as the unconditional
oracle theorem 1.2: the existence of an oracle-generated certificate sequence
still requires the one-stage algorithm and general power uniform convexity. -/
noncomputable section
open scoped BigOperators
namespace P31
open Schedule
variable {ι : Type*} [Fintype ι]

lemma radius_power_history {R p : ℝ} (hR : 0 ≤ R) (n : ℕ) :
    radius R n ^ (p-1) = R^(p-1) * theta p ^ n := by
  rw [radius, Real.div_rpow hR (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  dsimp [theta]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  rw [show (-(p-1)) * (n:ℝ) = -((n:ℝ)*(p-1)) by ring,
    Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), div_eq_mul_inv]

/-- The exact coefficient `a_p U^(p-1)` used by the vector method. -/
def vectorBiasCoefficient (p : ℝ) : ℝ := atomScale p * (3:ℝ)^(p-1)

lemma vectorBiasCoefficient_pos (p : ℝ) : 0 < vectorBiasCoefficient p :=
  mul_pos (atomScale_pos p) (Real.rpow_pos_of_pos (by norm_num) _)

/-- The full path--stationarity--Hölder proof of output accuracy from actual
stage certificates, with exactly the source's radii, increments, and stopping
stage. This theorem does not assume the terminal gradient conclusion. -/
theorem vector_outer_accuracy
    {p κ L R ε : ℝ} (hp : 2 ≤ p) (hκ : 1 < κ) (hκhi : κ ≤ 2)
    (hL : 0 < L) (hR : 0 < R) (hε : 0 < ε)
    (f : (ι → ℝ) → ℝ) (grad : (ι → ℝ) → ι → ℝ)
    (x exactMin : ℕ → ι → ℝ)
    (hgrad : ∀ y, HasFDerivAt f (coordinateFunctional (grad y)) y)
    (hholder : ∀ u v, lpNorm (dualExponent p) (grad u-grad v) ≤
      L * lpNorm p (u-v)^(κ-1))
    (hTransport : ∀ s, 1 ≤ s → s ≤ stageCount L R κ ε →
      lpNorm p (exactMin s - x (s-1)) ≤ radius R (s-1))
    (hContract : ∀ s, 1 ≤ s → s ≤ stageCount L R κ ε →
      lpNorm p (x s - exactMin s) ≤ radius R s)
    (hS : 1 ≤ stageCount L R κ ε)
    (hmin : let S := stageCount L R κ ε
      let σ₁ := initialWeight (vectorBiasCoefficient p * R^(p-1)) (theta p) (ratio κ) ε
      ∀ y, f (exactMin S) + ∑ k ∈ Finset.range S,
        alpha σ₁ (tau p κ) (k+1) * powerAtom p (x k) (exactMin S) ≤
        f y + ∑ k ∈ Finset.range S, alpha σ₁ (tau p κ) (k+1) * powerAtom p (x k) y) :
    lpNorm (dualExponent p) (grad (x (stageCount L R κ ε))) ≤ ε := by
  let S := stageCount L R κ ε
  let A := vectorBiasCoefficient p * R^(p-1)
  let σ₁ := initialWeight A (theta p) (ratio κ) ε
  let α := fun k => alpha σ₁ (tau p κ) (k+1)
  have hp1 : 1 < p := by linarith
  have hA : 0 < A := mul_pos (vectorBiasCoefficient_pos p) (Real.rpow_pos_of_pos hR _)
  have hσ : 0 < σ₁ := initialWeight_pos hA (theta_lt_one hp) (ratio_lt_one hκ) hε
  have hα (k : ℕ) : 0 ≤ α k := (alpha_pos hσ (tau_gt_one hp hκhi) (by omega)).le
  have hpath (k : ℕ) (hk : k ∈ Finset.range S) :
      lpNorm p (exactMin S-x k) ≤ 3 * radius R k := by
    have hkS : k+1 ≤ S := by simpa only [Finset.mem_range] using hk
    simpa [radius] using vector_path_bound (by linarith : 1 ≤ p) x exactMin R S hR.le
      hTransport hContract (k+1) (by omega) hkS
  have hb := vector_accumulated_gradient_bound hp1 (Finset.range S) f α x
    (exactMin S) (grad (exactMin S)) (hgrad _) (fun k _ => hα k) hmin
  have hsum : atomScale p * ∑ k ∈ Finset.range S,
      α k * lpNorm p (exactMin S-x k)^(p-1) ≤ ε/2 := by
    calc
      _ ≤ atomScale p * ∑ k ∈ Finset.range S, α k * (3*radius R k)^(p-1) := by
        apply mul_le_mul_of_nonneg_left _ (atomScale_pos p).le
        apply Finset.sum_le_sum
        intro k hk
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (lpNorm_nonneg _ _) (hpath k hk) (by linarith)) (hα k)
      _ = A * ∑ k ∈ Finset.range S, α k * theta p ^ k := by
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) (radius_pos hR k).le, radius_power_history hR.le]
        dsimp [A, vectorBiasCoefficient]
        ring
      _ ≤ ε/2 := calibrated_history_bound hp hκ hκhi hA hε S
  apply vector_holder_terminal_transfer hp1 grad (x S) (exactMin S) hL.le (by linarith)
    hholder (hContract S hS le_rfl) (hb.trans hsum)
  exact terminal_radius_bound hL hR hκ hε

end P31
