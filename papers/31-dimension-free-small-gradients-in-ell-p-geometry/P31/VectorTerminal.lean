import P31.LpEstimates

/-! Actual vector-gradient form of the terminal stationarity calculation.
The continuous derivative is represented under the ordinary coordinate pairing,
while every estimate is in the paper's genuine finite ℓₚ and ℓ_q norms. -/
noncomputable section
open scoped BigOperators
namespace P31
variable {ι κ : Type*} [Fintype ι]

lemma dualExponent_ge_one {p : ℝ} (hp : 1 < p) : 1 ≤ dualExponent p := by
  unfold dualExponent
  apply (le_div_iff₀ (by linarith : 0 < p - 1)).2
  linarith

/-- Equation (4.4), derived from differentiability and true minimization of
`f + H`, with the actual shifted-power atoms of (2.4). -/
theorem vector_accumulated_stationarity {p : ℝ} (hp : 1 < p)
    (s : Finset κ) (f : (ι → ℝ) → ℝ) (α : κ → ℝ) (c : κ → ι → ℝ)
    (z grad : ι → ℝ) (hf : HasFDerivAt f (coordinateFunctional grad) z)
    (hmin : ∀ y, f z + ∑ i ∈ s, α i * powerAtom p (c i) z ≤
      f y + ∑ i ∈ s, α i * powerAtom p (c i) y) :
    grad = -(∑ i ∈ s, α i • (atomScale p • dualityMap p (z-c i))) := by
  apply coordinateFunctional_injective
  rw [coordinateFunctional_neg, coordinateFunctional_sum]
  simp_rw [coordinateFunctional_smul]
  apply accumulated_stationarity s f (fun i => powerAtom p (c i)) α z
    (coordinateFunctional grad) (fun i => atomScale p • coordinateFunctional (dualityMap p (z-c i))) hf
  · intro i hi
    have ha : HasFDerivAt (powerAtom p (c i))
        (coordinateFunctional (atomScale p • dualityMap p (z-c i))) z :=
      powerAtom_hasFDerivAt hp (c i) z
    rw [coordinateFunctional_smul] at ha
    exact ha
  · exact hmin

/-- First line of (4.6), with all vector gradients and norms explicit. -/
theorem vector_accumulated_gradient_bound {p : ℝ} (hp : 1 < p)
    (s : Finset κ) (f : (ι → ℝ) → ℝ) (α : κ → ℝ) (c : κ → ι → ℝ)
    (z grad : ι → ℝ) (hf : HasFDerivAt f (coordinateFunctional grad) z)
    (hα : ∀ i ∈ s, 0 ≤ α i)
    (hmin : ∀ y, f z + ∑ i ∈ s, α i * powerAtom p (c i) z ≤
      f y + ∑ i ∈ s, α i * powerAtom p (c i) y) :
    lpNorm (dualExponent p) grad ≤
      atomScale p * ∑ i ∈ s, α i * lpNorm p (z-c i) ^ (p-1) := by
  rw [vector_accumulated_stationarity hp s f α c z grad hf hmin, lpNorm_neg]
  calc
    lpNorm (dualExponent p) (∑ i ∈ s, α i • (atomScale p • dualityMap p (z-c i)))
      ≤ ∑ i ∈ s, lpNorm (dualExponent p) (α i • (atomScale p • dualityMap p (z-c i))) :=
        lpNorm_sum_le (dualExponent_ge_one hp) _ _
    _ = atomScale p * ∑ i ∈ s, α i * lpNorm p (z-c i) ^ (p-1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [lpNorm_smul (dualExponent_pos hp), lpNorm_smul (dualExponent_pos hp),
        abs_of_nonneg (hα i hi), abs_of_nonneg (atomScale_pos p).le,
        dualityMap_norm hp]
      ring

/-- The source's zero-query regime in its displayed vector norms. -/
theorem vector_zero_query_bound {p t L R ε : ℝ} (_hp : 1 < p)
    (grad : (ι → ℝ) → ι → ℝ) (x₀ xstar : ι → ℝ)
    (hL : 0 ≤ L) (ht : 0 ≤ t)
    (hh : ∀ x y, lpNorm (dualExponent p) (grad x-grad y) ≤ L * lpNorm p (x-y)^t)
    (hstar : grad xstar = 0) (hr : lpNorm p (x₀-xstar) ≤ R)
    (heps : L * R^t ≤ ε) : lpNorm (dualExponent p) (grad x₀) ≤ ε := by
  have h := hh x₀ xstar
  rw [hstar, sub_zero] at h
  exact h.trans ((mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (lpNorm_nonneg _ _) hr ht) hL).trans heps)

/-- The genuine ℓ_q triangle/Hölder transfer at the output. -/
theorem vector_holder_terminal_transfer {p t L δ ε : ℝ} (hp : 1 < p)
    (grad : (ι → ℝ) → ι → ℝ) (x z : ι → ℝ)
    (hL : 0 ≤ L) (ht : 0 ≤ t)
    (hh : ∀ u v, lpNorm (dualExponent p) (grad u-grad v) ≤ L * lpNorm p (u-v)^t)
    (hd : lpNorm p (x-z) ≤ δ) (hbias : lpNorm (dualExponent p) (grad z) ≤ ε/2)
    (hscale : L * δ^t ≤ ε/2) : lpNorm (dualExponent p) (grad x) ≤ ε := by
  have htransfer : lpNorm (dualExponent p) (grad x-grad z) ≤ ε/2 :=
    (hh x z).trans ((mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (lpNorm_nonneg _ _) hd ht) hL).trans hscale)
  have htriangle := lpNorm_add_le (dualExponent_ge_one hp) (grad x-grad z) (grad z)
  rw [sub_add_cancel] at htriangle
  linarith

end P31
