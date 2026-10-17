import GeometricMedianCoresets.Threshold

/-! The literal mathlib `IsTheta` conclusions as ε tends to zero from above. -/
noncomputable section
open Filter
open scoped Topology
namespace GeometricMedianCoresets

lemma theta_of_threshold_bounds (f : ℝ → ℝ)
    (hf : ∀ ε, 0 < ε → ε ≤ 1/100 →
      1 / (24200 * ε ^ 2) < f ε ∧ f ε ≤ 21 / ε ^ 2)
    (hnonneg : ∀ ε, 0 ≤ f ε) :
    Asymptotics.IsTheta (𝓝[>] (0:ℝ)) f (fun ε => 1 / ε ^ 2) := by
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < 1/100 := by
    have h : ∀ᶠ ε : ℝ in 𝓝 0, ε < 1/100 :=
      Iio_mem_nhds (by norm_num : (0:ℝ) < 1/100)
    exact h.filter_mono nhdsWithin_le_nhds
  constructor
  · apply Asymptotics.IsBigO.of_bound 21
    filter_upwards [hpos, hsmall] with ε hp hs
    have h := (hf ε hp hs.le).2
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg ε), Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ 1 / ε ^ 2)]
    convert h using 1 <;> ring
  · apply Asymptotics.IsBigO.of_bound 24200
    filter_upwards [hpos, hsmall] with ε hp hs
    have h := (hf ε hp hs.le).1.le
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / ε ^ 2),
      Real.norm_eq_abs, abs_of_nonneg (hnonneg ε)]
    calc 1 / ε ^ 2 = 24200 * (1 / (24200 * ε ^ 2)) := by ring
      _ ≤ 24200 * f ε := mul_le_mul_of_nonneg_left h (by norm_num)

/-- Theorem 1.2: `m₂(ε) = Θ(ε⁻²)` with the least valid threshold from §1.1. -/
theorem Euclidean.sample_complexity_theta :
    Asymptotics.IsTheta (𝓝[>] (0:ℝ)) (fun ε => (Euclidean.threshold ε : ℝ))
      (fun ε => 1 / ε ^ 2) :=
  theta_of_threshold_bounds _ (fun _ => Euclidean.threshold_bounds) (fun _ => Nat.cast_nonneg _)

/-- Corollary 4.2: `m₁(ε) = Θ(ε⁻²)` for the actual finite-dimensional ℓ₁ costs. -/
theorem L1.sample_complexity_theta :
    Asymptotics.IsTheta (𝓝[>] (0:ℝ)) (fun ε => (L1.threshold ε : ℝ))
      (fun ε => 1 / ε ^ 2) :=
  theta_of_threshold_bounds _ (fun _ => L1.threshold_bounds) (fun _ => Nat.cast_nonneg _)

end GeometricMedianCoresets
