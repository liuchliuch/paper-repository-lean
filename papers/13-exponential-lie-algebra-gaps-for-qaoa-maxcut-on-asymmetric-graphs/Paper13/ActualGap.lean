import Paper13.NaturalDimension
import Paper13.MainCore
noncomputable section
namespace Paper13

/-- The dimension ratio in Theorem 1 uses the actual two Lie closures. -/
theorem theorem1_actual_ratio (k : ℕ) (hk : 7 ≤ k) :
    ((Module.finrank ℝ (graphNat (GkOrdinal k)) : ℚ) / Module.finrank ℝ (graphStd (GkOrdinal k))) ≥
      (2048/1985 : ℚ)^k-4/(15880 : ℚ)^k := by
  have hstd := Gk_std_dimension k (by omega : 1 ≤ k)
  have hpos := graphStd_finrank_pos (GkOrdinal k) (by omega : 0 < k*7)
  have hhalf : 1 ≤ (15880 : ℕ)^k/2 := by omega
  have heven : 2 ∣ (15880 : ℕ)^k := dvd_pow (by norm_num) (by omega : k≠0)
  have hcast : (((15880 : ℕ)^k/2-1 : ℕ) : ℚ)=(15880 : ℚ)^k/2-1 := by
    rw [Nat.cast_sub hhalf,Nat.cast_div heven (by norm_num)]
    push_cast
    rfl
  have hupper : (Module.finrank ℝ (graphStd (GkOrdinal k)) : ℚ) ≤ (15880 : ℚ)^k/2-1 := by
    rw [←hcast]
    exact_mod_cast hstd
  have hstdQ : (0 : ℚ) < Module.finrank ℝ (graphStd (GkOrdinal k)) := by exact_mod_cast hpos
  rw [Gk_natural_dimension k hk]
  exact (arithmetic_ratio_lower_bound k hk).trans
    (div_le_div_of_nonneg_left (by positivity) hstdQ hupper)

/-- The actual symmetry-gap ratio diverges. -/
theorem theorem1_actual_divergence : Filter.Tendsto
    (fun k : ℕ => (Module.finrank ℝ (graphNat (GkOrdinal k)) : ℚ) /
      Module.finrank ℝ (graphStd (GkOrdinal k))) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop.mpr
  intro M
  obtain ⟨k₀,hk₀⟩ := Arith.ratioBound_tendsto_atTop M
  filter_upwards [Filter.eventually_ge_atTop (max 7 k₀)] with k hk
  exact (hk₀ k (le_trans (le_max_right _ _) hk)).trans
    (theorem1_actual_ratio k (le_trans (le_max_left _ _) hk))
end Paper13
