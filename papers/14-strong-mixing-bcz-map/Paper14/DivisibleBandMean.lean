import Paper14.IntegerBandMean

open MeasureTheory Function Set Filter
namespace Paper14
noncomputable section

/-- Actual band indicator restricted to horizontal coefficients divisible
by ell; the vertical divisibility is handled separately in the sieve sum. -/
def divisibleBandSingle (ℓ : ℕ) (ε u : ℝ) : ℕ :=
  if (Int.ceil u : ℝ) < u+ε ∧ (ℓ : ℤ) ∣ Int.ceil u then 1 else 0

lemma divisibleBandSingle_eq_scaled {ℓ : ℕ} (hℓ : 0 < ℓ) (q : ℕ)
    {ε : ℝ} (hε : ε ≤ 1) (u : ℝ) :
    divisibleBandSingle ℓ ε u = sieveSingle 1 (q : ℤ) (ε/(ℓ : ℝ)) (u/(ℓ : ℝ)) := by
  have hℓr : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hη : ε/(ℓ : ℝ) ≤ 1 := (div_le_one hℓr).mpr (hε.trans hℓ1)
  have hiff : ((Int.ceil u : ℝ) < u+ε ∧ (ℓ : ℤ) ∣ Int.ceil u) ↔
      (Int.ceil (u/(ℓ : ℝ)) : ℝ) < u/(ℓ : ℝ)+ε/(ℓ : ℝ) := by
    constructor
    · rintro ⟨hband,⟨p,hp⟩⟩
      have hpR : (Int.ceil u : ℝ) = (ℓ : ℝ)*(p : ℝ) := by exact_mod_cast hp
      have hlo : u/(ℓ : ℝ) ≤ (p : ℝ) := (div_le_iff₀ hℓr).mpr (by nlinarith [Int.le_ceil u])
      have hhi : (p : ℝ) < u/(ℓ : ℝ)+ε/(ℓ : ℝ) := by
        rw [← add_div]
        exact (lt_div_iff₀ hℓr).mpr (by nlinarith)
      rw [← narrow_band_integer_unique hη hlo hhi]
      exact hhi
    · intro hband
      let p : ℤ := Int.ceil (u/(ℓ : ℝ))
      have hlo : u ≤ ((ℓ : ℤ)*p : ℤ) := by
        have hh := (div_le_iff₀ hℓr).mp (Int.le_ceil (u/(ℓ : ℝ)))
        push_cast
        nlinarith
      have hhi : (((ℓ : ℤ)*p : ℤ) : ℝ) < u+ε := by
        have hh : (p : ℝ)*(ℓ : ℝ) < u+ε := by
          apply (lt_div_iff₀ hℓr).mp
          simpa only [add_div] using hband
        push_cast
        nlinarith
      have hp : (ℓ : ℤ)*p = Int.ceil u := narrow_band_integer_unique hε hlo hhi
      exact ⟨by rw [← hp]; exact hhi,⟨p,hp.symm⟩⟩
  simp only [divisibleBandSingle,sieveSingle,Int.ofNat_eq_coe,Nat.cast_one,
    Int.gcd_one_right,Int.ofNat_one,isCoprime_one_right,and_true,hiff]

lemma measurable_divisibleBandSingle (ℓ : ℕ) (ε : ℝ) : Measurable (divisibleBandSingle ℓ ε) := by
  unfold divisibleBandSingle
  apply Measurable.ite _ measurable_const measurable_const
  apply MeasurableSet.inter
  · exact measurableSet_lt (by fun_prop) (measurable_id.add_const ε)
  · change MeasurableSet ((Int.ceil : ℝ → ℤ) ⁻¹' {p : ℤ | (ℓ : ℤ) ∣ p})
    exact Int.measurable_ceil (Set.to_countable _ |>.measurableSet)

/-- Exact fixed-c conditional mean for common-prime-divisible lattice
indices, the epsilon/ell term in source (19). -/
theorem integral_divisible_band {ℓ k : ℕ} (hℓ : 0 < ℓ) (hk : 0 < k)
    (c : ℝ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (∫ θ in Ioc (0 : ℝ) 1, (divisibleBandSingle ℓ ε (((ℓ*k : ℕ) : ℝ)*θ-c) : ℝ)) = ε/(ℓ : ℝ) := by
  have hℓr : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hη : ε/(ℓ : ℝ) ≤ 1 := (div_le_one hℓr).mpr (hε1.trans (by exact_mod_cast hℓ))
  have heq : (fun θ : ℝ => (divisibleBandSingle ℓ ε (((ℓ*k : ℕ) : ℝ)*θ-c) : ℝ)) =
      (fun θ => (sieveSingle 1 (k : ℤ) (ε/(ℓ : ℝ)) ((k : ℝ)*θ-c/(ℓ : ℝ)) : ℝ)) := by
    funext θ
    rw [divisibleBandSingle_eq_scaled hℓ k hε1]
    congr 2
    push_cast
    field_simp [hℓr.ne']
  rw [heq]
  exact integral_unit_band_integer_frequency hk (c/(ℓ : ℝ)) (div_nonneg hε0 hℓr.le) hη

end
end Paper14
