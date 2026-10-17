import Paper14.SieveIndicatorTorus
import Paper14.BoundedProductLimits
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory Set Finset Function
namespace Paper14
noncomputable section

def admissibleResidues (M : ℕ) (q : ℤ) : Finset ℤ :=
  (Finset.Icc 1 (Int.ofNat M)).filter (fun p => IsCoprime p ((Int.gcd q (Int.ofNat M) : ℕ) : ℤ))

/-- On one period, the actual single-q indicator is exactly the disjoint
sum of admissible short interval indicators. -/
lemma sieveSingle_interval_sum (M : ℕ) (q : ℤ) {ε u : ℝ}
    (hε : ε ≤ 1) (hu : u ∈ Ioc (0 : ℝ) (M : ℝ)) :
    (sieveSingle M q ε u : ℝ) =
      ∑ p ∈ admissibleResidues M q, (Ioc ((p : ℝ)-ε) (p : ℝ)).indicator (fun _ => (1 : ℝ)) u := by
  classical
  have hceil1 : (1 : ℤ) ≤ Int.ceil u := by
    have hp : (0 : ℤ) < Int.ceil u := Int.ceil_pos.mpr hu.1
    omega
  have hceilM : Int.ceil u ≤ Int.ofNat M := Int.ceil_le.mpr hu.2
  by_cases hg : (Int.ceil u : ℝ) < u+ε ∧ IsCoprime (Int.ceil u) ((Int.gcd q (Int.ofNat M) : ℕ) : ℤ)
  · have hmem : Int.ceil u ∈ admissibleResidues M q :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hceil1,hceilM⟩,hg.2⟩
    have heq : (∑ p ∈ admissibleResidues M q, (Ioc ((p : ℝ)-ε) (p : ℝ)).indicator (fun _ => (1 : ℝ)) u) = 1 := by
      rw [Finset.sum_eq_single (Int.ceil u)]
      · rw [indicator_of_mem (show u ∈ Ioc ((Int.ceil u : ℝ)-ε) (Int.ceil u : ℝ) from
          ⟨by linarith [hg.1],Int.le_ceil u⟩)]
      · intro p hp hpne
        rw [indicator_of_notMem]
        intro hup
        have heq := narrow_band_integer_unique hε hup.2 (by linarith [hup.1])
        exact hpne heq
      · exact fun h => False.elim (h hmem)
    simp only [sieveSingle,if_pos hg,Nat.cast_one,heq]
  · simp only [sieveSingle,if_neg hg,Nat.cast_zero]
    symm
    apply Finset.sum_eq_zero
    intro p hp
    rw [indicator_of_notMem]
    intro hup
    have heq := narrow_band_integer_unique hε hup.2 (by linarith [hup.1])
    have hcop := (Finset.mem_filter.mp hp).2
    apply hg
    rw [← heq]
    exact ⟨by linarith [hup.1],hcop⟩

lemma admissible_interval_subset (M : ℕ) (q : ℤ) {ε : ℝ} (hε : ε ≤ 1)
    {p : ℤ} (hp : p ∈ admissibleResidues M q) :
    Ioc ((p : ℝ)-ε) (p : ℝ) ⊆ Ioc (0 : ℝ) (M : ℝ) := by
  have hp' := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp'.1
  have hpM : (p : ℝ) ≤ M := by exact_mod_cast hp'.2
  intro u hu
  exact ⟨by linarith [hu.1],hu.2.trans hpM⟩

/-- Exact mean of a single band indicator over one real period, before
rewriting the admissible residue count by its Euler product. -/
theorem integral_sieveSingle_period (M : ℕ) (q : ℤ) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (∫ u in Ioc (0 : ℝ) (M : ℝ), (sieveSingle M q ε u : ℝ)) =
      ε*(admissibleResidues M q).card := by
  let I := Ioc (0 : ℝ) (M : ℝ)
  letI : IsFiniteMeasure (volume.restrict I) := ⟨by simp [I,Real.volume_Ioc]⟩
  have hae : (fun u : ℝ => (sieveSingle M q ε u : ℝ)) =ᵐ[volume.restrict I]
      (fun u => ∑ p ∈ admissibleResidues M q,
        (Ioc ((p : ℝ)-ε) (p : ℝ)).indicator (fun _ => (1 : ℝ)) u) := by
    filter_upwards [ae_restrict_mem (show MeasurableSet I from measurableSet_Ioc)] with u hu
    exact sieveSingle_interval_sum M q hε1 hu
  change (∫ u, (sieveSingle M q ε u : ℝ) ∂volume.restrict I) = _
  rw [integral_congr_ae hae,integral_finset_sum]
  · have ht (p : ℤ) (hp : p ∈ admissibleResidues M q) :
        (∫ u, (Ioc ((p : ℝ)-ε) (p : ℝ)).indicator (fun _ => (1 : ℝ)) u ∂volume.restrict I) = ε := by
      change (∫ u in I, (Ioc ((p : ℝ)-ε) (p : ℝ)).indicator (fun _ => (1 : ℝ)) u) = ε
      rw [setIntegral_indicator measurableSet_Ioc,
        inter_eq_right.mpr (admissible_interval_subset M q hε1 hp),integral_const]
      simp only [Measure.real,Measure.restrict_apply_univ,Real.volume_Ioc,sub_sub_cancel,
        ENNReal.toReal_ofReal hε0,smul_eq_mul,mul_one]
    calc _ = ∑ _p ∈ admissibleResidues M q, ε := Finset.sum_congr rfl ht
         _ = _ := by simp [mul_comm]
  · intro p hp
    exact (integrable_const (1 : ℝ)).indicator measurableSet_Ioc

end
end Paper14
