import Paper14.VoidLimit

open MeasureTheory Set Function Filter Topology Finset
namespace Paper14
noncomputable section

/-- The complete original Lemma 5, with its required order of quantifiers:
first choose alpha large, then take all sufficiently large n. -/
theorem Lemma5 : Lemma5Statement := by
  intro ε hε
  let d : ℝ := 6/Real.pi^2
  have hd : 0 < d := div_pos (by norm_num) (sq_pos_of_pos Real.pi_pos)
  have hKlim : Tendsto (fun K : ℕ => ((K : ℝ)⁻¹)^2) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))).pow 2
  obtain ⟨K,hK2,hKsmall⟩ := ((eventually_ge_atTop (2 : ℕ)).and
    (hKlim.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < ε/4)))).exists
  have hK : (1 : ℝ) < K := by exact_mod_cast (by omega : 1 < K)
  have hK0 : (0 : ℝ) < K := zero_lt_one.trans hK
  obtain ⟨p,hKp,hp⟩ := Nat.exists_infinite_primes K
  obtain ⟨P,hpP,hSP⟩ := ((eventually_ge_atTop p).and
    (SP_tendsto_zero.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < ε*d/8)))).exists
  have hpM : p ∣ primorial P := by
    unfold primorial
    exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hp⟩)
  have hKM : (K : ℝ) ≤ primorial P := by
    exact_mod_cast hKp.trans (Nat.le_of_dvd (primorial_pos P) hpM)
  have hδ : d ≤ deltaM P := deltaLowerBound P
  have hδ0 : 0 < deltaM P := deltaM_pos P
  have hSP0 : 0 ≤ SP P := SP_nonneg P
  have hSPsmall : 2*SP P/deltaM P < ε/4 := by
    have hdiv : 2*SP P/deltaM P ≤ 2*SP P/d :=
      div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hSP0) hd hδ
    apply hdiv.trans_lt
    apply (div_lt_iff₀ hd).mpr
    nlinarith
  let α0 : ℝ := 16*(primorial P : ℝ)*(K : ℝ)/(ε*d)
  have hα0 : 0 < α0 := by
    have hM : (0 : ℝ) < primorial P := by exact_mod_cast primorial_pos P
    exact div_pos (mul_pos (mul_pos (by norm_num) hM) hK0) (mul_pos hε hd)
  refine ⟨α0,?_⟩
  intro α hαbig
  have hα : 0 < α := hα0.trans hαbig
  have hmid : 4*(primorial P : ℝ)*(K : ℝ)/(α*deltaM P) < ε/4 := by
    have ha : 16*(primorial P : ℝ)*(K : ℝ) < α*(ε*d) :=
      (div_lt_iff₀ (mul_pos hε hd)).mp hαbig
    have hδs := mul_le_mul_of_nonneg_left hδ (mul_nonneg hα.le hε.le)
    apply (div_lt_iff₀ (mul_pos hα hδ0)).mpr
    nlinarith
  have htotal : ((K : ℝ)⁻¹)^2+4*(primorial P : ℝ)*(K : ℝ)/(α*deltaM P)+2*SP P/deltaM P < ε := by
    linarith
  exact Filter.eventually_atTop.mp (primitive_void_eventually_bound P hK hKM hα htotal)

end
end Paper14
