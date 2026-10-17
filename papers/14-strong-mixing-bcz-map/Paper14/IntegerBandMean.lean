import Paper14.SieveTorusMoments

open MeasureTheory Function Set Filter
namespace Paper14
noncomputable section

/-- Uniform integer-frequency band mean, for each fixed c. This is the
conditional mean used for the sieve remainder in (19). -/
theorem integral_unit_band_integer_frequency {q : ℕ} (hq : 0 < q)
    (c : ℝ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (∫ θ in Ioc (0 : ℝ) 1, (sieveSingle 1 (q : ℤ) ε ((q : ℝ)*θ-c) : ℝ)) = ε := by
  letI : Fact (0 < ((1 : ℕ) : ℝ)) := ⟨by norm_num⟩
  let L : AddCircle ((1 : ℕ) : ℝ) →+ AddCircle ((1 : ℕ) : ℝ) := {
    toFun := fun x => (q : ℤ) • x
    map_zero' := by simp
    map_add' := by intro x y; exact smul_add _ _ _ }
  have hL : MeasurePreserving L (sieveCircleProb 1) (sieveCircleProb 1) := by
    apply AddMonoidHom.measurePreserving (by change Continuous (fun x : AddCircle ((1 : ℕ) : ℝ) => (q : ℤ) • x); fun_prop)
      (smul_right_surj_of_divisibleBy (AddCircle ((1 : ℕ) : ℝ)) ℤ (n := (q : ℤ)) (by exact_mod_cast hq.ne'))
    rfl
  have hshift : MeasurePreserving (fun x : AddCircle ((1 : ℕ) : ℝ) => x-(c : AddCircle ((1 : ℕ) : ℝ)))
      (sieveCircleProb 1) (sieveCircleProb 1) := by
    exact measurePreserving_add_right (sieveCircleProb 1) (-(c : AddCircle ((1 : ℕ) : ℝ)))
  have hmp := hshift.comp hL
  let f : AddCircle ((1 : ℕ) : ℝ) → ℝ := fun u => (sieveCircleSingle 1 (q : ℤ) ε u : ℝ)
  have hf : Measurable f := (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
    (measurable_sieveCircleSingle 1 (q : ℤ) ε)
  have hi := integral_map (μ := sieveCircleProb 1) hmp.measurable.aemeasurable hf.aestronglyMeasurable
  rw [hmp.map_eq] at hi
  have hmean : (∫ u, f u ∂sieveCircleProb 1) = ε := by
    simpa [f,varrho] using integral_sieveCircleSingle (M := 1) (by simp) q hε0 hε1
  have hPv : sieveCircleProb 1 = (volume : Measure (AddCircle ((1 : ℕ) : ℝ))) := by simp [sieveCircleProb]
  have hr := AddCircle.integral_preimage ((1 : ℕ) : ℝ) 0
    (fun θ => f ((q : ℤ) • θ-(c : AddCircle ((1 : ℕ) : ℝ))))
  simp only [zero_add,← AddCircle.coe_zsmul,← AddCircle.coe_sub,sieveCircleSingle_coe,
    zsmul_eq_mul,Int.cast_natCast,f] at hr
  have hI : Ioc (0 : ℝ) ((1 : ℕ) : ℝ) = Ioc (0 : ℝ) 1 := by norm_num
  rw [hI] at hr
  rw [hr,← hPv]
  exact hi.symm.trans hmean

end
end Paper14
