import Paper37.RenewalOccupancy

/-! The true stationary renewal intensity derived from the source finite block
law, used for the completed-renewal count in Appendix F. -/
namespace Paper37.RenewalIntensity
open scoped BigOperators
open Paper37.Renewal Paper37.RenewalOccupancy

lemma count_true_positions (x : List Bool) :
    x.count true = ∑ i ∈ Finset.range x.length,
      if (x.drop i).take 1 = [true] then 1 else 0 := by
  induction x with
  | nil => simp
  | cons b x ih =>
    rw [List.length_cons,Finset.sum_range_succ']
    cases b <;> simp [List.drop_succ_cons,List.take_succ_cons,← ih]

lemma singleton_true_mass (μ : Law) : blockMass μ [true] = 1/mean μ := by
  simp [blockMass,stationaryNumerator,ordinary,tail_zero]

/-- The expected number of actual renewals in a stationary n-bit block equals
n divided by the true mean gap, with no renewal-intensity premise. -/
theorem expectedRenewalCount (μ : Law) (n : ℕ) :
    (∑ x ∈ (words n).toFinset, blockMass μ x*(x.count true:ℝ)) = (n:ℝ)/mean μ := by
  rw [← wordSum_eq_sum]
  have hrewrite : wordSum n (fun x => blockMass μ x*(x.count true:ℝ)) =
      wordSum n (fun x => ∑ i ∈ Finset.range n,
        blockMass μ x*(if (x.drop i).take 1=[true] then (1:ℝ) else 0)) := by
    apply wordSum_congr
    intro x hx
    rw [count_true_positions,hx]
    push_cast
    rw [Finset.mul_sum]
  rw [hrewrite,wordSum_finset_sum]
  have hterm : ∀ i ∈ Finset.range n, wordSum n (fun x =>
      blockMass μ x*(if (x.drop i).take 1=[true] then (1:ℝ) else 0)) = 1/mean μ := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hlen : i+[true].length+(n-i-1)=n := by simp;omega
    have hc := substring_cylinder_mass μ [true] i (n-i-1)
    rw [hlen,singleton_true_mass] at hc
    simpa only [List.length_singleton,mul_ite,mul_one,mul_zero] using hc
  calc
    (∑ i ∈ Finset.range n, wordSum n (fun x =>
      blockMass μ x*(if (x.drop i).take 1=[true] then (1:ℝ) else 0))) =
        ∑ _i ∈ Finset.range n, 1/mean μ := by
      apply Finset.sum_congr rfl
      exact hterm
    _ = _ := by simp;ring

end Paper37.RenewalIntensity
