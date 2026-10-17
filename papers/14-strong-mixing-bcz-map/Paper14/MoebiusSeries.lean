import Paper14.MoebiusCoprime
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

open Filter Topology
namespace Paper14
noncomputable section

/-- The exact reciprocal-square Möbius density constant in the coprime
rectangle asymptotic of Appendix A. -/
theorem hasSum_moebius_invSq : HasSum
    (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℝ)/(n : ℝ)^2)
      (6/Real.pi^2) := by
  have h2 : (1 : ℝ) < (2 : ℂ).re := by norm_num
  have hmul := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius h2
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta h2,riemannZeta_two] at hmul
  have hpi : ((Real.pi : ℂ)^2/6) ≠ 0 := by
    exact div_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) (by norm_num)
  have hval : LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) 2 =
      6/(Real.pi : ℂ)^2 := by
    apply mul_left_cancel₀ hpi
    rw [hmul]
    field_simp
  have hsum := (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr h2).LSeriesHasSum
  change HasSum (LSeries.term (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) 2)
    (LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) 2) at hsum
  rw [hval] at hsum
  have hr := Complex.hasSum_re hsum
  convert hr using 1
  · funext n
    by_cases hn : n = 0
    · simp [hn,LSeries.term]
    · simp only [LSeries.term,if_neg hn,Complex.cpow_ofNat]
      have hc : (((ArithmeticFunction.moebius n : ℤ) : ℂ)/(n : ℂ)^2) =
          Complex.ofReal (((ArithmeticFunction.moebius n : ℤ) : ℝ)/(n : ℝ)^2) := by push_cast; rfl
      rw [hc,Complex.ofReal_re]
  · simp [← Complex.ofReal_pow,← Complex.ofReal_div]

theorem tsum_moebius_invSq :
    (∑' n : ℕ, ((ArithmeticFunction.moebius n : ℤ) : ℝ)/(n : ℝ)^2) = 6/Real.pi^2 :=
  hasSum_moebius_invSq.tsum_eq

end
end Paper14
