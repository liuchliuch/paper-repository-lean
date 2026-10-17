import Paper34.Model
import Paper34.MedianWitness
import Mathlib.Algebra.MvPolynomial.CommRing

/-! Deterministic statements in Appendix A.1. The probabilistic sample count
and equivalence of LAD minimizers with medians are not asserted here. -/
namespace Paper34
noncomputable section

/-- Every source polynomial of coordinate degree zero is an actual constant. -/
theorem degree_zero_eq_C {n : ℕ} (q : PolynomialSpace n 0) :
    q.1 = MvPolynomial.C (q.1.coeff 0) := by
  have hsupport : ∀ s ∈ q.1.support, s = 0 := by
    intro s hs
    ext k
    exact Nat.eq_zero_of_le_zero ((MvPolynomial.mem_restrictDegree (Fin n) q.1 0).mp q.2 s hs k)
  apply MvPolynomial.ext
  intro s
  by_cases hs : s = 0
  · subst s; simp
  · have hn : s ∉ q.1.support := fun h => hs (hsupport s h)
    simp [MvPolynomial.notMem_support_iff.mp hn, MvPolynomial.coeff_C, hs, Ne.symm hs]

theorem degree_zero_eval_constant {n : ℕ} (q : PolynomialSpace n 0) (x : Point n) :
    polyEval q x = q.1.coeff 0 := by
  unfold polyEval
  rw [degree_zero_eq_C]
  simp

/-- Both the representative error and cell oscillation vanish at degree zero. -/
theorem degree_zero_evaluation_difference {n : ℕ} (q : PolynomialSpace n 0)
    (x z : Point n) : polyEval q x-polyEval q z = 0 := by
  simp only [degree_zero_eval_constant, sub_self]

theorem degree_zero_representative_error {n : ℕ} (q : PolynomialSpace n 0)
    (representative : Point n → Point n) :
    (∫ x, |polyEval q x-polyEval q (representative x)| ∂chebyshevLaw n) = 0 := by
  simp only [degree_zero_evaluation_difference, abs_zero, MeasureTheory.integral_zero]

/-- A strict majority of labels within sigma of a constant forces every actual
sample median to have error at most sigma. -/
theorem constant_median_error {ι : Type*} {I G : Finset ι}
    (Z : ι → ℝ) {p sigma y : ℝ} (hG : G ⊆ I)
    (hmajor : I.card < 2*G.card) (hnoise : ∀ i ∈ G, |Z i-p| ≤ sigma)
    (hmedian : IsSampleMedian I Z y) : |y-p| ≤ sigma := by
  obtain ⟨⟨im, him, hle⟩, ⟨ip, hip, hge⟩⟩ := sample_median_good_sides hG hmajor hmedian
  have hm := abs_le.mp (hnoise im him)
  have hp := abs_le.mp (hnoise ip hip)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem constant_median_exact {ι : Type*} {I G : Finset ι}
    (Z : ι → ℝ) {p y : ℝ} (hG : G ⊆ I)
    (hmajor : I.card < 2*G.card) (hnoise : ∀ i ∈ G, Z i = p)
    (hmedian : IsSampleMedian I Z y) : y = p := by
  have h := constant_median_error Z (p := p) (sigma := 0) hG hmajor
    (fun i hi => by simp [hnoise i hi]) hmedian
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h)

end
end Paper34
