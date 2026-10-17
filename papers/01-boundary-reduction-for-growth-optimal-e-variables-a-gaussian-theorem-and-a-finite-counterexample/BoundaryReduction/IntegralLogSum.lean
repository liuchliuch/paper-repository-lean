import BoundaryReduction.ExtendedLog

open Real Set MeasureTheory
open scoped Classical ENNReal
namespace BoundaryReduction

lemma log_sum_tangent {a b A B : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hA : 0 < A) (hB : 0 < B) :
    a*log (A/B)+a-(A/B)*b ≤ a*log (a/b) := by
  have ht := mul_le_mul_of_nonneg_left
    (log_le_sub_one_of_pos (div_pos (mul_pos hA hb) (mul_pos hB ha))) ha.le
  rw [log_div (mul_pos hA hb).ne' (mul_pos hB ha).ne',
    log_mul hA.ne' hb.ne', log_mul hB.ne' ha.ne'] at ht
  have heq : a*(A*b/(B*a)-1) = (A/B)*b-a := by field_simp
  rw [heq] at ht
  rw [log_div hA.ne' hB.ne', log_div ha.ne' hb.ne']
  nlinarith

/-- Integral log-sum inequality with an arbitrary common mixing measure. -/
theorem integral_log_sum {α : Type*} [MeasurableSpace α] {P : Measure α}
    {a b : α → ℝ} (ha : ∀ x, 0 < a x) (hb : ∀ x, 0 < b x)
    (hia : Integrable a P) (hib : Integrable b P)
    (hil : Integrable (fun x => a x*log (a x/b x)) P)
    (hA : 0 < ∫ x, a x ∂P) (hB : 0 < ∫ x, b x ∂P) :
    (∫ x, a x ∂P)*log ((∫ x, a x ∂P)/(∫ x, b x ∂P)) ≤
      ∫ x, a x*log (a x/b x) ∂P := by
  let A := ∫ x, a x ∂P
  let B := ∫ x, b x ∂P
  have hi : Integrable (fun x => a x*log (A/B)+a x-(A/B)*b x) P :=
    ((hia.mul_const _).add hia).sub (hib.const_mul _)
  have h := integral_mono hi hil (fun x => log_sum_tangent (ha x) (hb x) hA hB)
  have heq : (∫ x, a x*log (A/B)+a x-(A/B)*b x ∂P) = A*log (A/B) := by
    have hs := integral_sub ((hia.mul_const (log (A/B))).add hia) (hib.const_mul (A/B))
    have hadd := integral_add (hia.mul_const (log (A/B))) hia
    simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply] at hs hadd
    rw [hs,hadd,integral_mul_const,integral_const_mul]
    change A*log (A/B)+A-(A/B)*B = A*log (A/B)
    rw [div_mul_cancel₀ _ hB.ne']
    ring
  rwa [heq] at h

end BoundaryReduction
