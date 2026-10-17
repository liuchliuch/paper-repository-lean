import Paper20.PhiCoefficients
import Paper20.PolynomialEval

namespace Paper20.Phi
open Polynomial
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

lemma eval_even_step (m k j : ℕ) :
    peval (Apoly (((2*m:ℕ):ℤ)^2) true (j+1)) ((k:ℚ)*(k+1)) =
      peval (Apoly (((2*m:ℕ):ℤ)^2) true j) ((k:ℚ)*(k+1)) *
        ((((2*k+1)*m:ℕ):ℚ)^2-(j:ℚ)^2) / (2*(j+1:ℚ)*(2*j+1)) := by
  rw [peval_Apoly_succ]
  simp only [At, Bool.true_eq, ↓reduceIte, Nat.add_sub_cancel]
  rw [show 2*(j+1)-1=2*j+1 by omega]
  push_cast
  field_simp
  ring

lemma eval_odd_step (m k j : ℕ) :
    peval (Apoly (((2*m+1:ℕ):ℤ)^2) false (j+1)) ((k:ℚ)*(k+1)) =
      peval (Apoly (((2*m+1:ℕ):ℤ)^2) false j) ((k:ℚ)*(k+1)) *
        (((((2*k+1)*m+k:ℕ):ℚ)*(((2*k+1)*m+k:ℕ)+1))-
          (j:ℚ)*(j+1)) / (2*(j+1:ℚ)*(2*j+1)) := by
  rw [peval_Apoly_succ]
  simp only [At, Bool.false_eq_true, ↓reduceIte]
  rw [show 2*(j+1)-1=2*j+1 by omega]
  push_cast
  field_simp
  ring

lemma recurrence_den_ne (j : ℕ) : (2*(j+1:ℚ)*(2*j+1)) ≠ 0 := by positivity

/-- Equation (19), evaluated in the actual coefficient-list implementation,
is the normalized even quantum numerator. -/
theorem Apoly_eval_even (m k j : ℕ) :
    peval (Apoly (((2*m:ℕ):ℤ)^2) true j) ((k:ℚ)*(k+1)) =
      (even ((2*k+1)*m)).coeff j := by
  induction j with
  | zero => simp [Apoly, peval, Polynomial.coeff_zero_eq_eval_zero]
  | succ j ih =>
    rw [eval_even_step, ih]
    apply (div_eq_iff (recurrence_den_ne j)).2
    have h := even_coeff_recurrence ((2*k+1)*m) j
    linear_combination (norm := ring_nf) -h

/-- Equation (19) for odd content, with the same `Apoly` as equation (20). -/
theorem Apoly_eval_odd (m k j : ℕ) :
    peval (Apoly (((2*m+1:ℕ):ℤ)^2) false j) ((k:ℚ)*(k+1)) =
      (odd ((2*k+1)*m+k)).coeff j := by
  induction j with
  | zero => simp [Apoly, peval, Polynomial.coeff_zero_eq_eval_zero]
  | succ j ih =>
    rw [eval_odd_step, ih]
    apply (div_eq_iff (recurrence_den_ne j)).2
    have h := odd_coeff_recurrence ((2*k+1)*m+k) j
    linear_combination (norm := ring_nf) -h

/-- The normalized numerator for an absolute integral content. -/
def contentNumerator (a k : ℕ) : ℚ[X] :=
  if a%2=0 then even ((2*k+1)*(a/2)) else odd ((2*k+1)*(a/2)+k)

theorem Apoly_eval_nat (a k j : ℕ) :
    peval (Apoly ((a:ℤ)^2) (decide (a%2=0)) j) ((k:ℚ)*(k+1)) =
      (contentNumerator a k).coeff j := by
  unfold contentNumerator
  split_ifs with h
  · have ha : a = 2*(a/2) := by omega
    have hs : (a:ℤ)^2 = ((2*(a/2):ℕ):ℤ)^2 := by rw [← ha]
    rw [hs, show decide (a%2=0) = true by simp [h]]
    exact Apoly_eval_even _ _ _
  · have ha : a = 2*(a/2)+1 := by omega
    have hs : (a:ℤ)^2 = ((2*(a/2)+1:ℕ):ℤ)^2 := by rw [← ha]
    rw [hs, show decide (a%2=0) = false by simp [h]]
    exact Apoly_eval_odd _ _ _

lemma content_parity (c : ℤ) : (c%2=0) ↔ (c.natAbs%2=0) := by
  cases c with
  | ofNat a => change ((a:ℤ)%2=0) ↔ (a%2=0); omega
  | negSucc a => change (Int.negSucc a%2=0) ↔ ((a+1)%2=0); omega

/-- Actual evaluation of (19) for every signed partition content. -/
theorem Apoly_eval_content (c : ℤ) (k j : ℕ) :
    peval (Apoly (c*c) (decide (c%2=0)) j) ((k:ℚ)*(k+1)) =
      (contentNumerator c.natAbs k).coeff j := by
  have hs : c*c = (c.natAbs:ℤ)^2 := by rw [Int.natAbs_pow_two]; ring
  have hp : decide (c%2=0) = decide (c.natAbs%2=0) := by simp only [content_parity]
  rw [hs, hp]
  exact Apoly_eval_nat _ _ _

end
end Paper20.Phi
