import Paper20.PhiCoefficients

namespace Paper20.Phi
open Polynomial
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

theorem even_rec (n : ℕ) : even (n+2) = (X+2)*even (n+1)-even n := by
  have h := Polynomial.Chebyshev.T_add_two ℚ (n:ℤ)
  have hc := congrArg (fun p : ℚ[X] => p.comp affine) h
  simp only [sub_comp, mul_comp, ofNat_comp, X_comp] at hc
  norm_num only [Nat.cast_ofNat] at hc
  change (T ((n:ℤ)+2)).comp affine =
    2*affine*(T ((n:ℤ)+1)).comp affine-(T (n:ℤ)).comp affine at hc
  have hs : 2*affine = (X+2:ℚ[X]) := by
    unfold affine
    have hh : (2:ℚ[X])*C (1/2:ℚ) = 1 := by
      rw [← C_two, ← C_mul]; norm_num
    linear_combination (norm := ring_nf) X*hh
  rw [hs] at hc
  simpa only [even, Nat.cast_add, Nat.cast_ofNat, T] using hc

theorem odd_rec (n : ℕ) : odd (n+2) = (X+2)*odd (n+1)-odd n := by
  have ha := Polynomial.Chebyshev.U_add_two ℚ (n:ℤ)
  have hb := Polynomial.Chebyshev.U_add_one ℚ (n:ℤ)
  have h : U ((n:ℤ)+2)-U ((n:ℤ)+1) =
      2*X*(U ((n:ℤ)+1)-U (n:ℤ))-(U (n:ℤ)-U ((n:ℤ)-1)) := by
    dsimp only [U]
    linear_combination (norm := ring_nf) ha-hb
  have hc := congrArg (fun p : ℚ[X] => p.comp affine) h
  simp only [sub_comp, mul_comp, ofNat_comp, X_comp] at hc
  norm_num only [Nat.cast_ofNat] at hc
  have hs : 2*affine = (X+2:ℚ[X]) := by
    unfold affine
    have hh : (2:ℚ[X])*C (1/2:ℚ) = 1 := by
      rw [← C_two, ← C_mul]; norm_num
    linear_combination (norm := ring_nf) X*hh
  rw [hs] at hc
  simpa only [odd, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, sub_comp,
    show (n:ℤ)+2-1=(n:ℤ)+1 by omega, show (n:ℤ)+1-1=(n:ℤ) by omega] using hc

variable {K : Type*} [Field K] [CharZero K]

lemma quantum_variable (v : K) (hv : v ≠ 0) :
    (v-v⁻¹)^2+2 = v^2+(v⁻¹)^2 := by field_simp; ring

lemma sym_power_rec (v : K) (hv : v ≠ 0) (a : ℕ) :
    v^(a+4)+(v⁻¹)^(a+4) =
      (v^2+(v⁻¹)^2)*(v^(a+2)+(v⁻¹)^(a+2))-(v^a+(v⁻¹)^a) := by
  simp only [pow_add]
  field_simp
  ring

/-- The even normalized numerator is exactly `(v^a+v^-a)/2`, with
`a=2n`, in the paper's variable `w=(v-v^-1)^2`. -/
theorem even_quantum (n : ℕ) (v : K) (hv : v ≠ 0) :
    2*(aeval ((v-v⁻¹)^2) (even n)) = v^(2*n)+(v⁻¹)^(2*n) := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [even, T]
  | one =>
    simp [even, T, affine, aeval_def, eval₂_comp]
    field_simp
    ring
  | more n ih0 ih1 =>
    rw [even_rec]
    simp only [map_sub, map_mul, map_add, aeval_X, map_ofNat]
    rw [quantum_variable v hv]
    have h := sym_power_rec v hv (2*n)
    rw [show 2*(n+1)=2*n+2 by omega] at ih1
    rw [show 2*(n+2)=2*n+4 by omega]
    linear_combination (norm := ring_nf)
      (v^2+(v⁻¹)^2)*ih1-ih0-h

/-- The odd normalization is exact without dividing by `v+v^-1`, so
the identity also holds where that factor vanishes. -/
theorem odd_quantum (n : ℕ) (v : K) (hv : v ≠ 0) :
    (v+v⁻¹)*(aeval ((v-v⁻¹)^2) (odd n)) =
      v^(2*n+1)+(v⁻¹)^(2*n+1) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [odd, U]
  | one =>
    simp [odd, U, affine, aeval_def, eval₂_comp]
    field_simp
    ring
  | more n ih0 ih1 =>
    rw [odd_rec]
    simp only [map_sub, map_mul, map_add, aeval_X, map_ofNat]
    rw [quantum_variable v hv]
    have h := sym_power_rec v hv (2*n+1)
    rw [show 2*(n+1)+1=(2*n+1)+2 by omega] at ih1
    rw [show 2*(n+2)+1=(2*n+1)+4 by omega]
    linear_combination (norm := ring_nf)
      (v^2+(v⁻¹)^2)*ih1-ih0-h

end
end Paper20.Phi
