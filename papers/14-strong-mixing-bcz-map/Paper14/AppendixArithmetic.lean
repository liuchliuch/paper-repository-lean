import Paper14.CoprimeAsymptotic
import Mathlib.Data.Nat.ModEq

open Finset
namespace Paper14
noncomputable section

/-- Equality of the determinant and of the p-block determines the integer pair. -/
lemma determinant_block_injective {q q' : ℕ} (hq : 0 < q) {p₁ p₂ p₁' p₂' : ℕ}
    (hdet : (p₁' : ℤ)*q-(p₁ : ℤ)*q' = (p₂' : ℤ)*q-(p₂ : ℤ)*q')
    (hblock : p₁/(q/Nat.gcd q q') = p₂/(q/Nat.gcd q q')) :
    p₁ = p₂ ∧ p₁' = p₂' := by
  let d := Nat.gcd q q'
  let a := q/d
  let b := q'/d
  have hd : 0 < d := Nat.gcd_pos_of_pos_left q' hq
  have ha : 0 < a := Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_left q q')) hd
  have hqd : d*a = q := Nat.mul_div_cancel' (Nat.gcd_dvd_left q q')
  have hq'd : d*b = q' := Nat.mul_div_cancel' (Nat.gcd_dvd_right q q')
  have hcop : Nat.Coprime a b := Nat.coprime_div_gcd_div_gcd hd
  have hlin : (a : ℤ)*((p₂' : ℤ)-p₁') = (b : ℤ)*((p₂ : ℤ)-p₁) := by
    have hmul : (d : ℤ)*((a : ℤ)*((p₂' : ℤ)-p₁')-(b : ℤ)*((p₂ : ℤ)-p₁)) = 0 := by
      calc
        _ = ((p₂' : ℤ)*q-(p₂ : ℤ)*q')-((p₁' : ℤ)*q-(p₁ : ℤ)*q') := by
          rw [← hqd,← hq'd]
          push_cast
          ring
        _ = 0 := by rw [hdet]; ring
    have hdZ : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hdZ)
  have hdvd : (a : ℤ) ∣ (p₂ : ℤ)-p₁ :=
    hcop.isCoprime.dvd_of_dvd_mul_left ⟨(p₂' : ℤ)-p₁',hlin.symm⟩
  have hmod : p₁ % a = p₂ % a := Nat.modEq_iff_dvd.mpr hdvd
  have hp : p₁ = p₂ := by
    have hh₁ := Nat.mod_add_div p₁ a
    have hh₂ := Nat.mod_add_div p₂ a
    change p₁/a = p₂/a at hblock
    rw [hmod,hblock] at hh₁
    omega
  refine ⟨hp,?_⟩
  rw [hp] at hdet
  have hh : (p₁' : ℤ)*q = (p₂' : ℤ)*q := by linarith
  have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  exact_mod_cast (mul_right_cancel₀ hqZ hh)

end
end Paper14
