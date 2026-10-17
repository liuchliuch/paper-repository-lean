import Paper20.PhiQuantum
import Paper20.PolynomialEval

namespace Paper20
open Polynomial
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

theorem Dpolynomial_rec (a : ℕ) (ha : 5 ≤ a) :
    listPolynomial (Dpoly a) = (X+2)*listPolynomial (Dpoly (a-2))-
      listPolynomial (Dpoly (a-4)) := by
  rw [Dpoly_rec a ha, listPolynomial_padd, listPolynomial_pmul, listPolynomial_psmul]
  simp [listPolynomial, Phi.C_two]
  ring

variable {K : Type*} [Field K] [CharZero K]

lemma antisym_power_rec (v : K) (hv : v ≠ 0) (a : ℕ) :
    v^(a+4)-(v⁻¹)^(a+4) =
      (v^2+(v⁻¹)^2)*(v^(a+2)-(v⁻¹)^(a+2))-(v^a-(v⁻¹)^a) := by
  simp only [pow_add]
  field_simp
  ring

/-- Equation (16) for the actual D coefficient lists. The quantum integer
is specified independently by its defining numerator and denominator. -/
theorem Dpoly_quantum (a : ℕ) (ha : 1 ≤ a) (v : K) (hv : v ≠ 0) :
    (v-v⁻¹)*(if a%2=0 then v+v⁻¹ else 1)*
      aeval ((v-v⁻¹)^2) (listPolynomial (Dpoly a)) = v^a-(v⁻¹)^a := by
  induction a using Nat.strongRecOn with
  | ind a ih =>
    rcases a with _ | _ | _ | _ | _ | n
    · omega
    · simp [Dpoly, listPolynomial]
    · norm_num [Dpoly, listPolynomial]
      ring
    · norm_num [Dpoly, listPolynomial]
      field_simp
      ring
    · norm_num [Dpoly, listPolynomial]
      field_simp
      ring
    · have h3 := ih (n+3) (by omega) (by omega)
      have h1 := ih (n+1) (by omega) (by omega)
      have hp3 : (n+3)%2=0 ↔ (n+5)%2=0 := by omega
      have hp1 : (n+1)%2=0 ↔ (n+5)%2=0 := by omega
      rw [Dpolynomial_rec (n+5) (by omega),
        show n+5-2=n+3 by omega, show n+5-4=n+1 by omega]
      simp only [map_sub, map_mul, map_add, aeval_X, map_ofNat]
      rw [Phi.quantum_variable v hv]
      simp only [hp3, hp1] at h3 h1
      have he := antisym_power_rec v hv (n+1)
      rw [show n+1+4=n+5 by omega, show n+1+2=n+3 by omega] at he
      linear_combination (norm := ring_nf) (v^2+(v⁻¹)^2)*h3-h1-he

end
end Paper20
