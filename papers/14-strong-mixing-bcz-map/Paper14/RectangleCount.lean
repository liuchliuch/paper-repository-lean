import Paper14.LatticeCount

/-! Semantic justification of the finite box used in the rectangle count. -/
open Set
namespace Paper14

/-- Every lattice vector in the target rectangle has coefficients inside the
finite box used by `ZCount`; the artificial box loses no vector. -/
lemma rectangle_coeff_bounds {a b ε : ℝ} {n : ℕ} {p q : ℤ}
    (hx : (a, b) ∈ Omega) (hε : ε < 1)
    (hu : 1 - ε < (q : ℝ) * b - (p : ℝ) * a)
    (hu1 : (q : ℝ) * b - (p : ℝ) * a ≤ 1)
    (hv : 0 < (q : ℝ) / a) (hvn : (q : ℝ) / a ≤ 2 * n) :
    0 ≤ p ∧ p ≤ 2 * (n : ℤ) ∧ 1 ≤ q ∧ q ≤ 2 * (n : ℤ) := by
  rcases hx with ⟨ha, ha1, hb, hb1, hab⟩
  have hqpos : (0 : ℝ) < q := by
    have h := mul_pos hv ha
    rwa [div_mul_cancel₀ _ ha.ne'] at h
  have hq : (1 : ℤ) ≤ q := by exact_mod_cast (show (0 : ℤ) < q by exact_mod_cast hqpos)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqn : (q : ℝ) ≤ 2 * n * a := (div_le_iff₀ ha).mp hvn
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hqn' : (q : ℝ) ≤ 2 * n := by nlinarith
  have hqb : b ≤ (q : ℝ) * b := by nlinarith
  have hpneg : (-1 : ℝ) < p := by nlinarith
  have hp0 : (0 : ℤ) ≤ p := by
    have hp : (-1 : ℤ) < p := by exact_mod_cast hpneg
    omega
  have hppos : (0 : ℝ) ≤ p := by exact_mod_cast hp0
  have hqbupper : (q : ℝ) * b ≤ 2 * n * a := by
    have hmul := mul_le_mul_of_nonneg_left hb1 hqpos.le
    nlinarith
  have hpupper : (p : ℝ) < 2 * n := by
    have hu0 : 0 < (q : ℝ) * b - (p : ℝ) * a := by linarith
    nlinarith
  exact ⟨hp0, by exact_mod_cast hpupper.le, hq, by exact_mod_cast hqn'⟩

/-- `ZCount=0` means that no coprime integer pair supplies a vector in the
actual rectangle of Lemma 5. -/
theorem ZCount_eq_zero_iff {n : ℕ} {α : ℝ} {x : ℝ × ℝ}
    (hx : x ∈ Omega) (hα : α / n < 1) :
    ZCount n α x = 0 ↔ ¬ ∃ p q : ℤ,
      1 - α / n < (q : ℝ) * x.2 - (p : ℝ) * x.1 ∧
      (q : ℝ) * x.2 - (p : ℝ) * x.1 ≤ 1 ∧
      0 < (q : ℝ) / x.1 ∧ (q : ℝ) / x.1 ≤ 2 * n ∧ IsCoprime p q := by
  classical
  rw [ZCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h ⟨p, q, hu, hu1, hv, hvn, hcop⟩
    obtain ⟨hp0, hpn, hq1, hqn⟩ := rectangle_coeff_bounds hx hα hu hu1 hv hvn
    apply h (x := (p, q))
    · simp only [Finset.mem_product, Finset.mem_Icc]
      constructor <;> constructor <;> omega
    · refine ⟨by omega, ?_, hu, hu1, hv, hvn, hcop⟩
      exact_mod_cast hqn
  · intro h pq hpq hrect
    exact h ⟨pq.1, pq.2, hrect.2.2⟩

end Paper14
