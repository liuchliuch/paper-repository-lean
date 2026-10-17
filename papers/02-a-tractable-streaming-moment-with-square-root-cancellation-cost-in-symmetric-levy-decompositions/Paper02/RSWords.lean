import Paper02.RSCore
import Paper02.WordCounts

noncomputable section
open scoped BigOperators
namespace Paper02.RS
open Paper02

lemma neg_one_dyadic_succ (m : ℕ) : (-1:ℝ)^(2^(m+1)) = 1 := by
  rw [pow_succ', pow_mul]
  simp

/-- Prefixing an m-bit word by 10 or 11 gives the classical two blocks. -/
lemma rs_prefix_blocks (m : ℕ) : ∀ k < 2^m,
    rudinShapiro (2^(m+1)+k) = rudinShapiro k ∧
    rudinShapiro (2^(m+1)+2^m+k) = -rudinShapiro (2^m+k) := by
  induction m with
  | zero =>
    intro k hk
    have hk0 : k=0 := by simpa using hk
    subst k
    norm_num [rudinShapiro_zero, rudinShapiro_one, rudinShapiro_two, rudinShapiro_three]
  | succ m ih =>
    intro k hk
    have hq : k/2 < 2^m := by rw [pow_succ] at hk; omega
    obtain ⟨h1,h2⟩ := ih (k/2) hq
    have hpow : 2^(m+1+1)=2*2^(m+1) := by rw [pow_succ']
    have hpow' : 2^(m+1)=2*2^m := by rw [pow_succ']
    have hd : k=2*(k/2) ∨ k=2*(k/2)+1 := by omega
    rcases hd with hd | hd
    · constructor
      · rw [show 2^(m+1+1)+k=2*(2^(m+1)+k/2) by omega,
          rs_even, h1]
        conv_rhs => rw [hd, rs_even]
      · rw [show 2^(m+1+1)+2^(m+1)+k=2*(2^(m+1)+2^m+k/2) by omega,
          rs_even, h2, show 2^(m+1)+k=2*(2^m+k/2) by omega, rs_even]
    · constructor
      · rw [show 2^(m+1+1)+k=2*(2^(m+1)+k/2)+1 by omega,
          rs_odd, h1, pow_add, neg_one_dyadic_succ, one_mul]
        conv_rhs => rw [hd, rs_odd]
      · rw [show 2^(m+1+1)+2^(m+1)+k=2*(2^(m+1)+2^m+k/2)+1 by omega,
          rs_odd, h2,
          show 2^(m+1)+2^m+k/2=2^(m+1)+(2^m+k/2) by omega,
          pow_add, neg_one_dyadic_succ, one_mul,
          show 2^(m+1)+k=2*(2^m+k/2)+1 by omega, rs_odd]
        ring

/-- The coefficient words agree with the fixed overlapping-11 sequence. -/
lemma coeffsPQ_eq_rs (m : ℕ) :
    coeffsP m = (List.range (2^m)).map rudinShapiro ∧
    coeffsQ m = (List.range (2^m)).map (fun k => rudinShapiro (2^m+k)) := by
  induction m with
  | zero =>
    constructor <;> norm_num [coeffsP, coeffsQ, coeffsPQ, rudinShapiro_zero, rudinShapiro_one]
  | succ m ih =>
    obtain ⟨hp,hq⟩ := ih
    have hpw : 2^(m+1)=2^m+2^m := by rw [pow_succ]; omega
    constructor
    · rw [coeffsP_succ, hp, hq, hpw, List.range_add, List.map_append, List.map_map]
      rfl
    · rw [coeffsQ_succ, hp, hq, List.map_map]
      conv_rhs => rw [hpw, List.range_add, List.map_append, List.map_map]
      congr 1
      · apply List.map_congr_left
        intro k hk
        simpa only [hpw] using ((rs_prefix_blocks m k (List.mem_range.mp hk)).1).symm
      · apply List.map_congr_left
        intro k hk
        simpa only [Function.comp_apply, hpw, Nat.add_assoc] using
          ((rs_prefix_blocks m k (List.mem_range.mp hk)).2).symm

lemma coeffsP_eq_rs (m : ℕ) : coeffsP m = (List.range (2^m)).map rudinShapiro :=
  (coeffsPQ_eq_rs m).1

lemma coeffsQ_eq_rs (m : ℕ) :
    coeffsQ m = (List.range (2^m)).map (fun k => rudinShapiro (2^m+k)) :=
  (coeffsPQ_eq_rs m).2

/-- The paper's second polynomial, with the Q-word coefficients. -/
def SQ (m : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (2^m), (rudinShapiro (2^m+k):ℂ) * z^k

lemma RP_classical_succ (m : ℕ) (z : ℂ) :
    RP (m+1) z = RP m z + z^(2^m)*SQ m z := by
  unfold RP SQ
  rw [show 2^(m+1)=2^m+2^m by rw [pow_succ]; omega,
    Finset.sum_range_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [pow_add]
  ring

lemma SQ_zero (z : ℂ) : SQ 0 z = 1 := by simp [SQ, rudinShapiro_one]

lemma SQ_succ (m : ℕ) (z : ℂ) :
    SQ (m+1) z = RP m z - z^(2^m)*SQ m z := by
  unfold SQ RP
  conv_lhs => arg 1; arg 1; rw [show 2^(m+1)=2^m+2^m by rw [pow_succ]; omega]
  rw [Finset.sum_range_add, Finset.mul_sum]
  have hleft : (∑ k ∈ Finset.range (2^m), (rudinShapiro (2^(m+1)+k):ℂ)*z^k) =
      ∑ k ∈ Finset.range (2^m), (rudinShapiro k:ℂ)*z^k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [(rs_prefix_blocks m k (Finset.mem_range.mp hk)).1]
  rw [hleft]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Nat.add_assoc, (rs_prefix_blocks m k (Finset.mem_range.mp hk)).2,
    Complex.ofReal_neg, pow_add]
  ring

/-- The full P/Q identity (2.5), for the exact coefficient words (2.4). -/
lemma classical_energy (m : ℕ) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖RP m z‖^2 + ‖SQ m z‖^2 = 2*(2^m:ℕ) := by
  induction m with
  | zero => norm_num [RP_zero, SQ_zero]
  | succ m ih =>
    rw [RP_classical_succ, SQ_succ, complex_parallelogram, norm_mul, norm_pow, hz,
      one_pow, one_mul, ih]
    push_cast
    rw [pow_succ]
    ring

lemma classical_energy_exp (m : ℕ) (t : ℝ) :
    ‖RP m (Complex.exp ((t:ℂ)*Complex.I))‖^2 +
      ‖SQ m (Complex.exp ((t:ℂ)*Complex.I))‖^2 = 2*(2^m:ℕ) :=
  classical_energy m _ (Complex.norm_exp_ofReal_mul_I t)

lemma rs_last_shift (m : ℕ) : rudinShapiro (2^(m+1)-1) = (-1:ℝ)^m := by
  induction m with
  | zero => norm_num [rudinShapiro_one]
  | succ m ih =>
    have hp : 1 ≤ 2^(m+1) := Nat.one_le_two_pow
    have he : 2^(m+1+1)-1=2*(2^(m+1)-1)+1 := by rw [pow_succ']; omega
    rw [he, rs_odd, ih]
    have hs : (-1:ℝ)^(2^(m+1)-1) = -1 := by
      have hp0 : 1 ≤ 2^m := Nat.one_le_two_pow
      rw [show 2^(m+1)-1=2*(2^m-1)+1 by rw [pow_succ']; omega,
        pow_add, pow_mul]
      simp
    rw [hs, pow_succ]
    ring

lemma rs_penultimate_shift (m : ℕ) : rudinShapiro (2^(m+2)-2) = (-1:ℝ)^m := by
  have hp : 1 ≤ 2^(m+1) := Nat.one_le_two_pow
  rw [show 2^(m+2)-2=2*(2^(m+1)-1) by
    rw [show m+2=(m+1)+1 by omega, pow_succ']; omega, rs_even, rs_last_shift]

lemma rs_last (m : ℕ) (hm : 1 ≤ m) : rudinShapiro (2^m-1) = (-1:ℝ)^(m-1) := by
  obtain ⟨l, rfl⟩ : ∃ l, m=l+1 := ⟨m-1, by omega⟩
  simpa using rs_last_shift l

lemma rs_penultimate (m : ℕ) (hm : 2 ≤ m) : rudinShapiro (2^m-2) = (-1:ℝ)^(m-2) := by
  obtain ⟨l, rfl⟩ : ∃ l, m=l+2 := ⟨m-2, by omega⟩
  simpa using rs_penultimate_shift l

/-- The norm half of (2.5), with the classical Q-word in the proof. -/
lemma classical_bound (m : ℕ) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖RP m z‖ ≤ Real.sqrt (2*(2^m:ℕ)) := by
  have he := classical_energy m z hz
  have hs := Real.sq_sqrt (show 0 ≤ 2*((2^m:ℕ):ℝ) by positivity)
  have hn := norm_nonneg (RP m z)
  have hp := Real.sqrt_nonneg (2*((2^m:ℕ):ℝ))
  nlinarith [sq_nonneg ‖SQ m z‖]

end Paper02.RS
