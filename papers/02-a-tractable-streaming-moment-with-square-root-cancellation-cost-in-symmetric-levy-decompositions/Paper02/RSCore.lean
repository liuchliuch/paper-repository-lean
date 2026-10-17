import Paper02.RudinShapiro
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.BigOperators.Intervals

noncomputable section
open scoped BigOperators
namespace Paper02.RS
open Paper02

lemma rs_step (n : ℕ) (hn : n ≠ 0) :
    rudinShapiro n = (if n % 4 = 3 then -1 else 1) * rudinShapiro (n / 2) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [rudinShapiro, adjacentOnesCount_succ, pow_add]
  split_ifs <;> simp_all [rudinShapiro]

lemma rs_even (k : ℕ) : rudinShapiro (2*k) = rudinShapiro k := by
  by_cases hk : k = 0
  · simp [hk, rudinShapiro_zero]
  · rw [rs_step _ (by omega)]
    have hm : (2*k) % 4 ≠ 3 := by omega
    have hd : 2*k/2 = k := by omega
    simp [hm, hd]

lemma rs_odd (k : ℕ) : rudinShapiro (2*k+1) = (-1:ℝ)^k * rudinShapiro k := by
  rw [rs_step _ (by omega), neg_one_pow_eq_pow_mod_two]
  have hd : (2*k+1)/2 = k := by omega
  rw [hd]
  have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases hk with hk | hk
  · have hm : (2*k+1)%4 ≠ 3 := by omega
    simp [hm, hk]
  · have hm : (2*k+1)%4 = 3 := by omega
    simp [hm, hk]

lemma sum_pairs {α : Type*} [AddCommMonoid α] (a : ℕ → α) (n : ℕ) :
    (∑ k ∈ Finset.range (2*n), a k) =
      ∑ k ∈ Finset.range n, (a (2*k) + a (2*k+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    simp [add_assoc]

/-- The even and odd subsequence decomposition of the polynomial. -/
def RP (m : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (2^m), (rudinShapiro k : ℂ) * z^k

def RQ (m : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (2^m), ((-1:ℝ)^k * rudinShapiro k : ℝ) * z^k

lemma RP_zero (z : ℂ) : RP 0 z = 1 := by simp [RP, rudinShapiro_zero]
lemma RQ_zero (z : ℂ) : RQ 0 z = 1 := by simp [RQ, rudinShapiro_zero]

lemma RP_succ (m : ℕ) (z : ℂ) : RP (m+1) z = RP m (z^2) + z * RQ m (z^2) := by
  unfold RP RQ
  rw [pow_succ, show 2^m*2=2*2^m by omega, sum_pairs]
  simp_rw [rs_even, rs_odd, pow_add, pow_mul, Complex.ofReal_mul]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  ring

lemma RQ_succ (m : ℕ) (z : ℂ) : RQ (m+1) z = RP m (z^2) - z * RQ m (z^2) := by
  unfold RP RQ
  rw [pow_succ, show 2^m*2=2*2^m by omega, sum_pairs]
  simp_rw [rs_even, rs_odd, pow_add, pow_mul, Complex.ofReal_mul]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  simp
  ring

lemma complex_parallelogram (a b : ℂ) :
    ‖a+b‖^2 + ‖a-b‖^2 = 2*(‖a‖^2+‖b‖^2) := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  ring

lemma RP_RQ_energy (m : ℕ) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖RP m z‖^2 + ‖RQ m z‖^2 = 2*(2^m:ℕ) := by
  induction m generalizing z with
  | zero => norm_num [RP_zero, RQ_zero]
  | succ m ih =>
    rw [RP_succ, RQ_succ, complex_parallelogram, norm_mul, hz, one_mul]
    have h := ih (z^2) (by simp [norm_pow, hz])
    rw [h]
    push_cast
    rw [pow_succ]
    ring

lemma RP_bound (m : ℕ) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖RP m z‖ ≤ Real.sqrt (2*(2^m:ℕ)) := by
  have he := RP_RQ_energy m z hz
  have hs := Real.sq_sqrt (show 0 ≤ 2*((2^m:ℕ):ℝ) by positivity)
  have hn := norm_nonneg (RP m z)
  have hp := Real.sqrt_nonneg (2*((2^m:ℕ):ℝ))
  nlinarith [sq_nonneg ‖RQ m z‖]

lemma RP_exp_re (m : ℕ) (t : ℝ) :
    (RP m (Complex.exp ((t:ℂ)*Complex.I))).re =
      ∑ k ∈ Finset.range (2^m), rudinShapiro k * Real.cos ((k:ℝ)*t) := by
  simp only [RP, Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Complex.exp_nat_mul]
  have he : (k:ℂ) * ((t:ℂ)*Complex.I) = (((k:ℝ)*t:ℝ):ℂ)*Complex.I := by push_cast; ring
  rw [he, Complex.exp_ofReal_mul_I_re]

lemma range_interior_decomposition (a : ℕ → ℝ) (N : ℕ) (hN : 4 ≤ N) :
    ∑ k ∈ Finset.range N, a k =
      (∑ k ∈ Finset.Icc 2 (N-2), a k) + a 0 + a 1 + a (N-1) := by
  have h : N = N-1+1 := by omega
  conv_lhs => rw [h, Finset.sum_range_succ]
  have hsplit := Finset.sum_range_add_sum_Ico a (show 2 ≤ N-1 by omega)
  have hset : Finset.Ico 2 (N-1) = Finset.Icc 2 (N-2) := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [hset] at hsplit
  have hsmall : (∑ k ∈ Finset.range 2, a k) = a 0 + a 1 := by
    simp [Finset.sum_range_succ]
  rw [hsmall] at hsplit
  linarith

lemma interior_cos_bound (m : ℕ) (t : ℝ) (hN : 4 ≤ 2^m) :
    |∑ k ∈ Finset.Icc 2 (2^m-2), rudinShapiro k * Real.cos ((k:ℝ)*t)|
      ≤ Real.sqrt (2*(2^m:ℕ)) + 3 := by
  have hb := RP_bound m (Complex.exp ((t:ℂ)*Complex.I))
    (Complex.norm_exp_ofReal_mul_I t)
  have hr := Complex.abs_re_le_norm (RP m (Complex.exp ((t:ℂ)*Complex.I)))
  rw [RP_exp_re] at hr
  have hd := range_interior_decomposition
    (fun k => rudinShapiro k * Real.cos ((k:ℝ)*t)) (2^m) hN
  have hterm (k : ℕ) : |rudinShapiro k * Real.cos ((k:ℝ)*t)| ≤ 1 := by
    rw [abs_mul, abs_rudinShapiro, one_mul]
    exact Real.abs_cos_le_one _
  have h0 := hterm 0
  have h1 := hterm 1
  have hlast := hterm (2^m-1)
  simp only [Nat.cast_zero, Nat.cast_one] at hd h0 h1
  have hsum := abs_add_le (∑ k ∈ Finset.range (2^m), rudinShapiro k * Real.cos ((k:ℝ)*t))
    (-(rudinShapiro 0 * Real.cos ((0:ℝ)*t)) - rudinShapiro 1 * Real.cos ((1:ℝ)*t)
      - rudinShapiro (2^m-1) * Real.cos (((2^m-1:ℕ):ℝ)*t))
  have htail := abs_add_le (-(rudinShapiro 0 * Real.cos ((0:ℝ)*t)))
    (-(rudinShapiro 1 * Real.cos ((1:ℝ)*t)))
  have htail2 := abs_add_le (-(rudinShapiro 0 * Real.cos ((0:ℝ)*t))
      - rudinShapiro 1 * Real.cos ((1:ℝ)*t))
    (-(rudinShapiro (2^m-1) * Real.cos (((2^m-1:ℕ):ℝ)*t)))
  simp only [abs_neg] at htail htail2
  have he : (∑ k ∈ Finset.range (2^m), rudinShapiro k * Real.cos ((k:ℝ)*t)) +
      (-(rudinShapiro 0 * Real.cos ((0:ℝ)*t)) - rudinShapiro 1 * Real.cos ((1:ℝ)*t)
      - rudinShapiro (2^m-1) * Real.cos (((2^m-1:ℕ):ℝ)*t)) =
      ∑ k ∈ Finset.Icc 2 (2^m-2), rudinShapiro k * Real.cos ((k:ℝ)*t) := by linarith
  rw [he] at hsum
  simp only [sub_eq_add_neg] at hsum htail htail2
  linarith

/-- Adjacent products encode the transitions. -/
def edge (k : ℕ) : ℝ := rudinShapiro k * rudinShapiro (k+1)

lemma edge_even (k : ℕ) : edge (2*k) = (-1:ℝ)^k := by
  rw [edge, rs_even, rs_odd]
  calc
    rudinShapiro k * ((-1:ℝ)^k * rudinShapiro k) = (-1:ℝ)^k * (rudinShapiro k * rudinShapiro k) := by ring
    _ = (-1:ℝ)^k := by rw [rudinShapiro_mul_self, mul_one]

lemma edge_odd (k : ℕ) : edge (2*k+1) = (-1:ℝ)^k * edge k := by
  unfold edge
  rw [rs_odd, show 2*k+1+1=2*(k+1) by omega, rs_even]
  ring

lemma sum_pred_pairs {α : Type*} [AddCommMonoid α] (a : ℕ → α) (n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ Finset.range (2*n-1), a k) =
      (∑ k ∈ Finset.range n, a (2*k)) +
      ∑ k ∈ Finset.range (n-1), a (2*k+1) := by
  obtain ⟨l, rfl⟩ : ∃ l, n=l+1 := ⟨n-1, by omega⟩
  rw [show 2*(l+1)-1=2*l+1 by omega, Finset.sum_range_succ,
    sum_pairs, Finset.sum_add_distrib, Finset.sum_range_succ,
    show l+1-1=l by omega]
  simp only [add_assoc, add_comm]

lemma sum_alt_even (n : ℕ) : ∑ k ∈ Finset.range (2*n), (-1:ℝ)^k = 0 := by
  rw [sum_pairs]
  apply Finset.sum_eq_zero
  intro k hk
  rw [pow_add, pow_mul]
  simp

lemma sum_alt_dyadic (m : ℕ) (hm : 1 ≤ m) :
    ∑ k ∈ Finset.range (2^m), (-1:ℝ)^k = 0 := by
  obtain ⟨l, rfl⟩ : ∃ l, m=l+1 := ⟨m-1, by omega⟩
  rw [pow_succ, Nat.mul_comm]
  exact sum_alt_even _

def C (m : ℕ) : ℝ := ∑ k ∈ Finset.range (2^m-1), edge k
def W (m : ℕ) : ℝ := ∑ k ∈ Finset.range (2^m-1), (-1:ℝ)^k * edge k

lemma CW_succ (m : ℕ) (hm : 1 ≤ m) :
    C (m+1) = W m ∧ W (m+1) = -W m := by
  have hp : 1 ≤ 2^m := Nat.one_le_two_pow
  have ha := sum_alt_dyadic m hm
  constructor
  · unfold C W
    rw [pow_succ, show 2^m*2=2*2^m by omega, sum_pred_pairs _ _ hp]
    simp_rw [edge_even, edge_odd]
    rw [ha, zero_add]
  · unfold W
    rw [pow_succ, show 2^m*2=2*2^m by omega, sum_pred_pairs _ _ hp]
    simp_rw [edge_even, edge_odd, pow_add, pow_mul]
    simp only [neg_one_sq, one_pow, one_mul, pow_one, mul_neg, mul_one, neg_mul]
    rw [ha, zero_add, Finset.sum_neg_distrib]

lemma W_one : W 1 = 1 := by norm_num [W, edge, rudinShapiro_zero, rudinShapiro_one]

lemma W_closed (m : ℕ) : W (m+1) = (-1:ℝ)^m := by
  induction m with
  | zero => simpa using W_one
  | succ m ih =>
    rw [(CW_succ (m+1) (by omega)).2, ih, pow_succ]
    ring

lemma C_closed (m : ℕ) : C (m+2) = (-1:ℝ)^m := by
  rw [show m+2=(m+1)+1 by omega, (CW_succ (m+1) (by omega)).1, W_closed]

lemma edge_last (m : ℕ) (hm : 2 ≤ m) : edge (2^m-2) = -1 := by
  obtain ⟨l, rfl⟩ : ∃ l, m=l+2 := ⟨m-2, by omega⟩
  have hn : 1 ≤ 2^(l+1) := Nat.one_le_two_pow
  rw [show 2^(l+2)-2 = 2*(2^(l+1)-1) by rw [show l+2=(l+1)+1 by omega, pow_succ]; omega,
    edge_even]
  have he : 2^(l+1)-1 = 2*(2^l-1)+1 := by
    have hp := Nat.one_le_two_pow (n:=l)
    rw [pow_succ]
    omega
  rw [he, pow_add, pow_mul]
  simp

lemma sum_Icc_one (a : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, a k) = ∑ k ∈ Finset.range n, a (k+1) := by
  have he : Finset.Icc 1 n = Finset.Ico 1 (n+1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [he, Finset.sum_Ico_eq_sub a (by omega), Finset.sum_range_succ']
  simp

def rawPair (k : ℕ) : ℝ :=
  rudinShapiro k * (rudinShapiro (k+1)-2*rudinShapiro k+rudinShapiro (k-1))

lemma rawPair_succ (k : ℕ) : rawPair (k+1) = edge (k+1)+edge k-2 := by
  unfold rawPair edge
  rw [show k+1-1=k by omega]
  nlinarith [rudinShapiro_sq (k+1)]

lemma rawPair_one : rawPair 1 = 0 := by
  norm_num [rawPair, rudinShapiro_zero, rudinShapiro_one, rudinShapiro_two]

lemma rawPair_sum (m : ℕ) (hm : 2 ≤ m) :
    (∑ k ∈ Finset.Icc 2 (2^m-2), rawPair k) = 2*C m-2*(2^m:ℕ)+4 := by
  have hN : 4 ≤ 2^m := by
    calc 4 = (2:ℕ)^2 := by norm_num
         _ ≤ 2^m := Nat.pow_le_pow_right (by omega) hm
  have hset : Finset.Icc 2 (2^m-2) = Finset.Ico 2 (2^m-1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hset1 : Finset.Icc 1 (2^m-2) = Finset.Ico 1 (2^m-1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hdrop := Finset.sum_Ico_sub_bot rawPair (show 1 < 2^m-1 by omega)
  rw [rawPair_one, sub_zero, ← hset, ← hset1] at hdrop
  rw [← hdrop, sum_Icc_one]
  simp_rw [rawPair_succ, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hs1 := Finset.sum_range_succ' edge (2^m-2)
  have hs2 := Finset.sum_range_succ edge (2^m-2)
  have he : 2^m-2+1=2^m-1 := by omega
  rw [he, ← C] at hs1 hs2
  have hzero : edge 0 = 1 := by norm_num [edge, rudinShapiro_zero, rudinShapiro_one]
  rw [hzero] at hs1
  rw [edge_last m hm] at hs2
  have hc : ((2^m-2:ℕ):ℝ) = ((2^m:ℕ):ℝ)-2 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hc]
  linarith

lemma secondDiff_f_nat (k : ℕ) (hk : 2 ≤ k) :
    secondDiff f (k:ℤ) =
      (rudinShapiro (k+1)-2*rudinShapiro k+rudinShapiro (k-1))/2 := by
  have he1 : (k:ℤ)+1 = ((k+1:ℕ):ℤ) := by omega
  have he2 : (k:ℤ)-1 = ((k-1:ℕ):ℤ) := by omega
  rw [secondDiff, he1, he2, f_nat_of_ne_zero (by omega),
    f_nat_of_ne_zero (by omega), f_nat_of_ne_zero (by omega)]
  ring

lemma pairing_eq_C (m : ℕ) (hm : 2 ≤ m) :
    (∑ k ∈ Finset.Icc 2 (2^m-2), rudinShapiro k * secondDiff f (k:ℤ))
      = C m-(2^m:ℕ)+2 := by
  have he : (∑ k ∈ Finset.Icc 2 (2^m-2), rudinShapiro k * secondDiff f (k:ℤ))
      = (∑ k ∈ Finset.Icc 2 (2^m-2), rawPair k)/2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    have hk2 := (Finset.mem_Icc.mp hk).1
    rw [secondDiff_f_nat k hk2, rawPair]
    ring
  rw [he, rawPair_sum m hm]
  ring

lemma exact_pairing_shift (m : ℕ) :
    (∑ k ∈ Finset.Icc 2 (2^(m+2)-2), rudinShapiro k * secondDiff f (k:ℤ))
      = -(2^(m+2):ℕ)+2+(-1:ℝ)^m := by
  rw [pairing_eq_C (m+2) (by omega), C_closed]
  ring

lemma exact_pairing (m : ℕ) (hN : 16 ≤ 2^m) :
    (∑ k ∈ Finset.Icc 2 (2^m-2), rudinShapiro k * secondDiff f (k:ℤ))
      = if Odd m then -((2^m:ℕ):ℝ)+1 else -((2^m:ℕ):ℝ)+3 := by
  have hm : 2 ≤ m := by
    by_contra hn
    have : m=0 ∨ m=1 := by omega
    rcases this with rfl | rfl <;> norm_num at hN
  obtain ⟨l, rfl⟩ : ∃ l, m=l+2 := ⟨m-2, by omega⟩
  rw [exact_pairing_shift]
  by_cases ho : Odd (l+2)
  · have hl : Odd l := by
      rw [Nat.odd_iff] at ho ⊢
      omega
    rw [if_pos ho, hl.neg_one_pow]
    ring
  · have hl : Even l := by
      have he : Even (l+2) := Nat.not_odd_iff_even.mp ho
      rw [Nat.even_iff] at he ⊢
      omega
    rw [if_neg ho, hl.neg_one_pow]
    ring

lemma abs_pairing_lower (m : ℕ) (hN : 16 ≤ 2^m) :
    (2^m:ℕ)-3 ≤
      |∑ k ∈ Finset.Icc 2 (2^m-2), rudinShapiro k * secondDiff f (k:ℤ)| := by
  rw [exact_pairing m hN]
  have hNr : (16:ℝ) ≤ (2^m:ℕ) := by exact_mod_cast hN
  split_ifs <;> rw [abs_of_nonpos (by linarith)] <;> linarith

end Paper02.RS
