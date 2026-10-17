import Paper25.Basic
import Paper25.Bias
import Mathlib.Data.Nat.Log

/-!
Resource arithmetic for the construction in Sections 3–4.

The clock is the *least* power of two above `T + 1`, rather than the
exponentially larger `2^(T+1)` used by the old numerical certificate.
The conclusions below concern actual functions of input length. They do not
assert that a gate generator or a spectral-filter circuit has been constructed.
-/

noncomputable section

namespace Paper25

/-- Bits needed to index `N` values. -/
def ceilLog2 (N : ℕ) : ℕ := Nat.clog 2 N

/-- Least power of two at least `N`. -/
def powerTwoCeil (N : ℕ) : ℕ := 2 ^ ceilLog2 N

lemma le_powerTwoCeil (N : ℕ) : N ≤ powerTwoCeil N :=
  Nat.le_pow_clog (by decide) N

lemma powerTwoCeil_pos (N : ℕ) : 0 < powerTwoCeil N := by
  exact Nat.two_pow_pos _

lemma powerTwoCeil_minimal (N r : ℕ) (h : N ≤ 2 ^ r) :
    powerTwoCeil N ≤ 2 ^ r := by
  exact Nat.pow_le_pow_right (by decide)
    ((Nat.clog_le_iff_le_pow (by decide)).2 h)

lemma powerTwoCeil_le_twice {N : ℕ} (hN : 0 < N) : powerTwoCeil N ≤ 2 * N := by
  by_cases h : N = 1
  · subst N
    norm_num [powerTwoCeil, ceilLog2]
  have hN1 : 1 < N := by omega
  have hcl : 0 < Nat.clog 2 N := Nat.clog_pos (by decide) hN1
  have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hN1
  simp only [Nat.pred_eq_sub_one] at hp
  have he : Nat.clog 2 N = (Nat.clog 2 N - 1) + 1 := by omega
  unfold powerTwoCeil ceilLog2
  rw [he, pow_succ]
  omega

namespace IsPoly

lemma const (a : ℕ) : IsPoly (fun _ => a) := by
  refine ⟨0, (a : ℝ) + 1, by positivity, ?_⟩
  intro n
  simp only [pow_zero, mul_one]
  linarith

lemma mono {f g : ℕ → ℕ} (hg : IsPoly g) (hfg : ∀ n, f n ≤ g n) : IsPoly f := by
  obtain ⟨q, C, hC, h⟩ := hg
  exact ⟨q, C, hC, fun n => (Nat.cast_le.mpr (hfg n)).trans (h n)⟩

lemma mul {f g : ℕ → ℕ} (hf : IsPoly f) (hg : IsPoly g) :
    IsPoly (fun n => f n * g n) := by
  obtain ⟨q, C, hC, hf⟩ := hf
  obtain ⟨r, D, hD, hg⟩ := hg
  refine ⟨q + r, C * D, mul_pos hC hD, ?_⟩
  intro n
  push_cast
  calc
    (f n : ℝ) * g n ≤ (C * ((n : ℝ) + 1) ^ q) * (D * ((n : ℝ) + 1) ^ r) :=
      mul_le_mul (hf n) (hg n) (by positivity) (by positivity)
    _ = C * D * ((n : ℝ) + 1) ^ (q + r) := by rw [pow_add]; ring

lemma pow {f : ℕ → ℕ} (hf : IsPoly f) (r : ℕ) : IsPoly (fun n => f n ^ r) := by
  induction r with
  | zero => simpa using const 1
  | succ r ih => simpa [pow_succ] using ih.mul hf

lemma add {f g : ℕ → ℕ} (hf : IsPoly f) (hg : IsPoly g) :
    IsPoly (fun n => f n + g n) := by
  obtain ⟨q, C, hC, hf⟩ := hf
  obtain ⟨r, D, hD, hg⟩ := hg
  refine ⟨q + r, C + D, add_pos hC hD, ?_⟩
  intro n
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hq := pow_le_pow_right₀ hn (Nat.le_add_right q r)
  have hr := pow_le_pow_right₀ hn (Nat.le_add_left r q)
  push_cast
  calc
    (f n : ℝ) + g n ≤ C * ((n : ℝ) + 1) ^ q + D * ((n : ℝ) + 1) ^ r :=
      add_le_add (hf n) (hg n)
    _ ≤ C * ((n : ℝ) + 1) ^ (q + r) + D * ((n : ℝ) + 1) ^ (q + r) :=
      add_le_add (mul_le_mul_of_nonneg_left hq hC.le)
        (mul_le_mul_of_nonneg_left hr hD.le)
    _ = (C + D) * ((n : ℝ) + 1) ^ (q + r) := by ring

lemma powerTwoCeil {f : ℕ → ℕ} (hf : IsPoly f) (hpos : ∀ n, 0 < f n) :
    IsPoly (fun n => Paper25.powerTwoCeil (f n)) :=
  (const 2 |>.mul hf).mono (fun n => powerTwoCeil_le_twice (hpos n))

end IsPoly

/-- The least padded clock size prescribed by equation (5). -/
def clockSize (T : ℕ) : ℕ := powerTwoCeil (T + 1)

lemma clockSize_spec (T : ℕ) :
    T + 1 ≤ clockSize T ∧ clockSize T ≤ 2 * (T + 1) ∧
      ∀ r, T + 1 ≤ 2 ^ r → clockSize T ≤ 2 ^ r :=
  ⟨le_powerTwoCeil _, powerTwoCeil_le_twice (by omega), powerTwoCeil_minimal _⟩

lemma clockSize_isPoly {T : ℕ → ℕ} (hT : IsPoly T) :
    IsPoly (fun n => clockSize (T n)) :=
  (hT.add (IsPoly.const 1)).powerTwoCeil (by intro n; omega)

/-- `4096/(δ ε²)` after substituting the exact choices (21). -/
def phaseRequest (J K : ℕ) : ℕ := 491520000000000 * J ^ 6 * K ^ 11

def phaseLabels (J K : ℕ) : ℕ := powerTwoCeil (phaseRequest J K)

def phaseBits (J K : ℕ) : ℕ := ceilLog2 (phaseRequest J K)

lemma phaseRequest_identity {J K : ℕ} (hJ : 0 < J) (hK : 0 < K) :
    (phaseRequest J K : ℝ) =
      4096 / (biasDelta J K * (biasEps J K) ^ 2) := by
  unfold phaseRequest biasDelta biasEps biasLam
  push_cast
  have hJ' : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  field_simp [hJ', hK']
  <;> ring

lemma phaseLabels_spec {J K : ℕ} (hJ : 0 < J) (hK : 0 < K) :
    4096 / (biasDelta J K * (biasEps J K) ^ 2) ≤ (phaseLabels J K : ℝ) ∧
      phaseLabels J K ≤ 2 * phaseRequest J K := by
  constructor
  · rw [← phaseRequest_identity hJ hK]
    exact_mod_cast le_powerTwoCeil (phaseRequest J K)
  · exact powerTwoCeil_le_twice (by unfold phaseRequest; positivity)

lemma phaseLabels_isPoly {J K : ℕ → ℕ} (hJ : IsPoly J) (hK : IsPoly K)
    (hJpos : ∀ n, 0 < J n) (hKpos : ∀ n, 0 < K n) :
    IsPoly (fun n => phaseLabels (J n) (K n)) := by
  apply IsPoly.powerTwoCeil
  · exact ((IsPoly.const 491520000000000).mul (hJ.pow 6)).mul (hK.pow 11)
  · intro n
    have := hJpos n
    have := hKpos n
    unfold phaseRequest
    positivity

/-- All small registers: doubled work, clock, selector, four LCU ancillas,
phase register, and one rotation ancilla. -/
def simulatorSmallQubits (s T : ℕ) : ℕ :=
  2 * s + ceilLog2 (T + 1) + phaseBits (clockSize T) (2 ^ s) + 6

lemma simulatorSmallDimension (s T : ℕ) :
    2 ^ simulatorSmallQubits s T =
      64 * (2 ^ s) ^ 2 * clockSize T * phaseLabels (clockSize T) (2 ^ s) := by
  unfold simulatorSmallQubits clockSize phaseLabels powerTwoCeil phaseBits
  have he : 2 ^ (2 * s) = (2 ^ s) ^ 2 := by rw [Nat.mul_comm 2 s, pow_mul]
  simp only [pow_add]
  rw [he]
  norm_num
  ring

lemma simulatorSmallDimension_isPoly {s T : ℕ → ℕ}
    (hK : IsPoly (fun n => 2 ^ s n)) (hT : IsPoly T) :
    IsPoly (fun n => 2 ^ simulatorSmallQubits (s n) (T n)) := by
  have hJ := clockSize_isPoly hT
  have hM := phaseLabels_isPoly hJ hK
    (fun n => powerTwoCeil_pos _) (fun n => Nat.two_pow_pos _)
  have h := (((IsPoly.const 64).mul (hK.pow 2)).mul hJ).mul hM
  simpa only [simulatorSmallDimension] using h

/-- Reciprocal of a positive polynomially bounded natural function gives a
single fixed inverse-polynomial lower bound, with quantifiers over all `n`. -/
lemma inverse_nat_isInvPoly {D : ℕ → ℕ} (hD : IsPoly D) (hpos : ∀ n, 0 < D n) :
    IsInvPoly (fun n => 1 / (D n : ℝ)) := by
  obtain ⟨q, C, hC, hb⟩ := hD
  refine ⟨q, 1 / C, by positivity, ?_⟩
  intro n
  have hd : (0 : ℝ) < D n := by exact_mod_cast hpos n
  rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / (D n : ℝ))]
  calc
    (1 / C) / ((n : ℝ) + 1) ^ q = 1 / (C * ((n : ℝ) + 1) ^ q) := by ring
    _ ≤ 1 / (D n : ℝ) := one_div_le_one_div_of_le hd (hb n)

/-- The actual post-synthesis decision gap is inverse-polynomial once the
clock, work dimension, and small-register dimension have polynomial bounds. -/
lemma synthesized_gap_isInvPoly {J K k : ℕ → ℕ}
    (hJ : IsPoly J) (hK : IsPoly K) (hk : IsPoly (fun n => 2 ^ k n))
    (hJpos : ∀ n, 0 < J n) (hKpos : ∀ n, 0 < K n) :
    IsInvPoly (fun n =>
      biasLam (J n) (K n) / ((2 : ℝ) ^ (k n + 4) * Real.sqrt (K n))) := by
  let D : ℕ → ℕ := fun n => 1600 * J n ^ 2 * K n ^ 4 * 2 ^ k n
  have hD : IsPoly D :=
    (((IsPoly.const 1600).mul (hJ.pow 2)).mul (hK.pow 4)).mul hk
  have hDpos : ∀ n, 0 < D n := by
    intro n
    have := hJpos n
    have := hKpos n
    dsimp [D]
    positivity
  obtain ⟨q, C, hC, hb⟩ := inverse_nat_isInvPoly hD hDpos
  refine ⟨q, C, hC, fun n => (hb n).trans ?_⟩
  have hj : (0 : ℝ) < J n := by exact_mod_cast hJpos n
  have hk' : (0 : ℝ) < K n := by exact_mod_cast hKpos n
  have hk1 : (1 : ℝ) ≤ K n := by exact_mod_cast hKpos n
  have hs : Real.sqrt (K n) ≤ (K n : ℝ) := by
    nlinarith [Real.sq_sqrt hk'.le, Real.sqrt_nonneg (K n), sq_nonneg (Real.sqrt (K n) - 1)]
  have hgap : (0 : ℝ) < biasLam (J n) (K n) /
      ((2 : ℝ) ^ (k n + 4) * Real.sqrt (K n)) := by
    apply div_pos (biasLam_pos hj hk')
    exact mul_pos (by positivity) (Real.sqrt_pos.mpr hk')
  rw [abs_of_pos (by exact div_pos zero_lt_one (by exact_mod_cast hDpos n) :
    (0 : ℝ) < 1 / (D n : ℝ)), abs_of_pos hgap]
  calc
    1 / (D n : ℝ) = biasLam (J n) (K n) / ((2 : ℝ) ^ (k n + 4) * (K n : ℝ)) := by
      dsimp [D, biasLam]
      push_cast
      rw [pow_add]
      norm_num
      field_simp
      <;> ring
    _ ≤ _ := div_le_div_of_nonneg_left (biasLam_pos hj hk').le
      (mul_pos (by positivity) (Real.sqrt_pos.mpr hk'))
      (mul_le_mul_of_nonneg_left hs (by positivity))

/-- Total maximally mixed qubits, including the trace-cancellation selector. -/
def simulatorMixedQubits (s c T : ℕ) : ℕ := 2 * c + simulatorSmallQubits s T + 1

/-- Explicit logarithmic growth, with the finite-input convention `n+1`. -/
def IsLog (f : ℕ → ℕ) : Prop :=
  ∃ A B : ℕ, ∀ n, f n ≤ A * ceilLog2 (n + 1) + B

/-- A polynomial bound on a register's Hilbert-space dimension gives a
logarithmic bound on its number of qubits. -/
lemma isLog_of_power_two_isPoly {k : ℕ → ℕ} (hk : IsPoly (fun n => 2 ^ k n)) :
    IsLog k := by
  obtain ⟨q, C, hC, hb⟩ := hk
  let c : ℕ := ⌈C⌉₊
  have hc : C ≤ (c : ℝ) := Nat.le_ceil C
  refine ⟨q, ceilLog2 c, ?_⟩
  intro n
  have hnat : 2 ^ k n ≤ c * (n + 1) ^ q := by
    have h := (hb n).trans (mul_le_mul_of_nonneg_right hc (by positivity))
    exact_mod_cast h
  have hdim : c * (n + 1) ^ q ≤ 2 ^ (ceilLog2 c + q * ceilLog2 (n + 1)) := by
    calc
      c * (n + 1) ^ q ≤ powerTwoCeil c * (powerTwoCeil (n + 1)) ^ q :=
        Nat.mul_le_mul (le_powerTwoCeil c) (Nat.pow_le_pow_left (le_powerTwoCeil (n + 1)) q)
      _ = 2 ^ (ceilLog2 c + q * ceilLog2 (n + 1)) := by
        unfold powerTwoCeil
        rw [pow_add, ← pow_mul, Nat.mul_comm q]
  have := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).1 (hnat.trans hdim)
  omega

lemma simulatorSmallQubits_isLog {s T : ℕ → ℕ}
    (hK : IsPoly (fun n => 2 ^ s n)) (hT : IsPoly T) :
    IsLog (fun n => simulatorSmallQubits (s n) (T n)) :=
  isLog_of_power_two_isPoly (simulatorSmallDimension_isPoly hK hT)

lemma nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    have hp := Nat.two_pow_pos n
    omega

lemma simulatorMixedQubits_isPoly {s c T : ℕ → ℕ}
    (hK : IsPoly (fun n => 2 ^ s n)) (hc : IsPoly c) (hT : IsPoly T) :
    IsPoly (fun n => simulatorMixedQubits (s n) (c n) (T n)) := by
  have hk : IsPoly (fun n => simulatorSmallQubits (s n) (T n)) :=
    (simulatorSmallDimension_isPoly hK hT).mono (fun n => nat_le_two_pow _)
  exact (((IsPoly.const 2).mul hc).add hk).add (IsPoly.const 1)

/-- Source polynomial time and logarithmic initialized space suffice for the
numerical construction's final uniform inverse-polynomial gap. -/
theorem constructed_gap_isInvPoly {s T : ℕ → ℕ}
    (hK : IsPoly (fun n => 2 ^ s n)) (hT : IsPoly T) :
    IsInvPoly (fun n => biasLam (clockSize (T n)) (2 ^ s n : ℕ) /
      ((2 : ℝ) ^ (simulatorSmallQubits (s n) (T n) + 4) *
        Real.sqrt (2 ^ s n : ℕ))) :=
  synthesized_gap_isInvPoly (clockSize_isPoly hT) hK
    (simulatorSmallDimension_isPoly hK hT)
    (fun n => powerTwoCeil_pos _) (fun n => Nat.two_pow_pos _)

end Paper25
