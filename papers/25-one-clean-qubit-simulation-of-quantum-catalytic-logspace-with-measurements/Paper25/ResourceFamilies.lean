import Paper25.Resources
import Paper25.EffectiveCircuitModel

/-! Resource bounds quantified over complete binary input strings, rather than
only over one representative of each input length. -/
noncomputable section
namespace Paper25.OperationalModel

namespace PolynomialBound
lemma const (a : ℕ) : PolynomialBound (fun _ => a) := ⟨a, 0, by simp⟩

lemma mono {f g : Input → ℕ} (hg : PolynomialBound g) (h : ∀ x, f x ≤ g x) :
    PolynomialBound f := by
  obtain ⟨C,d,hg⟩ := hg
  exact ⟨C,d, fun x => (h x).trans (hg x)⟩

lemma mul {f g : Input → ℕ} (hf : PolynomialBound f) (hg : PolynomialBound g) :
    PolynomialBound (fun x => f x * g x) := by
  obtain ⟨C,d,hf⟩ := hf
  obtain ⟨E,e,hg⟩ := hg
  refine ⟨C*E,d+e,?_⟩
  intro x
  calc
    _ ≤ (C*(x.length+1)^d)*(E*(x.length+1)^e) := Nat.mul_le_mul (hf x) (hg x)
    _ = _ := by rw [pow_add]; ring

lemma pow {f : Input → ℕ} (hf : PolynomialBound f) (r : ℕ) :
    PolynomialBound (fun x => f x ^ r) := by
  induction r with
  | zero => simpa using const 1
  | succ r ih => simpa [pow_succ] using ih.mul hf

lemma add {f g : Input → ℕ} (hf : PolynomialBound f) (hg : PolynomialBound g) :
    PolynomialBound (fun x => f x + g x) := by
  obtain ⟨C,d,hf⟩ := hf
  obtain ⟨E,e,hg⟩ := hg
  refine ⟨C+E,d+e,?_⟩
  intro x
  have hd := Nat.pow_le_pow_right (by omega : 1 ≤ x.length+1) (Nat.le_add_right d e)
  have he := Nat.pow_le_pow_right (by omega : 1 ≤ x.length+1) (Nat.le_add_left e d)
  calc
    _ ≤ C*(x.length+1)^d + E*(x.length+1)^e := Nat.add_le_add (hf x) (hg x)
    _ ≤ C*(x.length+1)^(d+e) + E*(x.length+1)^(d+e) :=
      Nat.add_le_add (Nat.mul_le_mul_left C hd) (Nat.mul_le_mul_left E he)
    _ = _ := by ring

lemma paddedPowerTwo {f : Input → ℕ} (hf : PolynomialBound f) (hpos : ∀ x, 0 < f x) :
    PolynomialBound (fun x => powerTwoCeil (f x)) :=
  ((const 2).mul hf).mono (fun x => powerTwoCeil_le_twice (hpos x))
end PolynomialBound

/-- A logarithmic bound on initialized qubits gives a polynomial bound on the
actual work Hilbert-space dimension for every input. -/
theorem logarithmic_work_dimension {s : Input → ℕ} (hs : LogarithmicBound s) :
    PolynomialBound (fun x => 2 ^ s x) := by
  obtain ⟨C,hs⟩ := hs
  refine ⟨4^C,C,?_⟩
  intro x
  have hlog : 2 ^ Nat.log2 (x.length+2) ≤ x.length+2 := by
    rw [Nat.log2_eq_log_two]
    exact Nat.pow_log_le_self 2 (by omega)
  calc
    2 ^ s x ≤ 2 ^ (C*(Nat.log2 (x.length+2)+1)) :=
      Nat.pow_le_pow_right (by decide) (hs x)
    _ = (2 ^ (Nat.log2 (x.length+2)+1)) ^ C := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ (4*(x.length+1)) ^ C := by
      apply Nat.pow_le_pow_left
      rw [pow_succ]
      omega
    _ = 4^C*(x.length+1)^C := mul_pow _ _ _

theorem clock_size_polynomial {T : Input → ℕ} (hT : PolynomialBound T) :
    PolynomialBound (fun x => clockSize (T x)) :=
  (hT.add (PolynomialBound.const 1)).paddedPowerTwo (by intro x; omega)

theorem phase_labels_polynomial {J K : Input → ℕ}
    (hJ : PolynomialBound J) (hK : PolynomialBound K)
    (hJpos : ∀ x, 0 < J x) (hKpos : ∀ x, 0 < K x) :
    PolynomialBound (fun x => phaseLabels (J x) (K x)) := by
  apply PolynomialBound.paddedPowerTwo
  · exact ((PolynomialBound.const 491520000000000).mul (hJ.pow 6)).mul (hK.pow 11)
  · intro x
    have := hJpos x
    have := hKpos x
    unfold phaseRequest
    positivity

theorem small_register_dimension_polynomial {s T : Input → ℕ}
    (hs : LogarithmicBound s) (hT : PolynomialBound T) :
    PolynomialBound (fun x => 2 ^ simulatorSmallQubits (s x) (T x)) := by
  have hK := logarithmic_work_dimension hs
  have hJ := clock_size_polynomial hT
  have hM := phase_labels_polynomial hJ hK
    (fun x => powerTwoCeil_pos _) (fun x => Nat.two_pow_pos _)
  have h := (((PolynomialBound.const 64).mul (hK.pow 2)).mul hJ).mul hM
  simpa only [simulatorSmallDimension] using h

theorem mixed_qubits_polynomial {s c T : Input → ℕ}
    (hs : LogarithmicBound s) (hc : PolynomialBound c) (hT : PolynomialBound T) :
    PolynomialBound (fun x => simulatorMixedQubits (s x) (c x) (T x)) := by
  have hk : PolynomialBound (fun x => simulatorSmallQubits (s x) (T x)) :=
    (small_register_dimension_polynomial hs hT).mono (fun x => Paper25.nat_le_two_pow _)
  exact (((PolynomialBound.const 2).mul hc).add hk).add (PolynomialBound.const 1)

/-- A common reciprocal-polynomial lower bound, with its quantifiers over all
input strings and one fixed pair of constants. -/
theorem string_gap_inverse_polynomial {J K k : Input → ℕ}
    (hJ : PolynomialBound J) (hK : PolynomialBound K)
    (hk : PolynomialBound (fun x => 2 ^ k x))
    (hJpos : ∀ x, 0 < J x) (hKpos : ∀ x, 0 < K x) :
    ∃ (C : ℝ) (d : ℕ), 0 < C ∧ ∀ x,
      C / ((x.length : ℝ)+1)^d ≤
        biasLam (J x) (K x) / ((2:ℝ)^(k x+4)*Real.sqrt (K x)) := by
  let D : Input → ℕ := fun x => 1600*J x^2*K x^4*2^k x
  have hD : PolynomialBound D :=
    (((PolynomialBound.const 1600).mul (hJ.pow 2)).mul (hK.pow 4)).mul hk
  obtain ⟨N,d,hD⟩ := hD
  refine ⟨1/(N+1:ℝ),d,by positivity,?_⟩
  intro x
  have hj : (0:ℝ) < J x := by exact_mod_cast hJpos x
  have hkk : (0:ℝ) < K x := by exact_mod_cast hKpos x
  have hk1 : (1:ℝ) ≤ K x := by exact_mod_cast hKpos x
  have hsqrt : Real.sqrt (K x) ≤ (K x:ℝ) := by
    nlinarith [Real.sq_sqrt hkk.le, Real.sqrt_nonneg (K x), sq_nonneg (Real.sqrt (K x)-1)]
  have hd : (0:ℝ) < D x := by
    have hdNat : 0 < D x := by
      have := hJpos x
      have := hKpos x
      dsimp [D]
      positivity
    exact_mod_cast hdNat
  have hbound : (D x:ℝ) ≤ (N+1:ℝ)*((x.length:ℝ)+1)^d := by
    have h := hD x
    have h' : D x ≤ (N+1)*(x.length+1)^d :=
      h.trans (Nat.mul_le_mul_right _ (by omega : N ≤ N+1))
    exact_mod_cast h'
  calc
    (1/(N+1:ℝ))/((x.length:ℝ)+1)^d =
        1/((N+1:ℝ)*((x.length:ℝ)+1)^d) := by rw [div_div]
    _ ≤ 1/(D x:ℝ) := one_div_le_one_div_of_le hd hbound
    _ = biasLam (J x) (K x) / ((2:ℝ)^(k x+4)*(K x:ℝ)) := by
      dsimp [D,biasLam]
      push_cast
      rw [pow_add]
      norm_num
      field_simp
      <;> ring
    _ ≤ _ := div_le_div_of_nonneg_left (biasLam_pos hj hkk).le
      (mul_pos (by positivity) (Real.sqrt_pos.mpr hkk))
      (mul_le_mul_of_nonneg_left hsqrt (by positivity))

end Paper25.OperationalModel
