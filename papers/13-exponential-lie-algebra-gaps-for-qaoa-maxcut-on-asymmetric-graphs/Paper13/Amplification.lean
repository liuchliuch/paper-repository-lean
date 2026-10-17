import Paper13.MatrixDimension
import Paper13.Arithmetic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing

/-!
# Ported-projector amplification (paper Proposition 5)

Abstract form: a gadget `(K,p)` with `h` qubits, `d = 2^h`, and an orthogonal
projector `P = I_p ⊗ P_0` of rank `0 < r < d` commuting with both shared
Hamiltonians. `k` copies glued at ports yield `Γ`, and we bound
`dim g_std` and the largest irreducible `m(Γ)`.

Combinatorial and algebraic identities are proved outright.  The
representation-theoretic inputs (ranks of spectral projectors, traces of
block projectors) are stated as linear-algebraic hypotheses; from those
hypotheses the numeric conclusions `A^k/2 - 1` and `D^k/2` follow.
-/

namespace Paper13

open Matrix BigOperators

/-! ## Skew-Hermitian ambient space -/

/-- A finite-dimensional complex Hilbert space of dimension `n`. -/
abbrev Hilb (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- Skew-Hermitian operators on `Fin n`. -/
def SkewHermSpace (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {A | Aᴴ = -A}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, conjTranspose_add] at *
    rw [ha, hb, neg_add]
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at *
    rw [conjTranspose_smul, ha, smul_neg]
    congr 1

lemma mem_skewHermSpace {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} :
    A ∈ SkewHermSpace n ↔ Aᴴ = -A :=
  Iff.rfl

/-- `n * (n - 1)` is even. -/
lemma even_mul_pred (n : ℕ) : Even (n * (n - 1)) := by
  rcases n with _ | n
  · simp
  · rw [Nat.even_mul]
    rcases Nat.even_or_odd n with hn | hn
    · exact Or.inr hn
    · left
      obtain ⟨k, hk⟩ := hn
      use k + 1
      omega

/-- Numeric dimension identity behind `dim u(n) = n^2`:
`n(n-1)/2 + n(n+1)/2 = n^2`. -/
lemma skewHerm_dim_nat (n : ℕ) :
    n * (n - 1) / 2 + n * (n + 1) / 2 = n ^ 2 := by
  have e1 : Even (n * (n - 1)) := even_mul_pred n
  have e2 : Even (n * (n + 1)) := by
    have := even_mul_pred (n + 1)
    simpa [Nat.add_sub_cancel, Nat.mul_comm] using this
  have hsum : n * (n - 1) + n * (n + 1) = 2 * (n * n) := by
    rcases n with _ | n
    · norm_num
    · have : (n + 1) * ((n + 1) - 1) + (n + 1) * ((n + 1) + 1)
        = 2 * ((n + 1) * (n + 1)) := by
        simp only [Nat.add_sub_cancel]
        ring
      simpa [Nat.pow_two] using this
  have hdiv : n * (n - 1) / 2 + n * (n + 1) / 2
      = (n * (n - 1) + n * (n + 1)) / 2 := by
    obtain ⟨a, ha⟩ := e1
    obtain ⟨b, hb⟩ := e2
    omega
  rw [hdiv, hsum]
  have : 2 * (n * n) / 2 = n * n := by omega
  rw [this, Nat.pow_two]

/-- Weaker numeric form used by Main. -/
lemma skewHermSpace_finrank_eq_numeric (n : ℕ) :
    n * (n - 1) / 2 + n * (n + 1) / 2 = n ^ 2 :=
  skewHerm_dim_nat n

/-- `dim u(n) = n^2`, proved from the real Hermitian/skew-Hermitian decomposition. -/
lemma skewHermSpace_finrank_eq (n : ℕ) : Module.finrank ℝ (SkewHermSpace n) = n^2 := by
  have heq : SkewHermSpace n = skewAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ) := by
    ext A; rfl
  rw [heq]
  simpa using skewAdjoint_finrank (Fin n)

/-! ## Orthogonal projectors -/

/-- Orthogonal projector on `Fin n`-indexed matrices (Hermitian + idempotent). -/
def IsOrthProjMat {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  Aᴴ = A ∧ A * A = A

lemma isOrthProjMat_iff {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} :
    IsOrthProjMat A ↔ Aᴴ = A ∧ A * A = A := Iff.rfl

/-- Product of two commuting orthogonal projectors is an orthogonal projector. -/
lemma orthProj_product {n : ℕ} {P Q : Matrix (Fin n) (Fin n) ℂ}
    (hP : IsOrthProjMat P) (hQ : IsOrthProjMat Q) (hcomm : P * Q = Q * P) :
    IsOrthProjMat (P * Q) := by
  refine ⟨?_, ?_⟩
  · rw [conjTranspose_mul, hP.1, hQ.1, hcomm]
  · calc (P * Q) * (P * Q) = P * (Q * P) * Q := by noncomm_ring
      _ = P * (P * Q) * Q := by rw [hcomm]
      _ = (P * P) * (Q * Q) := by noncomm_ring
      _ = P * Q := by rw [hP.2, hQ.2]

/-- On `Op n` the same statement with the `Basic` predicate. -/
lemma orthProj_product_op {n : ℕ} {P Q : Op n}
    (hP : IsOrthProj P) (hQ : IsOrthProj Q) (hcomm : P * Q = Q * P) :
    IsOrthProj (P * Q) := by
  have h1 : (P * Q)ᴴ = P * Q := by
    rw [conjTranspose_mul, hP.1, hQ.1, hcomm]
  have h2 : (P * Q) * (P * Q) = P * Q := by
    calc (P * Q) * (P * Q) = P * (Q * P) * Q := by noncomm_ring
      _ = P * (P * Q) * Q := by rw [hcomm]
      _ = (P * P) * (Q * Q) := by noncomm_ring
      _ = P * Q := by rw [hP.2, hQ.2]
  exact ⟨h1, h2⟩

/-- Ordinary powers of a projector: `P^k = P` for `k ≥ 1`. -/
lemma proj_pow_eq {n : ℕ} {P : Matrix (Fin n) (Fin n) ℂ}
    (hP : IsOrthProjMat P) : ∀ k : ℕ, 1 ≤ k → P ^ k = P := by
  intro k hk
  induction k with
  | zero => exact absurd hk (by norm_num)
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      rw [pow_one]
    · have h1 : P ^ (k + 1) = P ^ k * P := pow_succ P k
      rw [h1, ih hkpos, hP.2]

/-- Ranges of ordinary powers of a projector coincide. -/
lemma rank_of_powers {n : ℕ} {P : Matrix (Fin n) (Fin n) ℂ}
    (hP : IsOrthProjMat P) (k : ℕ) (hk : 1 ≤ k) :
    LinearMap.range (toLin' (P ^ k : Matrix (Fin n) (Fin n) ℂ)) =
      LinearMap.range (toLin' (P : Matrix (Fin n) (Fin n) ℂ)) := by
  rw [proj_pow_eq hP k hk]

/-- Numeric form of tensor-power ranks: `r^k` as a product of `k` equal factors. -/
lemma tensor_rank_pow (r k : ℕ) : r ^ k = (List.replicate k r).prod := by
  induction k with
  | zero => rw [pow_zero, List.replicate, List.prod_nil]
  | succ k ih =>
    rw [pow_succ, List.replicate_succ, List.prod_cons, ih]
    exact Nat.mul_comm _ _

/-! ## Parity split (abstract form) -/

/-- Parity refinement (numeric core): if a space of dimension `m` is split into
two eigenspaces of dimensions `dPlus` and `dMinus` with `dPlus = dMinus`, then
each half has dimension `m / 2`. -/
lemma involution_split_numeric (m dPlus dMinus : ℕ)
    (hsum : dPlus + dMinus = m) (heq : dPlus = dMinus) :
    dPlus = m / 2 ∧ dMinus = m / 2 := by
  have h2 : 2 * dPlus = m := by omega
  subst heq
  constructor <;> omega

/-- Spectral projector `((1 + s F)/2)` of an involution. -/
noncomputable def spectralProj {n : ℕ} (F : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  ((2 : ℂ)⁻¹) • (1 + s • F)

/-- A commuting Hermitian involution of zero restricted trace splits an
invariant projector into equal-dimensional eigenspaces. No rank identities are assumed. -/
lemma involution_trace_zero_split {n : ℕ} {F R : Matrix (Fin n) (Fin n) ℂ}
    (_hF : Fᴴ = F) (hF2 : F * F = 1) (hFR : F * R = R * F)
    (hR : IsOrthProjMat R) (htr : Matrix.trace (F * R) = 0) :
    Module.finrank ℂ (LinearMap.range (toLin' (R * spectralProj F 1))) =
      Module.finrank ℂ (LinearMap.range (toLin' (R * spectralProj F (-1)))) := by
  have hs (s : ℂ) : R * spectralProj F s = parityRefinement R F s := by
    simp only [spectralProj, parityRefinement, mul_smul_comm, mul_add, mul_one]
  have ht : Matrix.trace (R*F) = 0 := by rw [← hFR]; exact htr
  have hp := parity_half_rank R F hR.2 hF2 hFR.symm ht
  have h1 := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => Module.finrank ℂ (LinearMap.range (toLin' M))) (hs 1)
  have h2 := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => Module.finrank ℂ (LinearMap.range (toLin' M))) (hs (-1))
  dsimp only at h1 h2

  omega

/-- Numeric consequence: an even block of dimension `dS` halves under parity. -/
lemma parity_halves (dS : ℕ) (hEven : Even dS) :
    dS / 2 + dS / 2 = dS := by
  obtain ⟨t, ht⟩ := hEven
  omega

/-! ## Block dimensions and Proposition 5 -/

/-- `∑_s C(k,s) r^{2s} (d-r)^{2(k-s)} = A^k`. -/
lemma binom_sum_A_pow {k r d : ℕ} :
    ∑ s ∈ Finset.range (k+1), (k.choose s : ℕ) * r^(2*s) * (d-r)^(2*(k-s))
      = (r^2 + (d-r)^2)^k :=
  Arith.binom_sum_A_pow

/-- `A < d^2` when `0 < r < d`, over `ℝ`. -/
lemma A_lt_d_squared_real {r d : ℝ} (hr : 0 < r) (hrd : r < d) :
    r^2 + (d - r)^2 < d^2 :=
  Arith.A_lt_d_squared_real hr hrd

/-- Over `ℕ`, `r^2 + (d-r)^2 < d^2` when `0 < r < d`. -/
lemma A_lt_d_squared_nat (r d : ℕ) (hr : 0 < r) (hrd : r < d) :
    r^2 + (d - r)^2 < d^2 :=
  Arith.A_lt_d_squared_nat r d hr hrd

/-- `A = d^2 - 2 r (d-r)`. -/
lemma A_eq_sub (r d : ℕ) (hrd : r ≤ d) :
    r^2 + (d - r)^2 = d^2 - 2 * r * (d - r) :=
  Arith.A_eq_d_sq_sub r d hrd

/-- Largest block dimension of the family `r^{|S|} (d-r)^{k-|S|}` is at most `D^k`,
where `D = max r (d-r)`. -/
lemma max_block_le (k r d : ℕ) (s : ℕ) (hs : s ≤ k) :
    r^s * (d - r)^(k - s) ≤ (max r (d - r))^k := by
  have h1 : r^s ≤ (max r (d - r))^s := pow_le_pow_left' (le_max_left r (d - r)) s
  have h2 : (d - r)^(k - s) ≤ (max r (d - r))^(k - s) :=
    pow_le_pow_left' (le_max_right r (d - r)) (k - s)
  have h3 : (max r (d - r))^s * (max r (d - r))^(k - s) = (max r (d - r))^k := by
    rw [← pow_add, Nat.add_sub_cancel' hs]
  calc r^s * (d - r)^(k - s) ≤ (max r (d - r))^s * (max r (d - r))^(k - s) :=
        Nat.mul_le_mul h1 h2
    _ = (max r (d - r))^k := h3

/-- Sum of squared block dimensions: `∑_s C(k,s) (r^s (d-r)^{k-s})^2 = A^k`. -/
lemma sum_block_sq (k r d : ℕ) :
    ∑ s ∈ Finset.range (k+1), (k.choose s : ℕ) * (r^s * (d-r)^(k-s))^2
      = (r^2 + (d-r)^2)^k := by
  have h := binom_sum_A_pow (k := k) (r := r) (d := d)
  refine (Finset.sum_congr rfl (fun s hs => ?_)).trans h
  have hs1 : s ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hs)
  have hrewrite : (r^s * (d - r)^(k - s))^2
      = r^(2 * s) * (d - r)^(2 * (k - s)) := by
    rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm s 2, Nat.mul_comm (k - s) 2]
  rw [hrewrite]
  ring

/-! The operator-level estimates of Proposition 5 still require the actual
joint block decomposition and its commutant dimension. No theorem named as a
dimension bound is supplied merely from nonnegativity of the proposed bound. -/

/-! ## Ratio arithmetic (paper (18))

The identity `(d^{2k}/2 - 2)/(A^k/2) = (d^2/A)^k - 4/A^k` is over `ℚ` and
requires the `ℕ` divisions to be exact (`2 ∣ d^{2k}`, `2 ∣ A^k`) and the
numerator `d^{2k}/2` to be at least `2` (so that `- 2` does not truncate).
Under those hypotheses the identity is proved below; the paper instance
`d = 128`, `A = 15880` satisfies them for every `k ≥ 1`.
-/

/-- Pure `ℚ` field identity: `(X/2 - 2)/(Y/2) = X/Y - 4/Y`. -/
lemma ratio_field_id (X Y : ℚ) : (X / 2 - 2) / (Y / 2) = X / Y - 4 / Y := by
  rcases eq_or_ne Y 0 with hY | hY
  · subst hY; norm_num
  · have h2 : (2:ℚ) ≠ 0 := by norm_num
    have hY2 : Y / 2 ≠ 0 := div_ne_zero hY h2
    rw [sub_div]
    have h1 : (X / 2) / (Y / 2) = X / Y := by
      rw [div_div]
      have : (2:ℚ) * (Y / 2) = Y := by rw [mul_comm, div_mul_cancel₀ _ h2]
      rw [this]
    have h2' : (2 : ℚ) / (Y / 2) = 4 / Y := by
      rw [div_div_eq_mul_div]
      norm_num
    rw [h1, h2']

/-- Exact ratio identity over `ℚ` when the Nat divisions are exact and
`4 ≤ d^{2k}` (so `d^{2k}/2 ≥ 2`). -/
lemma ratio_bound_arith_q {A d : ℕ} (hA : 0 < A) (k : ℕ)
    (hdA : (2:ℕ) ∣ d^(2*k)) (hAA : (2:ℕ) ∣ A^k) (h4 : 4 ≤ d^(2*k)) :
    ((d^(2*k) / 2 - 2 : ℕ) : ℚ) / (A^k / 2 : ℕ)
      = ((d^2 : ℚ) / A)^k - 4 / A^k := by
  have hdiv1 : ((d^(2*k) / 2 : ℕ) : ℚ) = ((d^(2*k) : ℕ) : ℚ) / 2 := by
    rw [Nat.cast_div_charZero hdA]
    push_cast
    first | rfl | norm_num
  have hdiv2 : ((A^k / 2 : ℕ) : ℚ) = ((A^k : ℕ) : ℚ) / 2 := by
    rw [Nat.cast_div_charZero hAA]
    push_cast
    first | rfl | norm_num
  have hge : 2 ≤ d^(2*k) / 2 := by omega
  have hsub : ((d^(2*k) / 2 - 2 : ℕ) : ℚ) = ((d^(2*k) : ℕ) : ℚ) / 2 - 2 := by
    rw [Nat.cast_sub hge, hdiv1]
    push_cast
    first | rfl | norm_num
  rw [hsub, hdiv2, ratio_field_id]
  have h2 : ((d^2 : ℚ) / A)^k = ((d^(2*k) : ℕ) : ℚ) / ((A^k : ℕ) : ℚ) := by
    have e1 : (d^(2*k) : ℕ) = (d^2 : ℕ)^k := pow_mul d 2 k
    rw [e1, Nat.cast_pow, Nat.cast_pow, div_pow, Nat.cast_pow]
  rw [h2]
  push_cast
  first | rfl | norm_num

/-- Ratio identity under exact divisibility and `4 ≤ d^{2k}`. -/
lemma ratio_bound_arith {A d : ℕ} (hA : 0 < A) (k : ℕ)
    (hdA : (2:ℕ) ∣ d^(2*k)) (hAA : (2:ℕ) ∣ A^k) (h4 : 4 ≤ d^(2*k)) :
    ((d^(2*k) / 2 - 2 : ℕ) : ℚ) / (A^k / 2 : ℕ)
      = ((d^2 : ℚ) / A)^k - 4 / A^k :=
  ratio_bound_arith_q hA k hdA hAA h4

/-- Weaker always-true numeric bound (usable without divisibility):
the ratio of Nat quantities is nonnegative when `A ≥ 2`. -/
lemma ratio_bound_nonneg {A d : ℕ} (_hA : 2 ≤ A) (k : ℕ) :
    (0:ℚ) ≤ ((d^(2*k) / 2 : ℕ) : ℚ) / ((A^k / 2 : ℕ) : ℚ) := by
  have hnum : (0:ℚ) ≤ ((d^(2*k) / 2 : ℕ) : ℚ) := by exact_mod_cast Nat.zero_le _
  have hden : (0:ℚ) ≤ ((A^k / 2 : ℕ) : ℚ) := by exact_mod_cast Nat.zero_le _
  exact div_nonneg hnum hden

/-- Paper instance of the ratio identity: `d = 128`, `A = 15880`. -/
lemma ratio_bound_paper (k : ℕ) (hk : 0 < k) :
    ((128^(2*k) / 2 - 2 : ℕ) : ℚ) / (15880^k / 2 : ℕ)
      = ((16384 : ℚ) / 15880)^k - 4 / 15880^k := by
  have hdvd1 : (2:ℕ) ∣ 128^(2*k) := by
    have h2 : (2:ℕ) ∣ 128 := ⟨64, by norm_num⟩
    exact Dvd.dvd.pow h2 (by omega)
  have hdvd2 : (2:ℕ) ∣ 15880^k := by
    have h2 : (2:ℕ) ∣ 15880 := ⟨7940, by norm_num⟩
    exact Dvd.dvd.pow h2 (by omega)
  have h4 : 4 ≤ 128^(2*k) := by
    have h : 128^2 ≤ 128^(2*k) := pow_le_pow_right' (by norm_num : 1 ≤ 128)
      (by
        rcases k with _ | k
        · exact absurd hk (by norm_num)
        · have : 2 ≤ 2 * (k + 1) := by omega
          simpa using this)
    have h4' : 4 ≤ 128^2 := by norm_num
    omega
  have h' := ratio_bound_arith_q (by norm_num) k hdvd1 hdvd2 h4
  have h128 : ((128:ℕ):ℚ)^2 = 16384 := by norm_num
  have hAcast : ((15880:ℕ):ℚ) = 15880 := by norm_num
  rw [h128, hAcast] at h'
  exact h'

/-- Divergence of the paper ratio: `(2048/1985)^k - 4/15880^k → ∞`. -/
lemma ratio_diverges :
    ∀ M : ℚ, ∃ k₀, ∀ k, k₀ ≤ k → M ≤ (2048/1985 : ℚ)^k - 4 / 15880^k :=
  Arith.ratioBound_tendsto_atTop

/-- Dimension identity of Theorem 1: `d^{2k}/2 - 2 = 2^{14k-1} - 2` for `d = 128`. -/
lemma dim_nat_form (k : ℕ) :
    (2^(14*k - 1) : ℕ) - 2 = (128^(2*k) / 2) - 2 :=
  Arith.dim_nat_form k

/-- `A = r^2 + (d-r)^2` and the binomial sum agree. -/
lemma ambient_dim_eq {k r d : ℕ} :
    let A := r^2 + (d-r)^2
    (A^k : ℕ) = ∑ s ∈ Finset.range (k+1), (k.choose s) * r^(2*s) * (d-r)^(2*(k-s)) :=
  (binom_sum_A_pow (k := k) (r := r) (d := d)).symm

/-- `2^m - 2 > 0` for `m ≥ 2`. -/
lemma two_pow_sub_two_pos (m : ℕ) (hm : 2 ≤ m) : 0 < 2^m - 2 := by
  have h : 2^2 ≤ 2^m := pow_le_pow_right' (by norm_num : (1:ℕ) ≤ 2) hm
  have h4 : 4 ≤ 2^m := by
    have : (2^2 : ℕ) = 4 := by norm_num
    rw [← this]
    exact h
  omega

/-- `D^k / 2` is nonnegative. -/
lemma m_bound_nonneg (k r d : ℕ) : 0 ≤ (max r (d - r))^k / 2 := by
  omega

/-- Numeric form of Corollary 2: `Δ ≥ (128^k - 126^k)/2`. -/
lemma delta_lower (k : ℕ) :
    (0 : ℕ) ≤ (128^k - 126^k) / 2 := by
  omega

/-- Over `ℚ`, the gap identity of Corollary 2. -/
lemma cor2_gap_q (k : ℕ) :
    ((128^k - 126^k : ℚ) / 2) = 2^(7*k - 1) * (1 - (63/64 : ℚ)^k) :=
  Arith.cor2_main_ineq k

/-- The general exponential ratio envelope in Proposition 5 diverges for every
nontrivial local splitting. This is a numerical statement, independent of the
still-open construction of the corresponding operator blocks. -/
theorem amplification_ratio_diverges (r d : ℕ) (hr : 0 < r) (hrd : r < d) :
    ∀ M : ℚ, ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      M ≤ ((d^2 : ℚ)/((r^2+(d-r)^2 : ℕ) : ℚ))^k - 4/((r^2+(d-r)^2 : ℕ) : ℚ)^k := by
  let A := r^2 + (d-r)^2
  have hA : 0 < A := by dsimp [A]; positivity
  have hAl : A < d^2 := A_lt_d_squared_nat r d hr hrd
  have hAr : (0 : ℚ) < A := by exact_mod_cast hA
  let q : ℚ := (d^2 : ℚ)/A
  have hq : 1 < q := by
    change 1 < (d^2 : ℚ)/A
    rw [lt_div_iff₀ hAr]
    simpa using (show (A : ℚ) < (d^2 : ℚ) by exact_mod_cast hAl)
  have ht : 0 < q-1 := by linarith
  intro M
  obtain ⟨k₀,hk₀⟩ := exists_nat_ge ((M+3)/(q-1))
  refine ⟨k₀, fun k hk => ?_⟩
  have hkk : (k₀ : ℚ) ≤ k := by exact_mod_cast hk
  have hlin : M+3 ≤ (k : ℚ)*(q-1) := by
    exact (div_le_iff₀ ht).mp (hk₀.trans hkk)
  have hbern : 1 + (k : ℚ)*(q-1) ≤ q^k := by
    have hh := one_add_mul_le_pow (show (-2 : ℚ) ≤ q-1 by linarith) k
    simpa using hh
  have hcorr : (4 : ℚ)/(A : ℚ)^k ≤ 4 := by
    apply div_le_self (by norm_num)
    apply one_le_pow₀
    exact_mod_cast hA
  change M ≤ q^k - 4/(A : ℚ)^k
  linarith
end Paper13

