import Mathlib

/-!
# Shared definitions for paper 24 (uniformity testing with purified access)

This file is definition-only plus elementary identities that every module
needs.  Heavier inequalities live in their natural modules.
-/

noncomputable section

namespace PUT

/-! ## Rising factorial -/

/-- Rising factorial `(x)_r = x(x+1)⋯(x+r-1)`, with `(x)_0 = 1`. -/
def risingFactorial (x : ℝ) : ℕ → ℝ
  | 0 => 1
  | r + 1 => x * risingFactorial (x + 1) r

@[simp] theorem risingFactorial_zero (x : ℝ) : risingFactorial x 0 = 1 := rfl

theorem risingFactorial_succ (x : ℝ) (r : ℕ) :
    risingFactorial x (r + 1) = x * risingFactorial (x + 1) r := rfl

@[simp] theorem risingFactorial_one (x : ℝ) : risingFactorial x 1 = x := by
  rw [risingFactorial_succ, risingFactorial_zero]
  ring

/-! ## Total variation and the uniform law -/

/-- Total variation distance `d_TV(p,q) = (1/2) ∑ |p_i - q_i|`. -/
def tvDist {d : ℕ} (p q : Fin d → ℝ) : ℝ := (1 / 2 : ℝ) * ∑ i, |p i - q i|

/-- Uniform distribution on `[d]`. -/
def uniform (d : ℕ) : Fin d → ℝ := fun _ => (1 : ℝ) / d

@[simp] theorem uniform_apply (d : ℕ) (i : Fin d) : uniform d i = (1 : ℝ) / d := rfl

theorem tvDist_nonneg {d : ℕ} (p q : Fin d → ℝ) : 0 ≤ tvDist p q := by
  unfold tvDist; positivity

@[simp] theorem tvDist_self {d : ℕ} (p : Fin d → ℝ) : tvDist p p = 0 := by
  unfold tvDist; simp

/-! ## Degree vectors -/

/-- Total degree `K(k) = ∑ k_i`. -/
def degK {d : ℕ} (k : Fin d → ℕ) : ℕ := ∑ i, k i

/-- Squared degree `R(k) = ∑ k_i²`. -/
def degR {d : ℕ} (k : Fin d → ℕ) : ℕ := ∑ i, (k i) ^ 2

theorem degK_coe {d : ℕ} (k : Fin d → ℕ) : (degK k : ℝ) = ∑ i, (k i : ℝ) := by
  simp [degK, Nat.cast_sum]

theorem degR_coe {d : ℕ} (k : Fin d → ℕ) : (degR k : ℝ) = ∑ i, (k i : ℝ) ^ 2 := by
  simp [degR, Nat.cast_sum]

/-! ## Quadratic cutoff `α(k) = (A - R(k))₊` -/

/-- Quadratic cutoff weight of a degree vector. -/
def cutoff {d : ℕ} (A : ℝ) (k : Fin d → ℕ) : ℝ :=
  max (A - ∑ i, (k i : ℝ) ^ 2) 0

theorem cutoff_nonneg {d : ℕ} (A : ℝ) (k : Fin d → ℕ) : 0 ≤ cutoff A k :=
  le_max_right _ _

/-! ## Posterior mean coordinates `q_i = (a+k_i)/(ad+K)` -/

/-- Posterior mean of `p_i` under `Dir(a+k)` written as a raw ratio. -/
def postMean (a : ℝ) {d : ℕ} (k : Fin d → ℕ) (i : Fin d) : ℝ :=
  (a + k i) / (a * d + degK k)

/-- Componentwise square root of the posterior mean. -/
def postSqrt (a : ℝ) {d : ℕ} (k : Fin d → ℕ) (i : Fin d) : ℝ :=
  Real.sqrt (postMean a k i)

/-- Erasure-side ratio `b_i⁻² = (a+k_i-1)/(ad+K-1)`. -/
def postMeanMinus (a : ℝ) {d : ℕ} (k : Fin d → ℕ) (i : Fin d) : ℝ :=
  (a + k i - 1) / (a * d + degK k - 1)

/-! ## Fourier multi-index -/

/-- Fourier character frequency on the phase torus `[0,2π)^{dM}`. -/
abbrev PhaseIndex (d M : ℕ) := Fin d → Fin M → ℤ

/-- Label-wise degree `k_i(n) = ∑_j |n_{ij}|`. -/
def labelDegree {d M : ℕ} (n : PhaseIndex d M) (i : Fin d) : ℕ :=
  ∑ j, (n i j).natAbs

/-- Degree vector of a Fourier index. -/
def degreeOf {d M : ℕ} (n : PhaseIndex d M) : Fin d → ℕ :=
  fun i => labelDegree n i

/-- Creation direction: increase `k_i` by one. -/
def degUp {d : ℕ} (k : Fin d → ℕ) (i : Fin d) : Fin d → ℕ :=
  Function.update k i (k i + 1)

/-- Erasure direction: decrease `k_i` by one. -/
def degDown {d : ℕ} (k : Fin d → ℕ) (i : Fin d) : Fin d → ℕ :=
  Function.update k i (k i - 1)

/-! ## Parameter sheet -/

/-- `L_A = (√A + 1)²`. -/
def LA (A : ℝ) : ℝ := (Real.sqrt A + 1) ^ 2

/-- Proof constant `c₀` of the eventual lower bound. -/
def c0 : ℝ := (1 : ℝ) / 3000

/-- Success probability threshold of Theorem 1. -/
def successThreshold : ℝ := (0.99 : ℝ)

/-- Alternative-prior mass `q₀ = 1/144` from Lemma 2. -/
def q0 : ℝ := (1 : ℝ) / 144

/-- Dirichlet scale `a = (48 ε)⁻²`. -/
def dirichletScale (ε : ℝ) : ℝ := (48 * ε) ^ (-2 : ℤ)

/-- Right-hand side of Lemma 1: `20(√(1+A/d) + A^{3/2}/(a√d) + A/√(ad))`. -/
def lemma1RHS (A a d : ℝ) : ℝ :=
  20 * (Real.sqrt (1 + A / d) + A ^ (3/2:ℝ) / (a * Real.sqrt d) + A / Real.sqrt (a * d))

/-- Right-hand side of Lemma 2: TV threshold `1/(24√a)`. -/
def lemma2Threshold (a : ℝ) : ℝ := 1 / (24 * Real.sqrt a)

/-- Target lower bound `c · min(d^{1/3} ε^{-4/3}, √d/ε)`. -/
def theorem1Bound (c d ε : ℝ) : ℝ :=
  c * min (d ^ (1/3:ℝ) * ε ^ ((-4/3:ℝ))) (Real.sqrt d / ε)

end PUT

/-! ## Dirichlet moments and normalized weights -/

namespace PUT

/-- Dirichlet moment `m_k = ∏_i (a)_{k_i} / (ad)_K`. -/
def dirMoment (a : ℝ) {d : ℕ} (k : Fin d → ℕ) : ℝ :=
  (∏ i, risingFactorial a (k i)) / risingFactorial (a * d) (degK k)

/-- Normalized radial weight `w_k(p) = ∏ p_i^{k_i/2} / √m_k`. -/
def weight (a : ℝ) {d : ℕ} (k : Fin d → ℕ) (p : Fin d → ℝ) : ℝ :=
  (∏ i, p i ^ ((k i : ℝ) / 2)) / Real.sqrt (dirMoment a k)

/-- Posterior total parameter `S = ad + K`. -/
def postTotal (a : ℝ) {d : ℕ} (k : Fin d → ℕ) : ℝ := a * d + degK k

/-- Creation coefficient `b_i = √((a+k_i)/S)`. -/
def createCoeff (a : ℝ) {d : ℕ} (k : Fin d → ℕ) (i : Fin d) : ℝ :=
  Real.sqrt ((a + k i) / postTotal a k)

/-- Erasure coefficient `b_i⁻ = √((a+k_i-1)/(S-1))`. -/
def eraseCoeff (a : ℝ) {d : ℕ} (k : Fin d → ℕ) (i : Fin d) : ℝ :=
  Real.sqrt ((a + k i - 1) / (postTotal a k - 1))

end PUT
