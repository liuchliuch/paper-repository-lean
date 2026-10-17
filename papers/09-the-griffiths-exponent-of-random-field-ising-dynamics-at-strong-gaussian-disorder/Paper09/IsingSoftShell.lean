/-
Copyright (c) 2026. Ising-specific soft-shell comparison (Lemma 2.2, eq. (2.2)).

Auxiliary fixed-shell Rayleigh algebra under an explicit density sandwich.
Actual Gibbs density bounds are derived in `GibbsShell`; actual joint-law
disintegration and spectral comparison are derived in `Disintegration`.
-/
import Paper09.Ising
import Paper09.SoftShell
import Paper09.Defects
import Paper09.Dynamics
import Paper09.Main

open Finset BigOperators Classical Real

noncomputable section

namespace Paper09

/-! ## Shell defects and field mass -/

/-- The paper's `b = 4 β max_{y ∈ S} |{x ∈ B : x ~ y}| ≤ 8 d β`. -/
def shellCoupling (β d : ℝ) : ℝ := 8 * d * β

theorem shellCoupling_nonneg {β d : ℝ} (hβ : 0 ≤ β) (hd : 0 ≤ d) :
    0 ≤ shellCoupling β d := by
  unfold shellCoupling
  positivity

/-- Oscillation bound `D_τ = 2 A_B + b k(τ)` of the logarithmic tilt (2.4). -/
def shellOscillation (A b : ℝ) (k : ℕ) : ℝ := 2 * A + b * k

theorem shellOscillation_nonneg {A b : ℝ} {k : ℕ}
    (hA : 0 ≤ A) (hb : 0 ≤ b) : 0 ≤ shellOscillation A b k := by
  unfold shellOscillation
  have : (0:ℝ) ≤ k := Nat.cast_nonneg _
  positivity

/-! ## Lemma 2.2, Ising form -/

/-- Lemma 2.2, paper (2.2), in the fixed-shell Rayleigh form.

If the conditional law `μ_τ` on the box satisfies the oscillation sandwich
`e^{-D} ν ≤ μ_τ ≤ e^{D} ν` with `D = 2 A_B + b k`, then the Rayleigh quotient
of the extended pure-system eigenfunction is at most `e^{4 A_B + 2 b k}` times
the pure Rayleigh quotient. -/
theorem lemma_2_2_ising_shell {V : Type*} [Fintype V]
    (Λ : Lattice V) (h : V → ℝ) (β : ℝ) (B S : Finset V) (ζ : V → Spin)
    (τ : V → Spin)
    (A b : ℝ) (hA : A = fieldMass h B) (hb : 0 ≤ b)
    (k : ℕ) (hk : k = defectCount S ζ τ)
    (ν : FinProb (V → Spin)) (μ : FinProb (V → Spin))
    (hν : ν = pureGibbs Λ β B S ζ)
    (gapν : ℝ)
    (f : (V → Spin) → ℝ)
    (hgap : dirichletForm ν f ≤ gapν * FinProb.variance ν f)
    (hA0 : 0 ≤ A)
    (hlo : ∀ η, exp (- shellOscillation A b k) * ν.w η ≤ μ.w η)
    (hhi : ∀ η, μ.w η ≤ exp (shellOscillation A b k) * ν.w η) :
    dirichletForm μ f * FinProb.variance ν f
      ≤ exp (4 * A + 2 * b * k) *
          (gapν * FinProb.variance ν f * FinProb.variance μ f) := by
  have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  have hD : 0 ≤ shellOscillation A b k :=
    shellOscillation_nonneg hA0 hb
  have hgapFull : (heatBathGraph V).dirichlet ν f ≤
      (2 * gapν) * FinProb.variance ν f := by
    dsimp [dirichletForm] at hgap
    linarith
  have h := lemma_2_2_fixed_shell (G := heatBathGraph V) f hgapFull
    hA0 hb hk0
    (by simpa [shellOscillation] using hlo)
    (by simpa [shellOscillation] using hhi)
  convert mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1 / 2) using 1 <;>
    dsimp [dirichletForm] <;> ring

/-- Combining Lemma 2.2 with Lemma 2.3: (2.6). -/
theorem lemma_2_2_2_3_combined (n : ℕ) (q b A gapπ gapν : ℝ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hb : 0 ≤ b) (hA : 0 ≤ A) (hgapν : 0 ≤ gapν)
    (hsoft : gapπ ≤ gapν * exp (4 * A)
      * ((∑ k ∈ range (n + 1),
          ((n.choose k : ℝ) * q ^ k * (1 - q) ^ (n - k)) * exp (b * k))
      / (∑ k ∈ range (n + 1),
          ((n.choose k : ℝ) * q ^ k * (1 - q) ^ (n - k)) * exp (-b * k)))) :
    gapπ ≤ gapν * exp (4 * A + (n : ℝ) * q * (exp b - 1 + b)) :=
  lemma_2_3_gap n q b A gapπ gapν hq hq1 hb hA hgapν hsoft

/-! ## Proposition 2.1 deterministic chain -/

/-- Proposition 2.1, deterministic form: given Assumption 1.1's pure gap
`gap(ν) ≤ exp(-c0 m^{d-1})` and the island event cost (2.9), the full-system
gap on the island is at most `exp(-(c0/2) m^{d-1})`. -/
theorem prop_2_1_gap_on_island (c0 ε0 m d qH0 b0 gapν gapπ : ℝ)
    (hm : 0 < m) (hd : 0 < d)
    (hq : 0 ≤ qH0) (hb0 : 0 ≤ b0)
    (hε : ε0 = c0 / 16)
    (hH : 2 * d * qH0 * (exp b0 - 1 + b0) ≤ c0 / 4)
    (hpure : gapν ≤ exp (- c0 * m ^ (d - 1)))
    (hsoft : gapπ ≤ gapν * exp (4 * ε0 * m ^ (d - 1)
        + 2 * d * m ^ (d - 1) * qH0 * (exp b0 - 1 + b0))) :
    gapπ ≤ exp (- (c0 / 2) * m ^ (d - 1)) := by
  have hcost := gap_bound_on_island c0 ε0 m d qH0 b0 hm hd hq hb0 hε hH
  have h1 : gapπ ≤ gapν * exp (4 * ε0 * m ^ (d - 1)
      + 2 * d * m ^ (d - 1) * qH0 * (exp b0 - 1 + b0)) := hsoft
  have h2 : gapν * exp (4 * ε0 * m ^ (d - 1)
      + 2 * d * m ^ (d - 1) * qH0 * (exp b0 - 1 + b0))
      ≤ exp (- c0 * m ^ (d - 1)) *
        exp (4 * ε0 * m ^ (d - 1)
          + 2 * d * m ^ (d - 1) * qH0 * (exp b0 - 1 + b0)) :=
    mul_le_mul_of_nonneg_right hpure (le_of_lt (exp_pos _))
  have h3 : exp (- c0 * m ^ (d - 1)) *
        exp (4 * ε0 * m ^ (d - 1)
          + 2 * d * m ^ (d - 1) * qH0 * (exp b0 - 1 + b0))
      = exp (- c0 * m ^ (d - 1) + 4 * ε0 * m ^ (d - 1)
          + 2 * d * m ^ (d - 1) * qH0 * (exp b0 - 1 + b0)) := by
    rw [← exp_add]
    ring
  have h4 : exp (- c0 * m ^ (d - 1) + 4 * ε0 * m ^ (d - 1)
      + 2 * d * m ^ (d - 1) * qH0 * (exp b0 - 1 + b0))
      ≤ exp (- (c0 / 2) * m ^ (d - 1)) :=
    exp_le_exp.mpr hcost
  have h5 : gapπ ≤ exp (- (c0 / 2) * m ^ (d - 1)) := by
    have h1' : gapπ ≤ exp (- c0 * m ^ (d - 1)) *
        exp (4 * ε0 * m ^ (d - 1)
          + 2 * d * m ^ (d - 1) * qH0 * (exp b0 - 1 + b0)) :=
      le_trans h1 h2
    rw [h3] at h1'
    exact le_trans h1' h4
  exact h5

end Paper09
