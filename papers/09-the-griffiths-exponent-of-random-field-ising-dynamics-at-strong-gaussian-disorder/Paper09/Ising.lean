/-
Copyright (c) 2026. Finite random-field Ising model for the Griffiths-exponent paper.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Paper09.Basic
import Paper09.FiniteProb

open Finset BigOperators Classical Real

noncomputable section

namespace Paper09

/-- A finite site set with nearest-neighbor structure. -/
structure Lattice (V : Type*) [Fintype V] where
  adj : V → V → Prop
  symm : ∀ {x y}, adj x y → adj y x
  irrefl : ∀ x, ¬ adj x x
  maxDegree : ℕ
  degree_le : ∀ x, (univ.filter (fun y => adj x y)).card ≤ maxDegree

namespace Lattice

variable {V : Type*} [Fintype V]

def boundary (Λ : Lattice V) (D : Finset V) : Finset V :=
  univ.filter (fun y => y ∉ D ∧ ∃ x ∈ D, Λ.adj x y)

theorem mem_boundary (Λ : Lattice V) {D : Finset V} {y : V} :
    y ∈ Λ.boundary D ↔ y ∉ D ∧ ∃ x ∈ D, Λ.adj x y := by
  simp [boundary]

/-- Interaction energy: each undirected internal edge contributes exactly once.
The sum below runs over ordered pairs, hence the factor `1/2`. -/
def interaction (Λ : Lattice V) (β : ℝ) (B : Finset V) (η : V → Spin) : ℝ :=
  (β / 2) * ∑ x ∈ B, ∑ y ∈ B,
    if Λ.adj x y then spinVal (η x) * spinVal (η y) else 0

/-- Field energy `Σ_{x ∈ B} h x * η x`. -/
def fieldEnergy (h : V → ℝ) (B : Finset V) (η : V → Spin) : ℝ :=
  ∑ x ∈ B, h x * spinVal (η x)

/-- Boundary energy. -/
def boundEnergy (Λ : Lattice V) (β : ℝ) (B S : Finset V) (φ : V → Spin) (η : V → Spin) : ℝ :=
  β * ∑ x ∈ B, ∑ y ∈ S, if Λ.adj x y then spinVal (η x) * spinVal (φ y) else 0

end Lattice

/-- Unnormalized Ising weight. -/
def isingWeight {V : Type*} [Fintype V]
    (Λ : Lattice V) (h : V → ℝ) (β : ℝ) (B S : Finset V) (φ : V → Spin)
    (η : V → Spin) : ℝ :=
  exp (Lattice.interaction Λ β B η + Lattice.fieldEnergy h B η
      + Lattice.boundEnergy Λ β B S φ η)

theorem isingWeight_pos {V : Type*} [Fintype V]
    (Λ : Lattice V) (h : V → ℝ) (β : ℝ) (B S : Finset V) (φ : V → Spin)
    (η : V → Spin) : 0 < isingWeight Λ h β B S φ η :=
  exp_pos _

/-- Partition function. -/
def isingZ {V : Type*} [Fintype V]
    (Λ : Lattice V) (h : V → ℝ) (β : ℝ) (B S : Finset V) (φ : V → Spin) : ℝ :=
  ∑ η : V → Spin, isingWeight Λ h β B S φ η

theorem isingZ_pos {V : Type*} [Fintype V]
    (Λ : Lattice V) (h : V → ℝ) (β : ℝ) (B S : Finset V) (φ : V → Spin) :
    0 < isingZ Λ h β B S φ := by
  unfold isingZ
  have hne : (univ : Finset (V → Spin)).Nonempty :=
    ⟨fun _ => 0, mem_univ _⟩
  exact sum_pos (fun η _ => isingWeight_pos _ _ _ _ _ _ _) hne

/-- The Ising Gibbs law as a finite probability. -/
def gibbs {V : Type*} [Fintype V]
    (Λ : Lattice V) (h : V → ℝ) (β : ℝ) (B S : Finset V) (φ : V → Spin) :
    FinProb (V → Spin) where
  w := fun η => isingWeight Λ h β B S φ η / isingZ Λ h β B S φ
  nonneg := fun η => div_nonneg (le_of_lt (isingWeight_pos _ _ _ _ _ _ _))
    (le_of_lt (isingZ_pos _ _ _ _ _ _))
  sum_one := by
    have hz : 0 < isingZ Λ h β B S φ := isingZ_pos _ _ _ _ _ _
    have hne : isingZ Λ h β B S φ ≠ 0 := ne_of_gt hz
    have hrewrite : (fun η : V → Spin =>
        isingWeight Λ h β B S φ η / isingZ Λ h β B S φ)
        = (fun η => isingWeight Λ h β B S φ η * (isingZ Λ h β B S φ)⁻¹) := by
      funext η; exact (div_eq_mul_inv _ _).symm
    rw [hrewrite, ← sum_mul]
    have hzsum : (∑ η : V → Spin, isingWeight Λ h β B S φ η) = isingZ Λ h β B S φ := rfl
    rw [hzsum, mul_inv_cancel₀ hne]

theorem gibbs_w {V : Type*} [Fintype V]
    (Λ : Lattice V) (h : V → ℝ) (β : ℝ) (B S : Finset V) (φ : V → Spin)
    (η : V → Spin) :
    (gibbs Λ h β B S φ).w η = isingWeight Λ h β B S φ η / isingZ Λ h β B S φ := rfl

/-- Zero-field Ising measure on `B` with boundary `ζ` on `S`. -/
def pureGibbs {V : Type*} [Fintype V]
    (Λ : Lattice V) (β : ℝ) (B S : Finset V) (ζ : V → Spin) :
    FinProb (V → Spin) :=
  gibbs Λ (fun _ => 0) β B S ζ

/-- `k(τ) = |{y ∈ S : τ y ≠ ζ y}|`. -/
def defectCount {V : Type*} [Fintype V]
    (S : Finset V) (ζ τ : V → Spin) : ℕ :=
  (S.filter (fun y => τ y ≠ ζ y)).card

theorem defectCount_le {V : Type*} [Fintype V]
    (S : Finset V) (ζ τ : V → Spin) :
    defectCount S ζ τ ≤ S.card := card_filter_le _ _

/-- `A_B = ∑_{x ∈ B} |h x|`. -/
def fieldMass {V : Type*} [Fintype V] (h : V → ℝ) (B : Finset V) : ℝ :=
  ∑ x ∈ B, |h x|

theorem fieldMass_nonneg {V : Type*} [Fintype V] (h : V → ℝ) (B : Finset V) :
    0 ≤ fieldMass h B :=
  sum_nonneg fun _ _ => abs_nonneg _

/-- `q_H = 1/(1+exp(2(H-2dβ)))`. -/
def qH (H d β : ℝ) : ℝ := 1 / (1 + exp (2 * (H - 2 * d * β)))

theorem qH_pos (H d β : ℝ) : 0 < qH H d β := by
  unfold qH; positivity

theorem qH_lt_one (H d β : ℝ) : qH H d β < 1 := by
  unfold qH
  have h : 0 < 1 + exp (2 * (H - 2 * d * β)) := by positivity
  have h2 : 1 < 1 + exp (2 * (H - 2 * d * β)) := by
    have := exp_pos (2 * (H - 2 * d * β))
    linarith
  rw [div_lt_one h]
  exact h2

/-- `ρ = 1/(1+exp(2(K-2dβ)))`. -/
def rho (K d β : ℝ) : ℝ := 1 / (1 + exp (2 * (K - 2 * d * β)))

theorem rho_pos (K d β : ℝ) : 0 < rho K d β := by
  unfold rho; positivity

theorem rho_lt_one (K d β : ℝ) : rho K d β < 1 := by
  unfold rho
  have h : 0 < 1 + exp (2 * (K - 2 * d * β)) := by positivity
  have h2 : 1 < 1 + exp (2 * (K - 2 * d * β)) := by
    have := exp_pos (2 * (K - 2 * d * β))
    linarith
  rw [div_lt_one h]
  exact h2

/-- `K_* = 2dβ + (1/2) log(80d)`. -/
def Kstar (d β : ℝ) : ℝ := 2 * d * β + (1 / 2) * log (80 * d)

/-- `σ_0 = 80 d K_*`. -/
def sigma0 (d β : ℝ) : ℝ := 80 * d * Kstar d β

/-- Algebraic identity: `ρ(K_*) = 1/(1+80d)`. -/
theorem rho_Kstar (d β : ℝ) (hd : 0 < d) :
    rho (Kstar d β) d β = 1 / (1 + 80 * d) := by
  unfold rho Kstar
  have harg : 2 * ((2 * d * β + (1 / 2) * log (80 * d)) - 2 * d * β) = log (80 * d) := by
    have : (2 * d * β + (1 / 2) * log (80 * d)) - 2 * d * β = (1 / 2) * log (80 * d) := by ring
    rw [this]; ring
  rw [harg]
  have h : exp (log (80 * d)) = 80 * d := by
    apply exp_log
    positivity
  rw [h]

/-- `1/(1+80d) < 1/(40d)` for `d ≥ 1`. -/
theorem inv_one_add_80d_lt_inv_40d {d : ℝ} (hd : 1 ≤ d) :
    1 / (1 + 80 * d) < 1 / (40 * d) := by
  have h1 : 0 < 1 + 80 * d := by positivity
  have h2 : 0 < 40 * d := by positivity
  rw [div_lt_div_iff₀ h1 h2]
  nlinarith

end Paper09
