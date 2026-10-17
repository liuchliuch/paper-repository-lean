/-
Copyright (c) 2026. Heat-bath dynamics, spectral gap, and mixing time.
-/
import Paper09.Ising
import Paper09.SoftShell
import Paper09.Spectral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset BigOperators Classical Real

noncomputable section

namespace Paper09

/-- One-site heat-bath edge: two configurations differing at exactly one site. -/
def oneSite {V : Type*} [Fintype V] (η η' : V → Spin) : Prop :=
  ∃ x, η x ≠ η' x ∧ ∀ y, y ≠ x → η y = η' y

/-- The heat-bath update graph on configurations. -/
def heatBathGraph (V : Type*) [Fintype V] : UpdateGraph (V → Spin) where
  edge := oneSite
  symm := by
    intro a b h
    obtain ⟨x, hx, hrest⟩ := h
    exact ⟨x, Ne.symm hx, fun y hy => (hrest y hy).symm⟩

/-- Dirichlet form of rate-one heat-bath dynamics under a law `p`. -/
def dirichletForm {V : Type*} [Fintype V]
    (p : FinProb (V → Spin)) (f : (V → Spin) → ℝ) : ℝ :=
  (1 / 2) * (heatBathGraph V).dirichlet p f

/-- The probability per rate-one clock ring of changing from `η` to its
one-site neighbor `η'`. The strict-positive Gibbs case is the usual
conditional heat-bath probability. -/
def heatBathRate {V : Type*} [Fintype V]
    (p : FinProb (V → Spin)) (η η' : V → Spin) : ℝ :=
  if oneSite η η' then p.w η' / (p.w η + p.w η') else 0

/-- Continuous-time heat-bath generator; unchanged-site clock rings have
zero increment and consequently do not occur in this expression. -/
def heatBathGenerator {V : Type*} [Fintype V]
    (p : FinProb (V → Spin)) (f : (V → Spin) → ℝ) (η : V → Spin) : ℝ :=
  ∑ η', heatBathRate p η η' * (f η' - f η)

theorem heatBathRate_nonneg {V : Type*} [Fintype V]
    (p : FinProb (V → Spin)) (η η' : V → Spin) :
    0 ≤ heatBathRate p η η' := by
  unfold heatBathRate
  split_ifs
  · exact div_nonneg (p.nonneg _) (add_nonneg (p.nonneg _) (p.nonneg _))
  · exact le_rfl

theorem heatBathRate_weight {V : Type*} [Fintype V]
    (p : FinProb (V → Spin)) (η η' : V → Spin) :
    p.w η * heatBathRate p η η' =
      if oneSite η η' then conductance p η η' else 0 := by
  unfold heatBathRate conductance
  split_ifs <;> ring

theorem heatBathRate_reversible {V : Type*} [Fintype V]
    (p : FinProb (V → Spin)) (η η' : V → Spin) :
    p.w η * heatBathRate p η η' = p.w η' * heatBathRate p η' η := by
  rw [heatBathRate_weight, heatBathRate_weight]
  have he : oneSite η η' ↔ oneSite η' η :=
    ⟨(heatBathGraph V).symm, (heatBathGraph V).symm⟩
  simp only [he, conductance, mul_comm, add_comm]

/-- The factor `1/2` in `dirichletForm` is forced by integration by parts
against the rate-one generator. -/
theorem dirichletForm_eq_neg_generator {V : Type*} [Fintype V]
    (p : FinProb (V → Spin)) (f : (V → Spin) → ℝ) :
    dirichletForm p f =
      - FinProb.expect p (fun η => f η * heatBathGenerator p f η) := by
  let c := fun η η' => p.w η * heatBathRate p η η'
  have hsym (η η' : V → Spin) : c η η' = c η' η := heatBathRate_reversible p η η'
  have hswap : (∑ η : V → Spin, ∑ η' : V → Spin, c η η' * (f η') ^ 2) =
      ∑ η : V → Spin, ∑ η' : V → Spin, c η η' * (f η) ^ 2 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro η _
    apply sum_congr rfl
    intro η' _
    rw [hsym]
  have he : dirichletForm p f =
      (1 / 2) * ∑ η : V → Spin, ∑ η' : V → Spin, c η η' * (f η - f η') ^ 2 := by
    unfold dirichletForm UpdateGraph.dirichlet
    congr 1
    apply sum_congr rfl
    intro η _
    apply sum_congr rfl
    intro η' _
    dsimp [c]
    rw [heatBathRate_weight]
    change (if oneSite η η' then _ else _) = _
    split_ifs <;> simp
  rw [he]
  have halg (η η' : V → Spin) :
      c η η' * (f η - f η') ^ 2 = c η η' * (f η) ^ 2 +
        c η η' * (f η') ^ 2 - 2 * (c η η' * f η * f η') := by ring
  simp_rw [halg, sum_sub_distrib, sum_add_distrib, ← mul_sum]
  rw [hswap]
  unfold FinProb.expect heatBathGenerator
  simp_rw [mul_sum]
  have hprod (η η' : V → Spin) :
      p.w η * (f η * (heatBathRate p η η' * (f η' - f η))) =
        c η η' * f η * f η' - c η η' * (f η) ^ 2 := by
    dsimp [c]
    ring
  simp_rw [hprod, sum_sub_distrib, ← mul_sum]
  ring

/-- Rayleigh quotients of nonconstant statistics in `L²(p)`. -/
def rayleighValues {V : Type*} [Fintype V]
    (p : FinProb (V → Spin)) : Set ℝ :=
  {r | ∃ f : (V → Spin) → ℝ,
    0 < FinProb.variance p f ∧ r = dirichletForm p f / FinProb.variance p f}

/-- Spectral gap of the rate-one heat-bath chain, as a Rayleigh infimum.
For a law supported at one configuration there are no positive-variance
statistics; we explicitly assign gap zero in that degenerate case. -/
def spectralGap {V : Type*} [Fintype V]
    (p : FinProb (V → Spin)) : ℝ :=
  if (rayleighValues p).Nonempty then sInf (rayleighValues p) else 0

/-- Relaxation time `t_rel = gap^{-1}`. -/
def tRel {V : Type*} [Fintype V] (p : FinProb (V → Spin)) : ℝ :=
  (spectralGap p)⁻¹

/-- Total-variation distance. -/
def tvDist {α : Type*} [Fintype α] (μ ν : FinProb α) : ℝ :=
  (1 / 2) * ∑ x, |μ.w x - ν.w x|

/-- Worst-start mixing time at error `ε`. -/
def tMix {α : Type*} [Fintype α]
    (p : FinProb α)
    (K : ℝ → α → FinProb α) (ε : ℝ) : ℝ :=
  sInf {t | 0 ≤ t ∧ ∀ η, tvDist (K t η) p ≤ ε}

theorem dirichletForm_nonneg {V : Type*} [Fintype V]
    (p : FinProb (V → Spin)) (f : (V → Spin) → ℝ) :
    0 ≤ dirichletForm p f := by
  exact mul_nonneg (by norm_num) ((heatBathGraph V).dirichlet_nonneg p f)

/-- The Rayleigh set is bounded below, even for laws with zero weights. -/
theorem rayleighValues_bddBelow {V : Type*} [Fintype V]
    (p : FinProb (V → Spin)) : BddBelow (rayleighValues p) := by
  refine ⟨0, ?_⟩
  rintro r ⟨f, hf, rfl⟩
  exact div_nonneg (dirichletForm_nonneg p f) hf.le

theorem spectralGap_nonneg {V : Type*} [Fintype V]
    (p : FinProb (V → Spin)) : 0 ≤ spectralGap p := by
  unfold spectralGap
  split_ifs with h
  · refine le_csInf h ?_
    rintro r ⟨f, hf, rfl⟩
    exact div_nonneg (dirichletForm_nonneg p f) hf.le
  · exact le_rfl

/-- Every positive-variance trial function gives a genuine upper bound on the gap. -/
theorem spectralGap_le_rayleigh {V : Type*} [Fintype V]
    (p : FinProb (V → Spin)) (f : (V → Spin) → ℝ)
    (hf : 0 < FinProb.variance p f) :
    spectralGap p ≤ dirichletForm p f / FinProb.variance p f := by
  have hm : dirichletForm p f / FinProb.variance p f ∈ rayleighValues p :=
    ⟨f, hf, rfl⟩
  rw [spectralGap, if_pos ⟨_, hm⟩]
  exact csInf_le (rayleighValues_bddBelow p) hm

/-- The variational definition implies the Poincaré inequality for every statistic. -/
theorem spectralGap_poincare {V : Type*} [Fintype V]
    (p : FinProb (V → Spin)) (f : (V → Spin) → ℝ) :
    spectralGap p * FinProb.variance p f ≤ dirichletForm p f := by
  by_cases hf : 0 < FinProb.variance p f
  · exact (le_div_iff₀ hf).mp (spectralGap_le_rayleigh p f hf)
  · have hz : FinProb.variance p f = 0 :=
      le_antisymm (le_of_not_gt hf) (FinProb.variance_nonneg p f)
    rw [hz, mul_zero]
    exact dirichletForm_nonneg p f

/-- Conversely a Poincaré constant bounds the gap from below whenever the
positive-variance subspace is nontrivial. -/
theorem le_spectralGap {V : Type*} [Fintype V]
    (p : FinProb (V → Spin)) (hn : (rayleighValues p).Nonempty) {c : ℝ}
    (hc : ∀ f : (V → Spin) → ℝ,
      c * FinProb.variance p f ≤ dirichletForm p f) :
    c ≤ spectralGap p := by
  rw [spectralGap, if_pos hn]
  refine le_csInf hn ?_
  rintro r ⟨f, hf, rfl⟩
  exact (le_div_iff₀ hf).mpr (hc f)

/-- A pointwise mixing estimate at an actual time bounds the infimum of good times. -/
theorem tMix_le {α : Type*} [Fintype α]
    (p : FinProb α)
    (K : ℝ → α → FinProb α) {ε t : ℝ}
    (ht : 0 ≤ t) (h : ∀ η, tvDist (K t η) p ≤ ε) :
    tMix p K ε ≤ t := by
  exact csInf_le ⟨0, fun _ hs => hs.1⟩ ⟨ht, h⟩

/-- A lower bound valid at every good time bounds the mixing time, provided
that the chain actually reaches the requested precision. -/
theorem le_tMix {α : Type*} [Fintype α]
    (p : FinProb α)
    (K : ℝ → α → FinProb α) {ε a : ℝ}
    (hne : ∃ t, 0 ≤ t ∧ ∀ η, tvDist (K t η) p ≤ ε)
    (h : ∀ t, 0 ≤ t → (∀ η, tvDist (K t η) p ≤ ε) → a ≤ t) :
    a ≤ tMix p K ε := by
  exact le_csInf hne (fun t ht => h t ht.1 ht.2)

/-- Assumption 1.2 numeric package. -/
structure StrongDisorder (d β K pK : ℝ) : Prop where
  K_pos : 0 < K
  rho_lt : rho K d β < 1 / (40 * d)
  pK_lt : pK < 1 / (40 * d)

theorem tRel_eq {V : Type*} [Fintype V] (p : FinProb (V → Spin)) :
    tRel p = (spectralGap p)⁻¹ := rfl

end Paper09
