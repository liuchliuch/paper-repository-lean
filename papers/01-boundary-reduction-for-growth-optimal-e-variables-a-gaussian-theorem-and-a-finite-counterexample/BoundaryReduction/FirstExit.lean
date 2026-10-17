/-
Copyright (c) 2026. Formalization of Lemma 4.3 (First-exit propagation)
from "Boundary reduction for growth-optimal e-variables".

Complete sorry-free proof of the first-exit lemma used to propagate
boundary optimality of a raywise-convex function to the full exterior
of an open set containing the origin.
-/
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Monotone

open Set Real
open scoped Topology

namespace BoundaryReduction

/-! ## Raywise convexity -/

/-- `g` is convex along each ray from the origin when `t ↦ g (t • u)`
is convex on `[0, ∞)` for every direction `u`. -/
def RaywiseConvex {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∀ u : EuclideanSpace ℝ (Fin d), ConvexOn ℝ (Ici (0 : ℝ)) (fun t : ℝ => g (t • u))

/-! ## First-exit time along a ray -/

variable {d : ℕ}

/-- Exit-time set along the ray of `μ` inside `[0,1]`. -/
def exitSet (B : Set (EuclideanSpace ℝ (Fin d)))
    (μ : EuclideanSpace ℝ (Fin d)) : Set ℝ :=
  {s ∈ Icc (0 : ℝ) 1 | s • μ ∉ B}

theorem exitSet_nonempty {B : Set (EuclideanSpace ℝ (Fin d))}
    {μ : EuclideanSpace ℝ (Fin d)} (hμ : μ ∉ B) :
    (exitSet B μ).Nonempty :=
  ⟨1, ⟨zero_le_one, le_refl (1 : ℝ)⟩, by simpa using hμ⟩

theorem exitSet_closed {B : Set (EuclideanSpace ℝ (Fin d))}
    (hB_open : IsOpen B) (μ : EuclideanSpace ℝ (Fin d)) :
    IsClosed (exitSet B μ) := by
  have h1 : IsClosed (Icc (0 : ℝ) 1) := isClosed_Icc
  have h2 : IsClosed {s : ℝ | s • μ ∉ B} := by
    have heq : {s : ℝ | s • μ ∉ B} = (fun s : ℝ => s • μ) ⁻¹' Bᶜ := by
      ext s; simp
    rw [heq]
    exact IsClosed.preimage
      (continuous_id.smul continuous_const : Continuous fun s : ℝ => s • μ)
      (isClosed_compl_iff.mpr hB_open)
  have heq : exitSet B μ = Icc (0 : ℝ) 1 ∩ {s : ℝ | s • μ ∉ B} := by
    ext s; simp [exitSet]
  rw [heq]
  exact h1.inter h2

theorem exitSet_bddBelow {B : Set (EuclideanSpace ℝ (Fin d))}
    (μ : EuclideanSpace ℝ (Fin d)) : BddBelow (exitSet B μ) :=
  bddBelow_Icc.mono (fun _ hs => hs.1)

/-- The first exit parameter belongs to the exit set and is positive. -/
theorem firstExit_mem_pos {B : Set (EuclideanSpace ℝ (Fin d))}
    {μ : EuclideanSpace ℝ (Fin d)}
    (hB_open : IsOpen B) (hB_zero : (0 : EuclideanSpace ℝ (Fin d)) ∈ B)
    (hμ : μ ∉ B) :
    sInf (exitSet B μ) ∈ exitSet B μ ∧ 0 < sInf (exitSet B μ) := by
  have hne := exitSet_nonempty hμ
  have hcl := exitSet_closed hB_open μ
  have hbdd := exitSet_bddBelow (B := B) μ
  have hmem : sInf (exitSet B μ) ∈ exitSet B μ := hcl.csInf_mem hne hbdd
  have hpos : 0 < sInf (exitSet B μ) := by
    by_contra hneg
    push_neg at hneg
    have hz : ¬ ((0 : ℝ) ∈ exitSet B μ) := by
      intro hz
      have hout : (0 : ℝ) • (μ : EuclideanSpace ℝ (Fin d)) ∉ B := hz.2
      rw [zero_smul] at hout
      exact hout hB_zero
    have hge : (0 : ℝ) ≤ sInf (exitSet B μ) :=
      le_csInf hne (fun s hs => hs.1.1)
    have h_eq : sInf (exitSet B μ) = 0 := le_antisymm hneg hge
    rw [h_eq] at hmem
    exact hz hmem
  exact ⟨hmem, hpos⟩

/-- The first exit point lies on the frontier of `B`. -/
theorem firstExit_frontier {B : Set (EuclideanSpace ℝ (Fin d))}
    {μ : EuclideanSpace ℝ (Fin d)}
    (hB_open : IsOpen B) (hB_zero : (0 : EuclideanSpace ℝ (Fin d)) ∈ B)
    (hμ : μ ∉ B) :
    sInf (exitSet B μ) • μ ∈ frontier B := by
  set τ : ℝ := sInf (exitSet B μ) with hτdef
  have hτS : τ ∈ exitSet B μ := (firstExit_mem_pos hB_open hB_zero hμ).1
  have hτ_pos : 0 < τ := (firstExit_mem_pos hB_open hB_zero hμ).2
  have hτ_out : τ • μ ∉ B := hτS.2
  have hnot_int : τ • μ ∉ interior B := by
    intro hint
    exact hτ_out (interior_subset hint)
  have h_in_B : ∀ s ∈ Icc (0 : ℝ) 1, s < τ → s • μ ∈ B := by
    intro s hs hlt
    by_contra hout
    have hsS : s ∈ exitSet B μ := ⟨hs, hout⟩
    have hτ_le : τ ≤ s := csInf_le (exitSet_bddBelow (B := B) μ) hsS
    exact (not_le.mpr hlt) hτ_le
  have hexist : ∃ s : ℕ → ℝ, (∀ n, s n ∈ Icc (0 : ℝ) 1) ∧ (∀ n, s n < τ) ∧
      Filter.Tendsto s Filter.atTop (nhds τ) := by
    refine ⟨fun n => τ - τ / (n + 2), ?_, ?_, ?_⟩
    · intro n
      have h2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by
        have : (0 : ℕ) ≤ n := Nat.zero_le n
        norm_cast; linarith
      have hdiv : τ / (n + 2) ≤ τ := by
        calc τ / ((n : ℝ) + 2) ≤ τ / 2 := by
              apply div_le_div_of_nonneg_left (le_of_lt hτ_pos) (by norm_num) h2
          _ ≤ τ / 1 := by
              apply div_le_div_of_nonneg_left (le_of_lt hτ_pos) (by norm_num) (by norm_num)
          _ = τ := by ring
      have hle1 : τ - τ / (n + 2) ≤ 1 := by
        have hτle : τ ≤ 1 := hτS.1.2
        have hdiv0 : 0 ≤ τ / ((n : ℝ) + 2) :=
          div_nonneg (le_of_lt hτ_pos) (by positivity)
        linarith
      have hge0 : 0 ≤ τ - τ / (n + 2) := by
        have : 0 ≤ τ / ((n : ℝ) + 2) := div_nonneg (le_of_lt hτ_pos) (by positivity)
        linarith
      exact ⟨hge0, hle1⟩
    · intro n
      have hpos : τ / ((n : ℝ) + 2) > 0 := by
        apply div_pos hτ_pos
        have : (0 : ℕ) ≤ n := Nat.zero_le n
        norm_cast; linarith
      linarith
    · have hdiv0 : Filter.Tendsto (fun n : ℕ => τ / ((n : ℝ) + 2)) Filter.atTop (nhds 0) := by
        have hconst : Filter.Tendsto (fun _ : ℕ => (τ : ℝ)) Filter.atTop (nhds τ) :=
          tendsto_const_nhds
        have hden : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 2)) Filter.atTop Filter.atTop := by
          rw [Filter.tendsto_atTop]
          intro b
          rw [Filter.eventually_atTop]
          refine ⟨Nat.ceil b, fun n hn => ?_⟩
          have hb : (b : ℝ) ≤ (n : ℝ) := by
            have h1 : (b : ℝ) ≤ ((Nat.ceil b : ℕ) : ℝ) := Nat.le_ceil b
            have h2 : ((Nat.ceil b : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
            exact le_trans h1 h2
          linarith
        exact hconst.div_atTop hden
      have hsub : Filter.Tendsto (fun n : ℕ => τ - τ / ((n : ℝ) + 2)) Filter.atTop (nhds (τ - 0)) :=
        tendsto_const_nhds.sub hdiv0
      simpa using hsub
  obtain ⟨s, hs_range, hs_lt, hs_tend⟩ := hexist
  have hlim : Filter.Tendsto (fun n => s n • μ) Filter.atTop (nhds (τ • μ)) := by
    have hcont : Continuous (fun t : ℝ => t • μ) :=
      continuous_id.smul continuous_const
    exact hcont.tendsto _ |>.comp hs_tend
  have hcl : τ • μ ∈ closure B := by
    rw [mem_closure_iff_nhds]
    intro N hN
    have hev : ∀ᶠ n in Filter.atTop, s n • μ ∈ N := hlim hN
    obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp hev
    exact ⟨s n • μ, hn n le_rfl, h_in_B (s n) (hs_range n) (hs_lt n)⟩
  exact ⟨hcl, hnot_int⟩

/-- **Lemma 4.3 (First-exit propagation).**

If `B` is an open neighbourhood of the origin, `g` is convex along every
ray from the origin, `g 0 ≤ c`, and `c` lower-bounds `g` on the frontier
of `B`, then `g μ ≥ c` for every exterior point `μ ∉ B`. -/
theorem first_exit_propagation {B : Set (EuclideanSpace ℝ (Fin d))}
    {g : EuclideanSpace ℝ (Fin d) → ℝ} {c : ℝ}
    (hB_open : IsOpen B) (hB_zero : (0 : EuclideanSpace ℝ (Fin d)) ∈ B)
    (hg : RaywiseConvex g) (hg0 : g 0 ≤ c)
    (hboundary : ∀ r ∈ frontier B, c ≤ g r)
    {μ : EuclideanSpace ℝ (Fin d)} (hμ : μ ∉ B) : c ≤ g μ := by
  set τ : ℝ := sInf (exitSet B μ) with hτdef
  have hfront := firstExit_frontier hB_open hB_zero hμ
  have hτS : τ ∈ exitSet B μ := (firstExit_mem_pos hB_open hB_zero hμ).1
  have hτ_pos : 0 < τ := (firstExit_mem_pos hB_open hB_zero hμ).2
  have hτ_le1 : τ ≤ 1 := hτS.1.2
  have hgr : c ≤ g (τ • μ) := hboundary (τ • μ) hfront
  have hg_ray : ConvexOn ℝ (Ici (0 : ℝ)) (fun t : ℝ => g (t • μ)) := hg μ
  have h0 : (0 : ℝ) ∈ Ici (0 : ℝ) := left_mem_Ici
  have h1 : (1 : ℝ) ∈ Ici (0 : ℝ) := by
    show (1 : ℝ) ∈ Ici 0
    exact mem_Ici.2 (by norm_num)
  have ha : 0 ≤ 1 - τ := by linarith
  have hb : 0 ≤ τ := le_of_lt hτ_pos
  have hab : (1 - τ) + τ = 1 := by ring
  have hconv := hg_ray.2 h0 h1 ha hb hab
  have harg : (((1 - τ) : ℝ) • (0 : ℝ) + τ • (1 : ℝ)) = τ := by
    rw [smul_eq_mul, smul_eq_mul, mul_zero, zero_add, mul_one]
  have hlhs : g ((((1 - τ) : ℝ) • (0 : ℝ) + τ • (1 : ℝ)) • μ) = g (τ • μ) := by
    rw [harg]
  have hconv' : g (τ • μ) ≤ (1 - τ) * g 0 + τ * g μ := by
    have h := hconv
    have h3 : (fun t : ℝ => g (t • μ)) 0 = g 0 := by
      change g ((0 : ℝ) • μ) = g 0
      rw [zero_smul]
    have h4 : (fun t : ℝ => g (t • μ)) 1 = g μ := by
      change g ((1 : ℝ) • μ) = g μ
      rw [one_smul]
    rw [harg, h3, h4] at h
    simpa [smul_eq_mul] using h
  by_cases hτ1 : τ = 1
  · have hμfront : μ ∈ frontier B := by
      have h1 : τ • μ = μ := by rw [hτ1, one_smul]
      rw [← h1]
      exact hfront
    exact hboundary μ hμfront
  · have hτ_lt1 : τ < 1 := lt_of_le_of_ne hτ_le1 hτ1
    have hstep : c ≤ (1 - τ) * c + τ * g μ := by
      have h1' : c ≤ (1 - τ) * g 0 + τ * g μ := le_trans hgr hconv'
      have h2' : (1 - τ) * g 0 ≤ (1 - τ) * c :=
        mul_le_mul_of_nonneg_left hg0 (by linarith)
      linarith
    have hτc : τ * c ≤ τ * g μ := by linarith
    exact (mul_le_mul_iff_right₀ hτ_pos).mp hτc

/-- Ball specialization of `first_exit_propagation`. -/
theorem first_exit_ball (g : EuclideanSpace ℝ (Fin d) → ℝ) (c r₀ : ℝ)
    (hr₀ : 0 < r₀)
    (hg : RaywiseConvex g) (hg0 : g 0 ≤ c)
    (hboundary : ∀ r, ‖r‖ = r₀ → c ≤ g r) :
    ∀ μ, r₀ ≤ ‖μ‖ → c ≤ g μ := by
  intro μ hμ
  have hopen : IsOpen (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r₀) :=
    Metric.isOpen_ball
  have hzero : (0 : EuclideanSpace ℝ (Fin d)) ∈ Metric.ball 0 r₀ := by
    simp [Metric.mem_ball, hr₀]
  have hfront : ∀ x ∈ frontier (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r₀),
      c ≤ g x := by
    intro x hx
    have hnorm : ‖x‖ = r₀ := by
      have hx_sphere : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) r₀ := by
        rw [← frontier_ball (0 : EuclideanSpace ℝ (Fin d)) (ne_of_gt hr₀)]
        exact hx
      simpa [Metric.mem_sphere, dist_eq_norm] using hx_sphere
    exact hboundary x hnorm
  have hnotin : μ ∉ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r₀ := by
    intro hmem
    have : dist μ (0 : EuclideanSpace ℝ (Fin d)) < r₀ := by
      simpa [Metric.mem_ball] using hmem
    simp [dist_eq_norm] at this
    linarith
  exact first_exit_propagation hopen hzero hg hg0 hfront hnotin

end BoundaryReduction
