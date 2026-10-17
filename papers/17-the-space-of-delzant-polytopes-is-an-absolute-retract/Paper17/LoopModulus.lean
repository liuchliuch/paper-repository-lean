import Paper17.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

/-! The actual modulus of continuity of a continuous map on a compact metric
parameter space, including the quotient-metric circle used in Appendix A. -/
noncomputable section
open scoped Topology
namespace Paper17
section
variable {Θ Z : Type*} [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MetricSpace Z]

def modulusValues (f : Θ → Z) (δ : ℝ) : Set ℝ :=
  (fun p : Θ × Θ => dist (f p.1) (f p.2)) '' {p | dist p.1 p.2 ≤ δ}

def loopModulus (f : Θ → Z) (δ : ℝ) : ℝ := sSup (modulusValues f δ)

theorem modulusValues_bddAbove {f : Θ → Z} (hf : Continuous f) (δ : ℝ) :
    BddAbove (modulusValues f δ) := by
  have hc : IsCompact (Set.range (fun p : Θ × Θ => dist (f p.1) (f p.2))) :=
    isCompact_range ((hf.comp continuous_fst).dist (hf.comp continuous_snd))
  apply hc.bddAbove.mono
  rintro b ⟨p, hp, rfl⟩
  exact ⟨p, rfl⟩

theorem modulusValues_nonempty (f : Θ → Z) {δ : ℝ} (hδ : 0 ≤ δ) :
    (modulusValues f δ).Nonempty := by
  let θ : Θ := Classical.choice inferInstance
  exact ⟨0, (θ, θ), by simpa only [Set.mem_setOf_eq, dist_self] using hδ, dist_self _⟩

theorem loopModulus_nonneg {f : Θ → Z} (hf : Continuous f) {δ : ℝ} (hδ : 0 ≤ δ) :
    0 ≤ loopModulus f δ := by
  let θ : Θ := Classical.choice inferInstance
  exact le_csSup (modulusValues_bddAbove hf δ)
    ⟨(θ, θ), by simpa only [Set.mem_setOf_eq, dist_self] using hδ, dist_self _⟩

theorem dist_le_loopModulus {f : Θ → Z} (hf : Continuous f) {δ : ℝ} {θ φ : Θ}
    (h : dist θ φ ≤ δ) : dist (f θ) (f φ) ≤ loopModulus f δ :=
  le_csSup (modulusValues_bddAbove hf δ) ⟨(θ, φ), h, rfl⟩

theorem loopModulus_mono {f : Θ → Z} (hf : Continuous f) {δ η : ℝ}
    (hδ : 0 ≤ δ) (hδη : δ ≤ η) : loopModulus f δ ≤ loopModulus f η := by
  apply csSup_le (modulusValues_nonempty f hδ)
  rintro b ⟨⟨θ, φ⟩, hθφ, rfl⟩
  exact dist_le_loopModulus hf (hθφ.trans hδη)

@[simp] theorem loopModulus_zero {f : Θ → Z} (hf : Continuous f) : loopModulus f 0 = 0 := by
  apply le_antisymm _ (loopModulus_nonneg hf (le_refl 0))
  apply csSup_le (modulusValues_nonempty f (le_refl 0))
  rintro b ⟨⟨θ, φ⟩, hθφ, rfl⟩
  have he : θ = φ := dist_eq_zero.mp (le_antisymm hθφ dist_nonneg)
  change dist (f θ) (f φ) ≤ 0
  rw [he, dist_self]

/-- Uniform continuity gives an actual uniform small-scale modulus bound. -/
theorem loopModulus_small {f : Θ → Z} (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 ≤ δ → δ < η → loopModulus f δ ≤ ε := by
  obtain ⟨η, hη, hbound⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hf) ε hε
  refine ⟨η, hη, ?_⟩
  intro δ hδ hδη
  apply csSup_le (modulusValues_nonempty f hδ)
  rintro b ⟨⟨θ, φ⟩, hθφ, rfl⟩
  exact (hbound (hθφ.trans_lt hδη)).le

/-- The source modulus tends to zero from the right, uniformly in both circle
parameters. -/
theorem loopModulus_tendsto_zero {f : Θ → Z} (hf : Continuous f) :
    Filter.Tendsto (loopModulus f) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨η, hη, hbound⟩ := loopModulus_small hf (by linarith : (0 : ℝ) < ε / 2)
  refine ⟨η, hη, ?_⟩
  intro δ hδ hdist
  have hδpos : 0 < δ := hδ
  have hδη : δ < η := by simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_pos hδpos] using hdist
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (loopModulus_nonneg hf hδpos.le)]
  linarith [hbound δ hδpos.le hδη]

end
end Paper17
