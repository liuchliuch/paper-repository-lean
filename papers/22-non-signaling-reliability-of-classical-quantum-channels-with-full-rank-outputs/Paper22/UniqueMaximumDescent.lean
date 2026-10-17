import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! A compact maximum with a unique active point admits a simultaneous strict
descent whenever a direction decreases that active value. -/
noncomputable section
namespace Paper22

variable {S : Type*} [TopologicalSpace S]

theorem unique_maximum_strict_descent {K : Set S} (hK : IsCompact K)
    {f h : S → ℝ} (hf : Continuous f) (hh : Continuous h) {s₀ : S} (hs₀ : s₀ ∈ K)
    (hmax : ∀ s ∈ K, f s ≤ f s₀)
    (hunique : ∀ s ∈ K, f s=f s₀ → s=s₀) (hneg : h s₀ < 0) :
    ∃ t : ℝ, t ∈ Set.Ioo 0 1 ∧ ∀ s ∈ K, f s+t*h s < f s₀ := by
  let D := K ∩ {s | 0 ≤ h s}
  have hD : IsCompact D := hK.inter_right (isClosed_le continuous_const hh)
  by_cases hne : D.Nonempty
  · obtain ⟨s₁,hs₁,hs₁max⟩ := hD.exists_isMaxOn hne hf.continuousOn
    have hlt : f s₁ < f s₀ := by
      apply lt_of_le_of_ne (hmax s₁ hs₁.1)
      intro heq
      have he := hunique s₁ hs₁.1 heq
      rw [he] at hs₁
      exact hneg.not_ge hs₁.2
    obtain ⟨s₂,hs₂,hs₂max⟩ := hK.exists_isMaxOn ⟨s₀,hs₀⟩ hh.continuousOn
    let M := max 0 (h s₂)
    have hM : 0 ≤ M := le_max_left _ _
    have hhM : ∀ s ∈ K, h s ≤ M := fun s hs => (hs₂max hs).trans (le_max_right _ _)
    have hgap : 0 < (f s₀-f s₁)/(M+1) := div_pos (sub_pos.mpr hlt) (by linarith)
    obtain ⟨t,ht0,ht⟩ := exists_between (lt_min zero_lt_one hgap)
    have ht1 : t < 1 := (lt_min_iff.mp ht).1
    have htm : t*(M+1) < f s₀-f s₁ :=
      (lt_div_iff₀ (by linarith : 0 < M+1)).mp (lt_min_iff.mp ht).2
    refine ⟨t,⟨ht0,ht1⟩,?_⟩
    intro s hs
    by_cases hpos : 0 ≤ h s
    · have hfs := hs₁max (show s ∈ D from ⟨hs,hpos⟩)
      change f s ≤ f s₁ at hfs
      have hhs := mul_le_mul_of_nonneg_left (hhM s hs) ht0.le
      nlinarith
    · have hhneg : h s < 0 := lt_of_not_ge hpos
      have hprod : t*h s < 0 := mul_neg_of_pos_of_neg ht0 hhneg
      have hfs := hmax s hs
      linarith
  · refine ⟨1/2,by norm_num,?_⟩
    intro s hs
    have hhneg : h s < 0 := lt_of_not_ge (fun hn => hne ⟨s,hs,hn⟩)
    have hfs := hmax s hs
    linarith

end Paper22
end
