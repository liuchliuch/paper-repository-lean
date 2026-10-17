import Paper08.CubeMarginal

/-! # A scoped multiplier bound for actual partial expectations -/
noncomputable section
namespace Paper08.CubeWeighted
open CubeMarginal

/-- Split off precisely the multiplier's integrated coordinates. No phase,
nonvanishing, or factorization premise is needed for this norm estimate. -/
theorem weighted_avg_norm_le {n : ℕ} (S J : Finset (Fin n))
    {f : (Fin n → ℝ) → ℂ} (hf : ContinuousOn f (Integral.cube n))
    {δ : (Fin n → ℝ) → ℝ} (hδcont : ContinuousOn δ (Integral.cube n)) {q : ℝ}
    (hδ : ∀ y ∈ Integral.cube n, |δ y| ≤ q)
    (hdep : ∀ x ∈ Integral.cube n, ∀ y ∈ Integral.cube n,
      (∀ i ∈ J, x i = y i) → δ x = δ y)
    {x : Fin n → ℝ} (hx : x ∈ Integral.cube n) :
    ‖avg S (fun y => (δ y : ℂ) * f y) x‖ ≤
      q * realAvg (S ∩ J) (fun y => ‖avg (S \ (S ∩ J)) f y‖) x := by
  let T := S ∩ J
  let D := S \ T
  have hDT : Disjoint D T := by
    apply Finset.disjoint_left.mpr
    intro i hiD hiT
    exact (Finset.mem_sdiff.mp hiD).2 hiT
  have hDJ : Disjoint D J := by
    apply Finset.disjoint_left.mpr
    intro i hiD hiJ
    have hiS := (Finset.mem_sdiff.mp hiD).1
    exact (Finset.mem_sdiff.mp hiD).2 (Finset.mem_inter.mpr ⟨hiS, hiJ⟩)
  have hDTunion : D ∪ T = S := Finset.sdiff_union_of_subset (Finset.inter_subset_left : T ⊆ S)
  have hδc : ContinuousOn (fun y => (δ y : ℂ)) (Integral.cube n) :=
    Complex.continuous_ofReal.comp_continuousOn hδcont
  have he := avg_union_mul_of_depends D T J hDT hDJ hf hδc
    (fun a ha b hb hab => congrArg Complex.ofReal (hdep a ha b hb hab)) hx
  rw [hDTunion] at he
  rw [he]
  have hA := continuousOn_avg D hf
  calc
    _ ≤ realAvg T (fun y => ‖(δ y : ℂ) * avg D f y‖) x := norm_avg_le_realAvg_norm _ _ _
    _ ≤ realAvg T (fun y => q * ‖avg D f y‖) x := by
      apply realAvg_mono T (hδc.mul hA).norm (continuousOn_const.mul hA.norm) _ hx
      intro y hy
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hδ y hy) (norm_nonneg _)
    _ = _ := realAvg_const_mul T q (fun y => ‖avg D f y‖) x

end Paper08.CubeWeighted
