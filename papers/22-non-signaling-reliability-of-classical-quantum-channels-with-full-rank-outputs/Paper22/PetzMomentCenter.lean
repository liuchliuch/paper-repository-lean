import Paper22.PetzMomentOptimize

/-! A minimizing input law produces a common Petz center for every input letter. -/
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
noncomputable section
namespace Paper22
variable {n d : ℕ}

abbrev DensityState (d : ℕ) := {σ : Matrix (Fin d) (Fin d) ℂ // IsDensity σ}

theorem exists_petzMoment_minimizer (V : CQChannel n d) (hn : 0 < n)
    {α : ℝ} (hα : α ∈ Set.Ioo 0 1) :
    ∃ q ∈ probabilitySimplex n, ∀ r ∈ probabilitySimplex n,
      petzMomentValue V q α ≤ petzMomentValue V r α := by
  obtain ⟨q,hq,hmin⟩ := (isCompact_probabilitySimplex n).exists_isMinOn
    (probabilitySimplex_nonempty hn) (continuousOn_petzMomentValue V hα)
  exact ⟨q,hq,fun r hr => hmin hr⟩

/-- A minimizer of the moment has a center whose trace against every input is
at least the minimized value. This follows from uniqueness of the density
maximizer and compact strict descent. -/
theorem petzMoment_minimizer_center (V : CQChannel n d)
    {q : Fin n → ℝ} (hq : q ∈ probabilitySimplex n) {α : ℝ} (hα : α ∈ Set.Ioo 0 1)
    (hmin : ∀ r ∈ probabilitySimplex n, petzMomentValue V q α ≤ petzMomentValue V r α) :
    ∀ x, petzMomentValue V q α ≤ petzTrace α (V.states x) (petzMomentCenter V q α) := by
  letI : CompactSpace (DensityState d) := isCompact_iff_compactSpace.mp (isCompact_densityOperators d)
  let σ₀ : DensityState d := ⟨petzMomentCenter V q α,petzMomentCenter_isDensity V hq.1 hq.2 hα.1⟩
  let f : DensityState d → ℝ := fun σ => ∑ y, q y*petzTrace α (V.states y) σ.val
  have hletter (x : Fin n) : Continuous (fun σ : DensityState d => petzTrace α (V.states x) σ.val) :=
    continuous_density_testing_trace (CFC.rpow (V.states x) α) (by linarith [hα.2])
  have hf : Continuous f := continuous_finset_sum _ (fun y _ => continuous_const.mul (hletter y))
  have hf₀ : f σ₀=petzMomentValue V q α := petzMomentValue_at_center V hq.1 hq.2 hα
  have hmax : ∀ σ ∈ (Set.univ : Set (DensityState d)), f σ ≤ f σ₀ := by
    intro σ _
    rw [hf₀]
    exact petzMomentValue_upper V hq.1 hα σ.prop
  have huniq : ∀ σ ∈ (Set.univ : Set (DensityState d)), f σ=f σ₀ → σ=σ₀ := by
    intro σ _ heq
    apply Subtype.ext
    exact (petzMomentValue_equality V hq.1 hq.2 hα σ.prop).mp (heq.trans hf₀)
  intro x
  by_contra hno
  let h : DensityState d → ℝ := fun σ => petzTrace α (V.states x) σ.val-f σ
  have hh : Continuous h := (hletter x).sub hf
  have hh₀ : h σ₀ < 0 := by
    change petzTrace α (V.states x) σ₀.val-f σ₀ < 0
    rw [hf₀]
    exact sub_neg.mpr (lt_of_not_ge hno)
  obtain ⟨t,ht,hdescent⟩ := unique_maximum_strict_descent isCompact_univ hf hh
    (Set.mem_univ σ₀) hmax huniq hh₀
  let r : Fin n → ℝ := fun y => (1-t)*q y+t*(if y=x then 1 else 0)
  have hr : r ∈ probabilitySimplex n := by
    constructor
    · intro y
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2.le) (hq.1 y))
        (mul_nonneg ht.1.le (by split_ifs <;> norm_num))
    · simp only [r,Finset.sum_add_distrib,← Finset.mul_sum,hq.2]
      simp
  let σ₁ : DensityState d := ⟨petzMomentCenter V r α,petzMomentCenter_isDensity V hr.1 hr.2 hα.1⟩
  have hrvalue : (∑ y, r y*petzTrace α (V.states y) σ₁.val)=petzMomentValue V r α :=
    petzMomentValue_at_center V hr.1 hr.2 hα
  have hexpr : (∑ y, r y*petzTrace α (V.states y) σ₁.val)=f σ₁+t*h σ₁ := by
    simp only [r,add_mul,Finset.sum_add_distrib,mul_assoc]
    rw [← Finset.mul_sum,← Finset.mul_sum]
    have hpure : (∑ y, (if y=x then (1:ℝ) else 0)*petzTrace α (V.states y) σ₁.val) =
        petzTrace α (V.states x) σ₁.val := by simp
    rw [hpure]
    dsimp only [h,f]
    ring
  have hstrict := hdescent σ₁ (Set.mem_univ _)
  rw [← hexpr,hrvalue,hf₀] at hstrict
  exact (hmin r hr).not_gt hstrict

end Paper22
end
