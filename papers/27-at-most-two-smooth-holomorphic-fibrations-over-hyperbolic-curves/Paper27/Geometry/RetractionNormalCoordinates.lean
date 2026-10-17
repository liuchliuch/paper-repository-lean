import Paper27.Geometry.CyclicModel
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Calculus.DSlope

/-!
# Straightening two target reparametrizations of a cyclic germ

The coordinate construction is an own deduction from ordinary analytic
calculus. The only explicit classical inputs are analyticity of a divided
difference and a local analytic root of a nonvanishing analytic function.
Both are quantified over arbitrary scalar functions; neither mentions
retractions, a normal form, or a ramification component. The holomorphic
inverse function theorem is implemented below using mathlib.
-/
noncomputable section
open scoped Topology
open Filter
namespace Paper27.Geometry.RetractionNormalCoordinates

/-- Ordinary analyticity of the divided difference across its diagonal. -/
def AnalyticDividedDifferences : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ), AnalyticAt ℂ f a →
    AnalyticAt ℂ (fun z : ℂ × ℂ => dslope f z.1 (z.1 + z.2)) (a, 0)

/-- Ordinary local analytic roots of arbitrary analytic units in two
variables. This is a local logarithm/root theorem, not a normal form. -/
def AnalyticUnitRoots : Prop :=
  ∀ (F : ℂ × ℂ → ℂ) (p : ℂ × ℂ), AnalyticAt ℂ F p → F p ≠ 0 →
    ∀ n : ℕ, 0 < n → ∃ ρ : ℂ × ℂ → ℂ,
      AnalyticAt ℂ ρ p ∧ ρ p ≠ 0 ∧ (fun z => ρ z ^ n) =ᶠ[𝓝 p] F

/-- A local analytic chart for an actual nonsingular analytic map, proved
using mathlib's strict inverse and analytic inverse theorems. -/
theorem analytic_chart_exists {F : ℂ × ℂ → ℂ × ℂ} {p : ℂ × ℂ}
    (hF : AnalyticAt ℂ F p) (hbij : Function.Bijective (fderiv ℂ F p)) :
    ∃ c : CyclicModel.AnalyticCoordinateChart p, (c.chart : (ℂ × ℂ) → (ℂ × ℂ)) = F := by
  let L := ContinuousLinearEquiv.ofBijective (fderiv ℂ F p)
    (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2)
  have hs : HasStrictFDerivAt F (L : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) p := hF.hasStrictFDerivAt
  let e := hs.toOpenPartialHomeomorph F
  have he : (e : (ℂ × ℂ) → (ℂ × ℂ)) = F := rfl
  have hunit : IsUnit (fderiv ℂ F p) := ContinuousLinearMap.isUnit_iff_bijective.mpr hbij
  have hnear : {z | AnalyticAt ℂ F z ∧ IsUnit (fderiv ℂ F z)} ∈ 𝓝 p := by
    filter_upwards [hF.eventually_analyticAt,
      hF.fderiv.continuousAt (Units.isOpen.mem_nhds hunit)] with z hz hu
    exact ⟨hz, hu⟩
  obtain ⟨V, hV, hVo, hpV⟩ := mem_nhds_iff.mp hnear
  let e' := e.restrOpen V hVo
  have he' : (e' : (ℂ × ℂ) → (ℂ × ℂ)) = F := rfl
  refine ⟨{ chart := e'
            source_mem := ⟨hs.mem_toOpenPartialHomeomorph_source, hpV⟩
            analytic := fun z hz => by simpa only [he'] using (hV hz.2).1
            inverse_analytic := ?_
            differential_bijective := ?_ }, he'⟩
  · intro y hy
    have hz := e'.map_target hy
    have ha := (hV hz.2).1
    have hb := ContinuousLinearMap.isUnit_iff_bijective.mp (hV hz.2).2
    let Ly := ContinuousLinearEquiv.ofBijective (fderiv ℂ F (e'.symm y))
      (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)
    apply e'.analyticAt_symm hy
    · simpa only [he'] using ha
    · change fderiv ℂ F (e'.symm y) = (Ly : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ))
      rfl
  · intro z hz
    change Function.Bijective (fderiv ℂ F z)
    exact ContinuousLinearMap.isUnit_iff_bijective.mp (hV hz.2).2

structure StraightenedPair (k l φ : ℂ → ℂ) (n : ℕ) (a : ℂ) where
  coordinate : CyclicModel.AnalyticCoordinateChart (a, 0)
  centre : coordinate.chart (a, 0) = (k a, 0)
  first : ∀ z ∈ coordinate.chart.source, (coordinate.chart z).1 = k z.1
  second : ∀ z ∈ coordinate.chart.source,
    l (φ z.1 + z.2 ^ n) = (coordinate.chart z).1 + (coordinate.chart z).2 ^ n

/-- Reparametrizing each target of a cyclic pair again gives normalized
coordinates, now using the same actual base coordinate for both maps. -/
theorem straightenedPair_exists (division : AnalyticDividedDifferences)
    (roots : AnalyticUnitRoots) {k l φ : ℂ → ℂ} {a : ℂ} {n : ℕ} (hn : 0 < n)
    (hk : AnalyticAt ℂ k a) (hl : AnalyticAt ℂ l (φ a)) (hφ : AnalyticAt ℂ φ a)
    (hk' : deriv k a ≠ 0) (hl' : deriv l (φ a) ≠ 0)
    (hcompat : (fun u => l (φ u)) =ᶠ[𝓝 a] k) : Nonempty (StraightenedPair k l φ n a) := by
  let p : ℂ × ℂ := (a, 0)
  let H : ℂ × ℂ → ℂ := fun z => dslope l (φ z.1) (φ z.1 + z.2 ^ n)
  have hH : AnalyticAt ℂ H p := by
    have hbase := division l (φ a) hl
    have hmap : AnalyticAt ℂ (fun z : ℂ × ℂ => (φ z.1, z.2 ^ n)) p :=
      (hφ.comp (show AnalyticAt ℂ Prod.fst p from analyticAt_fst)).prod
        (analyticAt_snd.pow n)
    have hbase' : AnalyticAt ℂ (fun z : ℂ × ℂ => dslope l z.1 (z.1 + z.2))
        ((fun z : ℂ × ℂ => (φ z.1, z.2 ^ n)) p) := by
      simpa only [p, zero_pow (Nat.ne_of_gt hn)] using hbase
    exact AnalyticAt.comp (f := fun z : ℂ × ℂ => (φ z.1, z.2 ^ n)) hbase' hmap
  have hH0 : H p = deriv l (φ a) := by
    simp only [H, p, zero_pow (Nat.ne_of_gt hn), add_zero, dslope_same]
  obtain ⟨ρ, hρ, hρ0, hpower⟩ := roots H p hH (hH0 ▸ hl') n hn
  let F : ℂ × ℂ → ℂ × ℂ := fun z => (k z.1, z.2 * ρ z)
  have hF : AnalyticAt ℂ F p :=
    (hk.comp (show AnalyticAt ℂ Prod.fst p from analyticAt_fst)).prod (analyticAt_snd.mul hρ)
  have hf := hk.differentiableAt.hasFDerivAt.comp p (hasFDerivAt_fst (𝕜 := ℂ) (p := p))
  have hs := (hasFDerivAt_snd (𝕜 := ℂ) (p := p)).mul hρ.differentiableAt.hasFDerivAt
  have hs' : HasFDerivAt (fun z : ℂ × ℂ => z.2 * ρ z)
      (ρ p • ContinuousLinearMap.snd ℂ ℂ ℂ) p := by
    have heq : p.2 • fderiv ℂ ρ p + ρ p • ContinuousLinearMap.snd ℂ ℂ ℂ =
        ρ p • ContinuousLinearMap.snd ℂ ℂ ℂ := by
      apply ContinuousLinearMap.ext
      intro v
      change (0 : ℂ) * fderiv ℂ ρ p v + ρ p * v.2 = ρ p * v.2
      ring
    rw [heq] at hs
    exact hs
  have hfull : HasFDerivAt F
      (((fderiv ℂ k a).comp (ContinuousLinearMap.fst ℂ ℂ ℂ)).prod
        (ρ p • ContinuousLinearMap.snd ℂ ℂ ℂ)) p := hf.prodMk hs'
  have happly : ∀ v : ℂ × ℂ, fderiv ℂ F p v = (deriv k a * v.1, ρ p * v.2) := by
    intro v
    rw [hfull.fderiv]
    simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, fderiv_eq_deriv_mul]
    rfl
  have hbij : Function.Bijective (fderiv ℂ F p) := by
    constructor
    · intro u v huv
      rw [happly, happly] at huv
      exact Prod.ext (mul_left_cancel₀ hk' (congrArg Prod.fst huv))
        (mul_left_cancel₀ hρ0 (congrArg Prod.snd huv))
    · intro w
      refine ⟨(w.1 / deriv k a, w.2 / ρ p), ?_⟩
      rw [happly]
      simp only [mul_div_cancel₀ _ hk', mul_div_cancel₀ _ hρ0, Prod.eta]
  obtain ⟨c, hc⟩ := analytic_chart_exists hF hbij
  have hbase : ∀ᶠ z : ℂ × ℂ in 𝓝 p, l (φ z.1) = k z.1 := by
    have ht : Tendsto (Prod.fst : ℂ × ℂ → ℂ) (𝓝 p) (𝓝 a) := continuousAt_fst
    exact ht hcompat
  have hnormal : ∀ᶠ z in 𝓝 p,
      l (φ z.1 + z.2 ^ n) = k z.1 + (z.2 * ρ z) ^ n := by
    filter_upwards [hbase, hpower] with z hz hpz
    have hdivide := sub_smul_dslope l (φ z.1) (φ z.1 + z.2 ^ n)
    change ρ z ^ n = H z at hpz
    rw [mul_pow, hpz, ← hz]
    dsimp only [H]
    simp only [smul_eq_mul] at hdivide
    linear_combination -hdivide
  obtain ⟨V, hV, hVo, hpV⟩ := mem_nhds_iff.mp hnormal
  let e := c.chart.restrOpen V hVo
  let coordinate : CyclicModel.AnalyticCoordinateChart p :=
    { chart := e
      source_mem := ⟨c.source_mem, hpV⟩
      analytic := fun z hz => c.analytic z hz.1
      inverse_analytic := fun z hz => c.inverse_analytic z hz.1
      differential_bijective := fun z hz => c.differential_bijective z hz.1 }
  refine ⟨{ coordinate := coordinate, centre := ?_, first := ?_, second := ?_ }⟩
  · change c.chart p = (k a, 0)
    rw [hc]
    simp only [F, p, zero_mul]
  · intro z _hz
    change (c.chart z).1 = k z.1
    rw [hc]
  · intro z hz
    change l (φ z.1 + z.2 ^ n) = (c.chart z).1 + (c.chart z).2 ^ n
    rw [hc]
    exact hV hz.2

end Paper27.Geometry.RetractionNormalCoordinates
