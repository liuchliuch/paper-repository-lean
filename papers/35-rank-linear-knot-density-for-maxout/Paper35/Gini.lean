import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# The sharp Gini–standard-deviation inequality (Lemma 4.2)

The proof uses the symmetrized rank score rather than a quantile. Its second
moment is at most `1/3`, including laws with atoms. The three-copy comparison
identity below is what gives the sharp constant.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace Paper35.Gini

/-- Antisymmetric comparison, with ties assigned score zero. -/
def cmp (x y : ℝ) : ℝ := if y < x then 1 else if x < y then -1 else 0

lemma cmp_neg (x y : ℝ) : cmp y x = -cmp x y := by
  unfold cmp
  split_ifs <;> (try simp_all) <;> linarith

lemma cmp_norm_le (x y : ℝ) : ‖cmp x y‖ ≤ 1 := by
  unfold cmp
  split_ifs <;> norm_num

lemma cmp_mul_sub (x y : ℝ) : (x - y) * cmp x y = |x-y| := by
  unfold cmp
  split_ifs with h h'
  · rw [abs_of_pos (sub_pos.mpr h)]; ring
  · rw [abs_of_neg (sub_neg.mpr h')]; ring
  · have : x = y := le_antisymm (le_of_not_gt h) (le_of_not_gt h')
    simp [this]

lemma cmp_three (x y z : ℝ) :
    cmp x y * cmp x z + cmp y x * cmp y z + cmp z x * cmp z y ≤ 1 := by
  unfold cmp
  split_ifs <;> norm_num at * <;> linarith

lemma measurable_cmp {α : Type*} [MeasurableSpace α] {f g : α → ℝ}
    (hf : Measurable f) (hg : Measurable g) : Measurable (fun x => cmp (f x) (g x)) := by
  exact Measurable.ite (measurableSet_lt hg hf) measurable_const
    (Measurable.ite (measurableSet_lt hf hg) measurable_const measurable_const)

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (X : Ω → ℝ)

/-- The mean signed rank of a value of `X` against an independent copy. -/
def score (x : Ω) : ℝ := ∫ y, cmp (X x) (X y) ∂μ

lemma score_stronglyMeasurable (hX : Measurable X) : StronglyMeasurable (score μ X) := by
  exact (measurable_cmp (hX.comp measurable_fst) (hX.comp measurable_snd)).stronglyMeasurable.integral_prod_right

lemma cmp_integrable (hX : Measurable X) (x : Ω) :
    Integrable (fun y => cmp (X x) (X y)) μ := by
  exact (MemLp.of_bound (measurable_cmp measurable_const hX).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun y => cmp_norm_le _ _) : MemLp _ 1 μ).integrable le_rfl

lemma score_norm_le (x : Ω) : ‖score μ X x‖ ≤ 1 := by
  calc
    ‖score μ X x‖ ≤ ∫ y, ‖cmp (X x) (X y)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ _y, (1 : ℝ) ∂μ := integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun _ => norm_nonneg _) (integrable_const 1)
      (Filter.Eventually.of_forall fun y => cmp_norm_le _ _)
    _ = 1 := by simp

lemma score_memLp (hX : Measurable X) (p : ℝ≥0∞) : MemLp (score μ X) p μ :=
  MemLp.of_bound (score_stronglyMeasurable μ X hX).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => score_norm_le μ X x)

/-- All products of two comparison scores on a probability space are integrable. -/
lemma cmp_product_integrable {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] {f g h k : α → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) (hk : Measurable k) :
    Integrable (fun a => cmp (f a) (g a) * cmp (h a) (k a)) ν := by
  apply (MemLp.of_bound ((measurable_cmp hf hg).mul (measurable_cmp hh hk)).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun a => ?_) : MemLp _ 1 ν).integrable le_rfl
  rw [norm_mul]
  exact (mul_le_mul (cmp_norm_le _ _) (cmp_norm_le _ _) (norm_nonneg _) (by norm_num)).trans (by norm_num)

/-- The sharp second-moment estimate for the signed rank, valid with atoms. -/
theorem score_second_moment (hX : Measurable X) :
    ∫ x, score μ X x ^ 2 ∂μ ≤ (1 : ℝ) / 3 := by
  let A : ℝ := ∫ x, ∫ y, ∫ z, cmp (X x) (X y) * cmp (X x) (X z) ∂μ ∂μ ∂μ
  have hfactor : A = ∫ x, score μ X x ^ 2 ∂μ := by
    dsimp [A, score]
    congr 1
    funext x
    simp_rw [integral_const_mul, integral_mul_const, pow_two]
  have hB : (∫ x, ∫ y, ∫ z, cmp (X y) (X x) * cmp (X y) (X z) ∂μ ∂μ ∂μ) = A := by
    change _ = ∫ y, ∫ x, ∫ z, cmp (X y) (X x) * cmp (X y) (X z) ∂μ ∂μ ∂μ
    exact integral_integral_swap (cmp_product_integrable ((μ.prod μ).prod μ)
      (hX.comp (measurable_snd.comp measurable_fst))
      (hX.comp (measurable_fst.comp measurable_fst))
      (hX.comp (measurable_snd.comp measurable_fst))
      (hX.comp measurable_snd)).integral_prod_left
  have hC : (∫ x, ∫ y, ∫ z, cmp (X z) (X x) * cmp (X z) (X y) ∂μ ∂μ ∂μ) = A := by
    calc
      _ = ∫ x, ∫ z, ∫ y, cmp (X z) (X x) * cmp (X z) (X y) ∂μ ∂μ ∂μ := by
        congr 1
        funext x
        exact integral_integral_swap (cmp_product_integrable (μ.prod μ)
          (hX.comp measurable_snd) measurable_const
          (hX.comp measurable_snd) (hX.comp measurable_fst))
      _ = ∫ z, ∫ x, ∫ y, cmp (X z) (X x) * cmp (X z) (X y) ∂μ ∂μ ∂μ := by
        exact integral_integral_swap (cmp_product_integrable ((μ.prod μ).prod μ)
          (hX.comp (measurable_snd.comp measurable_fst))
          (hX.comp (measurable_fst.comp measurable_fst))
          (hX.comp (measurable_snd.comp measurable_fst))
          (hX.comp measurable_snd)).integral_prod_left
      _ = A := rfl
  have hpoint (x y : Ω) :
      (∫ z, cmp (X x) (X y) * cmp (X x) (X z) ∂μ) +
      (∫ z, cmp (X y) (X x) * cmp (X y) (X z) ∂μ) +
      (∫ z, cmp (X z) (X x) * cmp (X z) (X y) ∂μ) ≤ 1 := by
    rw [← integral_add, ← integral_add]
    · simpa using integral_mono
        ((cmp_product_integrable μ measurable_const measurable_const measurable_const hX).add
          (cmp_product_integrable μ measurable_const measurable_const measurable_const hX) |>.add
          (cmp_product_integrable μ hX measurable_const hX measurable_const))
        (integrable_const (1 : ℝ)) (fun z => cmp_three (X x) (X y) (X z))
    all_goals first
      | exact cmp_product_integrable μ measurable_const measurable_const measurable_const hX
      | exact cmp_product_integrable μ hX measurable_const hX measurable_const
      | exact (cmp_product_integrable μ measurable_const measurable_const measurable_const hX).add
          (cmp_product_integrable μ measurable_const measurable_const measurable_const hX)
  have hbound : A + A + A ≤ 1 := by
    have hAB := (cmp_product_integrable ((μ.prod μ).prod μ)
      (hX.comp (measurable_fst.comp measurable_fst))
      (hX.comp (measurable_snd.comp measurable_fst))
      (hX.comp (measurable_fst.comp measurable_fst))
      (hX.comp measurable_snd)).integral_prod_left
    have hBB := (cmp_product_integrable ((μ.prod μ).prod μ)
      (hX.comp (measurable_snd.comp measurable_fst))
      (hX.comp (measurable_fst.comp measurable_fst))
      (hX.comp (measurable_snd.comp measurable_fst))
      (hX.comp measurable_snd)).integral_prod_left
    have hCB := (cmp_product_integrable ((μ.prod μ).prod μ)
      (hX.comp measurable_snd)
      (hX.comp (measurable_fst.comp measurable_fst))
      (hX.comp measurable_snd)
      (hX.comp (measurable_snd.comp measurable_fst))).integral_prod_left
    have hint : (∫ p : Ω × Ω,
      ((∫ z, cmp (X p.1) (X p.2) * cmp (X p.1) (X z) ∂μ) +
      (∫ z, cmp (X p.2) (X p.1) * cmp (X p.2) (X z) ∂μ) +
      (∫ z, cmp (X z) (X p.1) * cmp (X z) (X p.2) ∂μ)) ∂μ.prod μ) ≤ 1 := by
      simpa using integral_mono ((hAB.add hBB).add hCB) (integrable_const (1 : ℝ))
        (fun p => hpoint p.1 p.2)
    have heq := integral_add (hAB.add hBB) hCB
    have heq' := integral_add hAB hBB
    simp only [Pi.add_apply, Function.comp_apply] at heq heq'
    have heA := integral_prod _ hAB
    have heB := integral_prod _ hBB
    have heC := integral_prod _ hCB
    simp only [Function.comp_apply] at heA heB heC
    rw [heq, heq', heA, heB, heC, hB, hC] at hint
    exact hint
  rw [hfactor] at hbound
  linarith

/-- The Gini mean difference of canonical independent copies. -/
def meanDifference : ℝ := ∫ p : Ω × Ω, |X p.1 - X p.2| ∂μ.prod μ

lemma meanDifference_nonneg : 0 ≤ meanDifference μ X :=
  integral_nonneg (fun p => abs_nonneg _)

lemma meanDifference_score (hX : Measurable X) (hX2 : MemLp X 2 μ) :
    meanDifference μ X = 2 * ∫ x, (X x - ∫ y, X y ∂μ) * score μ X x ∂μ := by
  let f := fun x => X x - ∫ y, X y ∂μ
  have hf : MemLp f 2 μ := hX2.sub (memLp_const _)
  have hi : Integrable f μ := hf.integrable (by norm_num)
  have hc : Measurable (fun p : Ω × Ω => cmp (X p.1) (X p.2)) :=
    measurable_cmp (hX.comp measurable_fst) (hX.comp measurable_snd)
  have hleft : Integrable (fun p : Ω × Ω => f p.1 * cmp (X p.1) (X p.2)) (μ.prod μ) := by
    simpa only [mul_comm] using (hi.comp_fst μ).bdd_mul hc.aestronglyMeasurable
      ⟨1, fun p => cmp_norm_le _ _⟩
  have hright : Integrable (fun p : Ω × Ω => f p.2 * cmp (X p.1) (X p.2)) (μ.prod μ) := by
    simpa only [mul_comm] using (hi.comp_snd μ).bdd_mul hc.aestronglyMeasurable
      ⟨1, fun p => cmp_norm_le _ _⟩
  have hswap : (∫ p : Ω × Ω, f p.2 * cmp (X p.1) (X p.2) ∂μ.prod μ) =
      -(∫ p : Ω × Ω, f p.1 * cmp (X p.1) (X p.2) ∂μ.prod μ) := by
    calc
      _ = ∫ p : Ω × Ω, f p.1 * cmp (X p.2) (X p.1) ∂μ.prod μ :=
        (integral_prod_swap (fun p : Ω × Ω => f p.2 * cmp (X p.1) (X p.2))).symm
      _ = _ := by
        have heq : (fun p : Ω × Ω => f p.1 * cmp (X p.2) (X p.1)) =
            (fun p => -(f p.1 * cmp (X p.1) (X p.2))) := by
          funext p
          rw [cmp_neg (X p.1) (X p.2), mul_neg]
        rw [heq, integral_neg]
  have hrepr : (∫ p : Ω × Ω, f p.1 * cmp (X p.1) (X p.2) ∂μ.prod μ) =
      ∫ x, f x * score μ X x ∂μ := by
    rw [integral_prod _ hleft]
    simp_rw [score, integral_const_mul]
  calc
    meanDifference μ X = ∫ p : Ω × Ω,
        (f p.1 * cmp (X p.1) (X p.2) - f p.2 * cmp (X p.1) (X p.2)) ∂μ.prod μ := by
      unfold meanDifference
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun p => by
        change |X p.1-X p.2| = f p.1 * cmp (X p.1) (X p.2) - f p.2 * cmp (X p.1) (X p.2)
        rw [← sub_mul, show f p.1 - f p.2 = X p.1 - X p.2 by dsimp [f]; ring,
          cmp_mul_sub]
    _ = _ := by rw [integral_sub hleft hright, hswap, hrepr]; ring

/-- Sharp Gini bound for a square-integrable real variable and its canonical
independent copy. The hypotheses are ordinary measurability and an `L²` moment. -/
theorem sharp_gini_product (hX : Measurable X) (hX2 : MemLp X 2 μ) :
    meanDifference μ X ≤ (2 / Real.sqrt 3) * Real.sqrt (variance X μ) := by
  let f := fun x => X x - ∫ y, X y ∂μ
  let g := score μ X
  let c := ∫ x, f x * g x ∂μ
  have hf : MemLp f 2 μ := hX2.sub (memLp_const _)
  have hg : MemLp g 2 μ := score_memLp μ X hX 2
  have hfg : Integrable (fun x => f x * g x) μ := hf.integrable_mul hg
  have hnn : 0 ≤ ∫ x, (f x - (3*c) * g x)^2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  have hexp : (∫ x, (f x - (3*c) * g x)^2 ∂μ) =
      variance X μ - 6*c*c + 9*c*c * ∫ x, g x^2 ∂μ := by
    simp_rw [show ∀ x, (f x - (3*c) * g x)^2 =
      f x^2 - (6*c)*(f x*g x) + (9*c*c)*(g x^2) by intro x; ring]
    have heq := integral_add (hf.integrable_sq.sub (hfg.const_mul (6*c)))
      (hg.integrable_sq.const_mul (9*c*c))
    have heq' := integral_sub hf.integrable_sq (hfg.const_mul (6*c))
    simp only [Pi.add_apply, Pi.sub_apply] at heq heq'
    rw [heq, heq', integral_const_mul, integral_const_mul]
    change (∫ x, (X x - ∫ y, X y ∂μ)^2 ∂μ) - 6*c*c +
      9*c*c * ∫ x, g x^2 ∂μ = _
    rw [← variance_eq_integral hX.aemeasurable]
  have hscore : ∫ x, g x^2 ∂μ ≤ (1 : ℝ)/3 := score_second_moment μ X hX
  have hcs : 3*c^2 ≤ variance X μ := by
    rw [hexp] at hnn
    have : 9*c*c * (∫ x, g x^2 ∂μ) ≤ 3*c*c := by
      nlinarith [mul_nonneg (sq_nonneg c) (sub_nonneg.mpr hscore)]
    nlinarith
  have hvar : 0 ≤ variance X μ := variance_nonneg X μ
  have hs3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hsv := Real.sq_sqrt hvar
  have hs3pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hcp : 0 ≤ c := by
    have := meanDifference_nonneg μ X
    rw [meanDifference_score μ X hX hX2] at this
    change 0 ≤ 2*c at this
    linarith
  have hroot : c * Real.sqrt 3 ≤ Real.sqrt (variance X μ) := by
    apply (sq_le_sq₀ (mul_nonneg hcp hs3pos.le) (Real.sqrt_nonneg _)).mp
    rw [mul_pow, hs3, hsv]
    nlinarith
  rw [meanDifference_score μ X hX hX2]
  change 2*c ≤ (2 / Real.sqrt 3) * Real.sqrt (variance X μ)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hs3pos).2
  nlinarith

/-- Lemma 4.2 with the original random-variable quantifiers: `Y` is any
independent, identically distributed copy of the square-integrable variable `X`.
No continuity or density assumption on the common law is imposed. -/
theorem sharp_gini_iid (Y : Ω → ℝ) (hX2 : MemLp X 2 μ)
    (hiid : IdentDistrib X Y μ μ) (hind : IndepFun X Y μ) :
    (∫ ω, |X ω - Y ω| ∂μ) ≤ (2 / Real.sqrt 3) * Real.sqrt (variance X μ) := by
  let ν := μ.map X
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hiid.aemeasurable_fst
  have hmem : MemLp (id : ℝ → ℝ) 2 ν := by
    apply (memLp_map_measure_iff measurable_id.aestronglyMeasurable hiid.aemeasurable_fst).2
    exact hX2
  have H := sharp_gini_product ν (id : ℝ → ℝ) measurable_id hmem
  have hmap : μ.map (fun ω => (X ω, Y ω)) = ν.prod ν := by
    change μ.map (fun ω => (X ω, Y ω)) = (μ.map X).prod (μ.map X)
    rw [(indepFun_iff_map_prod_eq_prod_map_map hiid.aemeasurable_fst hiid.aemeasurable_snd).mp hind,
      hiid.map_eq]
  have hint : meanDifference ν (id : ℝ → ℝ) = ∫ ω, |X ω - Y ω| ∂μ := by
    unfold meanDifference
    rw [← hmap]
    exact integral_map (hiid.aemeasurable_fst.prodMk hiid.aemeasurable_snd)
      (by simpa only [Real.norm_eq_abs] using
        (measurable_fst.sub measurable_snd : Measurable (fun p : ℝ × ℝ => p.1-p.2)).norm.aestronglyMeasurable)
  have hv : variance (id : ℝ → ℝ) ν = variance X μ :=
    variance_map measurable_id.aemeasurable hiid.aemeasurable_fst
  rwa [hint, hv] at H

end Paper35.Gini


open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
namespace Paper35.Gini

/-- Lebesgue probability on the unit interval. -/
def unitLaw : Measure ℝ := volume.restrict (Set.Icc 0 1)

instance unitLaw_probability : IsProbabilityMeasure unitLaw := by
  constructor
  simp [unitLaw, Real.volume_Icc]

lemma unitLaw_memLp : MemLp (id : ℝ → ℝ) 2 unitLaw := by
  apply MemLp.of_bound measurable_id.aestronglyMeasurable 1
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  change ‖x‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
  exact hx.2

lemma unitLaw_mean : (∫ x : ℝ, x ∂unitLaw) = 1/2 := by
  change (∫ x : ℝ in Set.Icc 0 1, x) = 1/2
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_id]
  norm_num

lemma unitLaw_second : (∫ x : ℝ, x^2 ∂unitLaw) = 1/3 := by
  change (∫ x : ℝ in Set.Icc 0 1, x^2) = 1/3
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_pow]
  norm_num

lemma unitLaw_variance : variance (id : ℝ → ℝ) unitLaw = 1/12 := by
  rw [variance_eq_sub unitLaw_memLp]
  change (∫ x : ℝ, x^2 ∂unitLaw) - (∫ x : ℝ, x ∂unitLaw)^2 = 1/12
  rw [unitLaw_second, unitLaw_mean]
  norm_num

lemma cmp_indicator (x y : ℝ) : cmp x y =
    (Set.Iio x).indicator (fun _ : ℝ => (1 : ℝ)) y -
    (Set.Ioi x).indicator (fun _ : ℝ => (1 : ℝ)) y := by
  by_cases hyx : y < x <;> by_cases hxy : x < y <;>
    simp [cmp, Set.indicator, hyx, hxy] <;> linarith

lemma unitLaw_score (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    score unitLaw (id : ℝ → ℝ) x = 2*x-1 := by
  have hleft : Set.Iio x ∩ Set.Icc (0 : ℝ) 1 = Set.Ico 0 x := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Icc, Set.mem_Ico]
    constructor
    · rintro ⟨h1,h2,h3⟩; exact ⟨h2,h1⟩
    · rintro ⟨h1,h2⟩; exact ⟨h2,h1,le_trans h2.le hx.2⟩
  have hright : Set.Ioi x ∩ Set.Icc (0 : ℝ) 1 = Set.Ioc x 1 := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    constructor
    · rintro ⟨h1,h2,h3⟩; exact ⟨h1,h3⟩
    · rintro ⟨h1,h2⟩; exact ⟨h1,le_trans hx.1 h1.le,h2⟩
  have hL : unitLaw.real (Set.Iio x) = x := by
    rw [measureReal_def, unitLaw, Measure.restrict_apply measurableSet_Iio, hleft, Real.volume_Ico,
      ENNReal.toReal_ofReal (by linarith [hx.1])]
    ring
  have hR : unitLaw.real (Set.Ioi x) = 1-x := by
    rw [measureReal_def, unitLaw, Measure.restrict_apply measurableSet_Ioi, hright, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by linarith [hx.2])]
  dsimp [score]
  simp_rw [cmp_indicator]
  rw [integral_sub ((integrable_const 1).indicator measurableSet_Iio)
    ((integrable_const 1).indicator measurableSet_Ioi), integral_indicator measurableSet_Iio,
    integral_indicator measurableSet_Ioi]
  simp only [setIntegral_const, smul_eq_mul, mul_one, hL, hR]
  ring

lemma unitLaw_meanDifference : meanDifference unitLaw (id : ℝ → ℝ) = 1/3 := by
  rw [meanDifference_score unitLaw id measurable_id unitLaw_memLp]
  simp only [id_eq]
  rw [unitLaw_mean]
  have heq : (∫ x : ℝ, (x - 1/2) * score unitLaw id x ∂unitLaw) =
      ∫ x : ℝ, 2*x^2 - 2*x + 1/2 ∂unitLaw := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [unitLaw_score x hx]
    ring
  rw [heq]
  have hi := unitLaw_memLp.integrable (by norm_num)
  have hsum := integral_add ((unitLaw_memLp.integrable_sq.const_mul 2).sub (hi.const_mul 2))
    (integrable_const (1/2 : ℝ))
  have hsub := integral_sub (unitLaw_memLp.integrable_sq.const_mul 2) (hi.const_mul 2)
  simp only [Pi.add_apply, Pi.sub_apply, id_eq] at hsum hsub
  rw [hsum, hsub, integral_const_mul, integral_const_mul, unitLaw_second, unitLaw_mean]
  norm_num

/-- The sharp constant is attained by the nondegenerate unit uniform law. -/
theorem unitLaw_gini_equality :
    meanDifference unitLaw (id : ℝ → ℝ) =
      (2 / Real.sqrt 3) * Real.sqrt (variance (id : ℝ → ℝ) unitLaw) := by
  rw [unitLaw_meanDifference, unitLaw_variance]
  have hs3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hsv := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1/12)
  have hpos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hpos.ne').2
  have hs : Real.sqrt 3 = 6 * Real.sqrt (1/12) := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).mp
    rw [mul_pow, hsv]
    nlinarith [hs3]
  nlinarith

/-- The Gini functional scales by the absolute value of the affine scale. -/
lemma meanDifference_affine {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (a b : ℝ) :
    meanDifference μ (fun x => a+b*X x) = |b| * meanDifference μ X := by
  unfold meanDifference
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p => by
    change |a+b*X p.1-(a+b*X p.2)| = |b| * |X p.1-X p.2|
    rw [show a+b*X p.1-(a+b*X p.2) = b*(X p.1-X p.2) by ring, abs_mul]

/-- Every location and scale of the unit uniform law attains the bound.
For `b ≠ 0` these are the nondegenerate uniform laws. -/
theorem affine_uniform_gini_equality (a b : ℝ) :
    meanDifference unitLaw (fun x : ℝ => a+b*x) =
      (2 / Real.sqrt 3) * Real.sqrt (variance (fun x : ℝ => a+b*x) unitLaw) := by
  have hv : variance (fun x : ℝ => a+b*x) unitLaw =
      b^2 * variance (id : ℝ → ℝ) unitLaw := by
    have hv1 := variance_const_add (μ := unitLaw) (X := fun x : ℝ => b*x)
      (measurable_const.mul measurable_id).aestronglyMeasurable a
    have hv2 := variance_mul b (id : ℝ → ℝ) unitLaw
    simp only [id_eq] at hv2
    exact hv1.trans hv2
  have hm := meanDifference_affine unitLaw id a b
  simp only [id_eq] at hm
  rw [hv, Real.sqrt_mul (sq_nonneg b), Real.sqrt_sq_eq_abs, hm, unitLaw_gini_equality]
  ring

/-- Equality for any independent copies with an affine unit-uniform common law.
`hu` states the law itself and does not assume an equality about moments. -/
theorem uniform_iid_gini_equality {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ) (a b : ℝ)
    (hu : IdentDistrib X (fun t : ℝ => a+b*t) μ unitLaw)
    (hiid : IdentDistrib X Y μ μ) (hind : IndepFun X Y μ) :
    (∫ ω, |X ω - Y ω| ∂μ) = (2 / Real.sqrt 3) * Real.sqrt (variance X μ) := by
  let Z := fun t : ℝ => a+b*t
  have hZ : Measurable Z := measurable_const.add (measurable_const.mul measurable_id)
  have hp : IdentDistrib (fun ω => (X ω,Y ω))
      (fun p : ℝ × ℝ => (Z p.1,Z p.2)) μ (unitLaw.prod unitLaw) := by
    refine ⟨hiid.aemeasurable_fst.prodMk hiid.aemeasurable_snd,
      ((hZ.comp measurable_fst).prodMk (hZ.comp measurable_snd)).aemeasurable, ?_⟩
    rw [(indepFun_iff_map_prod_eq_prod_map_map hiid.aemeasurable_fst hiid.aemeasurable_snd).mp hind,
      ← hiid.map_eq, hu.map_eq, Measure.map_prod_map unitLaw unitLaw hZ hZ]
    rfl
  have hdist := hp.comp (show Measurable (fun p : ℝ × ℝ => |p.1-p.2|) by
    simpa only [Real.norm_eq_abs] using (measurable_fst.sub measurable_snd :
      Measurable (fun p : ℝ × ℝ => p.1-p.2)).norm)
  have hi : (∫ ω, |X ω-Y ω| ∂μ) = meanDifference unitLaw Z := hdist.integral_eq
  rw [hi, hu.variance_eq]
  exact affine_uniform_gini_equality a b

/-- No smaller universal coefficient can bound all square-integrable laws. -/
theorem sharp_coefficient (C : ℝ)
    (hC : ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν] (Z : ℝ → ℝ),
      Measurable Z → MemLp Z 2 ν →
      meanDifference ν Z ≤ C * Real.sqrt (variance Z ν)) : 2 / Real.sqrt 3 ≤ C := by
  have H := hC unitLaw (id : ℝ → ℝ) measurable_id unitLaw_memLp
  rw [unitLaw_gini_equality] at H
  exact (mul_le_mul_right (Real.sqrt_pos.mpr (by rw [unitLaw_variance]; norm_num))).mp H

end Paper35.Gini
