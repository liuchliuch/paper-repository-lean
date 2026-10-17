import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic
import Mathlib.Analysis.Real.Pi.Bounds
import Paper09.Ising

/-! Gaussian disorder estimates used in (1.7), (2.10), and (3.16).
All measures below are the genuine mathlib Gaussian law. -/

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace Paper09
namespace Gaussian

/-- The disorder law with standard deviation `σ`. -/
def law (σ : ℝ) : Measure ℝ := gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩

instance law_isProbabilityMeasure (σ : ℝ) : IsProbabilityMeasure (law σ) := by
  unfold law
  infer_instance

lemma variance_ne_zero {σ : ℝ} (hσ : 0 < σ) : (⟨σ ^ 2, sq_nonneg σ⟩ : ℝ≥0) ≠ 0 := by
  intro h
  have h' := congrArg (fun v : ℝ≥0 => (v : ℝ)) h
  exact (pow_ne_zero 2 hσ.ne') h'

lemma real_Icc_eq_integral {v : ℝ≥0} (hv : v ≠ 0) (a b : ℝ) :
    (gaussianReal 0 v).real (Icc a b) = ∫ x in Icc a b, gaussianPDFReal 0 v x := by
  rw [measureReal_def, gaussianReal_apply_eq_integral _ hv,
    ENNReal.toReal_ofReal]
  exact integral_nonneg (fun _ => gaussianPDFReal_nonneg _ _ _)

/-- On a centered interval, the Gaussian density is bounded below by its
value at either endpoint. -/
lemma pdf_lower {v : ℝ≥0} {r x : ℝ} (hr : 0 ≤ r) (hx : |x| ≤ r) :
    gaussianPDFReal 0 v r ≤ gaussianPDFReal 0 v x := by
  unfold gaussianPDFReal
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  simp only [sub_zero]
  have hsq : x ^ 2 ≤ r ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg x) hr).2 hx
  exact div_le_div_of_nonneg_right (neg_le_neg hsq) (by positivity)

/-- A quantitative small-ball lower bound from the minimum density on a
fixed interval. -/
theorem small_ball_lower {v : ℝ≥0} (hv : v ≠ 0) {r u : ℝ}
    (hu : 0 ≤ u) (hur : u ≤ r) :
    2 * u * gaussianPDFReal 0 v r ≤ (gaussianReal 0 v).real {x | |x| ≤ u} := by
  have hset : {x : ℝ | |x| ≤ u} = Icc (-u) u := by ext x; simp [abs_le]
  rw [hset, real_Icc_eq_integral hv]
  have hl := setIntegral_ge_of_const_le (μ := volume) (s := Icc (-u) u)
    measurableSet_Icc isCompact_Icc.measure_ne_top
    (fun x hx => pdf_lower (hu.trans hur) ((abs_le.mpr hx).trans hur))
    (integrable_gaussianPDFReal 0 v).integrableOn
  rw [Real.volume_real_Icc_of_le (by linarith : -u ≤ u)] at hl
  nlinarith

/-- The `c_σ / m` estimate used for the island's weak-field interior;
it holds for every `m ≥ 1`, with an explicit strictly positive constant. -/
theorem small_ball_inverse (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ c > 0, ∀ m : ℕ, 1 ≤ m →
      c / m ≤ (law σ).real {x | |x| ≤ ε / m} := by
  refine ⟨2 * ε * gaussianPDFReal 0 ⟨σ ^ 2, sq_nonneg σ⟩ ε, ?_, ?_⟩
  · exact mul_pos (mul_pos (by norm_num) hε)
      (gaussianPDFReal_pos _ _ _ (variance_ne_zero hσ))
  · intro m hm
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hpos : (0 : ℝ) < m := lt_of_lt_of_le zero_lt_one hm'
    have hu : 0 ≤ ε / m := div_nonneg hε.le hpos.le
    have hur : ε / m ≤ ε := div_le_self hε.le hm'
    convert small_ball_lower (variance_ne_zero hσ) hu hur using 1; ring

/-- The density never exceeds its value at the center. -/
lemma pdf_upper (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal 0 v x ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by
  unfold gaussianPDFReal
  calc
    _ ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ * 1 := by
      gcongr
      exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity))
    _ = _ := mul_one _

/-- The elementary density upper bound for a centered Gaussian interval. -/
theorem small_ball_upper {v : ℝ≥0} (hv : v ≠ 0) {K : ℝ} (hK : 0 ≤ K) :
    (gaussianReal 0 v).real {x | |x| ≤ K} ≤
      2 * K / Real.sqrt (2 * Real.pi * v) := by
  have hset : {x : ℝ | |x| ≤ K} = Icc (-K) K := by ext x; simp [abs_le]
  rw [hset, real_Icc_eq_integral hv]
  have hmono := setIntegral_mono_on
    (integrable_gaussianPDFReal 0 v).integrableOn
    (integrableOn_const isCompact_Icc.measure_ne_top) measurableSet_Icc
    (fun x (_ : x ∈ Icc (-K) K) => pdf_upper v x)
  rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith : -K ≤ K)] at hmono
  simpa [smul_eq_mul, div_eq_mul_inv, sub_neg_eq_add, two_mul] using hmono

/-- Both shell tails have positive Gaussian probability. -/
theorem upper_tail_pos {v : ℝ≥0} (hv : v ≠ 0) (H : ℝ) :
    0 < (gaussianReal 0 v).real (Ici H) := by
  have hn : gaussianReal 0 v (Ici H) ≠ 0 := by
    intro hz
    have hz' := gaussianReal_absolutelyContinuous' 0 hv hz
    simp at hz'
  exact ENNReal.toReal_pos hn (measure_ne_top _ _)

/-- Symmetry identifies the probability of either prescribed shell sign. -/
theorem symmetric_tails (v : ℝ≥0) (H : ℝ) :
    gaussianReal 0 v (Iic (-H)) = gaussianReal 0 v (Ici H) := by
  have hm := gaussianReal_map_neg (μ := (0 : ℝ)) (v := v)
  have he := congrArg (fun μ : Measure ℝ => μ (Ici H)) hm
  dsimp only at he
  rw [Measure.map_apply (by fun_prop) measurableSet_Ici] at he
  have hs : (fun x : ℝ => -x) ⁻¹' Ici H = Iic (-H) := by
    ext x
    simp only [mem_preimage, mem_Ici, mem_Iic]
    constructor <;> intro h <;> linarith
  rw [hs] at he
  simpa using he

/-- Positivity of both shell-sign probabilities in real-valued form. -/
theorem both_tails_positive (σ H : ℝ) (hσ : 0 < σ) :
    0 < (law σ).real (Ici H) ∧
      (law σ).real (Iic (-H)) = (law σ).real (Ici H) := by
  exact ⟨upper_tail_pos (variance_ne_zero hσ) H,
    congrArg ENNReal.toReal (symmetric_tails _ _)⟩

lemma sqrt_variance (σ : ℝ) (hσ : 0 ≤ σ) :
    Real.sqrt (2 * Real.pi * (⟨σ ^ 2, sq_nonneg σ⟩ : ℝ≥0)) =
      Real.sqrt (2 * Real.pi) * σ := by
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hσ]

/-- The sharp density coefficient appearing immediately after (1.7). -/
lemma density_coefficient : 2 / Real.sqrt (2 * Real.pi) = Real.sqrt (2 / Real.pi) := by
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  rw [div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  field_simp

/-- The paper's precise Gaussian weak-site probability estimate. -/
theorem small_ball_upper_sharp_sigma (σ K : ℝ) (hσ : 0 < σ) (hK : 0 ≤ K) :
    (law σ).real {x | |x| ≤ K} ≤ Real.sqrt (2 / Real.pi) * K / σ := by
  have hraw := small_ball_upper (variance_ne_zero hσ) hK
  simp only [NNReal.coe_mk, Real.sqrt_mul (show 0 ≤ 2 * Real.pi by positivity),
    Real.sqrt_sq hσ.le] at hraw
  convert hraw using 1
  rw [← density_coefficient]
  ring

/-- A convenient upper bound that is slightly weaker than the sharp
coefficient `sqrt (2/pi)`, and still proves the stated `σ₀` threshold. -/
theorem small_ball_upper_sigma (σ K : ℝ) (hσ : 0 < σ) (hK : 0 ≤ K) :
    (law σ).real {x | |x| ≤ K} ≤ K / σ := by
  have hraw := small_ball_upper (variance_ne_zero hσ) hK
  simp only [NNReal.coe_mk, Real.sqrt_mul (show 0 ≤ 2 * Real.pi by positivity),
    Real.sqrt_sq hσ.le] at hraw
  apply hraw.trans
  have hs : 2 ≤ Real.sqrt (2 * Real.pi) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).2
    nlinarith [Real.pi_gt_three]
  apply (div_le_div_iff₀ (by positivity : 0 < Real.sqrt (2 * Real.pi) * σ) hσ).2
  nlinarith [mul_le_mul_of_nonneg_right hs (mul_nonneg hK hσ.le)]

/-- Equation (1.7): sufficiently large standard deviation makes weak-field
sites sparse.  The bound is strict with exactly the paper's threshold. -/
theorem strong_disorder_small_ball (d β σ : ℝ) (hd : 1 ≤ d) (hβ : 0 < β)
    (hσ : sigma0 d β ≤ σ) :
    (law σ).real {x | |x| ≤ Kstar d β} < 1 / (40 * d) := by
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hlog : 0 < Real.log (80 * d) := Real.log_pos (by nlinarith)
  have hK : 0 < Kstar d β := by unfold Kstar; positivity
  have hs0 : 0 < sigma0 d β := by unfold sigma0; positivity
  have hs : 0 < σ := hs0.trans_le hσ
  apply lt_of_le_of_lt (small_ball_upper_sigma σ (Kstar d β) hs hK.le)
  apply (div_lt_div_iff₀ hs (by positivity : 0 < 40 * d)).2
  have hx : 80 * d * Kstar d β ≤ σ := hσ
  nlinarith [mul_pos hd0 hK]

/-- The actual Gaussian law meets both inequalities of Assumption 1.2
at the explicit standard-deviation threshold from (1.7). -/
theorem strong_disorder (d β σ : ℝ) (hd : 1 ≤ d) (hβ : 0 < β)
    (hσ : sigma0 d β ≤ σ) :
    ∃ K > 0, rho K d β < 1 / (40 * d) ∧
      (law σ).real {x | |x| ≤ K} < 1 / (40 * d) := by
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hlog : 0 < Real.log (80 * d) := Real.log_pos (by nlinarith)
  refine ⟨Kstar d β, ?_, ?_, strong_disorder_small_ball d β σ hd hβ hσ⟩
  · unfold Kstar
    positivity
  · rw [rho_Kstar d β hd0]
    exact inv_one_add_80d_lt_inv_40d hd

/-- Chernoff's optimal one-sided bound for the actual centered Gaussian. -/
theorem upper_tail_bound {v : ℝ≥0} (hv : 0 < v) {t : ℝ} (ht : 0 ≤ t) :
    (gaussianReal 0 v).real (Ici t) ≤ Real.exp (-t ^ 2 / (2 * v)) := by
  have hv' : (0 : ℝ) < v := hv
  have h := measure_ge_le_exp_mul_mgf (μ := gaussianReal 0 v)
    (X := fun x : ℝ => x) t (t := t / v) (by positivity)
    (integrable_exp_mul_gaussianReal _)
  rw [mgf_fun_id_gaussianReal] at h
  simp only [zero_mul, zero_add] at h
  rw [← Real.exp_add] at h
  convert h using 1
  congr 1
  field_simp
  ring

/-- The Gaussian absolute-value tail bound, with no independence premise. -/
theorem abs_tail_bound {v : ℝ≥0} (hv : 0 < v) {t : ℝ} (ht : 0 ≤ t) :
    (gaussianReal 0 v).real {x | t ≤ |x|} ≤
      2 * Real.exp (-t ^ 2 / (2 * v)) := by
  have hs : {x : ℝ | t ≤ |x|} = Ici t ∪ Iic (-t) := by
    ext x
    simp only [mem_setOf_eq, mem_union, mem_Ici, mem_Iic, le_abs]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · right; linarith
    · rintro (h | h)
      · exact Or.inl h
      · right; linarith
  rw [hs]
  have hsym := congrArg ENNReal.toReal (symmetric_tails v t)
  have h := measureReal_union_le (μ := gaussianReal 0 v) (Ici t) (Iic (-t))
  change (gaussianReal 0 v).real (Iic (-t)) = (gaussianReal 0 v).real (Ici t) at hsym
  rw [hsym] at h
  nlinarith [upper_tail_bound hv ht]

/-- The union bound for a finite family of Gaussian marginals. Independence
is unnecessary for this upper-tail estimate. -/
theorem maximum_tail_bound {Ω V : Type*} [MeasurableSpace Ω] [Fintype V]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : V → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) {v : ℝ≥0} (hv : 0 < v)
    (hlaw : ∀ i, μ.map (X i) = gaussianReal 0 v) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ∃ i, t < |X i ω|} ≤
      2 * Fintype.card V * Real.exp (-t ^ 2 / (2 * v)) := by
  have hsubset : {ω | ∃ i, t < |X i ω|} ⊆ ⋃ i, {ω | t ≤ |X i ω|} := by
    rintro ω ⟨i, hi⟩
    exact mem_iUnion.mpr ⟨i, hi.le⟩
  apply (measureReal_mono hsubset).trans
  apply (measureReal_iUnion_fintype_le _).trans
  calc
    (∑ i, μ.real {ω | t ≤ |X i ω|}) ≤
        ∑ _i : V, 2 * Real.exp (-t ^ 2 / (2 * v)) := by
      apply Finset.sum_le_sum
      intro i _
      have hm := Measure.map_apply_of_aemeasurable (μ := μ) (s := {x : ℝ | t ≤ |x|}) (hX i).aemeasurable
        (measurableSet_le measurable_const measurable_abs)
      have he : μ.real {ω | t ≤ |X i ω|} =
          (gaussianReal 0 v).real {x | t ≤ |x|} := by
        simp only [measureReal_def]
        rw [← hlaw i, hm]
        rfl
      rw [he]
      exact abs_tail_bound hv ht
    _ = _ := by simp; ring

/-- A finite Gaussian family obeys its deterministic maximum bound outside
an event of the displayed exponentially small probability. -/
theorem maximum_probability {Ω V : Type*} [MeasurableSpace Ω] [Fintype V]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : V → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) {v : ℝ≥0} (hv : 0 < v)
    (hlaw : ∀ i, μ.map (X i) = gaussianReal 0 v) {t : ℝ} (ht : 0 ≤ t) :
    1 - 2 * Fintype.card V * Real.exp (-t ^ 2 / (2 * v)) ≤
      μ.real {ω | ∀ i, |X i ω| ≤ t} := by
  have hm : MeasurableSet {ω | ∀ i, |X i ω| ≤ t} := by
    simpa only [setOf_forall] using
      MeasurableSet.iInter (fun i => measurableSet_le (hX i).abs (measurable_const (a := t)))
  have hc : {ω | ∀ i, |X i ω| ≤ t}ᶜ = {ω | ∃ i, t < |X i ω|} := by
    ext ω
    simp
  have h := maximum_tail_bound μ X hX hv hlaw ht
  rw [← hc, measureReal_compl hm] at h
  simp only [measureReal_univ_eq_one] at h
  linarith

/-- Equation (3.16), in terms of `N = |V|`.  Only the Gaussian marginals
are used; the result therefore also applies to the i.i.d. disorder law. -/
theorem maximum_field {Ω V : Type*} [MeasurableSpace Ω] [Fintype V]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : V → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (σ : ℝ) (hσ : 0 < σ)
    (hlaw : ∀ i, μ.map (X i) = law σ) (hN : 2 ≤ Fintype.card V) :
    1 - (Fintype.card V : ℝ)⁻¹ ^ 2 ≤
      μ.real {ω | ∀ i, |X i ω| ≤ σ * Real.sqrt (8 * Real.log (Fintype.card V))} := by
  let N : ℝ := Fintype.card V
  have hN2 : 2 ≤ N := by dsimp [N]; exact_mod_cast hN
  have hN0 : 0 < N := by linarith
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hv : (0 : ℝ≥0) < ⟨σ ^ 2, sq_nonneg σ⟩ := by
    change (0 : ℝ) < σ ^ 2
    positivity
  have h := maximum_probability μ X hX hv hlaw
    (show 0 ≤ σ * Real.sqrt (8 * Real.log N) by positivity)
  apply le_trans _ h
  have hexp : Real.exp (-(σ * Real.sqrt (8 * Real.log N)) ^ 2 /
      (2 * (⟨σ ^ 2, sq_nonneg σ⟩ : ℝ≥0))) = N⁻¹ ^ 4 := by
    have hs : (σ * Real.sqrt (8 * Real.log N)) ^ 2 = σ ^ 2 * (8 * Real.log N) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    rw [hs]
    change Real.exp (-(σ ^ 2 * (8 * Real.log N)) / (2 * σ ^ 2)) = _
    have he : -(σ ^ 2 * (8 * Real.log N)) / (2 * σ ^ 2) = (-4) * Real.log N := by
      field_simp
      ring
    rw [he]
    rw [show (-4 : ℝ) * Real.log N = -(Real.log N * 4) by ring,
      Real.exp_neg, mul_comm (Real.log N) 4]
    rw [show (4 : ℝ) * Real.log N = (4 : ℕ) * Real.log N by norm_num,
      Real.exp_nat_mul, Real.exp_log hN0]
    simp
  change 1 - N⁻¹ ^ 2 ≤ 1 - 2 * N *
    Real.exp (-(σ * Real.sqrt (8 * Real.log N)) ^ 2 / (2 * σ ^ 2))
  change Real.exp (-(σ * Real.sqrt (8 * Real.log N)) ^ 2 / (2 * σ ^ 2)) = _ at hexp
  rw [hexp]
  have hbound : 2 * N * N⁻¹ ^ 4 ≤ N⁻¹ ^ 2 := by
    field_simp
    nlinarith
  linarith

/-- Coordinates for a weak-field interior and a prescribed-sign shell.
`true` prescribes the positive tail and `false` the negative tail. -/
def islandEvent (B S : Type*) (ζ : S → Bool) (u H : ℝ) : Set (B ⊕ S → ℝ) :=
  Set.univ.pi (Sum.elim (fun _ : B => {x : ℝ | |x| ≤ u})
    (fun s : S => if ζ s then Ici H else Iic (-H)))

/-- Independence gives the exact island probability.  This is the genuine
finite product Gaussian law, with no probability certificate premises. -/
theorem island_probability (B S : Type*) [Fintype B] [Fintype S]
    (σ u H : ℝ) (ζ : S → Bool) :
    (Measure.pi (fun _ : B ⊕ S => law σ)).real (islandEvent B S ζ u H) =
      ((law σ).real {x | |x| ≤ u}) ^ Fintype.card B *
      ((law σ).real (Ici H)) ^ Fintype.card S := by
  unfold islandEvent
  rw [measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
  rw [Fintype.prod_sum_type]
  have hs : ∀ s : S, ((law σ) (if ζ s then Ici H else Iic (-H))).toReal =
      (law σ).real (Ici H) := by
    intro s
    cases h : ζ s
    · simpa only [h, Bool.false_eq_true, ↓reduceIte, law] using
        congrArg ENNReal.toReal (symmetric_tails ⟨σ ^ 2, sq_nonneg σ⟩ H)
    · rfl
  simp only [Sum.elim_inl, Sum.elim_inr, hs]
  simp [measureReal_def]

/-- The first bound in (2.10), for arbitrary finite interior and shell sizes.
The constant depends only on the fixed Gaussian law and thresholds. -/
theorem island_log_cost (σ ε H : ℝ) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ C > 0, ∀ (B S : Type*) [Fintype B] [Fintype S] (ζ : S → Bool)
      (m : ℕ), 1 ≤ m →
      -Real.log ((Measure.pi (fun _ : B ⊕ S => law σ)).real
        (islandEvent B S ζ (ε / m) H)) ≤
      Fintype.card B * (Real.log m + C) + C * Fintype.card S := by
  obtain ⟨c, hc, hsmall⟩ := small_ball_inverse σ ε hσ hε
  let q : ℝ := (law σ).real (Ici H)
  have hq : 0 < q := upper_tail_pos (variance_ne_zero hσ) H
  let C : ℝ := max 1 (max (-Real.log c) (-Real.log q))
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCc : -Real.log c ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCq : -Real.log q ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, lt_of_lt_of_le zero_lt_one hC1, ?_⟩
  intro B S _ _ ζ m hm
  let p : ℝ := (law σ).real {x | |x| ≤ ε / m}
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hp : 0 < p := (div_pos hc hm0).trans_le (hsmall m hm)
  have hlog : Real.log (c / m) ≤ Real.log p := Real.log_le_log (div_pos hc hm0) (hsmall m hm)
  rw [Real.log_div hc.ne' hm0.ne'] at hlog
  rw [island_probability]
  change -Real.log (p ^ Fintype.card B * q ^ Fintype.card S) ≤ _
  rw [Real.log_mul (pow_pos hp _).ne' (pow_pos hq _).ne', Real.log_pow, Real.log_pow]
  have hb : (Fintype.card B : ℝ) * (-Real.log p) ≤
      Fintype.card B * (Real.log m + C) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  have hs : (Fintype.card S : ℝ) * (-Real.log q) ≤ C * Fintype.card S := by
    nlinarith [mul_le_mul_of_nonneg_right hCq (Nat.cast_nonneg (Fintype.card S) : (0 : ℝ) ≤ _)]
  linarith

/-- Measurability of the Gaussian island event. -/
lemma measurableSet_islandEvent (B S : Type*) [Fintype B] [Fintype S]
    (ζ : S → Bool) (u H : ℝ) : MeasurableSet (islandEvent B S ζ u H) := by
  apply MeasurableSet.univ_pi
  intro i
  cases i with
  | inl b => exact measurableSet_le measurable_abs measurable_const
  | inr s => cases h : ζ s <;> simp only [Sum.elim_inr, h] <;> measurability

/-- Independent placements: the probability that every candidate misses a
measurable event is exactly `(1-P(E))^J`. -/
theorem no_occurrence_probability {A J : Type*} [MeasurableSpace A] [Fintype J]
    (ν : Measure A) [IsProbabilityMeasure ν] (E : Set A) (hE : MeasurableSet E) :
    (Measure.pi (fun _ : J => ν)).real (Set.univ.pi (fun _ => Eᶜ)) =
      (1 - ν.real E) ^ Fintype.card J := by
  rw [measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
  simp only [← measureReal_def, measureReal_compl hE, measureReal_univ_eq_one,
    Finset.prod_const, Finset.card_univ]

/-- The exact independent-placement probability implies the exponential
absence bound used after (2.11). -/
theorem no_occurrence_bound {A J : Type*} [MeasurableSpace A] [Fintype J]
    (ν : Measure A) [IsProbabilityMeasure ν] (E : Set A) (hE : MeasurableSet E) :
    (Measure.pi (fun _ : J => ν)).real (Set.univ.pi (fun _ => Eᶜ)) ≤
      Real.exp (-(Fintype.card J : ℝ) * ν.real E) := by
  rw [no_occurrence_probability ν E hE]
  calc
    (1 - ν.real E) ^ Fintype.card J ≤ (Real.exp (-ν.real E)) ^ Fintype.card J := by
      apply pow_le_pow_left₀
      · exact sub_nonneg.mpr (measureReal_le_one (μ := ν) (s := E))
      · simpa [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-ν.real E)
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- A positive lower bound for the probability of one Gaussian island. -/
theorem island_probability_lower (σ ε H : ℝ) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ C > 0, ∀ (B S : Type*) [Fintype B] [Fintype S] (ζ : S → Bool)
      (m : ℕ), 1 ≤ m →
      Real.exp (-(Fintype.card B * (Real.log m + C) + C * Fintype.card S)) ≤
      (Measure.pi (fun _ : B ⊕ S => law σ)).real
        (islandEvent B S ζ (ε / m) H) := by
  obtain ⟨C, hC, hcost⟩ := island_log_cost σ ε H hσ hε
  refine ⟨C, hC, ?_⟩
  intro B S _ _ ζ m hm
  have hp : 0 < (Measure.pi (fun _ : B ⊕ S => law σ)).real
      (islandEvent B S ζ (ε / m) H) := by
    rw [island_probability]
    have hsmall := small_ball_lower (variance_ne_zero hσ)
      (div_nonneg hε.le (Nat.cast_nonneg m))
      (div_le_self hε.le (by exact_mod_cast hm))
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
    have hpdf := gaussianPDFReal_pos 0 ⟨σ ^ 2, sq_nonneg σ⟩ ε (variance_ne_zero hσ)
    have hin : 0 < (law σ).real {x | |x| ≤ ε / m} :=
      (mul_pos (mul_pos (by norm_num) (div_pos hε hm0)) hpdf).trans_le hsmall
    exact mul_pos (pow_pos hin _) (pow_pos (upper_tail_pos (variance_ne_zero hσ) H) _)
  rw [← Real.exp_log hp]
  exact Real.exp_le_exp.mpr (by linarith [hcost B S ζ m hm])

/-- Independent Gaussian island candidates: no island appears with
probability at most `exp(-J exp(-cost))`. -/
theorem no_gaussian_island (σ ε H : ℝ) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ C > 0, ∀ (B S J : Type*) [Fintype B] [Fintype S] [Fintype J]
      (ζ : S → Bool) (m : ℕ), 1 ≤ m →
      (Measure.pi (fun _ : J => Measure.pi (fun _ : B ⊕ S => law σ))).real
        (Set.univ.pi (fun _ => (islandEvent B S ζ (ε / m) H)ᶜ)) ≤
      Real.exp (-(Fintype.card J : ℝ) *
        Real.exp (-(Fintype.card B * (Real.log m + C) + C * Fintype.card S))) := by
  obtain ⟨C, hC, hlower⟩ := island_probability_lower σ ε H hσ hε
  refine ⟨C, hC, ?_⟩
  intro B S J _ _ _ ζ m hm
  apply (no_occurrence_bound (Measure.pi (fun _ : B ⊕ S => law σ))
    (islandEvent B S ζ (ε / m) H) (measurableSet_islandEvent B S ζ _ H)).trans
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left (hlower B S ζ m hm) (neg_nonpos.mpr (Nat.cast_nonneg _))

/-- The geometric specialization of the cost in (2.10). -/
lemma geometric_cost_bound {C : ℝ} (hC : 0 ≤ C) (d m : ℕ) (hm : 2 ≤ m) :
    (m : ℝ) ^ d * (Real.log m + C) + C * (2 * d * (m : ℝ) ^ (d - 1)) ≤
      (1 + (1 + 2 * d) * C / Real.log 2) * (m : ℝ) ^ d * Real.log m := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlm : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) hm2
  have hpow : (m : ℝ) ^ (d - 1) ≤ (m : ℝ) ^ d :=
    pow_le_pow_right₀ hm1 (Nat.sub_le d 1)
  have htail := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 2 * (d : ℝ) * C by positivity)
  let A : ℝ := (1 + 2 * d) * C
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hratio : A ≤ A / Real.log 2 * Real.log m := by
    calc
      A = A / Real.log 2 * Real.log 2 := (div_mul_cancel₀ A hl2.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hlm (div_nonneg hA hl2.le)
  have hmul := mul_le_mul_of_nonneg_right hratio (show 0 ≤ (m : ℝ) ^ d by positivity)
  dsimp [A] at hmul
  nlinarith only [htail, hmul]

/-- All of (2.10): box volume `m^d` and shell size `2 d m^(d-1)`
give the cost `C₂ m^d log m`, with `C₂` independent of `m`. -/
theorem island_log_cost_geometric (σ ε H : ℝ) (hσ : 0 < σ) (hε : 0 < ε)
    (d : ℕ) :
    ∃ C₂ > 0, ∀ (B S : Type*) [Fintype B] [Fintype S] (ζ : S → Bool)
      (m : ℕ), 2 ≤ m → Fintype.card B = m ^ d →
      Fintype.card S = 2 * d * m ^ (d - 1) →
      -Real.log ((Measure.pi (fun _ : B ⊕ S => law σ)).real
        (islandEvent B S ζ (ε / m) H)) ≤ C₂ * (m : ℝ) ^ d * Real.log m := by
  obtain ⟨C, hC, hcost⟩ := island_log_cost σ ε H hσ hε
  refine ⟨1 + (1 + 2 * d) * C / Real.log 2, by positivity, ?_⟩
  intro B S _ _ ζ m hm hB hS
  have h := hcost B S ζ m (by omega)
  rw [hB, hS] at h
  push_cast at h
  exact h.trans (geometric_cost_bound hC.le d m hm)

end Gaussian
end Paper09
