import Paper26.PureCovariant
import Mathlib.Probability.Distributions.Beta
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-!
# The exact covariant overlap and tail Beta laws

Only generic Hausdorff moment uniqueness and the generic real Beta moment
recurrence are classical inputs. Neither mentions a quantum state, experiment,
Born law, dimension, or P26 risk. All covariant moments, their finite product,
and their identification with these ordinary Beta measures are proved below.

The Beta moment recurrence follows from Euler's beta integral and Gamma's
functional equation (NIST DLMF 5.12.1 and 5.5.1). The uniqueness input is the
classical Hausdorff moment uniqueness theorem on the compact interval [0,1]
(Diaconis--Freedman 2004, Theorem 1, DOI 10.1007/s00209-003-0633-9,
https://www.stat.berkeley.edu/~aldous/206-Exch/Papers/diaconis_2004.pdf).
Beta integral: https://dlmf.nist.gov/5.12.E1; Gamma recursion:
https://dlmf.nist.gov/5.5.E1.
-/
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
namespace Paper26.PureBetaLaw
open QuantumModel HaarFrames PureCovariant ContinuousPOVM

/-- Generic uniqueness of probability measures supported on the unit interval.
There is no quantum or Beta-distribution conclusion in this input. -/
structure HausdorffMomentInput : Prop where
  unique : ∀ (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
    (∀ᵐ x ∂μ, x ∈ Set.Icc (0:ℝ) 1) →
    (∀ᵐ x ∂ν, x ∈ Set.Icc (0:ℝ) 1) →
    (∀ k : ℕ, (∫ x, x^k ∂μ) = ∫ x, x^k ∂ν) → μ = ν

/-- Generic ordinary Beta moment recurrence, for all positive real shapes.
The base moment is the native mathlib probability normalization. -/
structure BetaMomentsInput : Prop where
  recurrence : ∀ (a b : ℝ), 0 < a → 0 < b → ∀ k : ℕ,
    (∫ x, x^(k+1) ∂betaMeasure a b) =
      (∫ x, x^k ∂betaMeasure a b) * (a+k)/(a+b+k)

def momentProduct (a b : ℝ) (k : ℕ) : ℝ :=
  ∏ i ∈ Finset.range k, (a+i)/(a+b+i)

theorem beta_moment_product (M : BetaMomentsInput) (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (k : ℕ) : (∫ x, x^k ∂betaMeasure a b) = momentProduct a b k := by
  letI : IsProbabilityMeasure (betaMeasure a b) := isProbabilityMeasureBeta ha hb
  induction k with
  | zero => simp [momentProduct]
  | succ k ih =>
    rw [M.recurrence a b ha hb k, ih]
    simp only [momentProduct, Finset.prod_range_succ]
    ring

lemma beta_supported (a b : ℝ) : ∀ᵐ x ∂betaMeasure a b, x ∈ Set.Icc (0:ℝ) 1 := by
  unfold betaMeasure
  apply (ae_withDensity_iff ((measurable_betaPDFReal a b).ennreal_ofReal)).mpr
  apply ae_of_all
  intro x hx
  constructor
  · by_contra h
    exact hx (betaPDF_eq_zero_of_nonpos (le_of_lt (lt_of_not_ge h)))
  · by_contra h
    exact hx (betaPDF_eq_zero_of_one_le (le_of_lt (lt_of_not_ge h)))

lemma beta_comm (a b : ℝ) : beta a b = beta b a := by
  unfold beta
  rw [mul_comm (Real.Gamma a), add_comm a b]

lemma betaPDF_reflection (a b x : ℝ) : betaPDF a b (1-x) = betaPDF b a x := by
  unfold betaPDF betaPDFReal
  by_cases hx : 0<x ∧ x<1
  · rw [if_pos hx, if_pos (by constructor <;> linarith [hx.1,hx.2])]
    rw [show (1-(1-x):ℝ) = x by ring, beta_comm]
    congr 1
    ring
  · rw [if_neg hx, if_neg (by intro h; exact hx ⟨by linarith [h.2],by linarith [h.1]⟩)]

/-- Ordinary Beta reflection follows natively from its actual mathlib density. -/
theorem beta_reflection (a b : ℝ) :
    (betaMeasure a b).map (fun x : ℝ => 1-x) = betaMeasure b a := by
  ext s hs
  have hm : Measurable (fun x : ℝ => 1-x) := measurable_const.sub measurable_id
  rw [Measure.map_apply hm hs]
  simp only [betaMeasure]
  rw [withDensity_apply _ (hm hs), withDensity_apply _ hs]
  rw [← lintegral_indicator (hm hs), ← lintegral_indicator hs]
  have hcomp := (volume.measurePreserving_sub_left (1:ℝ)).lintegral_comp
    (((measurable_betaPDFReal b a).ennreal_ofReal).indicator hs)
  change (∫⁻ x, s.indicator (betaPDF b a) (1-x) ∂volume) =
    ∫⁻ x, s.indicator (betaPDF b a) x ∂volume at hcomp
  rw [← hcomp]
  apply lintegral_congr
  intro x
  by_cases hx : 1-x ∈ s
  · rw [Set.indicator_of_mem hx,
      Set.indicator_of_mem (show x ∈ (fun x : ℝ => 1-x) ⁻¹' s from hx)]
    exact (betaPDF_reflection b a x).symm
  · rw [Set.indicator_of_notMem hx,
      Set.indicator_of_notMem (show x ∉ (fun x : ℝ => 1-x) ⁻¹' s from hx)]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Pushforward of the actual n-copy covariant Born outcome law. -/
def overlapLaw (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) {n : ℕ} (P : SymmetricSupport.SymmetricProjectorInput ι n)
    (U : Frame ι (Fin 1)) : Measure ℝ :=
  ((measurement μ H P).outcomeMeasure (TensorCopies.density U.density n)).map (overlap U)

instance overlapLaw_probability (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) {n : ℕ} (P : SymmetricSupport.SymmetricProjectorInput ι n)
    (U : Frame ι (Fin 1)) : IsProbabilityMeasure (overlapLaw μ H P U) :=
  Measure.isProbabilityMeasure_map (measurable_overlap U).aemeasurable

lemma overlapLaw_supported (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) {n : ℕ} (P : SymmetricSupport.SymmetricProjectorInput ι n)
    (U : Frame ι (Fin 1)) : ∀ᵐ x ∂overlapLaw μ H P U, x ∈ Set.Icc (0:ℝ) 1 := by
  apply (ae_map_iff (measurable_overlap U).aemeasurable measurableSet_Icc).mpr
  exact ae_of_all _ (fun V => overlap_mem_unit U V)

/-- Every actual covariant overlap moment is the ratio of the symmetric
subspace dimensions. This is derived from the native Born likelihood. -/
theorem overlapLaw_moment (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ)
    (P : ∀ n, SymmetricSupport.SymmetricProjectorInput ι n)
    (n k : ℕ) (U : Frame ι (Fin 1)) :
    (∫ x, x^k ∂overlapLaw μ H (P n) U) =
      (dimension ι n : ℝ)/(dimension ι (n+k):ℝ) := by
  let M := measurement μ H (P n)
  have hb (V : Frame ι (Fin 1)) : 0 ≤ M.born (TensorCopies.density U.density n) V :=
    M.born_nonneg _ (effect_positive (P n) V)
  have hpow : Measurable (fun x : ℝ => x^k) := by fun_prop
  rw [overlapLaw, integral_map (measurable_overlap U).aemeasurable hpow.aestronglyMeasurable]
  rw [DominatedPOVM.outcomeMeasure, integral_withDensity_eq_integral_toReal_smul
    (M.born_measurable _).ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (hb _), smul_eq_mul]
  change (∫ V : Frame ι (Fin 1), (measurement μ H (P n)).born
    (TensorCopies.density U.density n) V * overlap U V^k ∂μ) = _
  simp_rw [born_pure, mul_assoc, ← pow_add]
  rw [integral_const_mul, overlap_moment μ H (P (n+k)) U]
  rfl

/-- The dimension recurrence gives the ordinary Beta moment recurrence for
this actual Born distribution; no moment of the observation is an input. -/
theorem overlapLaw_moment_recurrence (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) (P : ∀ n, SymmetricSupport.SymmetricProjectorInput ι n)
    (n k : ℕ) (U : Frame ι (Fin 1)) :
    (∫ x, x^(k+1) ∂overlapLaw μ H (P n) U) =
      (∫ x, x^k ∂overlapLaw μ H (P n) U) * ((n:ℝ)+k+1)/((n:ℝ)+k+Fintype.card ι) := by
  rw [overlapLaw_moment μ H P n (k+1) U, overlapLaw_moment μ H P n k U]
  have hrec := dimension_recurrence (ι:=ι) (n+k)
  have hd₀ : (dimension ι (n+k):ℝ) ≠ 0 := by exact_mod_cast (dimension_pos (ι:=ι) (n+k)).ne'
  have hd₁ : (dimension ι (n+(k+1)):ℝ) ≠ 0 := by exact_mod_cast (dimension_pos (ι:=ι) (n+(k+1))).ne'
  have hden : (n:ℝ)+k+Fintype.card ι ≠ 0 := by
    have hcard : (0:ℝ)<Fintype.card ι := by exact_mod_cast Fintype.card_pos (α:=ι)
    positivity
  have he := congrArg (fun x : ℝ => (dimension ι n : ℝ)*x) hrec
  simp only [Nat.cast_add, show n+k+1 = n+(k+1) by omega] at he
  field_simp
  nlinarith [he]

/-- All moments agree with the explicit finite Beta product. -/
theorem overlapLaw_moment_product (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) (P : ∀ n, SymmetricSupport.SymmetricProjectorInput ι n)
    (m : ℕ) (hd : Fintype.card ι = m+1) (n k : ℕ) (U : Frame ι (Fin 1)) :
    (∫ x, x^k ∂overlapLaw μ H (P n) U) = momentProduct ((n:ℝ)+1) m k := by
  induction k with
  | zero => simp [momentProduct]
  | succ k ih =>
    rw [overlapLaw_moment_recurrence μ H P n k U, ih]
    simp only [momentProduct, Finset.prod_range_succ]
    have hdm : (Fintype.card ι:ℝ) = (m:ℝ)+1 := by exact_mod_cast hd
    rw [hdm]
    ring

/-- Actual overlap law Beta(n+1,m), proved from native moments and generic
compact-supported moment uniqueness. -/
theorem overlapLaw_eq_beta (D : HausdorffMomentInput) (M : BetaMomentsInput)
    (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) (P : ∀ n, SymmetricSupport.SymmetricProjectorInput ι n)
    (m : ℕ) (hm : 0<m) (hd : Fintype.card ι = m+1) (n : ℕ) (U : Frame ι (Fin 1)) :
    overlapLaw μ H (P n) U = betaMeasure ((n:ℝ)+1) m := by
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  letI : IsProbabilityMeasure (betaMeasure ((n:ℝ)+1) m) := isProbabilityMeasureBeta (by positivity) hmR
  apply D.unique _ _ (overlapLaw_supported μ H (P n) U) (beta_supported _ _)
  intro k
  rw [overlapLaw_moment_product μ H P m hd n k U,
    beta_moment_product M _ _ (by positivity) hmR k]

/-- Pushforward under actual complementary overlap, the source variable t. -/
def tailLaw (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) {n : ℕ} (P : SymmetricSupport.SymmetricProjectorInput ι n)
    (U : Frame ι (Fin 1)) : Measure ℝ :=
  ((measurement μ H P).outcomeMeasure (TensorCopies.density U.density n)).map
    (fun V => 1-overlap U V)

/-- The full exact printed distribution statement of Equation (36). -/
theorem tailLaw_eq_beta (D : HausdorffMomentInput) (M : BetaMomentsInput)
    (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) (P : ∀ n, SymmetricSupport.SymmetricProjectorInput ι n)
    (m : ℕ) (hm : 0<m) (hd : Fintype.card ι = m+1) (n : ℕ) (U : Frame ι (Fin 1)) :
    tailLaw μ H (P n) U = betaMeasure m ((n:ℝ)+1) := by
  have he : tailLaw μ H (P n) U = (overlapLaw μ H (P n) U).map (fun x : ℝ => 1-x) := by
    rw [overlapLaw, Measure.map_map (show Measurable (fun x : ℝ => 1-x) from
      measurable_const.sub measurable_id) (measurable_overlap U)]
    rfl
  rw [he, overlapLaw_eq_beta D M μ H P m hm hd n U, beta_reflection]

/-- The same actual tail pushforward has the already native mean; this
statement does not use either additional classical moment input. -/
theorem tailLaw_mean (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) (P : ∀ n, SymmetricSupport.SymmetricProjectorInput ι n)
    (m : ℕ) (hd : Fintype.card ι = m+1) (n : ℕ) (U : Frame ι (Fin 1)) :
    (∫ t, t ∂tailLaw μ H (P n) U) = (m:ℝ)/((n:ℝ)+Fintype.card ι) := by
  have ht : Measurable (fun V : Frame ι (Fin 1) => 1-overlap U V) :=
    measurable_const.sub (measurable_overlap U)
  rw [tailLaw, integral_map ht.aemeasurable
    (show AEStronglyMeasurable (fun x : ℝ => x) _ from measurable_id.aestronglyMeasurable)]
  rw [expected_tail μ H (P n) (P (n+1)) U]
  have hnum : (Fintype.card ι:ℝ)-1 = m := by rw [hd]; push_cast; ring
  rw [hnum]

/-- The two parts of the exact printed Equation (36), on the actual
covariant quantum outcome law and its scalar tail pushforward. -/
theorem equation_36 (D : HausdorffMomentInput) (M : BetaMomentsInput)
    (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) (P : ∀ n, SymmetricSupport.SymmetricProjectorInput ι n)
    (m : ℕ) (hm : 0<m) (hd : Fintype.card ι = m+1) (n : ℕ) (U : Frame ι (Fin 1)) :
    tailLaw μ H (P n) U = betaMeasure m ((n:ℝ)+1) ∧
      (∫ t, t ∂tailLaw μ H (P n) U) = (m:ℝ)/((n:ℝ)+Fintype.card ι) :=
  ⟨tailLaw_eq_beta D M μ H P m hm hd n U, tailLaw_mean μ H P m hd n U⟩

/-- Compatibility with the mean of the actual mathlib Beta measure. -/
theorem beta_mean_compatible (D : HausdorffMomentInput) (M : BetaMomentsInput)
    (μ : Measure (Frame ι (Fin 1))) [IsProbabilityMeasure μ]
    (H : HaarTensorMomentInput μ) (P : ∀ n, SymmetricSupport.SymmetricProjectorInput ι n)
    (m : ℕ) (hm : 0<m) (hd : Fintype.card ι = m+1) (n : ℕ) (U : Frame ι (Fin 1)) :
    (∫ t, t ∂betaMeasure m ((n:ℝ)+1)) = (m:ℝ)/((n:ℝ)+Fintype.card ι) := by
  rw [← tailLaw_eq_beta D M μ H P m hm hd n U]
  exact tailLaw_mean μ H P m hd n U

end Paper26.PureBetaLaw
