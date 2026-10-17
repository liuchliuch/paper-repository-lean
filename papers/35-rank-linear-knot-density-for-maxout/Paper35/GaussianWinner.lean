import Paper35.Deep
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp

/-!
# Proposition 8.2: actual Gaussian Maxout winner

The only theorem inputs below are standard Gaussian affine/regression laws and
an explicitly quantified independent finite marking identity. None supplies the
Maxout selected-weight moment formula. That formula is derived entry by entry.

External references:
* MIT 6.436J/15.085J, Fall 2018, Lecture 14, Theorem 1 (normal linear maps,
  Gaussian block independence and conditional Gaussian regression); Lecture 15,
  pp. 2--4 and 9 (including singular covariance).
* Durrett, Probability: Theory and Examples, 5th ed., Section 4.1.2:
  independence, conditioning and taking out measurable factors. The finite
  marking input is its finite partition corollary, for an arbitrary selector,
  not an assertion about Gaussian or Maxout winners.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix Set
open scoped BigOperators ENNReal NNReal

namespace Paper35.GaussianWinner
open Paper35.Deep

/-- Maximum of a nonempty finite real tuple, with exactly n+1 entries. -/
def finiteMax : (n : ℕ) → (Fin (n+1) → ℝ) → ℝ
  | 0, x => x 0
  | n+1, x => max (finiteMax n (fun j => x j.castSucc)) (x (Fin.last (n+1)))

/-- Explicit finite measurable maximizing index, including a deterministic tie rule. -/
def finiteWinner : (n : ℕ) → (Fin (n+1) → ℝ) → Fin (n+1)
  | 0, _ => 0
  | n+1, x => if finiteMax n (fun j => x j.castSucc) ≤ x (Fin.last (n+1))
      then Fin.last (n+1) else (finiteWinner n (fun j => x j.castSucc)).castSucc

lemma continuous_finiteMax (n : ℕ) : Continuous (finiteMax n) := by
  induction n with
  | zero => exact continuous_apply 0
  | succ n ih =>
    exact (ih.comp (continuous_pi (fun j => continuous_apply j.castSucc))).max
      (continuous_apply (Fin.last (n+1)))

lemma measurable_finiteWinner (n : ℕ) : Measurable (finiteWinner n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hp : Measurable (fun x : Fin (n+2) → ℝ => fun j : Fin (n+1) => x j.castSucc) :=
      measurable_pi_lambda _ (fun j => measurable_pi_apply j.castSucc)
    have hmax := ((continuous_finiteMax n).measurable.comp hp)
    exact Measurable.ite (measurableSet_le hmax (measurable_pi_apply _)) measurable_const
      ((measurable_of_countable Fin.castSucc).comp (ih.comp hp))

lemma finiteWinner_value (n : ℕ) (x : Fin (n+1) → ℝ) :
    x (finiteWinner n x) = finiteMax n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp only [finiteWinner, finiteMax]
    split_ifs with h
    · exact (max_eq_right h).symm
    · rw [ih (fun j => x j.castSucc)]
      exact (max_eq_left (le_of_not_ge h)).symm

lemma le_finiteMax (n : ℕ) (x : Fin (n+1) → ℝ) (j : Fin (n+1)) :
    x j ≤ finiteMax n x := by
  induction n with
  | zero =>
    have hj : j = 0 := by omega
    simpa only [hj, finiteMax] using (le_refl (x 0))
  | succ n ih =>
    refine Fin.lastCases ?_ (fun i => ?_) j
    · exact le_max_right _ _
    · exact (ih (fun k => x k.castSucc) i).trans (le_max_left _ _)

lemma finiteMax_scaled_prefix (n : ℕ) (a : ℝ) (ha : 0 ≤ a) (x : ℕ → ℝ) :
    finiteMax n (fun j => a * x j.val) = a * Paper35.prefixMax n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change max (finiteMax n (fun j => a * x j.val)) (a * x (n+1)) =
      a * max (Paper35.prefixMax n x) (x (n+1))
    rw [ih, mul_max_of_nonneg _ _ ha]

/-- A centered Gaussian weight law with its exact covariance, and an independent
strictly positive-variance centered Gaussian bias. Projected-law fields are the
standard definition of a (possibly singular) multivariate normal law. -/
structure GaussianUnit (q : ℕ) where
  covariance : Matrix (Fin q) (Fin q) ℝ
  covariance_psd : covariance.PosSemidef
  weightLaw : Measure (Fin q → ℝ)
  weight_probability : IsProbabilityMeasure weightLaw
  projected_law : ∀ v : Fin q → ℝ,
    weightLaw.map (fun w => v ⬝ᵥ w) = gaussianReal 0
      ⟨covarianceForm covariance v v, by simpa [covarianceForm] using covariance_psd.2 v⟩
  biasSd : ℝ
  biasSd_pos : 0 < biasSd

namespace GaussianUnit
variable {q : ℕ} (m : GaussianUnit q)

abbrev Candidate (q : ℕ) := (Fin q → ℝ) × ℝ
abbrev Sample (q K : ℕ) := Fin K → Candidate q

def candidateLaw : Measure (Candidate q) :=
  m.weightLaw.prod (gaussianReal 0 ⟨m.biasSd ^ 2, sq_nonneg _⟩)

instance candidate_probability : IsProbabilityMeasure m.candidateLaw := by
  letI := m.weight_probability
  unfold candidateLaw
  infer_instance

def sampleLaw (K : ℕ) : Measure (Sample q K) := Measure.pi (fun _ => m.candidateLaw)

instance sample_probability (K : ℕ) : IsProbabilityMeasure (m.sampleLaw K) := by
  unfold sampleLaw
  infer_instance

/-- Actual candidate score W_jᵀz+beta_j. -/
def scores {K : ℕ} (model : GaussianUnit q) (z : Fin q → ℝ) (ω : Sample q K) (j : Fin K) : ℝ :=
  (ω j).1 ⬝ᵥ z + (ω j).2

def scoreVariance (z : Fin q → ℝ) : ℝ :=
  m.biasSd ^ 2 + covarianceForm m.covariance z z

lemma scoreVariance_pos (z : Fin q → ℝ) : 0 < m.scoreVariance z := by
  have hz : 0 ≤ covarianceForm m.covariance z z := by
    simpa [covarianceForm] using m.covariance_psd.2 z
  dsimp [scoreVariance]
  have hb := m.biasSd_pos
  positivity

/-- The actual regression residual, rather than an arbitrary postulated field. -/
def residuals {K : ℕ} (z : Fin q → ℝ) (ω : Sample q K)
    (j : Fin K) (i : Fin q) : ℝ :=
  (ω j).1 i - (m.covariance *ᵥ z) i / m.scoreVariance z * m.scores z ω j

def winner (n : ℕ) (z : Fin q → ℝ) (ω : Sample q (n+1)) : Fin (n+1) :=
  finiteWinner n (m.scores z ω)

def maxValue (n : ℕ) (z : Fin q → ℝ) (ω : Sample q (n+1)) : ℝ :=
  finiteMax n (m.scores z ω)

def activeWeight (n : ℕ) (z : Fin q → ℝ) (ω : Sample q (n+1)) : Fin q → ℝ :=
  (ω (m.winner n z ω)).1

/-- Entrywise expectation of the actual selected weight outer product. -/
def selectedSecondMoment (n : ℕ) (z : Fin q → ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  fun i k => ∫ ω, m.activeWeight n z ω i * m.activeWeight n z ω k ∂m.sampleLaw (n+1)

lemma measurable_scores {K : ℕ} (z : Fin q → ℝ) : Measurable (m.scores (K := K) z) := by
  unfold scores dotProduct
  fun_prop

lemma measurable_residuals {K : ℕ} (z : Fin q → ℝ) : Measurable (m.residuals (K := K) z) := by
  unfold residuals scores dotProduct
  fun_prop

lemma winner_is_max (n : ℕ) (z : Fin q → ℝ) (ω : Sample q (n+1)) (j : Fin (n+1)) :
    m.scores z ω j ≤ m.scores z ω (m.winner n z ω) := by
  rw [winner, finiteWinner_value n (m.scores z ω)]
  exact le_finiteMax n _ j

lemma winner_score (n : ℕ) (z : Fin q → ℝ) (ω : Sample q (n+1)) :
    m.scores z ω (m.winner n z ω) = m.maxValue n z ω :=
  finiteWinner_value n _

end GaussianUnit

/-- Standard affine law of independent Gaussian linear forms; no winner or
selected-weight moment appears in this input. -/
def AffineGaussianLawInput : Prop :=
  ∀ (q n : ℕ) (m : GaussianUnit q) (z : Fin q → ℝ),
    (m.sampleLaw (n+1)).map (m.scores z) =
      Paper35.standardNormalSequence.map
        (fun x => fun j : Fin (n+1) => Real.sqrt (m.scoreVariance z) * x j.val)

/-- Standard Gaussian regression, including the full vector independence needed
for selection. Its moments concern each fixed candidate, never the winner. -/
def GaussianRegressionInput : Prop :=
  ∀ (q K : ℕ) (m : GaussianUnit q) (z : Fin q → ℝ),
    (∀ j i, MemLp (fun ω : GaussianUnit.Sample q K => m.residuals z ω j i) 2 (m.sampleLaw K)) ∧
    (∀ j i, (∫ ω : GaussianUnit.Sample q K, m.residuals z ω j i ∂m.sampleLaw K) = 0) ∧
    (∀ j i k, (∫ ω : GaussianUnit.Sample q K,
        m.residuals z ω j i * m.residuals z ω j k ∂m.sampleLaw K) =
      m.covariance i k - (m.covariance *ᵥ z) i * (m.covariance *ᵥ z) k / m.scoreVariance z) ∧
    IndepFun (m.scores (K := K) z) (m.residuals (K := K) z) (m.sampleLaw K)

/-- Generic independent finite marking. X and R are arbitrary independent
random elements, the selector and multiplier are arbitrary measurable functions
of X, and all fixed marks have the same centered covariance Gamma. -/
def IndependentMarkingInput : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K q : ℕ) (X : Ω → Fin K → ℝ) (R : Ω → Fin K → Fin q → ℝ)
    (g : (Fin K → ℝ) → Fin K) (F : (Fin K → ℝ) → ℝ)
    (Gamma : Matrix (Fin q) (Fin q) ℝ),
    Measurable X → Measurable R → Measurable g → Measurable F → IndepFun X R μ →
    (∀ j i, MemLp (fun ω => R ω j i) 2 μ) →
    (∀ j i, (∫ ω, R ω j i ∂μ) = 0) →
    (∀ j i k, (∫ ω, R ω j i * R ω j k ∂μ) = Gamma i k) →
    MemLp (fun ω => F (X ω)) 2 μ →
    (∀ i, MemLp (fun ω => R ω (g (X ω)) i) 2 μ) ∧
    (∀ i k, (∫ ω, R ω (g (X ω)) i * R ω (g (X ω)) k ∂μ) = Gamma i k) ∧
    (∀ i, (∫ ω, F (X ω) * R ω (g (X ω)) i ∂μ) = 0)

namespace GaussianUnit
variable {q : ℕ} (m : GaussianUnit q)

lemma maxValue_memLp (haffine : AffineGaussianLawInput) (n : ℕ) (z : Fin q → ℝ) :
    MemLp (m.maxValue n z) 2 (m.sampleLaw (n+1)) := by
  let T := fun x : ℕ → ℝ => fun j : Fin (n+1) => Real.sqrt (m.scoreVariance z) * x j.val
  have hT : Measurable T := by unfold T; fun_prop
  have hf := (continuous_finiteMax n).measurable
  have hn : MemLp ((finiteMax n) ∘ T) 2 Paper35.standardNormalSequence := by
    have H := (Paper35.memLp_prefixMax n 2).const_mul (Real.sqrt (m.scoreVariance z))
    simpa only [Function.comp_def, T, finiteMax_scaled_prefix n _ (Real.sqrt_nonneg _)] using H
  have hm : MemLp (finiteMax n) 2 (Paper35.standardNormalSequence.map T) :=
    (memLp_map_measure_iff hf.aestronglyMeasurable hT.aemeasurable).2 hn
  rw [← haffine q n m z] at hm
  exact hm.comp_of_map (m.measurable_scores z).aemeasurable

/-- The winner score is evaluated as a maximum of the actual iid score vector;
its second moment follows from the affine law, not from a winner-moment input. -/
lemma maxValue_secondMoment (haffine : AffineGaussianLawInput) (n : ℕ) (z : Fin q → ℝ) :
    (∫ ω, (m.maxValue n z ω)^2 ∂m.sampleLaw (n+1)) =
      m.scoreVariance z * gaussianMaxSecondMoment (n+1) := by
  let T := fun x : ℕ → ℝ => fun j : Fin (n+1) => Real.sqrt (m.scoreVariance z) * x j.val
  have hT : Measurable T := by unfold T; fun_prop
  have hf : Measurable (fun x => (finiteMax n x)^2) :=
    ((continuous_finiteMax n).pow 2).measurable
  calc
    _ = ∫ y, (finiteMax n y)^2 ∂(m.sampleLaw (n+1)).map (m.scores z) :=
      (integral_map (m.measurable_scores z).aemeasurable hf.aestronglyMeasurable).symm
    _ = ∫ y, (finiteMax n y)^2 ∂Paper35.standardNormalSequence.map T := by
      rw [haffine q n m z]
    _ = ∫ x, (finiteMax n (T x))^2 ∂Paper35.standardNormalSequence :=
      integral_map hT.aemeasurable hf.aestronglyMeasurable
    _ = ∫ x, m.scoreVariance z * (Paper35.prefixMax n x)^2 ∂Paper35.standardNormalSequence := by
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp only [T]
      rw [finiteMax_scaled_prefix n _ (Real.sqrt_nonneg _), mul_pow,
        Real.sq_sqrt (m.scoreVariance_pos z).le]
    _ = _ := by rw [integral_const_mul]; rfl

end GaussianUnit

/-- Pure expectation algebra, applicable to arbitrary square-integrable marks. -/
lemma integral_regression_product {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (V R S : Ω → ℝ) (hV : MemLp V 2 μ) (hR : MemLp R 2 μ) (hS : MemLp S 2 μ)
    (a b : ℝ) :
    (∫ ω, (a*V ω+R ω)*(b*V ω+S ω) ∂μ) =
      a*b*(∫ ω, (V ω)^2 ∂μ) + a*(∫ ω, V ω*S ω ∂μ) +
        b*(∫ ω, V ω*R ω ∂μ) + (∫ ω, R ω*S ω ∂μ) := by
  have hvv := hV.integrable_sq
  have hvs : Integrable (fun ω => V ω*S ω) μ := hV.integrable_mul hS
  have hvr : Integrable (fun ω => V ω*R ω) μ := hV.integrable_mul hR
  have hrs : Integrable (fun ω => R ω*S ω) μ := hR.integrable_mul hS
  simp_rw [show ∀ ω, (a*V ω+R ω)*(b*V ω+S ω) =
      (a*b)*(V ω)^2 + a*(V ω*S ω) + b*(V ω*R ω) + R ω*S ω by intro ω; ring]
  have H1 := integral_add (((hvv.const_mul (a*b)).add (hvs.const_mul a)).add (hvr.const_mul b)) hrs
  have H2 := integral_add ((hvv.const_mul (a*b)).add (hvs.const_mul a)) (hvr.const_mul b)
  have H3 := integral_add (hvv.const_mul (a*b)) (hvs.const_mul a)
  simp only [Pi.add_apply] at H1 H2 H3
  rw [H1, H2, H3, integral_const_mul, integral_const_mul, integral_const_mul]

namespace GaussianUnit
variable {q : ℕ} (m : GaussianUnit q)

/-- Proposition 8.2, equation (8.15), for the actual Maxout winning weight.
The external inputs are only the standard Gaussian laws and the generic
independent marking lemma, all stated above with their original quantifiers. -/
theorem winner_secondMoment (haffine : AffineGaussianLawInput)
    (hregression : GaussianRegressionInput) (hmarking : IndependentMarkingInput)
    (n : ℕ) (z : Fin q → ℝ) :
    m.selectedSecondMoment n z =
      activeSecondMomentMatrix m.covariance z (m.scoreVariance z)
        (gaussianMaxSecondMoment (n+1)) := by
  let Gamma : Matrix (Fin q) (Fin q) ℝ := fun i k =>
    m.covariance i k - (m.covariance *ᵥ z) i * (m.covariance *ᵥ z) k / m.scoreVariance z
  obtain ⟨hR, hmean, hcov, hindep⟩ := hregression q (n+1) m z
  have hV := m.maxValue_memLp haffine n z
  obtain ⟨hselected, hselectedCov, hcross⟩ := hmarking
    (Sample q (n+1)) (m.sampleLaw (n+1)) (n+1) q
    (m.scores z) (m.residuals z) (finiteWinner n) (finiteMax n) Gamma
    (m.measurable_scores z) (m.measurable_residuals z) (measurable_finiteWinner n)
    (continuous_finiteMax n).measurable hindep hR hmean hcov hV
  have hdec (ω : Sample q (n+1)) (i : Fin q) :
      m.activeWeight n z ω i = (m.covariance *ᵥ z) i / m.scoreVariance z *
          m.maxValue n z ω + m.residuals z ω (m.winner n z ω) i := by
    unfold activeWeight residuals
    rw [m.winner_score]
    ring
  ext i k
  change (∫ ω, m.activeWeight n z ω i * m.activeWeight n z ω k ∂m.sampleLaw (n+1)) = _
  simp_rw [hdec]
  rw [integral_regression_product (m.sampleLaw (n+1)) (m.maxValue n z)
    (fun ω => m.residuals z ω (m.winner n z ω) i)
    (fun ω => m.residuals z ω (m.winner n z ω) k) hV (hselected i) (hselected k)]
  change _ = m.covariance i k + (gaussianMaxSecondMoment (n+1)-1) *
    ((m.scoreVariance z)⁻¹ * ((m.covariance *ᵥ z) i * (m.covariance *ᵥ z) k))
  rw [m.maxValue_secondMoment haffine n z]
  have hi := hcross i
  have hk := hcross k
  have hik := hselectedCov i k
  change (∫ ω, m.maxValue n z ω * m.residuals z ω (m.winner n z ω) i ∂m.sampleLaw (n+1)) = 0 at hi
  change (∫ ω, m.maxValue n z ω * m.residuals z ω (m.winner n z ω) k ∂m.sampleLaw (n+1)) = 0 at hk
  change (∫ ω, m.residuals z ω (m.winner n z ω) i *
      m.residuals z ω (m.winner n z ω) k ∂m.sampleLaw (n+1)) = Gamma i k at hik
  rw [hi, hk, hik]
  dsimp only [Gamma]
  have hs := (m.scoreVariance_pos z).ne'
  field_simp
  <;> ring

/-- Every coordinate of the actually selected weight has a finite second
moment. This is obtained from its actual regression decomposition. -/
theorem activeWeight_memLp (haffine : AffineGaussianLawInput)
    (hregression : GaussianRegressionInput) (hmarking : IndependentMarkingInput)
    (n : ℕ) (z : Fin q → ℝ) (i : Fin q) :
    MemLp (fun ω => m.activeWeight n z ω i) 2 (m.sampleLaw (n+1)) := by
  let Gamma : Matrix (Fin q) (Fin q) ℝ := fun i k =>
    m.covariance i k - (m.covariance *ᵥ z) i * (m.covariance *ᵥ z) k / m.scoreVariance z
  obtain ⟨hR,hmean,hcov,hindep⟩ := hregression q (n+1) m z
  have hV := m.maxValue_memLp haffine n z
  obtain ⟨hselected,_,_⟩ := hmarking (Sample q (n+1)) (m.sampleLaw (n+1)) (n+1) q
    (m.scores z) (m.residuals z) (finiteWinner n) (finiteMax n) Gamma
    (m.measurable_scores z) (m.measurable_residuals z) (measurable_finiteWinner n)
    (continuous_finiteMax n).measurable hindep hR hmean hcov hV
  have H := (hV.const_mul ((m.covariance *ᵥ z) i / m.scoreVariance z)).add (hselected i)
  convert H using 1
  funext ω
  dsimp only [activeWeight, residuals, Pi.add_apply, winner, maxValue]
  rw [finiteWinner_value n (m.scores z ω)]
  ring

end GaussianUnit

/-- Finite-dimensional expectation/outer-product identity with all cross-term
integrability justified by coordinate L² hypotheses. -/
lemma integral_dotProduct_square {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (W : Ω → ι → ℝ) (hW : ∀ i, MemLp (fun ω => W ω i) 2 μ)
    (v : ι → ℝ) :
    (∫ ω, (v ⬝ᵥ W ω)^2 ∂μ) =
      covarianceForm (fun i k => ∫ ω, W ω i*W ω k ∂μ) v v := by
  have hexp (ω : Ω) : (v ⬝ᵥ W ω)^2 = ∑ i, ∑ k, (v i*v k)*(W ω i*W ω k) := by
    simp only [dotProduct, pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro k hk
    ring
  simp_rw [hexp]
  have hprod (i k : ι) : Integrable (fun ω => (v i*v k)*(W ω i*W ω k)) μ :=
    ((hW i).integrable_mul (hW k)).const_mul _
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun k _ => hprod i k))]
  simp_rw [integral_finset_sum _ (fun k _ => hprod _ k), integral_const_mul]
  simp only [covarianceForm, Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  ring

namespace GaussianUnit
variable {q : ℕ} (m : GaussianUnit q)

/-- The exact active projected second moment used by the Gaussian length bound. -/
theorem activeProjection_secondMoment (haffine : AffineGaussianLawInput)
    (hregression : GaussianRegressionInput) (hmarking : IndependentMarkingInput)
    (n : ℕ) (z v : Fin q → ℝ) :
    (∫ ω, (v ⬝ᵥ m.activeWeight n z ω)^2 ∂m.sampleLaw (n+1)) =
      covarianceForm (activeSecondMomentMatrix m.covariance z (m.scoreVariance z)
        (gaussianMaxSecondMoment (n+1))) v v := by
  rw [integral_dotProduct_square (m.sampleLaw (n+1)) (m.activeWeight n z)
    (m.activeWeight_memLp haffine hregression hmarking n z)]
  change covarianceForm (m.selectedSecondMoment n z) v v = _
  rw [m.winner_secondMoment haffine hregression hmarking n z]

/-- The source PSD conclusion now applies to the actual expectation of the
winning weight, rather than only to the deterministic candidate Q expression. -/
theorem winner_secondMoment_domination (haffine : AffineGaussianLawInput)
    (hregression : GaussianRegressionInput) (hmarking : IndependentMarkingInput)
    (n : ℕ) (z : Fin q → ℝ) :
    (gaussianLengthCorrection (n+1) • m.covariance - m.selectedSecondMoment n z).PosSemidef := by
  rw [m.winner_secondMoment haffine hregression hmarking n z]
  exact gaussian_secondMomentMatrix_domination m.covariance_psd z m.biasSd_pos (n+1)

end GaussianUnit
end Paper35.GaussianWinner
