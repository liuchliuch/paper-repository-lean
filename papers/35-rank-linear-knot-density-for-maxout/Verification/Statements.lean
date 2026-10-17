import Paper35

open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

namespace Verification.Specification

/-- Frozen explicit statement for the proved-subset Comparator. -/
def rank_one : Prop :=
  ∀ (f : Fin 1 → ℝ → ℝ) (L : ℝ), Paper35.switchCount f L = 0

/-- Frozen explicit statement for the proved-subset Comparator. -/
def pair_decomposition : Prop :=
  ∀ {K : ℕ} (f : Fin K → ℝ → ℝ) (L : ℝ), Paper35.switchCount f L = ∑ p : Paper35.OrderedCandidatePair K, ((Paper35.pairSwitchSet f L p).encard : ℝ≥0∞)

/-- Frozen explicit statement for the proved-subset Comparator. -/
def opposite_mass : Prop :=
  ∀ {B p T U H : ℝ}, 0 ≤ B → 0 ≤ p → p ≤ 1 → H ≤ B * p * (T - U) → H ≤ B * (1 - p) * U → H ≤ B * T * p * (1 - p)

/-- Frozen explicit statement for the proved-subset Comparator. -/
def layer_cake : Prop :=
  ∀ (μ : Measure ℝ) [SFinite μ], (∫⁻ z : ℝ × ℝ, ENNReal.ofReal |z.1 - z.2| ∂μ.prod μ) = 2 * ∫⁻ r : ℝ, μ (Set.Iic r) * μ (Set.Ioi r)

/-- Frozen explicit statement for the proved-subset Comparator. -/
def gini_bound : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ), MemLp X 2 μ → IdentDistrib X Y μ μ → IndepFun X Y μ → (∫ ω, |X ω - Y ω| ∂μ) ≤ (2 / Real.sqrt 3) * Real.sqrt (variance X μ)

/-- Frozen explicit statement for the proved-subset Comparator. -/
def atomic_bias : Prop :=
  ∀ (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ] [IsProbabilityMeasure ν] {ε : ℝ}, 0 < ε → (ν.real {0}) ^ 2 / (2 * ε) ≤ Paper35.Counterexamples.independentExpectedDensity μ ν (-ε) ε

/-- Frozen explicit statement for the proved-subset Comparator. -/
def dependent_bias : Prop :=
  ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ] (x₀ : ℝ) {ε : ℝ}, 0 < ε → Paper35.Counterexamples.dependentExpectedDensity μ x₀ ε = 1 / (2 * ε)

/-- Frozen explicit statement for the proved-subset Comparator. -/
def binary_count : Prop :=
  ∀ (lo hi a b c d : ℝ), Paper35.switchCount (Paper35.Counterexamples.binaryScores lo a b c d) (hi - lo) = ENNReal.ofReal (Paper35.Counterexamples.binarySwitchCount lo hi a b c d)

/-- Frozen explicit statement for the proved-subset Comparator. -/
def positive_rescaling : Prop :=
  ∀ {K : ℕ} (f : Fin K → ℝ → ℝ) (c r : ℝ → ℝ) (L : ℝ), (∀ t ∈ Set.Ioo 0 L, 0 < r t) → Paper35.switchCount (fun j t => c t + r t * f j t) L = Paper35.switchCount f L

/-- Frozen explicit statement for the proved-subset Comparator. -/
def normalized_speed : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (y v : E), y ≠ 0 → ‖Paper35.Gaussian.normalizedVelocity y v‖ ^ 2 = ‖v‖ ^ 2 / ‖y‖ ^ 2 - (inner ℝ y v) ^ 2 / ‖y‖ ^ 4

/-- Frozen explicit statement for the proved-subset Comparator. -/
def rank_increase : Prop :=
  StrictMono (fun n => Paper35.gaussianMaxMean (n + 1))

/-- Frozen explicit statement for the proved-subset Comparator. -/
def rank_concavity : Prop :=
  ∀ n : ℕ, Paper35.gaussianMaxMean (n + 3) - Paper35.gaussianMaxMean (n + 2) < Paper35.gaussianMaxMean (n + 2) - Paper35.gaussianMaxMean (n + 1)

/-- Frozen explicit statement for the proved-subset Comparator. -/
def length_recursion : Prop :=
  ∀ (A L : ℕ → ℝ), (∀ n, 0 ≤ A n) → (∀ n, L (n + 1) ≤ A n * L n) → ∀ n, L n ≤ L 0 * Paper35.Deep.lengthProduct A n

/-- Frozen explicit statement for the proved-subset Comparator. -/
def switch_recursion : Prop :=
  ∀ (A D L S : ℕ → ℝ), (∀ n, 0 ≤ A n) → (∀ n, 0 ≤ D n) → (∀ n, L (n + 1) ≤ A n * L n) → S 0 = 0 → (∀ n, S (n + 1) ≤ S n + D n * L n) → ∀ n, S n ≤ L 0 * Paper35.Deep.switchCoefficient A D n

/-- Frozen explicit statement for the proved-subset Comparator. -/
def psd_domination : Prop :=
  ∀ {ι : Type} [Fintype ι] {C : Matrix ι ι ℝ}, C.PosSemidef → ∀ z : ι → ℝ, ∀ {σ : ℝ}, 0 < σ → ∀ m₂ : ℝ, (max 1 m₂ • C - Paper35.Deep.activeSecondMomentMatrix C z (σ ^ 2 + Paper35.Deep.covarianceForm C z z) m₂).PosSemidef

/-- Frozen explicit statement for the proved-subset Comparator. -/
def source_atomic_bias : Prop :=
  ∀ (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ] [IsProbabilityMeasure ν] {ε : ℝ}, 0 < ε → ENNReal.ofReal ((ν.real {0}) ^ 2 / (2 * ε)) ≤ Paper35.Counterexamples.expectedIndependentSourceDensity μ ν (-ε) ε

/-- Frozen explicit statement for the proved-subset Comparator. -/
def source_dependent_bias : Prop :=
  ∀ {a x₀ : ℝ}, 0 < a → x₀ ≠ 0 → ∀ {ε : ℝ}, 0 < ε → (∃ f : ℝ → ℝ≥0∞, ∃ C : ℝ≥0∞, Measurable f ∧ C ≠ ∞ ∧ (∀ y, f y ≤ C) ∧ Paper35.Counterexamples.uniformSlope a = volume.withDensity f) ∧ (∃ f : ℝ → ℝ≥0∞, ∃ C : ℝ≥0∞, Measurable f ∧ C ≠ ∞ ∧ (∀ y, f y ≤ C) ∧ Paper35.Counterexamples.dependentBiasLaw a x₀ = volume.withDensity f) ∧ (∫⁻ z : ℝ × ℝ, Paper35.switchDensity (Paper35.Counterexamples.binaryScores (x₀ - ε) z.1 (-x₀ * z.1) z.2 (-x₀ * z.2)) (2 * ε) ∂(Paper35.Counterexamples.uniformSlope a).prod (Paper35.Counterexamples.uniformSlope a)) = (1 : ℝ≥0∞) / ENNReal.ofReal (2 * ε)

/-- Frozen explicit statement for the proved-subset Comparator. -/
def tilt_probability : Prop :=
  ∀ {α : Type} [MeasurableSpace α] {μ : Measure α} {b : α → ℝ} {B : ℝ}, Integrable b μ → (∀ w, 0 ≤ b w) → 0 < B → (∫ w, b w ∂μ) = B → IsProbabilityMeasure (Paper35.Visibility.tiltedLaw μ b B)

/-- Frozen explicit statement for the proved-subset Comparator. -/
def integrated_visibility_split : Prop :=
  ∀ {β : Type} [MeasurableSpace β] {ν : Measure β} {qplus qminus : β → ℝ} {B p T : ℝ}, 0 ≤ B → 0 ≤ p → p ≤ 1 → Integrable qplus ν → Integrable qminus ν → (∀ᵐ y ∂ν, 0 ≤ qplus y) → (∀ᵐ y ∂ν, 0 ≤ qminus y) → (∀ᵐ y ∂ν, qplus y ≤ B * p) → (∀ᵐ y ∂ν, qminus y ≤ B * (1 - p)) → (∫ y, (qplus y + qminus y) ∂ν) = T → Integrable (fun y => qplus y * qminus y) ν ∧ (∫ y, qplus y * qminus y ∂ν) ≤ B * T * p * (1 - p)

/-- Frozen explicit statement for the proved-subset Comparator. -/
def gini_uniform_equality : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ) (a b : ℝ), IdentDistrib X (fun t : ℝ => a + b * t) μ Paper35.Gini.unitLaw → IdentDistrib X Y μ μ → IndepFun X Y μ → (∫ ω, |X ω - Y ω| ∂μ) = (2 / Real.sqrt 3) * Real.sqrt (variance X μ)

/-- Frozen explicit statement for the proved-subset Comparator. -/
def gini_sharpness : Prop :=
  ∀ C : ℝ, (∀ (ν : Measure ℝ) [IsProbabilityMeasure ν] (Z : ℝ → ℝ), Measurable Z → MemLp Z 2 ν → Paper35.Gini.meanDifference ν Z ≤ C * Real.sqrt (variance Z ν)) → 2 / Real.sqrt 3 ≤ C

/-- Frozen explicit statement for the proved-subset Comparator. -/
def gaussian_rank_two : Prop :=
  Paper35.gaussianRankCoefficient 2 = 1 / Real.pi

/-- Frozen explicit statement for the proved-subset Comparator. -/
def gaussian_rank_linear : Prop :=
  ∀ {K : ℕ}, 1 ≤ K → Paper35.gaussianRankCoefficient K ≤ (K - 1 : ℕ) / Real.pi

/-- Frozen explicit statement for the proved-subset Comparator. -/
def tilted_directional_gini : Prop :=
  ∀ {d : ℕ} (m : Paper35.Source.WeightedModel d), MemLp (fun w => w) 2 m.tilted → ∀ u : Paper35.Source.Space d, m.directionalGini u ≤ ENNReal.ofReal (2 / Real.sqrt 3) * ENNReal.ofReal (Real.sqrt (m.projectedVariance u))

/-- Frozen explicit statement for the proved-subset Comparator. -/
def cdf_power : Prop :=
  ∀ {h : ℝ → ℝ≥0∞}, AEMeasurable h volume → (∫⁻ y, h y) = 1 → ∀ n : ℕ, let μ := volume.withDensity h; (∫⁻ y : ℝ, μ (Set.Iic y) ^ n * h y) = (n + 1 : ℝ≥0∞)⁻¹

/-- Frozen explicit statement for the proved-subset Comparator. -/
def gaussian_half_rank : Prop :=
  ∀ {K : ℕ}, 2 ≤ K → Paper35.gaussianRankCoefficient K ≤ (K : ℝ) / (2 * Real.pi)

/-- Frozen explicit statement for the proved-subset Comparator. -/
def gaussian_uniform_sharpness : Prop :=
  ∀ C : ℝ, (∀ K : ℕ, 2 ≤ K → Paper35.gaussianRankCoefficient K ≤ C * ((K : ℝ) - 1)) ↔ 1 / Real.pi ≤ C

end Verification.Specification
