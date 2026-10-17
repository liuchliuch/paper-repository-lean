import Paper35.SourceTheorems
import Mathlib.MeasureTheory.Function.EssSup

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace Paper35.SourceSupremum
open Source Source.WeightedModel ClassicalInputs Sharpness

/-- The original admissible law class for (2.10). Both bias independence and
actual common coordinate densities are explicit. B is the essential supremum
of the bias density, and B*sigma is strictly positive. -/
structure AdmissibleLaw (d : ℕ) where
  model : WeightedModel d
  B : ℝ≥0
  B_pos : 0 < B
  sigma : ℝ
  sigma_pos : 0 < sigma
  constantEnvelope : ∀ᵐ w ∂model.weights, model.b₀ w = B
  independentCoordinates : iIndepFun (fun (i : Fin d) (w : Space d) => w i) model.weights
  identicallyDistributed : ∀ i j : Fin d, IdentDistrib (fun w : Space d => w i)
    (fun w : Space d => w j) model.weights model.weights
  coordinateL2 : ∀ i : Fin d, MemLp (fun w : Space d => w i) 2 model.weights
  coordinateVariance : ∀ i : Fin d, variance (fun w : Space d => w i) model.weights = sigma^2
  coordinateDensity : ∃ ρ : ℝ → ℝ≥0∞, Measurable ρ ∧
    ∀ i : Fin d, model.weights.map (fun w => w i) = volume.withDensity ρ
  independentBias : ∃ ρ : ℝ → ℝ≥0∞, Measurable ρ ∧ essSup ρ volume = B ∧
    ∀ᵐ w ∂model.weights, ∀ b, model.g w b = ρ b

namespace AdmissibleLaw
variable {d : ℕ}
def normalizedDensity (a : AdmissibleLaw d) (K : ℕ) (p : Probe d) : ℝ≥0∞ :=
  a.model.expectedDensity K p / ((a.B : ℝ≥0∞)*ENNReal.ofReal a.sigma)

lemma normalizedDensity_le (hLN : LusinNovikovLaw) (hUP : BorelProjectionLaw)
    (a : AdmissibleLaw d) (K : ℕ) (hK : 2 ≤ K) (p : Probe d) :
    a.normalizedDensity K p ≤ (K : ℝ≥0∞)/ENNReal.ofReal (Real.sqrt 3) := by
  apply ENNReal.div_le_of_le_mul
  have H := SourceTheorems.corollary_2_5_upper hLN hUP a.model a.B a.constantEnvelope
    a.independentCoordinates a.coordinateL2 a.sigma a.sigma_pos.le a.coordinateVariance K hK p
  convert H using 1
  simp only [div_eq_mul_inv]
  ac_rfl

end AdmissibleLaw

lemma uniform_bias_essSup : essSup (biasDensity 1) volume = (1 : ℝ≥0∞) := by
  unfold biasDensity
  rw [ENNReal.essSup_indicator_eq_essSup_restrict measurableSet_Icc]
  simp only [ENNReal.ofReal_one]
  apply essSup_const
  intro hz
  have H := congrArg (fun ν : Measure ℝ => ν univ) hz
  norm_num [Measure.restrict_apply_univ, biasHalfWidth, Real.volume_Icc] at H

/-- The sharp construction belongs to the full original admissible class,
including all density and independence requirements. -/
def uniformLaw (d : ℕ) : AdmissibleLaw d where
  model := independentUniformModel (uniformWeights d (Real.sqrt 3)) 1 (by norm_num)
  B := 1
  B_pos := by norm_num
  sigma := 1
  sigma_pos := by norm_num
  constantEnvelope := Filter.Eventually.of_forall (fun _ => by simp [independentUniformModel])
  independentCoordinates := (uniformWeights_coordinates_iid (Real.sqrt 3)).1
  identicallyDistributed := (uniformWeights_coordinates_iid (Real.sqrt 3)).2
  coordinateL2 := uniformWeights_coordinate_memLp _
  coordinateVariance := by
    intro i
    simpa only [mul_one] using sharp_coordinates_variance 1 i
  coordinateDensity := by
    refine ⟨(Icc (-Real.sqrt 3) (Real.sqrt 3)).indicator
      (fun _ => (ENNReal.ofReal (2*Real.sqrt 3))⁻¹),
      measurable_const.indicator measurableSet_Icc, ?_⟩
    intro i
    exact uniformWeights_coordinate_density (Real.sqrt_pos.2 (by norm_num)) i
  independentBias := ⟨biasDensity 1, measurable_biasDensity 1, uniform_bias_essSup,
    Filter.Eventually.of_forall (fun _ _ => rfl)⟩

lemma uniform_normalizedDensity {d K : ℕ} (hLN : LusinNovikovLaw) (hUP : BorelProjectionLaw)
    (hK : 2 ≤ K) (i : Fin d) (ε : ℝ) (hε : 0 < ε) :
    (uniformLaw d).normalizedDensity K (centeredProbe i ε hε) =
      ENNReal.ofReal (centeredExpectedDensity (uniformLaw d).model K i ε) := by
  have hb := (uniformLaw d).normalizedDensity_le hLN hUP K hK (centeredProbe i ε hε)
  have heq : (uniformLaw d).normalizedDensity K (centeredProbe i ε hε) =
      (uniformLaw d).model.expectedDensity K (centeredProbe i ε hε) := by
    simp [AdmissibleLaw.normalizedDensity, uniformLaw]
  rw [heq] at hb ⊢
  have hfinite : (uniformLaw d).model.expectedDensity K (centeredProbe i ε hε) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.div_ne_top (by simp) (by positivity)) hb
  rw [centeredExpectedDensity_source _ _ _ hε]
  exact (ENNReal.ofReal_toReal hfinite).symm

/-- Source equation (2.10), with the supremum taken over the full original
admissible laws and every positive-length deterministic rectifiable Probe.
This is a global law-class statement, beyond the exhibited uniform subfamily. -/
theorem full_admissible_supremum {d : ℕ} (hd : 1 ≤ d)
    (hLN : LusinNovikovLaw) (hUP : BorelProjectionLaw) (K : ℕ) (hK : 2 ≤ K) :
    (⨆ a : AdmissibleLaw d, ⨆ p : Probe d, a.normalizedDensity K p) =
      ENNReal.ofReal ((K : ℝ)/Real.sqrt 3) := by
  have hcoef : ENNReal.ofReal ((K : ℝ)/Real.sqrt 3) =
      (K : ℝ≥0∞)/ENNReal.ofReal (Real.sqrt 3) := by
    rw [ENNReal.ofReal_div_of_pos (Real.sqrt_pos.2 (by norm_num)), ENNReal.ofReal_natCast]
  apply le_antisymm
  · rw [hcoef]
    exact iSup_le (fun a => iSup_le (fun p => a.normalizedDensity_le hLN hUP K hK p))
  · let i : Fin d := ⟨0,hd⟩
    have H := SourceTheorems.corollary_2_5_sharp_family hLN hUP
      (B := 1) (σ := 1) (by norm_num) (by norm_num) K hK i
    simp only [mul_one] at H
    rw [← H]
    apply iSup_le
    intro ε
    have hm := uniform_normalizedDensity hLN hUP hK i ε ε.property
    simp only [uniformLaw] at hm
    rw [← hm]
    exact le_iSup_of_le (uniformLaw d) (le_iSup_of_le (centeredProbe i ε ε.property) le_rfl)

/-- Source (2.11) with the complete all-laws/all-ranks quantifiers. -/
theorem universal_rank_linear_coefficient_iff {d : ℕ} (hd : 1 ≤ d)
    (hLN : LusinNovikovLaw) (hUP : BorelProjectionLaw) (C : ℝ) :
    (∀ K : ℕ, 2 ≤ K → ∀ a : AdmissibleLaw d, ∀ p : Probe d,
      a.normalizedDensity K p ≤ ENNReal.ofReal (C*((K : ℝ)-1))) ↔
        2/Real.sqrt 3 ≤ C := by
  constructor
  · intro hbound
    have H : (⨆ a : AdmissibleLaw d, ⨆ p : Probe d, a.normalizedDensity 2 p) ≤
        ENNReal.ofReal C := by
      apply iSup_le
      intro a
      apply iSup_le
      intro p
      simpa only [Nat.cast_ofNat, sub_self, sub_add_cancel, show (2:ℝ)-1=1 by norm_num, mul_one]
        using hbound 2 (by norm_num) a p
    rw [full_admissible_supremum hd hLN hUP 2 (by norm_num)] at H
    have hpos : (0:ℝ) < 2/Real.sqrt 3 := by positivity
    exact (ENNReal.ofReal_le_ofReal_iff'.mp H).resolve_right (not_le_of_gt hpos)
  · intro hC K hK a p
    apply (a.normalizedDensity_le hLN hUP K hK p).trans
    rw [← ENNReal.ofReal_natCast K,
      ← ENNReal.ofReal_div_of_pos (Real.sqrt_pos.2 (by norm_num))]
    apply ENNReal.ofReal_le_ofReal
    have hk : (0:ℝ) ≤ (K:ℝ)-1 := by have h := (show (2:ℝ) ≤ K by exact_mod_cast hK); linarith
    have H := Paper35.isotropic_rank_constant_bound K hK (B := 1) (σ := 1)
      (by norm_num) (by norm_num)
    simp only [mul_one] at H
    exact H.trans (mul_le_mul_of_nonneg_right hC hk)

end Paper35.SourceSupremum
