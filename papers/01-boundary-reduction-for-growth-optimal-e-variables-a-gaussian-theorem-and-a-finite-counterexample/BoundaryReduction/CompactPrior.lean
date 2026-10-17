/- Compactness of Borel probability priors on compact metric spaces.
The proof represents priors by positive normalized linear functionals,
uses Tychonoff compactness, and reconstructs measures by Riesz–Markov. -/
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.ContinuousMap.Bounded.Normed

open Set MeasureTheory
open scoped Classical CompactlySupported BoundedContinuousFunction
namespace BoundaryReduction.CompactPrior

variable (X : Type*) [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

abbrev Test := C_c(X, ℝ)
abbrev Functional := Test X → ℝ

noncomputable def unitTest : Test X :=
  ⟨⟨fun _ => 1, continuous_const⟩, HasCompactSupport.of_compactSpace _⟩

@[simp] lemma unitTest_apply (x : X) : unitTest X x = 1 := rfl

def positiveNormalized : Set (Functional X) :=
  {L | (∀ f g, L (f+g) = L f+L g) ∧
       (∀ (a : ℝ) f, L (a • f) = a*L f) ∧
       (∀ f g, f ≤ g → L f ≤ L g) ∧ L (unitTest X) = 1}

def boundedCoordinates : Set (Functional X) :=
  Set.univ.pi (fun f => Icc (-‖f.toContinuousMap‖) ‖f.toContinuousMap‖)

def stateSet : Set (Functional X) := positiveNormalized X ∩ boundedCoordinates X

lemma positiveNormalized_closed : IsClosed (positiveNormalized X) := by
  have ha : IsClosed {L : Functional X | ∀ f g, L (f+g) = L f+L g} := by
    simp only [setOf_forall]
    apply isClosed_iInter
    intro f
    apply isClosed_iInter
    intro g
    exact isClosed_eq (continuous_apply (f+g)) ((continuous_apply f).add (continuous_apply g))
  have hs : IsClosed {L : Functional X | ∀ (a : ℝ) f, L (a • f) = a*L f} := by
    simp only [setOf_forall]
    apply isClosed_iInter
    intro a
    apply isClosed_iInter
    intro f
    exact isClosed_eq (continuous_apply _) (continuous_const.mul (continuous_apply _))
  have hp : IsClosed {L : Functional X | ∀ f g, f ≤ g → L f ≤ L g} := by
    simp only [setOf_forall]
    apply isClosed_iInter
    intro f
    apply isClosed_iInter
    intro g
    apply isClosed_iInter
    intro _
    exact isClosed_le (continuous_apply _) (continuous_apply _)
  have hn : IsClosed {L : Functional X | L (unitTest X) = 1} := isClosed_eq (continuous_apply _) continuous_const
  exact ha.inter (hs.inter (hp.inter hn))

lemma stateSet_compact : IsCompact (stateSet X) :=
  (isCompact_univ_pi (fun _ => isCompact_Icc)).inter_left (positiveNormalized_closed X)

abbrev State := stateSet X

instance : CompactSpace (State X) := isCompact_iff_compactSpace.mp (stateSet_compact X)

noncomputable def stateFunctional (s : State X) : Test X →ₚ[ℝ] ℝ where
  toFun := s.1
  map_add' := s.2.1.1
  map_smul' := s.2.1.2.1
  monotone' := s.2.1.2.2.1

lemma stateFunctional_one (s : State X) : stateFunctional X s (unitTest X) = 1 := s.2.1.2.2.2

lemma riesz_state_probability (s : State X) : IsProbabilityMeasure (RealRMK.rieszMeasure (stateFunctional X s)) := by
  constructor
  have hu := RealRMK.rieszMeasure_le_of_eq_one (stateFunctional X s)
    (f := (unitTest X)) (fun x => by simp) isCompact_univ (fun x _ => by simp)
  have hl := RealRMK.le_rieszMeasure_tsupport_subset (stateFunctional X s)
    (f := (unitTest X)) (fun x => by simp) (Set.subset_univ _)
  rw [stateFunctional_one] at hu hl
  norm_num at hu hl
  exact le_antisymm hu hl

noncomputable def statePrior (s : State X) : ProbabilityMeasure X :=
  ⟨RealRMK.rieszMeasure (stateFunctional X s), riesz_state_probability X s⟩

lemma integral_statePrior (s : State X) (f : Test X) :
    (∫ x, f x ∂(statePrior X s : Measure X)) = s.1 f :=
  RealRMK.integral_rieszMeasure (stateFunctional X s) f

lemma statePrior_continuous : Continuous (statePrior X) := by
  rw [continuous_iff_continuousAt]
  intro s
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  let fc : Test X := CompactlySupportedContinuousMap.ContinuousMap.liftCompactlySupported f.toContinuousMap
  change Filter.Tendsto (fun t : State X => ∫ x, fc x ∂(statePrior X t : Measure X))
    (nhds s) (nhds (∫ x, fc x ∂(statePrior X s : Measure X)))
  simp only [integral_statePrior]
  exact ((continuous_apply fc).comp continuous_subtype_val).continuousAt

lemma integrable_test (W : ProbabilityMeasure X) (f : Test X) : Integrable f (W : Measure X) :=
  f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport

noncomputable def priorFunctional (W : ProbabilityMeasure X) : Functional X := fun f => ∫ x, f x ∂W

lemma priorFunctional_mem (W : ProbabilityMeasure X) : priorFunctional X W ∈ stateSet X := by
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro f g
      exact integral_add (integrable_test X W f) (integrable_test X W g)
    · intro a f
      exact integral_const_mul a _
    · intro f g hfg
      exact integral_mono (integrable_test X W f) (integrable_test X W g) hfg
    · simp [priorFunctional]
  · intro f _
    have hn : ‖∫ x, f x ∂(W : Measure X)‖ ≤ ‖f.toContinuousMap‖ := by
      have hh := norm_integral_le_integral_norm (f := fun x => f x) (μ := (W : Measure X))
      have hb := integral_mono (integrable_test X W f).norm (integrable_const ‖f.toContinuousMap‖)
        (fun x => f.toContinuousMap.norm_coe_le_norm x)
      simpa using hh.trans hb
    exact abs_le.mp hn

noncomputable def priorState (W : ProbabilityMeasure X) : State X :=
  ⟨priorFunctional X W, priorFunctional_mem X W⟩

lemma statePrior_surjective : Function.Surjective (statePrior X) := by
  intro W
  refine ⟨priorState X W, ?_⟩
  apply ProbabilityMeasure.toMeasure_injective
  have h := FiniteMeasure.ext_of_forall_integral_eq
    (μ := (statePrior X (priorState X W)).toFiniteMeasure) (ν := W.toFiniteMeasure) (fun f => ?_)
  · exact congrArg FiniteMeasure.toMeasure h
  · let fc : Test X := CompactlySupportedContinuousMap.ContinuousMap.liftCompactlySupported f.toContinuousMap
    change (∫ x, fc x ∂(statePrior X (priorState X W) : Measure X)) = ∫ x, fc x ∂(W : Measure X)
    rw [integral_statePrior]
    rfl

/-- Borel probabilities on a compact metric space form a weakly compact space. -/
theorem probabilityMeasure_compact : IsCompact (Set.univ : Set (ProbabilityMeasure X)) := by
  have h := isCompact_univ.image (statePrior_continuous X)
  rwa [Set.image_univ, (statePrior_surjective X).range_eq] at h

end BoundaryReduction.CompactPrior
