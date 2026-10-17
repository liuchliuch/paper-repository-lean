import Paper26.AdaptiveCoordinateTransport
import Paper26.OperatorPOVMTransport
import Paper26.FinitePolarization
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Raw operator steps and fixed-history-measure repair

This module does not postulate a jointly measurable family RN theorem.
`OperatorStep` is an actual weakly measurable family of operator POVMs.
Its Born kernels are constructed from the existing fixed-measure operator RN
input; all event probabilities are intrinsic and independent of that choice.

The second part proves a useful fixed-history-measure substep: global joint
integrability, positivity and rectangle-normalization of a candidate matrix
density imply common a.e. conditional POVM conditions. A measurable null set
of histories can then be repaired by the identity effect. These are explicit
intermediate hypotheses, not an assumed representation of an operator family
or an assumed protocol-equivalence conclusion. The joint matrix operator
measure, its RN density and its rectangle identities are then constructed
using finite positive polarization and ordinary fixed-space RN. Finally the
actual entire raw operator protocol is transported lawwise to the dominated
model, and both adaptive main lower bounds are applied.
-/

noncomputable section
open scoped BigOperators ComplexOrder ENNReal
open MeasureTheory ProbabilityTheory Set

namespace Paper26.AdaptiveOperatorModelTransport
open QuantumModel ContinuousPOVM CollectiveModel AdaptiveModel
open OperatorPOVMTransport AdaptiveCollectiveEmbedding

variable {ι H Ω : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace H] [MeasurableSpace Ω]

/-- A measurable classical-history choice of actual operator-valued POVMs.
Only measurable-event matrix entries are required to depend measurably on
history. No RN density, Fisher quantity or learning conclusion is a field. -/
structure OperatorStep (ι H Ω : Type*) [Fintype ι] [DecidableEq ι]
    [MeasurableSpace H] [MeasurableSpace Ω] where
  measurement : H → OperatorPOVM ι Ω
  entry_measurable : ∀ S, MeasurableSet S → ∀ i j,
    Measurable (fun h => (measurement h).operator S i j)

namespace OperatorStep
variable (M : OperatorStep ι H Ω)

/-- The actual measurable-event Born trace of the chosen operator POVM. -/
def eventBorn (ρ : Density ι) (h : H) (S : Set Ω) : ℝ :=
  (Matrix.trace (ρ.matrix * (M.measurement h).operator S)).re

theorem eventBorn_measurable (ρ : Density ι) (S : Set Ω) (hS : MeasurableSet S) :
    Measurable (fun h => M.eventBorn ρ h S) := by
  change Measurable (fun h => (∑ i, ∑ j,
    ρ.matrix i j * (M.measurement h).operator S j i).re)
  exact (Finset.measurable_sum Finset.univ fun i _ =>
    Finset.measurable_sum Finset.univ fun j _ =>
      (M.entry_measurable S hS j i).const_mul (ρ.matrix i j)).re

def bornKernel (R : OperatorRadonNikodymInput ι Ω) (ρ : Density ι) : Kernel H Ω where
  toFun h := operatorOutcomeMeasure R (M.measurement h) ρ
  measurable' := Measure.measurable_measure.mpr fun S hS => by
    simp_rw [operatorOutcomeMeasure_apply R _ ρ S hS]
    exact (M.eventBorn_measurable ρ S hS).ennreal_ofReal

instance bornKernel_isMarkovKernel (R : OperatorRadonNikodymInput ι Ω) (ρ : Density ι) :
    IsMarkovKernel (M.bornKernel R ρ) :=
  ⟨fun h => operatorOutcomeMeasure_probability R (M.measurement h) ρ⟩

theorem bornKernel_apply (R : OperatorRadonNikodymInput ι Ω) (ρ : Density ι)
    (h : H) (S : Set Ω) (hS : MeasurableSet S) :
    M.bornKernel R ρ h S = ENNReal.ofReal (M.eventBorn ρ h S) :=
  operatorOutcomeMeasure_apply R (M.measurement h) ρ S hS

theorem bornKernel_choice_independent (R R' : OperatorRadonNikodymInput ι Ω)
    (ρ : Density ι) : M.bornKernel R ρ = M.bornKernel R' ρ := by
  apply Kernel.ext
  intro h
  exact operatorOutcomeMeasure_choice_independent R R' (M.measurement h) ρ

section Nonempty
variable [Nonempty ι]

theorem uniform_eventBorn (h : H) (S : Set Ω) :
    M.eventBorn (uniformState ι) h S =
      (Fintype.card ι : ℝ)⁻¹ * (Matrix.trace ((M.measurement h).operator S)).re := by
  simp [eventBorn, uniformState, Matrix.trace_smul, Complex.real_smul]

/-- Every input-state transition law is absolutely continuous with respect
to the parameter-free uniform-state transition, without any outcome
countability or jointly measurable RN choice. -/
theorem bornKernel_absolutelyContinuous_uniform (R : OperatorRadonNikodymInput ι Ω)
    (ρ : Density ι) (h : H) :
    M.bornKernel R ρ h ≪ M.bornKernel R (uniformState ι) h := by
  apply Measure.AbsolutelyContinuous.mk
  intro S hS hz
  rw [M.bornKernel_apply R _ h S hS] at hz ⊢
  have hp := (M.measurement h).positive S hS
  have hn : 0 ≤ M.eventBorn (uniformState ι) h S :=
    event_trace_nonneg (M.measurement h) _ S hS
  have hb : M.eventBorn (uniformState ι) h S = 0 :=
    le_antisymm (ENNReal.ofReal_eq_zero.mp hz) hn
  rw [M.uniform_eventBorn] at hb
  have hd : (Fintype.card ι : ℝ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have ht : (Matrix.trace ((M.measurement h).operator S)).re = 0 :=
    (mul_eq_zero.mp hb).resolve_left hd
  have hztrace : Matrix.trace ((M.measurement h).operator S) = 0 := by
    apply Complex.ext
    · exact ht
    · exact (RCLike.nonneg_iff.mp hp.trace_nonneg).2
  have he := hp.trace_eq_zero_iff.mp hztrace
  simp [eventBorn, he]

end Nonempty
end OperatorStep

universe v

/-- A raw measurable adaptive protocol. Its measurements are genuine
operator-valued POVMs; no family of outcome densities is included. -/
structure OperatorLearner (ι : Type*) (Seed Ω : Type v) [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Seed] [MeasurableSpace Ω] (n : ℕ) where
  seed : Measure Seed
  seed_probability : IsProbabilityMeasure seed
  step : ∀ k : Fin n, OperatorStep ι (History Seed Ω k.val) Ω
  estimator : Estimator ι (History Seed Ω n)

namespace OperatorLearner
universe u
variable {Seed Ω : Type u} [MeasurableSpace Seed] [MeasurableSpace Ω] {n : ℕ}
  (A : OperatorLearner ι Seed Ω n) (R : OperatorRadonNikodymInput ι Ω)

include R

/-- Actual nested Born probability laws, defined before any family RN choice. -/
def prefixLaw (ρ : Density ι) : (k : ℕ) → k ≤ n → Measure (History Seed Ω k)
  | 0, _ => A.seed
  | k + 1, hk => (prefixLaw ρ k (Nat.le_trans (Nat.le_succ k) hk)).compProd
      ((A.step ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩).bornKernel R ρ)

instance prefixLaw_probability (ρ : Density ι) (k : ℕ) (hk : k ≤ n) :
    IsProbabilityMeasure (A.prefixLaw R ρ k hk) := by
  induction k with
  | zero => exact A.seed_probability
  | succ k ih =>
      change IsProbabilityMeasure ((A.prefixLaw R ρ k
        (Nat.le_trans (Nat.le_succ k) hk)).compProd _)
      letI := ih (Nat.le_trans (Nat.le_succ k) hk)
      infer_instance

variable [Nonempty ι]

/-- The fixed uniform-state history measure dominates every actual input's
prefix law. This induction uses only actual operator Born kernels and native
absolute continuity of measure/kernel composition. -/
theorem prefixLaw_absolutelyContinuous_uniform (ρ : Density ι) (k : ℕ) (hk : k ≤ n) :
    A.prefixLaw R ρ k hk ≪ A.prefixLaw R (uniformState ι) k hk := by
  induction k with
  | zero => exact Measure.AbsolutelyContinuous.rfl
  | succ k ih =>
      change (A.prefixLaw R ρ k (Nat.le_trans (Nat.le_succ k) hk)).compProd _ ≪
        (A.prefixLaw R (uniformState ι) k (Nat.le_trans (Nat.le_succ k) hk)).compProd _
      apply ((ih _).compProd_left _).trans
      exact Measure.AbsolutelyContinuous.compProd_right
        (Filter.Eventually.of_forall fun h =>
          (A.step ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩).bornKernel_absolutelyContinuous_uniform R ρ h)

end OperatorLearner

section PositiveProbes
open FinitePolarization
variable [Nonempty ι] (M : OperatorStep ι H Ω) (R : OperatorRadonNikodymInput ι Ω)

/-- The zero probe has mass0, so its arbitrary normalized state is immaterial. -/
def probeState (v : ι → ℂ) : Density ι :=
  if hv : 0 < normSq v then vectorDensity v hv else uniformState ι

/-- Actual positive quadratic-form kernel, built from an ordinary pure-state
Born kernel and its true vector mass. It requires no family RN derivative. -/
def quadraticKernel (v : ι → ℂ) : Kernel H Ω where
  toFun h := ENNReal.ofReal (normSq v) • M.bornKernel R (probeState v) h
  measurable' := Measure.measurable_measure.mpr fun _S hS =>
    measurable_const.mul ((M.bornKernel R (probeState v)).measurable_coe hS)

instance quadraticKernel_finite (v : ι → ℂ) : IsFiniteKernel (quadraticKernel M R v) where
  exists_univ_le := ⟨ENNReal.ofReal (normSq v), ENNReal.ofReal_lt_top, fun h => by
    change (ENNReal.ofReal (normSq v) • M.bornKernel R (probeState v) h) univ ≤ _
    simp⟩

theorem quadraticKernel_event (v : ι → ℂ) (h : H) (S : Set Ω) (hS : MeasurableSet S) :
    quadraticKernel M R v h S = ENNReal.ofReal (quadratic ((M.measurement h).operator S) v) := by
  classical
  change (ENNReal.ofReal (normSq v) • M.bornKernel R (probeState v) h) S = _
  rw [Measure.smul_apply, smul_eq_mul, M.bornKernel_apply R _ h S hS]
  by_cases hv : 0 < normSq v
  · rw [probeState, dif_pos hv, ← ENNReal.ofReal_mul (normSq_nonneg v)]
    congr 1
    exact (quadratic_eq_mass_born _ v hv).symm
  · have hz : normSq v = 0 := le_antisymm (le_of_not_gt hv) (normSq_nonneg v)
    rw [hz, ENNReal.ofReal_zero, zero_mul, quadratic_eq_zero_of_normSq_zero _ v hz,
      ENNReal.ofReal_zero]

include R

/-- Finite positive polarization proves the previously needed joint-event
section measurability on arbitrary outcome sigma-algebras. -/
theorem measurable_operator_section (S : Set (H × Ω)) (hS : MeasurableSet S) (i j : ι) :
    Measurable (fun h => (M.measurement h).operator (Prod.mk h ⁻¹' S) i j) := by
  have hq (v : ι → ℂ) : Measurable (fun h => quadratic
      ((M.measurement h).operator (Prod.mk h ⁻¹' S)) v) := by
    have hm : Measurable (fun h => quadraticKernel M R v h (Prod.mk h ⁻¹' S)) :=
      Kernel.measurable_kernel_prodMk_left hS
    have he : (fun h => quadratic ((M.measurement h).operator (Prod.mk h ⁻¹' S)) v) =
        fun h => (quadraticKernel M R v h (Prod.mk h ⁻¹' S)).toReal := by
      funext h
      rw [quadraticKernel_event M R v h _ (hS.preimage measurable_prodMk_left),
        ENNReal.toReal_ofReal (quadratic_nonneg
          ((M.measurement h).positive _ (hS.preimage measurable_prodMk_left)) v)]
    rw [he]
    exact hm.ennreal_toReal
  have hreal := ((hq (Pi.single i 1 + Pi.single j 1)).sub
    (hq (Pi.single i 1 - Pi.single j 1))).div_const 4
  have himag := ((hq (Pi.single i 1 + Pi.single j Complex.I)).sub
    (hq (Pi.single i 1 - Pi.single j Complex.I))).div_const 4
  have hc := (Complex.continuous_ofReal.measurable.comp hreal).sub
    ((Complex.continuous_ofReal.measurable.comp himag).const_mul Complex.I)
  convert hc using 1
  funext h
  exact polarization _ ((M.measurement h).positive _
    (hS.preimage measurable_prodMk_left)).isHermitian i j

end PositiveProbes

section JointAverage
variable [Nonempty ι] (M : OperatorStep ι H Ω)
  (R : OperatorRadonNikodymInput ι Ω)
include R

/-- A normalized operator event has every entry bounded by the ambient
dimension. This follows from its actual uniform-state Born probability. -/
theorem operator_entry_bound (h : H) (S : Set Ω) (hS : MeasurableSet S) (i j : ι) :
    ‖(M.measurement h).operator S i j‖ ≤ (Fintype.card ι : ℝ) := by
  have hp := (M.measurement h).positive S hS
  have hb : M.bornKernel R (uniformState ι) h S ≤ 1 := by
    calc
      _ ≤ M.bornKernel R (uniformState ι) h univ := measure_mono (subset_univ _)
      _ = 1 := measure_univ
  rw [M.bornKernel_apply R _ h S hS] at hb
  have hn : 0 ≤ M.eventBorn (uniformState ι) h S :=
    event_trace_nonneg (M.measurement h) (uniformState ι) S hS
  have hbR := ENNReal.toReal_mono ENNReal.one_ne_top hb
  rw [ENNReal.toReal_one, ENNReal.toReal_ofReal hn] at hbR
  change M.eventBorn (uniformState ι) h S ≤ 1 at hbR
  have ht : (Matrix.trace ((M.measurement h).operator S)).re =
      (Fintype.card ι : ℝ) * M.eventBorn (uniformState ι) h S := by
    rw [M.uniform_eventBorn]
    field_simp
  exact (psd_entry_norm_le_trace _ hp i j).trans
    (ht ▸ by simpa using mul_le_mul_of_nonneg_left hbR (Nat.cast_nonneg (Fintype.card ι)))

omit [Nonempty ι] in
/-- Finite additivity on actual operator events, obtained from the ordinary
fixed-POVM RN representation. No jointly measurable family is selected. -/
theorem operator_finset_union (h : H) (t : Finset ℕ) (S : ℕ → Set Ω)
    (hS : ∀ k, MeasurableSet (S k)) (hd : Pairwise (fun k l => Disjoint (S k) (S l)))
    (i j : ι) :
    (M.measurement h).operator (⋃ k ∈ t, S k) i j =
      ∑ k ∈ t, (M.measurement h).operator (S k) i j := by
  let N := chosenPOVM R (M.measurement h)
  have hN := chosenPOVM_represents R (M.measurement h)
  calc
    _ = ∫ y in ⋃ k ∈ t, S k, N.effect y i j ∂N.reference :=
      hN _ (MeasurableSet.biUnion (Finset.countable_toSet t) (fun k _ => hS k)) i j
    _ = ∑ k ∈ t, ∫ y in S k, N.effect y i j ∂N.reference :=
      integral_biUnion_finset t (fun k _ => hS k)
        (fun k _ l _ hkl => hd hkl) (fun k _ => (N.entry_integrable i j).integrableOn)
    _ = _ := Finset.sum_congr rfl fun k _ => (hN (S k) (hS k) i j).symm

variable (μ : Measure H) [IsProbabilityMeasure μ]
  (hsection : ∀ S : Set (H × Ω), MeasurableSet S → ∀ i j,
    Measurable (fun h => (M.measurement h).operator (Prod.mk h ⁻¹' S) i j))

/-- This section-measurability premise is discharged below by finite positive
polarization kernels; the average itself is the literal matrix integral. -/
def jointOperator (S : Set (H × Ω)) : Matrix ι ι ℂ :=
  fun i j => ∫ h, (M.measurement h).operator (Prod.mk h ⁻¹' S) i j ∂μ

include R hsection

theorem joint_entry_integrable (S : Set (H × Ω)) (hS : MeasurableSet S) (i j : ι) :
    Integrable (fun h => (M.measurement h).operator (Prod.mk h ⁻¹' S) i j) μ := by
  apply (integrable_const (Fintype.card ι : ℝ)).mono' (hsection S hS i j).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun h => operator_entry_bound M R h _
    (hS.preimage measurable_prodMk_left) i j

theorem jointOperator_positive (S : Set (H × Ω)) (hS : MeasurableSet S) :
    (jointOperator M μ S).PosSemidef := by
  letI : NormedAddCommGroup (Matrix ι ι ℂ) :=
    inferInstanceAs (NormedAddCommGroup (ι → ι → ℂ))
  letI : NormedSpace ℝ (Matrix ι ι ℂ) :=
    inferInstanceAs (NormedSpace ℝ (ι → ι → ℂ))
  have hi : Integrable (fun h => ((M.measurement h).operator (Prod.mk h ⁻¹' S) : ι → ι → ℂ)) μ :=
    Integrable.of_eval fun i => Integrable.of_eval fun j => joint_entry_integrable M R μ hsection S hS i j
  have hc : Convex ℝ {E : Matrix ι ι ℂ | E.PosSemidef} := by
    intro E hE F hF a b ha hb _
    exact (hE.smul ha).add (hF.smul hb)
  have hp := hc.integral_mem (isClosed_setOf_posSemidef (ι := ι))
    (Filter.Eventually.of_forall fun h => (M.measurement h).positive _
      (hS.preimage measurable_prodMk_left)) hi
  have he : (∫ h, (M.measurement h).operator (Prod.mk h ⁻¹' S) ∂μ) = jointOperator M μ S := by
    funext i j
    rw [eval_integral (fun i => hi.eval i), eval_integral (fun j => (hi.eval i).eval j)]
    rfl
  rwa [he] at hp

theorem jointOperator_countable_additivity
    (S : ℕ → Set (H × Ω)) (hS : ∀ k, MeasurableSet (S k))
    (hd : Pairwise (fun k l => Disjoint (S k) (S l))) (i j : ι) :
    HasSum (fun k => jointOperator M μ (S k) i j) (jointOperator M μ (⋃ k, S k) i j) := by
  classical
  have hint (k : ℕ) := joint_entry_integrable M R μ hsection (S k) (hS k) i j
  have hp (h : H) := (M.measurement h).countable_additivity
    (fun k => Prod.mk h ⁻¹' S k) (fun k => (hS k).preimage measurable_prodMk_left)
    (fun _ _ hkl => (hd hkl).preimage _) i j
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (l := Filter.atTop) (fun _h : H => (Fintype.card ι : ℝ))
    (Filter.Eventually.of_forall fun t : Finset ℕ =>
      (Finset.aestronglyMeasurable_fun_sum t fun k _ => (hint k).aestronglyMeasurable))
    (Filter.Eventually.of_forall fun t : Finset ℕ => Filter.Eventually.of_forall fun h => by
      rw [← operator_finset_union M R h t (fun k => Prod.mk h ⁻¹' S k)
        (fun k => (hS k).preimage measurable_prodMk_left) (fun _ _ hkl => (hd hkl).preimage _) i j]
      exact operator_entry_bound M R h _
        (MeasurableSet.biUnion (Finset.countable_toSet t) (fun k _ =>
          (hS k).preimage measurable_prodMk_left)) i j)
    (integrable_const _) (Filter.Eventually.of_forall fun h => by
      simpa only [Set.preimage_iUnion] using hp h)
  change Filter.Tendsto (fun t : Finset ℕ => ∑ k ∈ t, jointOperator M μ (S k) i j)
    Filter.atTop (nhds (jointOperator M μ (⋃ k, S k) i j))
  simpa only [jointOperator, Set.preimage_iUnion, integral_finset_sum _ (fun k _ => hint k)] using hlim

/-- The joint matrix-valued measure is truly constructed, including native
positivity, normalization and countable additivity. Only its section
measurability remains the named intermediate argument. -/
def jointPOVM : OperatorPOVM ι (H × Ω) where
  operator := jointOperator M μ
  empty := by
    funext i j
    simp [jointOperator, (M.measurement _).empty]
  positive := jointOperator_positive M R μ hsection
  total := by
    funext i j
    simp [jointOperator, (M.measurement _).total]
  countable_additivity := jointOperator_countable_additivity M R μ hsection

theorem joint_complexBorn_integrable (ρ : Density ι) (S : Set (H × Ω)) (hS : MeasurableSet S) :
    Integrable (fun h => Matrix.trace (ρ.matrix *
      (M.measurement h).operator (Prod.mk h ⁻¹' S))) μ := by
  change Integrable (fun h => ∑ i : ι, ∑ j : ι,
    ρ.matrix i j * (M.measurement h).operator (Prod.mk h ⁻¹' S) j i) μ
  exact integrable_finset_sum Finset.univ fun i _ =>
    integrable_finset_sum Finset.univ fun j _ =>
      (joint_entry_integrable M R μ hsection S hS j i).const_mul (ρ.matrix i j)

/-- The Born trace commutes with the literal joint operator average. -/
theorem joint_complexBorn_integral (ρ : Density ι) (S : Set (H × Ω)) (hS : MeasurableSet S) :
    (∫ h, Matrix.trace (ρ.matrix * (M.measurement h).operator (Prod.mk h ⁻¹' S)) ∂μ) =
      Matrix.trace (ρ.matrix * jointOperator M μ S) := by
  change (∫ h, ∑ i : ι, ∑ j : ι,
    ρ.matrix i j * (M.measurement h).operator (Prod.mk h ⁻¹' S) j i ∂μ) = _
  rw [integral_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ =>
      (joint_entry_integrable M R μ hsection S hS j i).const_mul (ρ.matrix i j)))]
  simp_rw [integral_finset_sum Finset.univ (fun j _ =>
    (joint_entry_integrable M R μ hsection S hS j _).const_mul (ρ.matrix _ j)), integral_const_mul]
  rfl

/-- Every input state's genuine joint Born history/outcome measure is
represented by the single constructed joint operator POVM. -/
theorem joint_bornLaw_event (ρ : Density ι) (S : Set (H × Ω)) (hS : MeasurableSet S) :
    μ.compProd (M.bornKernel R ρ) S =
      ENNReal.ofReal (Matrix.trace (ρ.matrix * (jointPOVM M R μ hsection).operator S)).re := by
  rw [Measure.compProd_apply hS]
  simp_rw [M.bornKernel_apply R ρ _ _ (hS.preimage measurable_prodMk_left)]
  have hi := joint_complexBorn_integrable M R μ hsection ρ S hS
  have hn : ∀ h, 0 ≤ (Matrix.trace
      (ρ.matrix * (M.measurement h).operator (Prod.mk h ⁻¹' S))).re := fun h =>
    event_trace_nonneg (M.measurement h) ρ _ (hS.preimage measurable_prodMk_left)
  simp only [OperatorStep.eventBorn]
  have hie := ofReal_integral_eq_lintegral_ofReal hi.re (Filter.Eventually.of_forall hn)
  simp only [RCLike.re_eq_complex_re] at hie
  rw [← hie]
  congr 1
  have he := integral_re hi
  simp only [RCLike.re_eq_complex_re] at he
  exact he.trans (congrArg Complex.re (joint_complexBorn_integral M R μ hsection ρ S hS))

/-- Ordinary fixed-space operator RN is now applicable to the joint POVM.
No conditional or parameterized family RN theorem occurs here. -/
theorem chosen_joint_outcomeMeasure
    (RJ : OperatorRadonNikodymInput ι (H × Ω)) (ρ : Density ι) :
    (chosenPOVM RJ (jointPOVM M R μ hsection)).outcomeMeasure ρ =
      μ.compProd (M.bornKernel R ρ) := by
  apply Measure.ext
  intro S hS
  rw [outcomeMeasure_event_trace _ _ (chosenPOVM_represents RJ _) ρ S hS,
    joint_bornLaw_event M R μ hsection ρ S hS]

/-- The chosen joint RN reference is exactly dimension times the joint
uniform-state Born probability. This identifies the desired conditional
probability reference without a kernel RN derivative. -/
theorem chosen_joint_reference
    (RJ : OperatorRadonNikodymInput ι (H × Ω)) :
    (chosenPOVM RJ (jointPOVM M R μ hsection)).reference =
      (Fintype.card ι : ℝ≥0∞) • (μ.compProd (M.bornKernel R (uniformState ι))) := by
  apply Measure.ext
  intro S hS
  rw [chosenPOVM_reference _ _ S hS, Measure.smul_apply,
    joint_bornLaw_event M R μ hsection (uniformState ι) S hS]
  have hd : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  change ENNReal.ofReal (Matrix.trace ((jointPOVM M R μ hsection).operator S)).re = _
  rw [show (Matrix.trace ((uniformState ι).matrix * (jointPOVM M R μ hsection).operator S)).re =
      (Fintype.card ι : ℝ)⁻¹ * (Matrix.trace ((jointPOVM M R μ hsection).operator S)).re by
    simp [uniformState, Matrix.trace_smul, Complex.real_smul]]
  rw [smul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg (Fintype.card ι))]
  congr 1
  field_simp

/-- The joint RN matrix density relative to the probability reference
μ.compProd(uniform Born), rather than the dimension-mass trace reference. -/
def jointDensity (RJ : OperatorRadonNikodymInput ι (H × Ω)) (z : H × Ω) : Matrix ι ι ℂ :=
  (Fintype.card ι : ℝ) • (chosenPOVM RJ (jointPOVM M R μ hsection)).effect z

theorem jointDensity_entry_measurable (RJ : OperatorRadonNikodymInput ι (H × Ω)) (i j : ι) :
    Measurable (fun z => jointDensity M R μ hsection RJ z i j) := by
  change Measurable (fun z => (Fintype.card ι : ℝ) •
    (chosenPOVM RJ (jointPOVM M R μ hsection)).effect z i j)
  exact ((chosenPOVM RJ (jointPOVM M R μ hsection)).entry_measurable i j).const_smul
    (Fintype.card ι : ℝ)

theorem jointDensity_entry_integrable (RJ : OperatorRadonNikodymInput ι (H × Ω)) (i j : ι) :
    Integrable (fun z => jointDensity M R μ hsection RJ z i j)
      (μ.compProd (M.bornKernel R (uniformState ι))) := by
  have hi := (chosenPOVM RJ (jointPOVM M R μ hsection)).entry_integrable i j
  rw [chosen_joint_reference M R μ hsection RJ] at hi
  have hc : (Fintype.card ι : ℝ≥0∞) ≠ 0 := by simp
  have hn := (integrable_smul_measure hc (ENNReal.natCast_ne_top _)).mp hi
  exact hn.fun_smul (Fintype.card ι : ℝ)

theorem jointDensity_positive (RJ : OperatorRadonNikodymInput ι (H × Ω)) :
    ∀ᵐ z ∂μ.compProd (M.bornKernel R (uniformState ι)),
      (jointDensity M R μ hsection RJ z).PosSemidef := by
  have hp := (chosenPOVM RJ (jointPOVM M R μ hsection)).positive_ae
  rw [chosen_joint_reference M R μ hsection RJ] at hp
  have hc : (Fintype.card ι : ℝ≥0∞) ≠ 0 := by simp
  exact ((Measure.ae_smul_measure_iff hc).mp hp).mono fun z hz => hz.smul (Nat.cast_nonneg _)

/-- Actual joint operator representation under the probability reference. -/
theorem jointDensity_represents (RJ : OperatorRadonNikodymInput ι (H × Ω))
    (S : Set (H × Ω)) (hS : MeasurableSet S) (i j : ι) :
    (jointPOVM M R μ hsection).operator S i j =
      ∫ z in S, jointDensity M R μ hsection RJ z i j
        ∂μ.compProd (M.bornKernel R (uniformState ι)) := by
  have he := chosenPOVM_represents RJ (jointPOVM M R μ hsection) S hS i j
  rw [chosen_joint_reference M R μ hsection RJ, Measure.restrict_smul,
    integral_smul_measure] at he
  simpa only [jointDensity, Pi.smul_apply, Matrix.smul_apply, integral_smul,
    ENNReal.toReal_natCast] using he

omit [Nonempty ι] R [IsProbabilityMeasure μ] hsection in
/-- The actual history rectangle effect is its history probability timesI. -/
theorem jointOperator_rectangle (S : Set H) (hS : MeasurableSet S) (i j : ι) :
    jointOperator M μ (S ×ˢ (univ : Set Ω)) i j = μ.real S • (1 : Matrix ι ι ℂ) i j := by
  have he : (fun h => (M.measurement h).operator (Prod.mk h ⁻¹' (S ×ˢ (univ : Set Ω))) i j) =
      S.indicator (fun _ => (1 : Matrix ι ι ℂ) i j) := by
    funext h
    by_cases hh : h ∈ S
    · have hs : Prod.mk h ⁻¹' (S ×ˢ (univ : Set Ω)) = univ := by ext y; simp [hh]
      simp [hs, hh, (M.measurement h).total]
    · have hs : Prod.mk h ⁻¹' (S ×ˢ (univ : Set Ω)) = ∅ := by ext y; simp [hh]
      simp [hs, hh, (M.measurement h).empty]
  unfold jointOperator
  rw [he, integral_indicator_const _ hS]

/-- The fixed joint RN density has the precise rectangle normalization
needed for the common-a.e. conditional POVM repair. -/
theorem jointDensity_rectangle (RJ : OperatorRadonNikodymInput ι (H × Ω))
    (S : Set H) (hS : MeasurableSet S) (i j : ι) :
    (∫ h in S, ∫ y, jointDensity M R μ hsection RJ (h, y) i j
      ∂M.bornKernel R (uniformState ι) h ∂μ) = μ.real S • (1 : Matrix ι ι ℂ) i j := by
  have hi := jointDensity_entry_integrable M R μ hsection RJ i j
  have he := jointDensity_represents M R μ hsection RJ (S ×ˢ (univ : Set Ω)) (hS.prod MeasurableSet.univ) i j
  rw [Measure.setIntegral_compProd hS MeasurableSet.univ hi.integrableOn] at he
  simp only [Measure.restrict_univ] at he
  exact he.symm.trans (jointOperator_rectangle M μ S hS i j)

theorem jointDensity_born_measurable (RJ : OperatorRadonNikodymInput ι (H × Ω)) (ρ : Density ι) :
    Measurable (fun z => ENNReal.ofReal
      (Matrix.trace (ρ.matrix * jointDensity M R μ hsection RJ z)).re) := by
  change Measurable (fun z => ENNReal.ofReal
    (∑ i : ι, ∑ j : ι, ρ.matrix i j * jointDensity M R μ hsection RJ z j i).re)
  exact (Finset.measurable_sum Finset.univ fun i _ =>
    Finset.measurable_sum Finset.univ fun j _ =>
      (jointDensity_entry_measurable M R μ hsection RJ j i).const_mul (ρ.matrix i j)).re.ennreal_ofReal

/-- The fixed joint RN density represents every original input's joint law,
with no condition on individual history-wise RN representatives. -/
theorem jointDensity_bornLaw (RJ : OperatorRadonNikodymInput ι (H × Ω)) (ρ : Density ι) :
    μ.compProd (M.bornKernel R ρ) =
      (μ.compProd (M.bornKernel R (uniformState ι))).withDensity
        (fun z => ENNReal.ofReal (Matrix.trace (ρ.matrix * jointDensity M R μ hsection RJ z)).re) := by
  rw [← chosen_joint_outcomeMeasure M R μ hsection RJ ρ]
  change (chosenPOVM RJ (jointPOVM M R μ hsection)).reference.withDensity
    (fun z => ENNReal.ofReal ((chosenPOVM RJ (jointPOVM M R μ hsection)).born ρ z)) = _
  rw [chosen_joint_reference M R μ hsection RJ, withDensity_smul_measure,
    ← withDensity_smul' _ _ (ENNReal.natCast_ne_top _)]
  apply withDensity_congr_ae
  filter_upwards [] with z
  simp only [Pi.smul_apply, smul_eq_mul, jointDensity, DominatedPOVM.born,
    DominatedPOVM.complexBorn, Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg (Fintype.card ι))]

end JointAverage

section Repair
variable (μ : Measure H) [IsProbabilityMeasure μ]
  (β : Kernel H Ω) [IsMarkovKernel β]
  (F : H × Ω → Matrix ι ι ℂ)
  (hF : ∀ i j, Measurable (fun z => F z i j))
  (hI : ∀ i j, Integrable (fun z => F z i j) (μ.compProd β))

include hI

omit [Fintype ι] [DecidableEq ι] in
/-- Kernel Fubini gives conditional entry integrability on a common a.e.
set; only finitely many entries will be intersected below. -/
theorem conditional_entry_integrable (i j : ι) :
    ∀ᵐ h ∂μ, Integrable (fun y => F (h, y) i j) (β h) :=
  (Measure.integrable_compProd_iff (hI i j).aestronglyMeasurable).mp (hI i j) |>.1

include hF

omit [Fintype ι] in
/-- Rectangle identities suffice to recover totalI a.e. in history. This
uses equality of integrals on all history events, not equality of kernels on
all outcome events at every history. -/
theorem conditional_total
    (hrect : ∀ S, MeasurableSet S → ∀ i j,
      (∫ h in S, ∫ y, F (h, y) i j ∂β h ∂μ) = μ.real S • (1 : Matrix ι ι ℂ) i j)
    (i j : ι) :
    ∀ᵐ h ∂μ, (∫ y, F (h, y) i j ∂β h) = (1 : Matrix ι ι ℂ) i j := by
  have hint : Integrable (fun h => ∫ y, F (h, y) i j ∂β h) μ := by
    have hnorm := (Measure.integrable_compProd_iff
      (hI i j).aestronglyMeasurable).mp (hI i j) |>.2
    apply hnorm.mono'
      ((hF i j).stronglyMeasurable.integral_kernel_prod_right' (κ := β)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun h => norm_integral_le_integral_norm _
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ hint (integrable_const _)
  intro S hS _
  simpa only [integral_const, measureReal_def, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter] using hrect S hS i j

/-- Conditional POVM conditions on one common full-history-measure set. -/
theorem conditional_good
    (hpos : ∀ᵐ z ∂μ.compProd β, (F z).PosSemidef)
    (hrect : ∀ S, MeasurableSet S → ∀ i j,
      (∫ h in S, ∫ y, F (h, y) i j ∂β h ∂μ) = μ.real S • (1 : Matrix ι ι ℂ) i j) :
    ∀ᵐ h ∂μ, (∀ᵐ y ∂β h, (F (h, y)).PosSemidef) ∧
      ∀ i j, Integrable (fun y => F (h, y) i j) (β h) ∧
        (∫ y, F (h, y) i j ∂β h) = (1 : Matrix ι ι ℂ) i j := by
  have hentry : ∀ᵐ h ∂μ, ∀ i j,
      Integrable (fun y => F (h, y) i j) (β h) ∧
        (∫ y, F (h, y) i j ∂β h) = (1 : Matrix ι ι ℂ) i j := by
    simp only [ae_all_iff]
    intro i j
    exact (conditional_entry_integrable μ β F hI i j).and
      (conditional_total μ β F hF hI hrect i j)
  exact (Measure.ae_ae_of_ae_compProd hpos).and hentry

/-- An a.e. conditional POVM can be repaired to a genuine all-history step
without choosing any history-dependent RN representative. The bad histories
use the identity effect against the probability reference kernel. -/
theorem exists_repairedStep
    (hpos : ∀ᵐ z ∂μ.compProd β, (F z).PosSemidef)
    (hrect : ∀ S, MeasurableSet S → ∀ i j,
      (∫ h in S, ∫ y, F (h, y) i j ∂β h ∂μ) = μ.real S • (1 : Matrix ι ι ℂ) i j) :
    ∃ M : OneCopyStep ι H Ω, M.reference = β ∧
      ∀ᵐ h ∂μ, ∀ y, M.effect h y = F (h, y) := by
  classical
  obtain ⟨S, hSae, hS, hgood⟩ := (conditional_good μ β F hF hI hpos hrect).exists_measurable_mem
  let M : OneCopyStep ι H Ω := {
    reference := β
    reference_sfinite := inferInstance
    effect h y := if h ∈ S then F (h, y) else 1
    entry_measurable i j := by
      have he : (fun z : H × Ω => (if z.1 ∈ S then F (z.1, z.2) else 1) i j) =
          fun z => if z.1 ∈ S then F z i j else (1 : Matrix ι ι ℂ) i j := by
        funext z
        split_ifs <;> rfl
      rw [he]
      exact Measurable.ite (hS.preimage measurable_fst) (hF i j) measurable_const
    positive_ae h := by
      by_cases hs : h ∈ S
      · simpa only [if_pos hs] using (hgood h hs).1
      · exact Filter.Eventually.of_forall fun y => by simpa only [if_neg hs] using Matrix.PosSemidef.one
    entry_integrable h i j := by
      by_cases hs : h ∈ S
      · simpa only [if_pos hs] using ((hgood h hs).2 i j).1
      · simpa only [if_neg hs] using (integrable_const ((1 : Matrix ι ι ℂ) i j) :
          Integrable (fun _ : Ω => (1 : Matrix ι ι ℂ) i j) (β h))
    total h i j := by
      by_cases hs : h ∈ S
      · simpa only [if_pos hs] using ((hgood h hs).2 i j).2
      · simp [hs] }
  refine ⟨M, rfl, ?_⟩
  filter_upwards [hSae] with h hh y
  change (if h ∈ S then F (h, y) else 1) = F (h, y)
  exact if_pos hh

end Repair
section Lawwise
variable (μ : Measure H) [IsProbabilityMeasure μ]
  (β κ : Kernel H Ω) [IsMarkovKernel β] [IsMarkovKernel κ]

/-- A fixed-history-measure joint density identity persists after *any*
absolutely continuous change of history law. This is a scalar fixed-measure
RN argument and does not assert equality of conditional kernels at all
histories or require any countability assumption on the outcome space. -/
theorem compProd_density_change_history
    (f : H × Ω → ℝ≥0∞) (hf : Measurable f)
    (hj : μ.compProd κ = (μ.compProd β).withDensity f)
    (η : Measure H) [IsFiniteMeasure η] (hη : η ≪ μ) :
    η.compProd κ = (η.compProd β).withDensity f := by
  let w : H → ℝ≥0∞ := fun h => ENNReal.ofReal ((η.rnDeriv μ h).toReal)
  have hw : Measurable w := (Measure.measurable_rnDeriv η μ).ennreal_toReal.ennreal_ofReal
  have hfin : ∀ h, w h ≠ ∞ := fun _ => ENNReal.ofReal_ne_top
  have hwith : μ.withDensity w = η := by
    rw [← Measure.withDensity_rnDeriv_eq η μ hη]
    apply withDensity_congr_ae
    filter_upwards [Measure.rnDeriv_ne_top η μ] with h hh
    exact ENNReal.ofReal_toReal hh
  have hwf : Measurable (fun z : H × Ω => w z.1) := hw.comp measurable_fst
  calc
    η.compProd κ = (μ.compProd κ).withDensity (fun z => w z.1) := by
      rw [← hwith]
      exact AdaptiveCollectiveEmbedding.compProd_withDensity_left μ κ w hw hfin
    _ = ((μ.compProd β).withDensity f).withDensity (fun z => w z.1) := by rw [hj]
    _ = ((μ.compProd β).withDensity (fun z => w z.1)).withDensity f := by
      rw [← withDensity_mul _ hf hwf, ← withDensity_mul _ hwf hf, mul_comm]
    _ = (η.compProd β).withDensity f := by
      rw [← AdaptiveCollectiveEmbedding.compProd_withDensity_left μ β w hw hfin, hwith]

omit [IsProbabilityMeasure μ] in
/-- Repairing a common null set of histories preserves the joint Born law
under every history measure absolutely continuous with respect to the fixed
one. The candidate density F remains the original joint density in the final
formula. -/
theorem repairedStep_joint_bornLaw
    (F : H × Ω → Matrix ι ι ℂ)
    (M : OneCopyStep ι H Ω) (href : M.reference = β)
    (heffect : ∀ᵐ h ∂μ, ∀ y, M.effect h y = F (h, y))
    (η : Measure H) [IsFiniteMeasure η] (hη : η ≪ μ) (ρ : Density ι) :
    η.compProd (M.bornKernel ρ) = (η.compProd β).withDensity
      (fun z => ENNReal.ofReal (Matrix.trace (ρ.matrix * F z)).re) := by
  have he : ∀ᵐ z ∂η.compProd β, M.effect z.1 z.2 = F z := by
    have hmp : MeasurePreserving Prod.fst (η.compProd β) η :=
      ⟨measurable_fst, Measure.fst_compProd η β⟩
    filter_upwards [hmp.quasiMeasurePreserving.ae (hη.ae_le heffect)] with z hz
    exact hz z.2
  have hm : Measurable (fun z : H × Ω => ENNReal.ofReal (M.born ρ z.1 z.2)) :=
    (M.born_joint_measurable ρ).ennreal_ofReal
  letI : IsSFiniteKernel (M.reference.withDensity
      (fun h y => ENNReal.ofReal (M.born ρ h y))) :=
    inferInstanceAs (IsSFiniteKernel (M.bornKernel ρ))
  calc
    η.compProd (M.bornKernel ρ) =
        (η.compProd M.reference).withDensity
          (fun z : H × Ω => ENNReal.ofReal (M.born ρ z.1 z.2)) :=
      Measure.compProd_withDensity hm
    _ = (η.compProd β).withDensity
        (fun z : H × Ω => ENNReal.ofReal (M.born ρ z.1 z.2)) := by rw [href]
    _ = _ := by
      apply withDensity_congr_ae
      filter_upwards [he] with z hz
      simp only [OneCopyStep.born, OneCopyStep.complexBorn, hz]

end Lawwise
section OneStepReduction
variable [Nonempty ι] (M : OperatorStep ι H Ω) (R : OperatorRadonNikodymInput ι Ω)
  (μ : Measure H) [IsProbabilityMeasure μ]
  (RJ : OperatorRadonNikodymInput ι (H × Ω))
include RJ

/-- Every weakly measurable operator-POVM family has a dominated step with
exactly the same joint Born laws under every history distribution dominated
by the fixed μ. This is proved from ordinary fixed-space operator RN on Ω
and H×Ω, finite polarization, Fubini and null-history repair. There is no
countability restriction and no parameterized-family RN input. -/
theorem exists_lawwise_dominated_step :
    ∃ D : OneCopyStep ι H Ω, D.reference = M.bornKernel R (uniformState ι) ∧
      ∀ (ρ : Density ι) (η : Measure H) [IsFiniteMeasure η], η ≪ μ →
        η.compProd (D.bornKernel ρ) = η.compProd (M.bornKernel R ρ) := by
  let hs := measurable_operator_section M R
  let β := M.bornKernel R (uniformState ι)
  let F := jointDensity M R μ hs RJ
  have hF := jointDensity_entry_measurable M R μ hs RJ
  have hI := jointDensity_entry_integrable M R μ hs RJ
  obtain ⟨D, href, heffect⟩ := exists_repairedStep μ β F hF hI
    (jointDensity_positive M R μ hs RJ) (jointDensity_rectangle M R μ hs RJ)
  refine ⟨D, href, ?_⟩
  intro ρ η _ hη
  calc
    η.compProd (D.bornKernel ρ) = (η.compProd β).withDensity
        (fun z => ENNReal.ofReal (Matrix.trace (ρ.matrix * F z)).re) :=
      repairedStep_joint_bornLaw μ β F D href heffect η hη ρ
    _ = η.compProd (M.bornKernel R ρ) :=
      (compProd_density_change_history μ β (M.bornKernel R ρ) _
        (jointDensity_born_measurable M R μ hs RJ ρ)
        (jointDensity_bornLaw M R μ hs RJ ρ) η hη).symm

end OneStepReduction
namespace OperatorLearner
universe u
variable {Seed Ω : Type u} [MeasurableSpace Seed] [MeasurableSpace Ω] {n : ℕ}
  (A : OperatorLearner ι Seed Ω n) (R : OperatorRadonNikodymInput ι Ω)
include R

/-- Actual full transcript of the raw measurable operator protocol. -/
def transcriptLaw (ρ : Density ι) : Measure (History Seed Ω n) :=
  A.prefixLaw R ρ n (Nat.le_refl n)

def outputLaw (ρ : Density ι) : Measure (Density ι) :=
  (A.transcriptLaw R ρ).map A.estimator.estimate

/-- The source's event in the unrestricted reconstructed-density output. -/
def successSet (loss : Density ι → Density ι → ℝ≥0∞) (ρ : Density ι)
    (ε : ℝ≥0∞) : Set (History Seed Ω n) :=
  {z | loss ρ (A.estimator.estimate z) ≤ ε}

def successProbability (loss : Density ι → Density ι → ℝ≥0∞)
    (ρ : Density ι) (ε : ℝ≥0∞) : ℝ≥0∞ :=
  A.transcriptLaw R ρ (A.successSet loss ρ ε)

def LearnsRank (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε q : ℝ≥0∞) : Prop :=
  ∀ ρ : Density ι, ρ.matrix.rank ≤ r →
    MeasurableSet (A.successSet loss ρ ε) ∧ q ≤ A.successProbability R loss ρ ε

def BuresSuccess (r : ℕ) (ε : ℝ≥0∞) : Prop := A.LearnsRank R chiB r ε ((2 : ℝ≥0∞) / 3)
def RightSuccess (r : ℕ) (ε : ℝ≥0∞) : Prop := A.LearnsRank R chiR r ε ((2 : ℝ≥0∞) / 3)

/-- RN witness choices do not alter any genuine raw protocol prefix law. -/
theorem prefixLaw_choice_independent (R' : OperatorRadonNikodymInput ι Ω)
    (ρ : Density ι) (k : ℕ) (hk : k ≤ n) :
    A.prefixLaw R ρ k hk = A.prefixLaw R' ρ k hk := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change (A.prefixLaw R ρ k (Nat.le_trans (Nat.le_succ k) hk)).compProd
        ((A.step ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩).bornKernel R ρ) = _
      rw [ih _, (A.step ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩).bornKernel_choice_independent R R']
      rfl

theorem successProbability_choice_independent (R' : OperatorRadonNikodymInput ι Ω)
    (loss : Density ι → Density ι → ℝ≥0∞) (ρ : Density ι) (ε : ℝ≥0∞) :
    A.successProbability R loss ρ ε = A.successProbability R' loss ρ ε := by
  change A.prefixLaw R ρ n (Nat.le_refl n) (A.successSet loss ρ ε) = _
  rw [A.prefixLaw_choice_independent R R' ρ n (Nat.le_refl n)]
  rfl

variable [Nonempty ι]
  (RJ : ∀ k : Fin n, OperatorRadonNikodymInput ι (History Seed Ω k.val × Ω))
include RJ

/-- Each dominating step uses the parameter-free actual uniform-state
history law at that round. All required joint-space RN inputs are ordinary
fixed-space operator RN instances, not a family RN principle. -/
def dominatedStep (k : Fin n) : OneCopyStep ι (History Seed Ω k.val) Ω :=
  Classical.choose (exists_lawwise_dominated_step (A.step k) R
    (A.prefixLaw R (uniformState ι) k.val (Nat.le_of_lt k.isLt)) (RJ k))

theorem dominatedStep_jointLaw (k : Fin n) (ρ : Density ι)
    (η : Measure (History Seed Ω k.val)) [IsFiniteMeasure η]
    (hη : η ≪ A.prefixLaw R (uniformState ι) k.val (Nat.le_of_lt k.isLt)) :
    η.compProd ((A.dominatedStep R RJ k).bornKernel ρ) =
      η.compProd ((A.step k).bornKernel R ρ) :=
  (Classical.choose_spec (exists_lawwise_dominated_step (A.step k) R
    (A.prefixLaw R (uniformState ι) k.val (Nat.le_of_lt k.isLt)) (RJ k))).2 ρ η hη

/-- The original raw protocol represented by actual jointly measurable
densities, retaining exactly its seed, histories, outcomes, estimator and copy
count. This is a construction with a proved law-equivalence theorem. -/
def toDominated : AdaptiveModel.Learner ι Seed Ω n where
  seed := A.seed
  seed_probability := A.seed_probability
  step := A.dominatedStep R RJ
  estimator := A.estimator

/-- Induction of the actual Born laws. Each step uses the proved lawwise
identity and domination of its original history law, never an unproved
history-wise equality of entire conditional kernels. -/
theorem toDominated_prefixLaw (ρ : Density ι) (k : ℕ) (hk : k ≤ n) :
    (A.toDominated R RJ).prefixLaw ρ k hk = A.prefixLaw R ρ k hk := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change ((A.toDominated R RJ).prefixLaw ρ k (Nat.le_trans (Nat.le_succ k) hk)).compProd
        ((A.dominatedStep R RJ ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩).bornKernel ρ) =
          (A.prefixLaw R ρ k (Nat.le_trans (Nat.le_succ k) hk)).compProd
            ((A.step ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩).bornKernel R ρ)
      rw [ih _]
      exact A.dominatedStep_jointLaw R RJ
        ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩ ρ
        (A.prefixLaw R ρ k (Nat.le_trans (Nat.le_succ k) hk))
        (A.prefixLaw_absolutelyContinuous_uniform R ρ k _)

theorem toDominated_transcriptLaw (ρ : Density ι) :
    (A.toDominated R RJ).transcriptLaw ρ = A.transcriptLaw R ρ :=
  A.toDominated_prefixLaw R RJ ρ n _

theorem toDominated_outputLaw (ρ : Density ι) :
    (A.toDominated R RJ).outputLaw ρ = A.outputLaw R ρ := by
  change ((A.toDominated R RJ).transcriptLaw ρ).map A.estimator.estimate = _
  rw [A.toDominated_transcriptLaw R RJ]
  rfl

theorem toDominated_successProbability
    (loss : Density ι → Density ι → ℝ≥0∞) (ρ : Density ι) (ε : ℝ≥0∞) :
    (A.toDominated R RJ).successProbability loss ρ ε = A.successProbability R loss ρ ε := by
  change (A.toDominated R RJ).transcriptLaw ρ (A.successSet loss ρ ε) = _
  rw [A.toDominated_transcriptLaw R RJ]
  rfl

theorem toDominated_learnsRank_iff (loss : Density ι → Density ι → ℝ≥0∞)
    (r : ℕ) (ε q : ℝ≥0∞) :
    (A.toDominated R RJ).LearnsRank loss r ε q ↔ A.LearnsRank R loss r ε q := by
  unfold AdaptiveModel.Learner.LearnsRank LearnsRank
  simp_rw [A.toDominated_successProbability R RJ]
  rfl

/-- Full adaptive Bures main lower bound for the raw measurable operator
model, on arbitrary finite ambient indices and arbitrary measurable outcomes.
The RN parameters are the previously registered ordinary fixed-space fact. -/
theorem bures_adaptive {d r : ℕ} (hcard : Fintype.card ι = d)
    (hd : 2 ≤ d) (hr : 1 ≤ r) (hrd : r ≤ d)
    (V : CollectiveMainLowerBounds.RawVolumeInputs
      (RankReduction.reducedRank d r) (d - RankReduction.reducedRank d r))
    (An : 2 ≤ RankReduction.reducedRank d r * (d - RankReduction.reducedRank d r) →
      CollectiveMainLowerBounds.AnalysisInputs
        (2 * RankReduction.reducedRank d r * (d - RankReduction.reducedRank d r)))
    (P : SymmetricSupport.SymmetricProjectorInput (CollectiveMainLowerBounds.AmbientIndex d r) n)
    (G : GraphFisherBudget.GraphTangentInput) {C ε : ℝ} (hC : 0 < C)
    (N : GraphPrior.NZSmoothLocalPriorInput C) (hε : 0 < ε)
    (hsmall : ε ≤ CollectiveMainLowerBounds.accuracyThreshold C)
    (hA : A.BuresSuccess R r (ENNReal.ofReal ε)) :
    CollectiveMainLowerBounds.sampleConstant C *
      ((r : ℝ) * Real.sqrt (r : ℝ) * d * Real.sqrt (d : ℝ) / ε) ≤ (n : ℝ) :=
  AdaptiveCoordinateTransport.bures_adaptive hcard hd hr hrd V An P (A.toDominated R RJ)
    G hC N hε hsmall ((A.toDominated_learnsRank_iff R RJ chiB r _ _).mpr hA)

/-- Full adaptive right-inverse main lower bound for the same raw model,
with exactly the common positive coefficient and accuracy threshold. -/
theorem right_adaptive {d r : ℕ} (hcard : Fintype.card ι = d)
    (hd : 2 ≤ d) (hr : 1 ≤ r) (hrd : r ≤ d)
    (V : CollectiveMainLowerBounds.RawVolumeInputs
      (RankReduction.reducedRank d r) (d - RankReduction.reducedRank d r))
    (An : 2 ≤ RankReduction.reducedRank d r * (d - RankReduction.reducedRank d r) →
      CollectiveMainLowerBounds.AnalysisInputs
        (2 * RankReduction.reducedRank d r * (d - RankReduction.reducedRank d r)))
    (P : SymmetricSupport.SymmetricProjectorInput (CollectiveMainLowerBounds.AmbientIndex d r) n)
    (G : GraphFisherBudget.GraphTangentInput) {C ε : ℝ} (hC : 0 < C)
    (N : GraphPrior.NZSmoothLocalPriorInput C) (hε : 0 < ε)
    (hsmall : ε ≤ CollectiveMainLowerBounds.accuracyThreshold C)
    (hA : A.RightSuccess R r (ENNReal.ofReal ε)) :
    CollectiveMainLowerBounds.sampleConstant C * ((r : ℝ) * (d : ℝ) ^ 2 / ε ^ 2) ≤ (n : ℝ) :=
  AdaptiveCoordinateTransport.right_adaptive hcard hd hr hrd V An P (A.toDominated R RJ)
    G hC N hε hsmall ((A.toDominated_learnsRank_iff R RJ chiR r _ _).mpr hA)

end OperatorLearner
end Paper26.AdaptiveOperatorModelTransport
