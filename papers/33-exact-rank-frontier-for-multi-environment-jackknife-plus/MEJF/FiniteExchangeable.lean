import MEJF.Exchangeability
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.GroupTheory.Perm.Finite

/-! # A genuine finite exchangeable extremal orbit

Uniformly sample a permutation of the block types and expose its coordinate
array. The resulting probability law is exchangeable, and a designated
coordinate has a type in `S` with probability exactly `S.card / N`.
-/

namespace MEJF.FiniteExchangeable

open MeasureTheory Finset
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Every bijection preserves the uniform probability law on a finite type. -/
theorem uniform_measurePreserving {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (e : α ≃ α) :
    MeasurePreserving e (PMF.uniformOfFintype α).toMeasure
      (PMF.uniformOfFintype α).toMeasure := by
  classical
  refine ⟨measurable_of_finite e, ?_⟩
  ext s hs
  rw [Measure.map_apply (measurable_of_finite e) hs]
  rw [PMF.toMeasure_uniformOfFintype_apply _ (hs.preimage (measurable_of_finite e)),
    PMF.toMeasure_uniformOfFintype_apply _ hs]
  let es : {x // e x ∈ s} ≃ {x // x ∈ s} :=
    { toFun := fun x => ⟨e x, x.property⟩
      invFun := fun y => ⟨e.symm y, by simpa only [e.apply_symm_apply] using y.property⟩
      left_inv := by intro x; apply Subtype.ext; exact e.symm_apply_apply x
      right_inv := by intro y; apply Subtype.ext; exact e.apply_symm_apply y }
  exact congrArg (fun n : ℕ => (n : ℝ≥0∞) / Fintype.card α) (Fintype.card_congr es)

/-- The expectation identity for an exact pointwise label count. -/
theorem probability_eq_of_count_eq {Ω I : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : Ω → I → Prop) (hH : ∀ i, MeasurableSet {z | H z i})
    (s : ℕ) (hcount : ∀ z, (univ.filter (H z)).card = s)
    (i₀ : I) (hequal : ∀ i, μ.real {z | H z i} = μ.real {z | H z i₀}) :
    μ.real {z | H z i₀} = (s : ℝ) / Fintype.card I := by
  classical
  let f : I → Ω → ℝ := fun i => Set.indicator {z | H z i} (fun _ => 1)
  have hf : ∀ i, Integrable (f i) μ := fun i =>
    (integrable_const (1 : ℝ)).indicator (hH i)
  have hsum : (∑ i, μ.real {z | H z i}) = (s : ℝ) := by
    calc
      (∑ i, μ.real {z | H z i}) = ∫ z, ∑ i, f i z ∂μ := by
        rw [integral_finset_sum _ (fun i _ => hf i)]
        apply sum_congr rfl
        intro i _
        exact (integral_indicator_one (hH i)).symm
      _ = ∫ _ : Ω, (s : ℝ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with z
        simp only [f, Set.indicator_apply, Set.mem_setOf_eq]
        simpa only [sum_boole, Nat.cast_inj] using hcount z
      _ = s := by simp
  have hcard : (Fintype.card I : ℝ) ≠ 0 := by
    have hp : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨i₀⟩
    exact_mod_cast Nat.ne_of_gt hp
  apply (eq_div_iff hcard).mpr
  simpa only [hequal, sum_const, card_univ, nsmul_eq_mul, mul_comm] using hsum

variable {I : Type*} [Fintype I] [DecidableEq I]

local instance permMeasurableSpace : MeasurableSpace (Equiv.Perm I) := ⊤
local instance permMeasurableSingletonClass : MeasurableSingletonClass (Equiv.Perm I) :=
  ⟨fun _ => trivial⟩

/-- Uniform probability on every permutation, before exposing the block array. -/
def permutationMeasure (I : Type*) [Fintype I] [DecidableEq I] :
    Measure (Equiv.Perm I) := (PMF.uniformOfFintype (Equiv.Perm I)).toMeasure

instance permutationMeasure_isProbabilityMeasure :
    IsProbabilityMeasure (permutationMeasure I) := by
  unfold permutationMeasure
  infer_instance

/-- Precomposing a sampled permutation is itself a permutation of the finite
sample space. -/
def rightRelabel (e : Equiv.Perm I) : Equiv.Perm (Equiv.Perm I) where
  toFun p := e.symm.trans p
  invFun p := e.trans p
  left_inv p := by ext i; simp
  right_inv p := by ext i; simp

theorem rightRelabel_measurePreserving (e : Equiv.Perm I) :
    MeasurePreserving (rightRelabel e) (permutationMeasure I) (permutationMeasure I) :=
  uniform_measurePreserving _

variable [MeasurableSpace I] [MeasurableSingletonClass I]

/-- The finite array of block types carried by one permutation. -/
def typeArray (p : Equiv.Perm I) : I → I := p

/-- Actual probability law of the uniform permutation array. -/
def uniformPermutationLaw (I : Type*) [Fintype I] [DecidableEq I]
    [MeasurableSpace I] : Measure (I → I) :=
  (permutationMeasure I).map typeArray

instance uniformPermutationLaw_isProbabilityMeasure :
    IsProbabilityMeasure (uniformPermutationLaw I) := by
  unfold uniformPermutationLaw
  exact Measure.isProbabilityMeasure_map (measurable_of_finite typeArray).aemeasurable

/-- Relabeling coordinate positions corresponds to a bijection of the uniformly
sampled permutation space, so the array law is exchangeable. -/
theorem uniformPermutationLaw_exchangeable :
    Exchangeability.Exchangeable (uniformPermutationLaw I) := by
  intro e
  refine ⟨measurable_of_finite _, ?_⟩
  change Measure.map (Exchangeability.relabel e)
    (Measure.map typeArray (permutationMeasure I)) =
    Measure.map typeArray (permutationMeasure I)
  rw [Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
  have heq : Exchangeability.relabel e ∘ typeArray = typeArray ∘ rightRelabel e := rfl
  rw [heq, ← Measure.map_map (measurable_of_finite _) (measurable_of_finite _),
    (rightRelabel_measurePreserving e).map_eq]

omit [MeasurableSpace I] [MeasurableSingletonClass I] in
/-- A permutation has exactly `S.card` coordinates whose types belong to `S`. -/
theorem permutation_selected_count (S : Finset I) (p : Equiv.Perm I) :
    (univ.filter (fun i => p i ∈ S)).card = S.card := by
  classical
  refine Finset.card_bij (fun i _ => p i) ?_ ?_ ?_
  · intro i hi
    exact (mem_filter.mp hi).2
  · intro a ha b hb hab
    exact p.injective hab
  · intro b hb
    refine ⟨p.symm b, ?_, p.apply_symm_apply b⟩
    simp [hb]

omit [MeasurableSpace I] [MeasurableSingletonClass I] in
/-- Every coordinate has the same selected-type probability on the actual
uniform permutation sample space. -/
theorem permutation_selected_probability_equal (S : Finset I) (i j : I) :
    (permutationMeasure I).real {p | p i ∈ S} =
      (permutationMeasure I).real {p | p j ∈ S} := by
  let e := Equiv.swap i j
  have hp : rightRelabel e ⁻¹' {p | p j ∈ S} = {p | p i ∈ S} := by
    ext p
    simp [rightRelabel, e]
  rw [← hp]
  exact (rightRelabel_measurePreserving e).measureReal_preimage
    ((Set.toFinite _).measurableSet).nullMeasurableSet

omit [MeasurableSpace I] [MeasurableSingletonClass I] in
/-- Exact selected-type probability directly on the finite permutation sample
space. -/
theorem permutation_selected_probability (S : Finset I) (i₀ : I) :
    (permutationMeasure I).real {p | p i₀ ∈ S} =
      (S.card : ℝ) / Fintype.card I := by
  exact probability_eq_of_count_eq (permutationMeasure I)
    (fun p i => p i ∈ S) (fun _ => (Set.toFinite _).measurableSet)
    S.card (fun p => by
      calc
        _ = (univ.filter (fun i => p i ∈ S)).card := by
          congr 1
          ext j
          simp
        _ = S.card := permutation_selected_count S p) i₀
    (fun i => permutation_selected_probability_equal S i i₀)

/-- Exact success/failure probability for an arbitrary designated label in the
uniform permutation model. No independence between coordinates is needed. -/
theorem uniformPermutationLaw_selected_probability (S : Finset I) (i₀ : I) :
    (uniformPermutationLaw I).real {z | z i₀ ∈ S} =
      (S.card : ℝ) / Fintype.card I := by
  change ((permutationMeasure I).map typeArray).real {z | z i₀ ∈ S} = _
  rw [Measure.real, Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet]
  exact permutation_selected_probability S i₀

variable {B : Type*} [MeasurableSpace B]

/-- Apply the deterministic block data to an array of type labels. -/
def dataArray (data : I → B) (types : I → I) : I → B := data ∘ types

/-- Actual block law obtained by uniformly permuting any deterministic array.
The block space may be infinite, and the blocks need not be distinct. -/
def blockPermutationLaw (data : I → B) : Measure (I → B) :=
  (uniformPermutationLaw I).map (dataArray data)

instance blockPermutationLaw_isProbabilityMeasure (data : I → B) :
    IsProbabilityMeasure (blockPermutationLaw data) := by
  unfold blockPermutationLaw
  exact Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable

omit [Fintype I] [DecidableEq I] [MeasurableSpace I] [MeasurableSingletonClass I] in
/-- Coordinate relabeling is measurable on an arbitrary product block space. -/
theorem measurable_relabel (e : Equiv.Perm I) :
    Measurable (Exchangeability.relabel e : (I → B) → (I → B)) := by
  apply measurable_pi_iff.mpr
  intro i
  exact measurable_pi_apply (e.symm i)

/-- Every deterministic array, exposed in uniform random order, has an
exchangeable probability law. -/
theorem blockPermutationLaw_exchangeable (data : I → B) :
    Exchangeability.Exchangeable (blockPermutationLaw data) := by
  intro e
  refine ⟨measurable_relabel e, ?_⟩
  change Measure.map (Exchangeability.relabel e)
    (Measure.map (dataArray data) (uniformPermutationLaw I)) =
    Measure.map (dataArray data) (uniformPermutationLaw I)
  rw [Measure.map_map (measurable_relabel e) (measurable_of_finite _)]
  have heq : Exchangeability.relabel e ∘ dataArray data =
      dataArray data ∘ Exchangeability.relabel e := rfl
  rw [heq, ← Measure.map_map (measurable_of_finite _) (measurable_of_finite _),
    (uniformPermutationLaw_exchangeable e).map_eq]

/-- For every measurable equivariant label event, its actual probability on the
uniform permutation orbit is precisely its label count on the base data divided
by the number of labels. The event is arbitrary; no event-probability conclusion
is assumed in the hypotheses. -/
theorem blockPermutationLaw_equivariant_probability (data : I → B)
    (H : (I → B) → I → Prop)
    (hH : ∀ i, MeasurableSet {z | H z i}) (heq : Exchangeability.Equivariant H)
    (i₀ : I) :
    (blockPermutationLaw data).real {z | H z i₀} =
      (((univ.filter (H data)).card : ℕ) : ℝ) / Fintype.card I := by
  classical
  let S := univ.filter (H data)
  have hperm (p : Equiv.Perm I) : H (data ∘ p) i₀ ↔ p i₀ ∈ S := by
    have h := heq p.symm data (p i₀)
    simpa [Exchangeability.relabel, S] using h
  have hevent :
      (dataArray data ∘ typeArray) ⁻¹' {z | H z i₀} = {p | p i₀ ∈ S} := by
    ext p
    exact hperm p
  change (((permutationMeasure I).map typeArray).map (dataArray data)).real
    {z | H z i₀} = _
  rw [Measure.real, Measure.map_map (measurable_of_finite _) (measurable_of_finite _),
    Measure.map_apply ((measurable_of_finite _).comp (measurable_of_finite _)) (hH i₀),
    hevent]
  exact permutation_selected_probability S i₀

end
end MEJF.FiniteExchangeable
