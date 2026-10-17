import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-! The exchangeability step in §4, for an arbitrary measurable block space.
The event family is an explicit parameter. Its identification with jackknife+
failure is a separate deterministic theorem and is not assumed here. -/
namespace MEJF.Exchangeability
open MeasureTheory Finset
noncomputable section
attribute [local instance] Classical.propDecidable

variable {I B Ω : Type*} [Fintype I] [DecidableEq I]
variable [MeasurableSpace B] [MeasurableSpace Ω]

/-- Relabel all blocks, with the inverse convention from (4.5). -/
def relabel (e : Equiv.Perm I) (z : I → B) : I → B := z ∘ e.symm

/-- Invariance of the joint block law under every block permutation. -/
def Exchangeable (μ : Measure (I → B)) : Prop :=
  ∀ e : Equiv.Perm I, MeasurePreserving (relabel e) μ μ

/-- The event at the relabeled position is the original event. -/
def Equivariant (H : (I → B) → I → Prop) : Prop :=
  ∀ e z i, H (relabel e z) (e i) ↔ H z i

lemma event_probability_eq (μ : Measure (I → B))
    (hμ : Exchangeable μ) (H : (I → B) → I → Prop)
    (hH : ∀ i, MeasurableSet {z | H z i}) (heq : Equivariant H) (i j : I) :
    μ.real {z | H z i} = μ.real {z | H z j} := by
  let e := Equiv.swap i j
  have hp : relabel e ⁻¹' {z | H z j} = {z | H z i} := by
    ext z
    change H (relabel e z) j ↔ H z i
    simpa [e] using heq e z i
  rw [← hp]
  exact (hμ e).measureReal_preimage (hH j).nullMeasurableSet

/-- An equal-marginal family of measurable events with at most `s` simultaneous
occurrences has marginal probability at most `s / card I`. No independence is
needed. This is the expectation step following (4.8). -/
theorem probability_le_of_count_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : Ω → I → Prop) (hH : ∀ i, MeasurableSet {z | H z i})
    (s : ℕ) (hcount : ∀ z, (univ.filter (H z)).card ≤ s)
    (i₀ : I) (hequal : ∀ i, μ.real {z | H z i} = μ.real {z | H z i₀}) :
    μ.real {z | H z i₀} ≤ (s : ℝ) / Fintype.card I := by
  classical
  let f : I → Ω → ℝ := fun i => Set.indicator {z | H z i} (fun _ => 1)
  have hf : ∀ i, Integrable (f i) μ := fun i =>
    (integrable_const (1 : ℝ)).indicator (hH i)
  have hsum : (∑ i, μ.real {z | H z i}) ≤ (s : ℝ) := by
    calc
      (∑ i, μ.real {z | H z i}) = ∫ z, ∑ i, f i z ∂μ := by
        rw [integral_finset_sum _ (fun i _ => hf i)]
        apply sum_congr rfl
        intro i _
        exact (integral_indicator_one (hH i)).symm
      _ ≤ ∫ _ : Ω, (s : ℝ) ∂μ := by
        apply integral_mono (integrable_finset_sum _ (fun i _ => hf i)) (integrable_const _)
        intro z
        simp only [f, Set.indicator_apply, Set.mem_setOf_eq]
        simpa only [sum_boole, Nat.cast_le] using hcount z
      _ = s := by simp
  have hcard : (0 : ℝ) < Fintype.card I := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨i₀⟩
  apply (le_div_iff₀ hcard).mpr
  simpa only [hequal, sum_const, card_univ, nsmul_eq_mul, mul_comm] using hsum

/-- Uniform block exchangeability plus equivariance yields the sharp label-count
probability upper bound; this works on infinite block spaces as well. -/
theorem exchangeable_probability_le (μ : Measure (I → B)) [IsProbabilityMeasure μ]
    (hμ : Exchangeable μ) (H : (I → B) → I → Prop)
    (hH : ∀ i, MeasurableSet {z | H z i}) (heq : Equivariant H)
    (s : ℕ) (hcount : ∀ z, (univ.filter (H z)).card ≤ s) (i₀ : I) :
    μ.real {z | H z i₀} ≤ (s : ℝ) / Fintype.card I :=
  probability_le_of_count_le μ H hH s hcount i₀
    (fun i => event_probability_eq μ hμ H hH heq i i₀)

/-- The exact averaging identity used both in the base law and the stability
refinement. The count remains inside the expectation. -/
theorem probability_eq_average_count (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : Ω → I → Prop) (hH : ∀ i, MeasurableSet {z | H z i}) (i₀ : I)
    (hequal : ∀ i, μ.real {z | H z i} = μ.real {z | H z i₀}) :
    μ.real {z | H z i₀} =
      (∫ z, ((univ.filter (H z)).card : ℝ) ∂μ) / Fintype.card I := by
  classical
  let f : I → Ω → ℝ := fun i => Set.indicator {z | H z i} (fun _ => 1)
  have hf : ∀ i, Integrable (f i) μ := fun i =>
    (integrable_const (1 : ℝ)).indicator (hH i)
  have hc : (fun z => ((univ.filter (H z)).card : ℝ)) = fun z => ∑ i, f i z := by
    funext z
    simp [f, Set.indicator_apply]
  rw [hc, integral_finset_sum _ (fun i _ => hf i)]
  have hm : ∀ i, ∫ z, f i z ∂μ = μ.real {z | H z i₀} := by
    intro i
    exact (integral_indicator_one (hH i)).trans (hequal i)
  simp only [hm, sum_const, card_univ, nsmul_eq_mul]
  have hp : (Fintype.card I : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos_iff.mpr ⟨i₀⟩))
  field_simp

/-- The measure-theoretic two-count interpolation underlying (6.29).
An invariant stability event can supply the equal marginals; only its probability
and the two pointwise counts enter this last step. -/
theorem probability_le_two_counts (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : Ω → I → Prop) (hH : ∀ i, MeasurableSet {z | H z i}) (i₀ : I)
    (hequal : ∀ i, μ.real {z | H z i} = μ.real {z | H z i₀})
    (E : Set Ω) (hE : MeasurableSet E) (ell s : ℕ) (hes : ell ≤ s)
    (hon : ∀ z ∈ E, (univ.filter (H z)).card ≤ ell)
    (hoff : ∀ z ∉ E, (univ.filter (H z)).card ≤ s)
    (gamma : ℝ) (hprob : 1-gamma ≤ μ.real E) :
    μ.real {z | H z i₀} ≤
      (ell : ℝ) / Fintype.card I + ((s : ℝ)-ell) / Fintype.card I * gamma := by
  classical
  let C : Ω → ℝ := fun z => ((univ.filter (H z)).card : ℝ)
  let b : Ω → ℝ := fun z => (ell : ℝ) + ((s : ℝ)-ell) *
    Eᶜ.indicator (fun _ => (1 : ℝ)) z
  have hc : Integrable C μ := by
    have heq : C = fun z => ∑ i, Set.indicator {z | H z i} (fun _ => (1:ℝ)) z := by
      funext z
      simp [C, Set.indicator_apply]
    rw [heq]
    exact integrable_finset_sum _ (fun i _ => (integrable_const (1:ℝ)).indicator (hH i))
  have hb : Integrable b μ :=
    (integrable_const _).add (((integrable_const (1:ℝ)).indicator hE.compl).const_mul _)
  have hle : ∫ z, C z ∂μ ≤ ∫ z, b z ∂μ := by
    apply integral_mono hc hb
    intro z
    by_cases hz : z ∈ E
    · simpa [C, b, Set.indicator_apply, hz] using (Nat.cast_le (α := ℝ)).mpr (hon z hz)
    · simpa [C, b, Set.indicator_apply, hz] using (Nat.cast_le (α := ℝ)).mpr (hoff z hz)
  have hi : (∫ a, Eᶜ.indicator (fun _ : Ω => (1:ℝ)) a ∂μ) = μ.real Eᶜ := by
    simpa using (integral_indicator_const (μ := μ) (1:ℝ) hE.compl)
  have hbi : ∫ z, b z ∂μ = (ell : ℝ) + ((s : ℝ)-ell) * μ.real Eᶜ := by
    simp only [b, integral_add (integrable_const _) (((integrable_const (1:ℝ)).indicator hE.compl).const_mul _),
      integral_const, measureReal_univ_eq_one, one_smul, integral_const_mul,
      hi]
  have hec : μ.real Eᶜ ≤ gamma := by
    have ht := measureReal_add_measureReal_compl (μ := μ) hE
    rw [measureReal_univ_eq_one] at ht
    linarith
  have hn : (0:ℝ) ≤ (s:ℝ)-ell := by exact_mod_cast (sub_nonneg.mpr ((Nat.cast_le (α := ℝ)).mpr hes))
  rw [probability_eq_average_count μ H hH i₀ hequal]
  have hcard : (0:ℝ) < Fintype.card I := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨i₀⟩
  apply (div_le_iff₀ hcard).mpr
  have ht := (mul_le_mul_of_nonneg_left hec hn)
  rw [hbi] at hle
  dsimp [C] at hle
  field_simp
  nlinarith

end
end MEJF.Exchangeability
