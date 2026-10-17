import Paper29.Sequentialization

noncomputable section
open scoped Classical ENNReal
open MeasureTheory
namespace Paper29.QueryModel

def queryBits {Ω : Type} {n d : ℕ} (a : NonadaptiveProcedure Ω n d) (ω : Ω) : Fin n → Bool :=
  fun i => decide (i∈a.queried ω)

theorem measurable_queryBits {Ω : Type} [MeasurableSpace Ω] {n d : ℕ}
    (a : NonadaptiveProcedure Ω n d) (hq : ∀ i,MeasurableSet {ω | i∈a.queried ω}) :
    Measurable (queryBits a) := by
  apply measurable_pi_lambda
  intro i
  have hh : Measurable (fun ω => if i∈a.queried ω then true else false) :=
    Measurable.ite (hq i) measurable_const measurable_const
  convert hh using 1

theorem queried_from_bits {Ω : Type} {n d : ℕ} (a : NonadaptiveProcedure Ω n d) (ω : Ω) :
    Finset.univ.filter (fun i => queryBits a ω i)=a.queried ω := by
  ext i
  simp [queryBits]

theorem measurable_nextFresh {Ω : Type} [MeasurableSpace Ω] {n d : ℕ}
    (a : NonadaptiveProcedure Ω n d) (hq : ∀ i,MeasurableSet {ω | i∈a.queried ω}) (h : History n) :
    Measurable (fun ω => nextFresh (remaining a ω h)) := by
  have hh := (measurable_of_countable (fun z : Fin n → Bool =>
    nextFresh ((Finset.univ.filter (fun i => z i)) \ (h.map Prod.fst).toFinset))).comp (measurable_queryBits a hq)
  simpa only [Function.comp_def,queried_from_bits,remaining] using hh

theorem sequentialPolicy_measurable {Ω : Type} [MeasurableSpace Ω] {n d : ℕ}
    (a : NonadaptiveProcedure Ω n d) (hq : ∀ i,MeasurableSet {ω | i∈a.queried ω})
    (ha : ∀ b,Measurable (fun ω => a.answer ω b)) (h : History n) :
    Measurable (fun ω => sequentialPolicy a ω h) := by
  let qencode : (Fin n ⊕ Unit) → ((Fin d → ℝ) ⊕ (Fin n ⊕ Unit)) := fun s =>
    match s with
    | .inl i => .inr (.inl i)
    | .inr _ => .inl 0
  have hn := measurable_nextFresh a hq h
  have hm : Measurable (fun ω => if nextFresh (remaining a ω h)=Sum.inr () then
      Sum.inl (a.answer ω (historyLabels h)) else qencode (nextFresh (remaining a ω h))) :=
    Measurable.ite (hn (measurableSet_singleton (Sum.inr ())))
      (measurable_inl.comp (ha _)) ((measurable_of_countable qencode).comp hn)
  have he : (fun ω => Decision.encode (sequentialPolicy a ω h)) =
      (fun ω => if nextFresh (remaining a ω h)=Sum.inr () then
        Sum.inl (a.answer ω (historyLabels h)) else qencode (nextFresh (remaining a ω h))) := by
    funext ω
    cases hs : nextFresh (remaining a ω h) with
    | inl i => simp [sequentialPolicy,hs,Decision.encode,qencode]
    | inr u => cases u; simp [sequentialPolicy,hs,Decision.encode]
  rw [← he] at hm
  apply Measurable.of_comap_le
  change (MeasurableSpace.comap Decision.encode inferInstance).comap (fun ω => sequentialPolicy a ω h) ≤ _
  rw [MeasurableSpace.comap_comp]
  exact hm.comap_le

/-- Sequentializing the finite selected set preserves the official measurable
correctness predicate and exact distinct-query count. -/
theorem sequential_correct {Ω : Type} [MeasurableSpace Ω] {n d : ℕ}
    (μ : Measure Ω) (a : NonadaptiveProcedure Ω n d) (A : Matrix (Fin n) (Fin d) ℝ) (ε : ℝ)
    (ha : NonadaptiveCorrect μ a A ε) : Correct μ (sequentialPolicy a) A ε := by
  refine ⟨sequentialPolicy_fresh a,sequentialPolicy_measurable a ha.1 ha.2.1,?_⟩
  intro b
  have hs : {ω | Successful (sequentialPolicy a) A b ε ω} =
      {ω | ∀ y,Real.sqrt (objective A b (a.answer ω b)) ≤ (1+ε)*Real.sqrt (objective A b y)} := by
    ext ω
    exact sequential_success_iff a A b ε ω
  refine ⟨hs ▸ (ha.2.2 b).1,?_,hs ▸ (ha.2.2 b).2⟩
  have hq := (measurable_of_countable (fun z : Fin n → Bool =>
    ((Finset.univ.filter (fun i => z i)).card : ℝ≥0∞))).comp (measurable_queryBits a ha.1)
  simpa only [Function.comp_def,queried_from_bits,sequential_queryCount] using hq

end Paper29.QueryModel
