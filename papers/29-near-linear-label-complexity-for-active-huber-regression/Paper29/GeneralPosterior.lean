import Paper29.GeneralTranscriptDefs

noncomputable section
open scoped Classical ENNReal
open MeasureTheory
namespace Paper29.GeneralTranscript
open GeneralInformation

/-- The actual posterior information of a slot is bounded by κ times its
active indicator. The inactive case is deterministic; the active case uses a
measurable reversible tagging of the selected response. -/
theorem posterior_slot_bound {E S R : Type} [MeasurableSpace E] [MeasurableSpace S] [MeasurableSpace R]
    {n : ℕ} (rules : StandardRules) (p : Choices E n R) (t : ℕ) (h : History E n R t)
    (P : Measure (S × (Fin n → R))) [IsProbabilityMeasure P] (κ : ℝ≥0∞)
    (hlocal : ∀ j,p t h=Sum.inl j → information P Prod.fst (fun sb => sb.2 j) ≤ κ) :
    information P Prod.fst (fixedSlot p t h) ≤ κ*(active p t h : ℝ≥0∞) := by
  cases hc : p t h with
  | inl j =>
    haveI : Nonempty (S × (Fin n → R)) := QueryModel.seed_nonempty P
    let b0 : R := (Classical.choice (inferInstance : Nonempty (S × (Fin n → R)))).2 j
    let f : R → Slot n R := fun b => Sum.inl (j,b)
    let g : Slot n R → R := Sum.elim Prod.snd (fun _ => b0)
    have hf : Measurable f := measurable_inl.comp (measurable_const.prodMk measurable_id)
    have hg : Measurable g := measurable_fun_sum measurable_snd measurable_const
    have hleft : Function.LeftInverse g f := fun _ => rfl
    have hr := rules.relabel P Prod.fst (fun sb => sb.2 j) f g measurable_fst
      ((measurable_pi_apply j).comp measurable_snd) hf hg hleft
    have he : fixedSlot (S:=S) p t h=(fun sb => f (sb.2 j)) := by
      funext sb
      simp only [fixedSlot,hc,f]
    rw [he,hr]
    simpa only [active,hc,Sum.inl_ne_inr,if_false,Nat.cast_one,mul_one] using hlocal j hc
  | inr u =>
    have he : fixedSlot (S:=S) p t h=(fun _ => Sum.inr ()) := by funext sb; simp only [fixedSlot,hc]
    rw [he,rules.constant P Prod.fst (Sum.inr ()) measurable_fst]
    exact zero_le _

end Paper29.GeneralTranscript
