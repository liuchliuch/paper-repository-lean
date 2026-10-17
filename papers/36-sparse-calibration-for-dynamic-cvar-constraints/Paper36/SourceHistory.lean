import Paper36.SourceProtocol

/-! Finite indexed histories for the concrete source experiment. These maps are
used for the episode-by-episode joint-law induction. -/
namespace Paper36.SourceHistory
noncomputable section
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Trajectories
  Paper36.AdaptiveTapes Paper36.SourceReplay
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {Meta : Type*} [MeasurableSpace Meta]

abbrev Data (Meta : Type*) (S A : Type u) (T k : ℕ) :=
  (Fin k → Meta) × (Fin k → Trajectory S A T)

def append (T k : ℕ) (h : Data Meta S A T k) (z : Meta × Trajectory S A T) :
    Data Meta S A T (k+1) :=
  (Fin.lastCases z.1 h.1, Fin.lastCases z.2 h.2)

lemma measurable_append (T k : ℕ) :
    Measurable (fun z : Data Meta S A T k × (Meta × Trajectory S A T) => append T k z.1 z.2) := by
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [append, Fin.lastCases_last] using measurable_snd.fst
    · simpa only [append, Fin.lastCases_castSucc] using (measurable_pi_apply j).comp measurable_fst.fst
  · apply measurable_pi_lambda
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [append, Fin.lastCases_last] using measurable_snd.snd
    · simpa only [append, Fin.lastCases_castSucc] using (measurable_pi_apply j).comp measurable_fst.snd

lemma count_append (T k : ℕ) (h : Data Meta S A T k) (z : Meta × Trajectory S A T) (row : S × A) :
    historyCount (⟨k+1,append T k h z⟩ : History Meta S A T) row =
      historyCount (⟨k,h⟩ : History Meta S A T) row + visitCount row T z.2 := by
  change rowCount (finiteTrace (Fin.lastCases z.2 h.2)) row =
    rowCount (finiteTrace h.2) row + visitCount row T z.2
  rw [finiteTrace_succ]
  simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
  exact rowCount_append_trace _ T z.2 row

/-- Appending the newly sampled metadata/actions appends precisely the actual
new path to the indexed observed history. -/
theorem finiteHistory_append (raw : RawTape S A) (s₀ : S) (T k : ℕ)
    (d : Fin k → Draw Meta A T) (z : Draw Meta A T) :
    finiteHistory raw s₀ (Fin.lastCases z d) =
      (⟨k+1, append T k (finiteHistory raw s₀ d).2
        (z.1,replayStep raw (historyCount (finiteHistory raw s₀ d)) T s₀ z.2)⟩ : History Meta S A T) := by
  apply Sigma.ext (by rfl)
  apply heq_of_eq
  apply Prod.ext
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [finiteHistory, append]
    · simp [finiteHistory, append]
  · change finitePaths raw s₀ (k+1) (Fin.lastCases z d) = _
    simp only [finitePaths, Fin.lastCases_castSucc, Fin.lastCases_last]
    rfl

end
end Paper36.SourceHistory
