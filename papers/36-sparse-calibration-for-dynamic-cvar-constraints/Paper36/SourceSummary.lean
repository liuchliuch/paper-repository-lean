import Paper36.SourceHistory
import Paper36.SourceMarginals
import Paper36.SourceBlockReplay

/-! The sufficient observable state and actual unused windows of each finite
prefix of the one infinite source experiment. -/
namespace Paper36.SourceSummary
noncomputable section
open scoped ENNReal
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation
  Paper36.Trajectories Paper36.AdaptiveTapes Paper36.SourceReplay
  Paper36.SourceProtocol Paper36.SourceHistory
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {M Meta : Type*} [MeasurableSpace M] [MeasurableSpace Meta]

abbrev Input (M Meta : Type*) (S A : Type u) (T k : ℕ) :=
  (M × ((S × A) × ℕ → S)) × (Fin k → Draw Meta A T)
abbrev Ctx (M Meta : Type*) (S A : Type u) (T k : ℕ) := M × Data Meta S A T k

def context (T k : ℕ) (s₀ : S) (x : Input M Meta S A T k) : Ctx M Meta S A T k :=
  (x.1.1,(past T k s₀ x).2)

def summary (T k L : ℕ) (s₀ : S) (x : Input M Meta S A T k) :
    Ctx M Meta S A T k × Stack (S × A) S L :=
  (context T k s₀ x,window (fun row j => x.1.2 (row,j)) (historyCount (past T k s₀ x)) L)

lemma measurable_context (T k : ℕ) (s₀ : S) :
    Measurable (context (M := M) (Meta := Meta) (S := S) (A := A) T k s₀) := by
  apply measurable_fst.fst.prodMk
  apply Measurable.prodMk
  · exact measurable_pi_lambda _ fun i => ((measurable_pi_apply i).comp measurable_snd).fst
  · exact measurable_finitePaths _ s₀ (measurable_curry_raw.comp measurable_fst.snd) k _ measurable_snd

lemma measurable_summary (T k L : ℕ) (s₀ : S) :
    Measurable (summary (M := M) (Meta := Meta) (S := S) (A := A) T k L s₀) := by
  apply (measurable_context T k s₀).prodMk
  apply measurable_pi_lambda
  intro c
  have hc : Measurable (fun x : Input M Meta S A T k =>
      historyCount (past T k s₀ x) c.1 + c.2.val) :=
    ((measurable_historyCount c.1).comp (measurable_past T k s₀)).add_const _
  exact measurable_eval_countable.comp (measurable_fst.snd.prodMk (measurable_const.prodMk hc))

/-- The newly generated episode appends its actual path, and the next unused
window starts at precisely the old count plus those actual visits. -/
theorem summary_append (T k L : ℕ) (s₀ : S) (x : Input M Meta S A T k) (d : Draw Meta A T) :
    summary T (k+1) L s₀ (SourceMarginals.appendDraw k (x,d)) =
      let p := replayStep (fun row j => x.1.2 (row,j)) (historyCount (past T k s₀ x)) T s₀ d.2
      ((x.1.1,append T k (context T k s₀ x).2 (d.1,p)),
        window (fun row j => x.1.2 (row,j))
          (SourceBlockReplay.afterPath (historyCount (past T k s₀ x)) T p) L) := by
  dsimp only [summary,context,past,SourceMarginals.appendDraw]
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [finiteHistory,append]
        · simp [finiteHistory,append]
      · simp only [finiteHistory,finitePaths,Fin.lastCases_castSucc,Fin.lastCases_last]
        rfl
  · dsimp only
    rw [finiteHistory_append]
    congr 1
    funext row
    exact count_append T k _ _ row

end
end Paper36.SourceSummary
