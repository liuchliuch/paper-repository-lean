import Paper36.SourceConditional
import Paper36.SourceProtocol

/-! The concrete action-vector protocol is exactly native row-head execution,
including the unused rows. This supplies the episode step used in the source
fresh-window induction, without replacing it by a trajectory-law hypothesis. -/
namespace Paper36.SourceBlockReplay
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation
  Paper36.Trajectories Paper36.AdaptiveTapes Paper36.SourceBlocks Paper36.SourceReplay

universe u
variable {S A : Type u} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]

/-- The actual frozen row counts plus exactly the visits in the current path. -/
def afterPath (counts : S × A → ℕ) (T : ℕ) (path : Trajectory S A T) : S × A → ℕ :=
  fun row => counts row + visitCount row T path

lemma afterPath_zero (counts : S × A → ℕ) (s : S) : afterPath counts 0 s = counts := by
  funext row
  simp [afterPath,visitCount]

lemma afterPath_succ (counts : S × A → ℕ) (T : ℕ) (s : S) (a : A)
    (path : Trajectory S A T) :
    afterPath counts (T+1) (s,a,path) = afterPath (increment counts (s,a)) T path := by
  funext row
  simp only [afterPath,visitCount,increment]
  by_cases he : row=(s,a)
  · subst row
    simp [Nat.add_assoc]
  · simp [he,ne_comm.mp he,Nat.add_assoc]

/-- Native block execution is taped path execution plus its actual updated row
windows. All windows refer to the same original raw tape. -/
theorem blockLaw_expect_replay (π : Policy S A) (raw : RawTape S A) (counts : S × A → ℕ)
    (L T h : ℕ) (s₀ : S) (f : Trajectory S A T × Stack (S × A) S L → ℝ) :
    expect (blockLaw π L T h s₀ (window raw counts (L+T))).mass f =
      expect (tapedTrajectory π T h s₀ (window raw counts T)).mass
        (fun path => f (path,window raw (afterPath counts T path) L)) := by
  induction T generalizing counts h s₀ with
  | zero => simp only [blockLaw,expect_dirac,tapedTrajectory,afterPath_zero,Nat.add_zero]
  | succ T ih =>
    rw [blockLaw,bindLaw_expect,tapedTrajectory,expect_joint]
    simp only [dirac,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    rw [expect_joint]
    simp_rw [pushLaw_expect,head_window,remaining_window]
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    dsimp only
    have hh : head (s₀,a) (window raw counts (L+(T+1))) = raw (s₀,a) (counts (s₀,a)) :=
      head_window raw counts (L+T) (s₀,a)
    have hr : remaining (s₀,a) (window raw counts (L+(T+1))) =
        window raw (increment counts (s₀,a)) (L+T) := remaining_window raw counts (L+T) (s₀,a)
    rw [hh,hr,ih]
    apply Finset.sum_congr rfl
    intro path _
    dsimp only
    rw [afterPath_succ]

/-- The actual action-vector law, replayed on the original tape, preserves the
native path law and the complete unused window jointly. -/
theorem replay_actionLaw_eq_blockLaw (π : Policy S A) (raw : RawTape S A)
    (counts : S × A → ℕ) (L T : ℕ) (s₀ : S) :
    pushLaw (SourceProtocol.actionLaw π T s₀ (window raw counts T))
      (fun actions => let path := replayStep raw counts T s₀ actions
        (path,window raw (afterPath counts T path) L)) =
      blockLaw π L T 0 s₀ (window raw counts (L+T)) := by
  apply law_ext
  funext z
  let f := SourceConditional.pointTest z
  have he : expect (pushLaw (SourceProtocol.actionLaw π T s₀ (window raw counts T))
      (fun actions => let path := replayStep raw counts T s₀ actions
        (path,window raw (afterPath counts T path) L))).mass f =
      expect (blockLaw π L T 0 s₀ (window raw counts (L+T))).mass f := by
    rw [pushLaw_expect,SourceProtocol.actionLaw,pushLaw_expect,blockLaw_expect_replay]
    apply Finset.sum_congr rfl
    intro path _
    dsimp only
    by_cases hp : 0 < (tapedTrajectory π T 0 s₀ (window raw counts T)).mass path
    · rw [replayStep_of_positive_tapedTrajectory π raw counts T 0 s₀ path hp]
    · have hz : (tapedTrajectory π T 0 s₀ (window raw counts T)).mass path = 0 :=
        le_antisymm (le_of_not_gt hp) ((tapedTrajectory π T 0 s₀ (window raw counts T)).nonneg path)
      simp only [hz,zero_mul]
  exact (SourceConditional.expect_indicator_point _ z).symm.trans
    (he.trans (SourceConditional.expect_indicator_point _ z))

section NativeMaps
variable {X Y : Type u} [Fintype X] [Fintype Y]
  [MeasurableSpace X] [MeasurableSpace Y] [DiscreteMeasurableSpace X] [DiscreteMeasurableSpace Y]

lemma lawMeasure_pushLaw (P : Law X) (f : X → Y) :
    lawMeasure (pushLaw P f) = (lawMeasure P).map f := by
  classical
  apply Measure.ext_of_singleton
  intro y
  rw [lawMeasure_singleton,Measure.map_apply (measurable_of_countable f) (measurableSet_singleton _)]
  symm
  calc
    _ = ∑ x, if f x=y then ENNReal.ofReal (P.mass x) else 0 := by
      rw [lawMeasure,PMF.toMeasure_apply_fintype]
      simp only [lawPMF,PMF.ofFintype_apply,Set.indicator_apply,Set.mem_preimage,Set.mem_singleton_iff]
    _ = ENNReal.ofReal (∑ x, if f x=y then P.mass x else 0) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => by split; exact P.nonneg x; exact le_rfl)]
      apply Finset.sum_congr rfl
      intro x _
      split <;> simp_all
    _ = _ := by
      congr 1
      simp [pushLaw,bindLaw,dirac,eq_comm,mul_ite]

end NativeMaps

/-- The exact native measure identity for the actual action-vector protocol,
including its original-tape residual window. -/
theorem actionLaw_joint_replay (π : Policy S A) (raw : RawTape S A)
    (counts : S × A → ℕ) (L T : ℕ) (s₀ : S) :
    (lawMeasure (SourceProtocol.actionLaw π T s₀ (window raw counts T))).map
      (fun actions => let path := replayStep raw counts T s₀ actions
        (path,window raw (afterPath counts T path) L)) =
      lawMeasure (blockLaw π L T 0 s₀ (window raw counts (L+T))) := by
  rw [← lawMeasure_pushLaw,replay_actionLaw_eq_blockLaw]


end
end Paper36.SourceBlockReplay
