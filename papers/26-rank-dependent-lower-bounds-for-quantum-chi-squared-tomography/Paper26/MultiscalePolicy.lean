import Paper26.MultiscaleEstimator
import Paper26.StagePolicy
import Paper26.CollectiveBlockProtocol

/-! Recorded stage outcomes drive the actual multiscale recursion. The
policy reads only past outcomes. Every execution certificate, mass bound and
final loss implication is derived from those records and actual block errors. -/
noncomputable section
open scoped BigOperators ComplexOrder ENNReal
open MeasureTheory

namespace Paper26.MultiscalePolicy
open QuantumModel ContinuousPOVM AdaptiveModel MultiscaleUpdate
open MultiscaleMatrixBridge MultiscaleEstimator MultiscaleRefinement

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
  {Ω : Type u} [MeasurableSpace Ω] {L : ℕ}
local instance matrixMeasurableSpace (m n : Type*) : MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))
local instance subsetMeasurableSpace : MeasurableSpace (Finset ι) := ⊤
local instance subsetMeasurableSingleton : MeasurableSingletonClass (Finset ι) := ⟨fun _ => trivial⟩

def zeroFamily : EstimateFamily (ι := ι) := fun _ => ⟨0, Matrix.PosSemidef.zero⟩

/-- The jth record is filled only when the jth actual stage outcome arrives. -/
def records (decode : ℕ → Ω → EstimateFamily (ι := ι)) :
    (k : ℕ) → History PUnit Ω k → (Fin L → EstimateFamily (ι := ι))
  | 0, _ => fun _ => zeroFamily
  | k+1, h => fun j => if j.val=k then decode k h.2 else records decode k h.1 j

theorem measurable_records (decode : ℕ → Ω → EstimateFamily (ι := ι)) (hd : ∀ k, Measurable (decode k)) (k : ℕ) :
    Measurable (records (L := L) decode k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    apply measurable_pi_lambda
    intro j
    by_cases hj : j.val=k
    · simp only [records, if_pos hj]
      exact (hd k).comp measurable_snd
    · simp only [records, if_neg hj]
      exact ((measurable_pi_apply j).comp ih).comp measurable_fst

theorem execute_congr_before (B : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
    (lower : Fin L → ℝ) (F G : Fin L → EstimateFamily (ι := ι)) (k : ℕ)
    (h : ∀ j : Fin L, j.val<k → F j=G j) : execute B L lower F k=execute B L lower G k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases hk : k<L
    · simp only [execute, dif_pos hk]
      rw [ih (fun j hj => h j (by omega)), h ⟨k,hk⟩ (by simp)]
    · simp only [execute, dif_neg hk]
      exact ih (fun j hj => h j (by omega))

variable (B : MeasurableSpectralSelection.CompactFiberSelectionInput.{u,u})
  (lower : Fin L → ℝ) (decode : ℕ → Ω → EstimateFamily (ι := ι))

theorem records_next_execute (k : ℕ) (h : History PUnit Ω k) (y : Ω) :
    execute B L lower (records decode (k+1) (h,y)) k = execute B L lower (records decode k h) k := by
  apply execute_congr_before
  intro j hj
  simp only [records, if_neg (ne_of_lt hj)]

/-- The actual policy state after precisely k completed stages. -/
def state (k : ℕ) (h : History PUnit Ω k) : State (ι := ι) :=
  execute B L lower (records decode k h) k

theorem measurable_state (hd : ∀ k, Measurable (decode k)) (k : ℕ) : Measurable (state B lower decode k) :=
  (measurable_execute B L lower k).comp (measurable_records decode hd k)

theorem state_zero (h : PUnit) : state B lower decode 0 h=initial L := rfl

theorem state_next (k : ℕ) (hk : k<L) (h : History PUnit Ω k) (y : Ω) :
    state B lower decode (k+1) (h,y) = step B k (lower ⟨k,hk⟩) (state B lower decode k h) (decode k y) := by
  unfold state
  rw [execute, dif_pos hk, records_next_execute]
  simp only [records, ite_true]

/-- Only the active subset and current basis control the next measurement. -/
def control (k : ℕ) (h : History PUnit Ω k) : Finset ι × Matrix.unitaryGroup ι ℂ :=
  ((state B lower decode k h).1, (state B lower decode k h).2.1)

theorem measurable_control (hd : ∀ k, Measurable (decode k)) (k : ℕ) : Measurable (control B lower decode k) :=
  ((measurable_state B lower decode hd k).fst).prodMk (measurable_state B lower decode hd k).snd.fst

def good (ρ : Density ι) (η : Fin L → ℝ) (k : ℕ) : Set (History PUnit Ω (k+1)) :=
  if hk : k<L then {h | stateError ρ (state B lower decode k h.1,decode k h.2) ≤ η ⟨k,hk⟩} else Set.univ

theorem measurableSet_good (hd : ∀ k, Measurable (decode k)) (ρ : Density ι) (η : Fin L → ℝ) (k : ℕ) :
    MeasurableSet (good B lower decode ρ η k) := by
  by_cases hk : k<L
  · simp only [good, dif_pos hk]
    exact measurableSet_le ((measurable_stateError ρ).comp
      (((measurable_state B lower decode hd k).comp measurable_fst).prodMk ((hd k).comp measurable_snd)))
      measurable_const
  · simp only [good, dif_neg hk]
    exact MeasurableSet.univ

theorem currentError_records_next_old (ρ : Density ι) (k : ℕ)
    (h : History PUnit Ω k) (y : Ω) (j : Fin L) (hj : j.val<k) :
    currentError B L lower ρ j (records decode (k+1) (h,y)) =
      currentError B L lower ρ j (records decode k h) := by
  unfold currentError
  have he := execute_congr_before B lower (records decode (k+1) (h,y)) (records decode k h) j.val
    (fun q hq => by simp only [records, if_neg (show q.val ≠ k by omega)])
  rw [he]
  simp only [records, if_neg (ne_of_lt hj)]

/-- Every earlier current block estimate is accurate on the actual good
prefix event. Future unfilled records are irrelevant to this deduction. -/
theorem goodPrefix_accuracy (ρ : Density ι) (η : Fin L → ℝ) (k : ℕ)
    (h : History PUnit Ω k) (hh : h ∈ StagePolicy.goodPrefix (good B lower decode ρ η) k) :
    ∀ j : Fin L, j.val<k → currentError B L lower ρ j (records decode k h) ≤ η j := by
  induction k with
  | zero => intro j hj; omega
  | succ k ih =>
    rcases h with ⟨h,y⟩
    change h ∈ StagePolicy.goodPrefix (good B lower decode ρ η) k ∧
      (h,y) ∈ good B lower decode ρ η k at hh
    intro j hj
    by_cases hjk : j.val<k
    · rw [currentError_records_next_old B lower decode ρ k h y j hjk]
      exact ih h hh.1 j hjk
    · have he : j.val=k := by omega
      have hk : k<L := by omega
      have hg : stateError ρ (state B lower decode k h,decode k y) ≤ η ⟨k,hk⟩ := by
        simpa only [good, dif_pos hk, Set.mem_setOf_eq] using hh.2
      unfold currentError
      rw [he, records_next_execute B lower decode k h y]
      simp only [records, if_pos he]
      have hjEq : j=(⟨k,hk⟩ : Fin L) := Fin.ext he
      simpa only [state, hjEq] using hg

section Nonempty
variable [Nonempty ι] [NeZero L]

def estimator (hd : ∀ k, Measurable (decode k)) (hlower : ∀ j,0<lower j) : Estimator ι (History PUnit Ω L) where
  estimate h := MultiscaleEstimator.estimate B L lower hlower (records decode L h)
  measurable_estimate := (MultiscaleEstimator.measurable_estimate B L lower hlower).comp
    (measurable_records decode hd L)

theorem current_mass_le (ρ : Density ι) {r : ℕ} {e : ℝ}
    (hr : ρ.matrix.rank ≤ r) (j : Fin L) (h : History PUnit Ω j.val)
    (hh : h ∈ StagePolicy.goodPrefix
      (good B (dyadicLower L) decode ρ (stageAccuracy e L)) j.val) :
    (Matrix.trace (compressedBlock (state B (dyadicLower L) decode j.val h).1
      (state B (dyadicLower L) decode j.val h).2.1 ρ)).re ≤ massAllowance r e L j := by
  have ha := goodPrefix_accuracy B (dyadicLower L) decode ρ (stageAccuracy e L) j.val h hh
  have hm := MultiscaleEstimator.current_mass_le_allowance B L ρ (records decode j.val h) hr j ha
  simpa only [state, MultiscaleExecutionFacts.activeAt, MultiscaleExecutionFacts.basisAt] using hm

theorem allGood_chiB (hd : ∀ k, Measurable (decode k)) (ρ : Density ι)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hL : L=dyadicStages (Fintype.card ι) (ε/16)) (h : History PUnit Ω L)
    (hh : h ∈ StagePolicy.goodPrefix
      (good B (dyadicLower L) decode ρ (stageAccuracy (ε/16) L)) L) :
    chiB ρ ((estimator B (dyadicLower L) decode hd (dyadicLower_pos L)).estimate h) ≤
      ENNReal.ofReal ε := by
  apply le_of_lt
  exact actual_chiB_epsilon B L ρ (records decode L h) hε hε1 hL
    (fun j => goodPrefix_accuracy B (dyadicLower L) decode ρ (stageAccuracy (ε/16) L) L h hh j j.isLt)

theorem allocated_failure_sum {δ : ℝ} (hδ : 0 ≤ δ) :
    (∑ _j ∈ Finset.range L, ENNReal.ofReal (δ/(L : ℝ))) = ENNReal.ofReal δ := by
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg L)]
  congr 1
  have hL : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  field_simp

/-- A genuine sequential policy needs a routine bound only on successful
past histories. This generic theorem derives simultaneous accuracy and the
actual density output's chiB event; quantum policies are instantiated with
their actual Born transitions by the upper-bound constructions. -/
theorem policy_success (hd : ∀ k, Measurable (decode k))
    (P : StagePolicy.Policy PUnit Ω L) (ρ : Density ι)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 ≤ δ)
    (hL : L=dyadicStages (Fintype.card ι) (ε/16))
    (hc : ∀ k (hk : k<L) h,
      h ∈ StagePolicy.goodPrefix
        (good B (dyadicLower L) decode ρ (stageAccuracy (ε/16) L)) k →
      P.transition ⟨k,hk⟩ h
        {y | (h,y) ∉ good B (dyadicLower L) decode ρ (stageAccuracy (ε/16) L) k} ≤
          ENNReal.ofReal (δ/(L : ℝ))) :
    1-ENNReal.ofReal δ ≤ P.transcriptLaw
      {h | chiB ρ ((estimator B (dyadicLower L) decode hd (dyadicLower_pos L)).estimate h) ≤
        ENNReal.ofReal ε} := by
  have hp := P.allGood_probability_ge
    (good B (dyadicLower L) decode ρ (stageAccuracy (ε/16) L))
    (measurableSet_good B (dyadicLower L) decode hd ρ (stageAccuracy (ε/16) L))
    (fun _ => ENNReal.ofReal (δ/(L : ℝ))) hc
  rw [allocated_failure_sum hδ] at hp
  apply hp.trans
  exact measure_mono fun h hh => allGood_chiB B decode hd ρ hε hε1 hL h hh

end Nonempty
end Paper26.MultiscalePolicy
