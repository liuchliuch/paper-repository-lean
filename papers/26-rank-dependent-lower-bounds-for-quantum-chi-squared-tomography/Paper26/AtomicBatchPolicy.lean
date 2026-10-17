import Paper26.FrozenOneCopyBlock

/-! Compile finite measurable batch policies into genuine atomic one-copy
protocols.  A copy reads only the completed earlier batches.  The resulting
protocol has `L * B` fresh-copy steps; a batch is never counted as one copy. -/

noncomputable section

namespace Paper26.AtomicBatchPolicy

open MeasureTheory ProbabilityTheory QuantumModel ContinuousPOVM AdaptiveModel
open FrozenOneCopyBlock OneCopyStageComposition
open scoped BigOperators ENNReal

universe u

variable {Ω State : Type u} [MeasurableSpace Ω] [MeasurableSpace State]

abbrev MacroHistory (B : ℕ) (Ω : Type u) := History PUnit (Fin B → Ω)

/-- Chronological regrouping of exactly `j` complete batches. -/
def batchHistory (B : ℕ) : (j : ℕ) → History PUnit Ω (j * B) ≃ᵐ MacroHistory B Ω j
  | 0 => historyCast (Nat.zero_mul B)
  | j + 1 => (historyCast (Nat.succ_mul j B)).trans
      ((historyTail (j * B) B).trans ((historyCoordinates B).trans
        ((batchHistory B j).prodCongr (MeasurableEquiv.refl (Fin B → Ω)))))

def copyIndex {L B : ℕ} (j : Fin L) (k : Fin B) : Fin (L * B) :=
  ⟨j.val * B + k.val, by
    have h := (finProdFinEquiv (j, k)).isLt
    simpa only [finProdFinEquiv, Nat.add_comm, Nat.mul_comm] using h⟩

theorem copyIndex_eq {L B : ℕ} (j : Fin L) (k : Fin B) :
    copyIndex j k = finProdFinEquiv (j, k) := by
  apply Fin.ext
  change j.val * B + k.val = k.val + B * j.val
  ac_rfl

def position {L B : ℕ} (k : Fin (L * B)) : Fin L × Fin B := finProdFinEquiv.symm k

theorem position_copyIndex {L B : ℕ} (j : Fin L) (k : Fin B) :
    position (copyIndex j k) = (j, k) := by
  rw [copyIndex_eq]
  exact finProdFinEquiv.symm_apply_apply _

theorem position_val {L B : ℕ} (k : Fin (L * B)) :
    k.val = (position k).1.val * B + (position k).2.val := by
  have h := congrArg Fin.val (finProdFinEquiv.apply_symm_apply k)
  change (position k).2.val + B * (position k).1.val = k.val at h
  simpa only [Nat.add_comm, Nat.mul_comm] using h.symm

def copyEquiv (L B : ℕ) : Fin L × Fin B ≃ Fin (L * B) where
  toFun p := copyIndex p.1 p.2
  invFun := position
  left_inv p := position_copyIndex p.1 p.2
  right_inv k := by
    change copyIndex (position k).1 (position k).2 = k
    rw [copyIndex_eq]
    exact finProdFinEquiv.apply_symm_apply k

def pairControl {L B : ℕ} (state : ∀ j : Fin L, MacroHistory B Ω j.val → State)
    (p : Fin L × Fin B) : History PUnit Ω (copyIndex p.1 p.2).val → State :=
  state p.1 ∘ batchHistory B p.1.val ∘ initial p.2.val ∘ historyTail (p.1.val * B) p.2.val

/-- The parameter for a copy is computed only from the completed batches;
the currently accumulating batch is absent from this function's input. -/
def control {L B : ℕ} (state : ∀ j : Fin L, MacroHistory B Ω j.val → State)
    (k : Fin (L * B)) : History PUnit Ω k.val → State :=
  Equiv.piCongrLeft (fun k : Fin (L * B) => History PUnit Ω k.val → State)
    (copyEquiv L B) (pairControl state) k

theorem measurable_control {L B : ℕ}
    (state : ∀ j : Fin L, MacroHistory B Ω j.val → State)
    (hs : ∀ j, Measurable (state j)) (k : Fin (L * B)) : Measurable (control state k) := by
  obtain ⟨p, rfl⟩ := (copyEquiv L B).surjective k
  simp only [control, Equiv.piCongrLeft_apply_apply]
  exact (hs _).comp ((batchHistory B _).measurable.comp ((measurable_initial _).comp
    (historyTail _ _).measurable))

omit [MeasurableSpace State] in
theorem control_frozen {L B : ℕ}
    (state : ∀ j : Fin L, MacroHistory B Ω j.val → State) (j : Fin L) (k : Fin B) :
    control state (copyIndex j k) ∘ (historyTail (j.val * B) k.val).symm =
      state j ∘ batchHistory B j.val ∘ initial k.val := by
  funext h
  change control state (copyEquiv L B (j, k)) ((historyTail (j.val * B) k.val).symm h) = _
  simp only [control, Equiv.piCongrLeft_apply_apply, pairControl, Function.comp_apply]
  rw [MeasurableEquiv.apply_symm_apply]

theorem pullbackStep_pullback {ι H H' H'' : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace H] [MeasurableSpace H'] [MeasurableSpace H'']
    (M : OneCopyStep ι H Ω) (f : H' → H) (hf : Measurable f)
    (g : H'' → H') (hg : Measurable g) :
    StagePolicy.pullbackStep (StagePolicy.pullbackStep M f hf) g hg =
      StagePolicy.pullbackStep M (f ∘ g) (hf.comp hg) := rfl

theorem pullbackStep_congr {ι H H' : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace H] [MeasurableSpace H'] (M : OneCopyStep ι H Ω)
    {f g : H' → H} (hf : Measurable f) (hg : Measurable g) (h : f = g) :
    StagePolicy.pullbackStep M f hf = StagePolicy.pullbackStep M g hg := by
  cases h
  rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {L B : ℕ}

/-- The actual atomic learner, with no statistical assumption in its
construction.  The estimator sees the complete chronological batch history. -/
def learner (M : OneCopyStep ι State Ω)
    (state : ∀ j : Fin L, MacroHistory B Ω j.val → State)
    (hs : ∀ j, Measurable (state j)) (T : Estimator ι (MacroHistory B Ω L)) :
    AdaptiveModel.Learner ι PUnit Ω (L * B) where
  seed := Measure.dirac PUnit.unit
  seed_probability := inferInstance
  step := fun k => StagePolicy.pullbackStep M (control state k) (measurable_control state hs k)
  estimator := ⟨T.estimate ∘ batchHistory B L, T.measurable_estimate.comp (batchHistory B L).measurable⟩

def stageStep (M : OneCopyStep ι State Ω)
    (state : ∀ j : Fin L, MacroHistory B Ω j.val → State)
    (hs : ∀ j, Measurable (state j)) (j : Fin L) :
    OneCopyStep ι (History PUnit Ω (j.val * B)) Ω :=
  StagePolicy.pullbackStep M (state j ∘ batchHistory B j.val)
    ((hs j).comp (batchHistory B j.val).measurable)

/-- The frozen physical step identity is proved from the compiled control;
it is not a field or a caller-supplied law assumption. -/
theorem learner_frozen_step (M : OneCopyStep ι State Ω)
    (state : ∀ j : Fin L, MacroHistory B Ω j.val → State)
    (hs : ∀ j, Measurable (state j)) (T : Estimator ι (MacroHistory B Ω L))
    (j : Fin L) (k : Fin B) :
    StagePolicy.pullbackStep ((learner M state hs T).step (copyIndex j k))
        (historyTail (j.val * B) k.val).symm (MeasurableEquiv.measurable _) =
      StagePolicy.pullbackStep (stageStep M state hs j)
        (initial k.val) (measurable_initial k.val) := by
  change StagePolicy.pullbackStep
    (StagePolicy.pullbackStep M (control state (copyIndex j k)) _)
      (historyTail (j.val * B) k.val).symm _ = _
  rw [pullbackStep_pullback]
  change StagePolicy.pullbackStep M (control state (copyIndex j k) ∘
    (historyTail (j.val * B) k.val).symm) _ =
      StagePolicy.pullbackStep M ((state j ∘ batchHistory B j.val) ∘ initial k.val)
        (((hs j).comp (batchHistory B j.val).measurable).comp (measurable_initial k.val))
  exact pullbackStep_congr M _ _ (control_frozen state j k)

theorem learner_interval_tupleLaw (M : OneCopyStep ι State Ω)
    (state : ∀ j : Fin L, MacroHistory B Ω j.val → State)
    (hs : ∀ j, Measurable (state j)) (T : Estimator ι (MacroHistory B Ω L))
    (ρ : Density ι) (j : Fin L) (h : History PUnit Ω (j.val * B)) :
    (intervalKernel (learner M state hs T) ρ (j.val * B) B (by
      have hh := Nat.mul_le_mul_right B (Nat.succ_le_of_lt j.isLt)
      simpa only [Nat.succ_mul] using hh) h).map (intervalSamples (j.val * B) B) =
      Measure.pi (fun _ : Fin B => M.bornKernel ρ (state j (batchHistory B j.val h))) := by
  rw [intervalKernel_tupleLaw (M := stageStep M state hs j)]
  · simp only [stageStep, StagePolicy.pullbackStep_bornKernel, Kernel.comap_apply,
      Function.comp_apply]
  · intro k hk
    exact learner_frozen_step M state hs T j ⟨k, hk⟩

/-- The actual macro policy uses the sequentially constructed `B`-copy
block kernel, not an assumed product experiment. -/
def macroPolicy (M : OneCopyStep ι State Ω)
    (state : ∀ j : Fin L, MacroHistory B Ω j.val → State)
    (hs : ∀ j, Measurable (state j)) (ρ : Density ι) :
    StagePolicy.Policy PUnit (Fin B → Ω) L where
  seed := Measure.dirac PUnit.unit
  seed_probability := inferInstance
  transition := fun j => StagePolicy.quantumBlockKernel
    (StagePolicy.pullbackStep M (state j) (hs j)) ρ B
  transition_markov := fun _ => inferInstance

theorem historyCast_symm {Seed : Type u} [MeasurableSpace Seed] {a b : ℕ} (h : a = b) :
    (historyCast (Seed := Seed) (Ω := Ω) h).symm = historyCast h.symm := by
  cases h
  rfl

def nextBatchMap (B j : ℕ) : History PUnit Ω (j * B + B) → MacroHistory B Ω (j + 1) :=
  batchHistory B (j + 1) ∘ historyCast (Nat.succ_mul j B).symm

theorem nextBatchMap_eq (B j : ℕ) : nextBatchMap (Ω := Ω) B j =
    ((batchHistory B j).prodCongr (MeasurableEquiv.refl (Fin B → Ω))) ∘
      historyCoordinates B ∘ historyTail (j * B) B := by
  funext h
  change ((batchHistory B j).prodCongr (MeasurableEquiv.refl (Fin B → Ω)))
    (historyCoordinates B (historyTail (j * B) B
      (historyCast (Nat.succ_mul j B) (historyCast (Nat.succ_mul j B).symm h)))) = _
  rw [← historyCast_symm (Nat.succ_mul j B), MeasurableEquiv.apply_symm_apply]
  rfl

theorem pathKernel_map_coordinates {H : Type u} [MeasurableSpace H]
    (κ : Kernel H Ω) [IsMarkovKernel κ] (n : ℕ) :
    (pathKernel κ n).map (historyCoordinates n) = jointKernel κ n := by
  rw [pathKernel, ← Kernel.map_comp_right _ (MeasurableEquiv.measurable _)
    (MeasurableEquiv.measurable _), MeasurableEquiv.self_comp_symm, Kernel.map_id]

theorem jointKernel_comap_map {H H' : Type u} [MeasurableSpace H] [MeasurableSpace H']
    (κ : Kernel H Ω) [IsMarkovKernel κ] (f : H' → H) (hf : Measurable f) (n : ℕ) :
    (jointKernel (κ.comap f hf) n).map (Prod.map f id) = (jointKernel κ n).comap f hf := by
  apply Kernel.ext
  intro h
  rw [Kernel.map_apply _ (hf.prodMap measurable_id), jointKernel, Kernel.prod_apply,
    Kernel.id_apply, ← Measure.map_prod_map _ _ hf measurable_id,
    Measure.map_dirac hf, Measure.map_id, Kernel.comap_apply, jointKernel,
    Kernel.prod_apply, Kernel.id_apply, StagePolicy.tupleKernel_apply,
    StagePolicy.tupleKernel_apply]
  rfl

/-- The kernel taking an actual atomic boundary to the next macro history
is exactly the macro policy's next append kernel. -/
theorem learner_interval_macroKernel (M : OneCopyStep ι State Ω)
    (state : ∀ j : Fin L, MacroHistory B Ω j.val → State)
    (hs : ∀ j, Measurable (state j)) (T : Estimator ι (MacroHistory B Ω L))
    (ρ : Density ι) (j : Fin L) :
    (intervalKernel (learner M state hs T) ρ (j.val * B) B (by
      simpa only [Nat.succ_mul] using Nat.mul_le_mul_right B (Nat.succ_le_of_lt j.isLt))).map
        (nextBatchMap B j.val) =
      (Kernel.id.prod ((macroPolicy M state hs ρ).transition j)).comap
        (batchHistory B j.val) (MeasurableEquiv.measurable _) := by
  have hi := intervalKernel_historyTail (learner M state hs T) ρ (j.val * B) B
    (by simpa only [Nat.succ_mul] using Nat.mul_le_mul_right B (Nat.succ_le_of_lt j.isLt))
    (stageStep M state hs j) (fun k hk => learner_frozen_step M state hs T j ⟨k, hk⟩)
    B (le_refl B)
  rw [nextBatchMap_eq]
  change (intervalKernel (learner M state hs T) ρ (j.val * B) B _).map
    ((((batchHistory B j.val).prodCongr (MeasurableEquiv.refl (Fin B → Ω))) ∘
      historyCoordinates B) ∘ historyTail (j.val * B) B) = _
  rw [Kernel.map_comp_right _ (MeasurableEquiv.measurable _)
    (((batchHistory B j.val).prodCongr (MeasurableEquiv.refl (Fin B → Ω))).measurable.comp
      (historyCoordinates B).measurable), hi,
    Kernel.map_comp_right _ (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _),
    pathKernel_map_coordinates]
  have hb : (stageStep M state hs j).bornKernel ρ =
      ((StagePolicy.pullbackStep M (state j) (hs j)).bornKernel ρ).comap
        (batchHistory B j.val) (MeasurableEquiv.measurable _) := by
    exact StagePolicy.pullbackStep_bornKernel
      (StagePolicy.pullbackStep M (state j) (hs j)) (batchHistory B j.val)
        (MeasurableEquiv.measurable _) ρ
  rw [hb]
  exact jointKernel_comap_map _ _ _ _

theorem learner_batch_prefixLaw (M : OneCopyStep ι State Ω)
    (state : ∀ j : Fin L, MacroHistory B Ω j.val → State)
    (hs : ∀ j, Measurable (state j)) (T : Estimator ι (MacroHistory B Ω L))
    (ρ : Density ι) (j : ℕ) (hj : j ≤ L) :
    ((learner M state hs T).prefixLaw ρ (j * B) (Nat.mul_le_mul_right B hj)).map
      (batchHistory B j) = (macroPolicy M state hs ρ).prefixLaw j hj := by
  induction j with
  | zero =>
      exact prefixLaw_map_historyCast (learner M state hs T) ρ (Nat.zero_mul B)
        (Nat.mul_le_mul_right B hj) (Nat.zero_le _)
  | succ j ih =>
      let A := learner M state hs T
      letI := (macroPolicy M state hs ρ).transition_markov ⟨j, by omega⟩
      have hbound : j * B + B ≤ L * B := by
        simpa only [Nat.succ_mul] using Nat.mul_le_mul_right B hj
      have hp := prefixLaw_map_historyCast A ρ (Nat.succ_mul j B).symm hbound
        (Nat.mul_le_mul_right B hj)
      rw [← hp, Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _),
        ← intervalKernel_comp_prefixLaw A ρ (j * B) B hbound,
        Measure.map_comp _ _ ((batchHistory B (j + 1)).measurable.comp
          (historyCast (Nat.succ_mul j B).symm).measurable)]
      change ((intervalKernel A ρ (j * B) B hbound).map (nextBatchMap B j)) ∘ₘ _ = _
      rw [learner_interval_macroKernel M state hs T ρ ⟨j, by omega⟩,
        ← Kernel.comp_deterministic_eq_comap, ← Measure.comp_assoc,
        Measure.deterministic_comp_eq_map (MeasurableEquiv.measurable _), ih (by omega)]
      exact (Measure.compProd_eq_comp_prod _ _).symm

theorem learner_batch_transcriptLaw (M : OneCopyStep ι State Ω)
    (state : ∀ j : Fin L, MacroHistory B Ω j.val → State)
    (hs : ∀ j, Measurable (state j)) (T : Estimator ι (MacroHistory B Ω L)) (ρ : Density ι) :
    ((learner M state hs T).transcriptLaw ρ).map (batchHistory B L) =
      (macroPolicy M state hs ρ).transcriptLaw :=
  learner_batch_prefixLaw M state hs T ρ L (le_refl L)

theorem learner_successProbability (M : OneCopyStep ι State Ω)
    (state : ∀ j : Fin L, MacroHistory B Ω j.val → State)
    (hs : ∀ j, Measurable (state j)) (T : Estimator ι (MacroHistory B Ω L))
    (ρ : Density ι) (loss : Density ι → Density ι → ℝ≥0∞) (ε : ℝ≥0∞)
    (hm : MeasurableSet {z : MacroHistory B Ω L | loss ρ (T.estimate z) ≤ ε}) :
    (learner M state hs T).successProbability loss ρ ε =
      (macroPolicy M state hs ρ).transcriptLaw {z | loss ρ (T.estimate z) ≤ ε} := by
  rw [← learner_batch_transcriptLaw M state hs T ρ,
    Measure.map_apply (MeasurableEquiv.measurable _) hm]
  rfl

theorem learner_learnsRank_iff (M : OneCopyStep ι State Ω)
    (state : ∀ j : Fin L, MacroHistory B Ω j.val → State)
    (hs : ∀ j, Measurable (state j)) (T : Estimator ι (MacroHistory B Ω L))
    (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε q : ℝ≥0∞) :
    (learner M state hs T).LearnsRank loss r ε q ↔
      ∀ ρ : Density ι, ρ.matrix.rank ≤ r →
        MeasurableSet {z : MacroHistory B Ω L | loss ρ (T.estimate z) ≤ ε} ∧
          q ≤ (macroPolicy M state hs ρ).transcriptLaw {z | loss ρ (T.estimate z) ≤ ε} := by
  constructor
  · intro h ρ hr
    have hm : MeasurableSet {z : MacroHistory B Ω L | loss ρ (T.estimate z) ≤ ε} :=
      (batchHistory B L).measurableSet_preimage.mp (h ρ hr).1
    exact ⟨hm, by simpa only [learner_successProbability M state hs T ρ loss ε hm] using (h ρ hr).2⟩
  · intro h ρ hr
    refine ⟨(h ρ hr).1.preimage (batchHistory B L).measurable, ?_⟩
    rw [learner_successProbability M state hs T ρ loss ε (h ρ hr).1]
    exact (h ρ hr).2

section UpdateRecursion

/-- A measurable finite-stage state update generates the classical policy
recursively from its initial state and its actually observed batch tuples. -/
def stateFromUpdate (s₀ : State) (update : ℕ → State × (Fin B → Ω) → State) :
    (j : ℕ) → MacroHistory B Ω j → State
  | 0, _ => s₀
  | j + 1, h => update j (stateFromUpdate s₀ update j h.1, h.2)

theorem measurable_stateFromUpdate (s₀ : State)
    (update : ℕ → State × (Fin B → Ω) → State) (hu : ∀ j, Measurable (update j)) (j : ℕ) :
    Measurable (stateFromUpdate s₀ update j) := by
  induction j with
  | zero => exact measurable_const
  | succ j ih => exact (hu j).comp ((ih.comp measurable_fst).prodMk measurable_snd)

/-- A complete operational compiler from measurable state updates and a
measurable actual density output, with exactly `L * B` one-copy rounds. -/
def learnerOfUpdate (M : OneCopyStep ι State Ω) (s₀ : State)
    (update : ℕ → State × (Fin B → Ω) → State) (hu : ∀ j, Measurable (update j))
    (output : State → Density ι) (ho : Measurable output) :
    AdaptiveModel.Learner ι PUnit Ω (L * B) :=
  learner M (fun j => stateFromUpdate s₀ update j.val)
    (fun j => measurable_stateFromUpdate s₀ update hu j.val)
    ⟨output ∘ stateFromUpdate s₀ update L,
      ho.comp (measurable_stateFromUpdate s₀ update hu L)⟩

end UpdateRecursion

section Raw
variable [Nonempty ι]

def operatorLearner (M : OneCopyStep ι State Ω)
    (state : ∀ j : Fin L, MacroHistory B Ω j.val → State)
    (hs : ∀ j, Measurable (state j)) (T : Estimator ι (MacroHistory B Ω L)) :
    AdaptiveOperatorModelTransport.OperatorLearner ι PUnit Ω (L * B) :=
  StagePolicy.operatorLearner (learner M state hs T)

theorem operatorLearner_successProbability (M : OneCopyStep ι State Ω)
    (state : ∀ j : Fin L, MacroHistory B Ω j.val → State)
    (hs : ∀ j, Measurable (state j)) (T : Estimator ι (MacroHistory B Ω L))
    (R : CollectiveModel.OperatorRadonNikodymInput ι Ω) (ρ : Density ι)
    (loss : Density ι → Density ι → ℝ≥0∞) (ε : ℝ≥0∞)
    (hm : MeasurableSet {z : MacroHistory B Ω L | loss ρ (T.estimate z) ≤ ε}) :
    (operatorLearner M state hs T).successProbability R loss ρ ε =
      (macroPolicy M state hs ρ).transcriptLaw {z | loss ρ (T.estimate z) ≤ ε} := by
  rw [operatorLearner, StagePolicy.operatorLearner_successProbability,
    learner_successProbability M state hs T ρ loss ε hm]

end Raw

section SourceMinimum

variable {ι Ω State : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace Ω] [MeasurableSpace State] {L B : ℕ}

theorem Nonecopy_le (M : OneCopyStep ι State Ω)
    (state : ∀ j : Fin L, MacroHistory B Ω j.val → State)
    (hs : ∀ j, Measurable (state j)) (T : Estimator ι (MacroHistory B Ω L))
    (RN : SourceCopyComplexity.AllFixedOperatorRN ι)
    (loss : Density ι → Density ι → ℝ≥0∞) (r : ℕ) (ε : ℝ≥0∞)
    (h : ∀ ρ : Density ι, ρ.matrix.rank ≤ r →
      MeasurableSet {z : MacroHistory B Ω L | loss ρ (T.estimate z) ≤ ε} ∧
        (2 : ℝ≥0∞) / 3 ≤ (macroPolicy M state hs ρ).transcriptLaw
          {z | loss ρ (T.estimate z) ≤ ε}) :
    SourceCopyComplexity.Nonecopy RN loss r ε ≤ (L * B : ℕ) :=
  StagePolicy.Nonecopy_le (learner M state hs T) RN loss r ε
    ((learner_learnsRank_iff M state hs T loss r ε _).mpr h)

end SourceMinimum

end Paper26.AtomicBatchPolicy
