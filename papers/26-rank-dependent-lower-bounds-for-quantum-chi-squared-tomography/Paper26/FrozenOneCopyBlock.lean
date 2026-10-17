import Paper26.OneCopyStageComposition
import Mathlib.Probability.Kernel.Composition.Lemmas

/-! A stage holds its classical measurement parameter fixed while consuming
its prescribed number of fresh copies.  Its full path kernel is proved equal
to sequential actual one-copy transitions, and its tuple marginal is the
conditional product of actual Born laws. -/

noncomputable section

namespace Paper26.FrozenOneCopyBlock

open MeasureTheory ProbabilityTheory QuantumModel ContinuousPOVM AdaptiveModel
open scoped BigOperators ENNReal

universe u

variable {H Ω : Type u} [MeasurableSpace H] [MeasurableSpace Ω]

def appendCoordinates (n : ℕ) : ((H × (Fin n → Ω)) × Ω) ≃ᵐ (H × (Fin (n + 1) → Ω)) :=
  MeasurableEquiv.prodAssoc.trans
    ((MeasurableEquiv.refl H).prodCongr (OneCopyProductProtocol.tupleSplit n).symm)

/-- Retain the initial stage history together with its newly observed tuple. -/
def historyCoordinates : (n : ℕ) → History H Ω n ≃ᵐ (H × (Fin n → Ω))
  | 0 =>
    { toEquiv :=
        { toFun := fun h => (h, fun i => Fin.elim0 i)
          invFun := Prod.fst
          left_inv := fun _ => rfl
          right_inv := fun p => by
            apply Prod.ext
            · rfl
            · funext i
              exact Fin.elim0 i }
      measurable_toFun := measurable_id.prodMk measurable_const
      measurable_invFun := measurable_fst }
  | n + 1 => ((historyCoordinates n).prodCongr (MeasurableEquiv.refl Ω)).trans
      (appendCoordinates n)

def initial (n : ℕ) (h : History H Ω n) : H := (historyCoordinates n h).1
def samples (n : ℕ) (h : History H Ω n) : Fin n → Ω := (historyCoordinates n h).2

theorem measurable_initial (n : ℕ) : Measurable (initial (H := H) (Ω := Ω) n) :=
  measurable_fst.comp (historyCoordinates n).measurable

theorem measurable_samples (n : ℕ) : Measurable (samples (H := H) (Ω := Ω) n) :=
  measurable_snd.comp (historyCoordinates n).measurable

def jointKernel (κ : Kernel H Ω) (n : ℕ) : Kernel H (H × (Fin n → Ω)) :=
  Kernel.id.prod (StagePolicy.tupleKernel κ n)

instance jointKernel_markov (κ : Kernel H Ω) [IsMarkovKernel κ] (n : ℕ) :
    IsMarkovKernel (jointKernel κ n) := by
  unfold jointKernel
  infer_instance

theorem tupleKernel_succ_prod (κ : Kernel H Ω) [IsMarkovKernel κ] (n : ℕ) :
    StagePolicy.tupleKernel κ (n + 1) =
      ((StagePolicy.tupleKernel κ n).prod κ).map (OneCopyProductProtocol.tupleSplit n).symm := by
  apply Kernel.ext
  intro h
  rw [StagePolicy.tupleKernel_succ, Kernel.map_apply _ (MeasurableEquiv.measurable _),
    Kernel.prod_apply]

theorem jointKernel_succ (κ : Kernel H Ω) [IsMarkovKernel κ] (n : ℕ) :
    ((jointKernel κ n).prod κ).map (appendCoordinates n) = jointKernel κ (n + 1) := by
  have hm : (appendCoordinates (H := H) (Ω := Ω) n :
      ((H × (Fin n → Ω)) × Ω) → H × (Fin (n + 1) → Ω)) =
      (Prod.map id (OneCopyProductProtocol.tupleSplit n).symm) ∘
        MeasurableEquiv.prodAssoc := rfl
  rw [hm, Kernel.map_comp_right _ (MeasurableEquiv.measurable _)
    ((measurable_id).prodMap (MeasurableEquiv.measurable _)), jointKernel,
    Kernel.prodAssoc_prod]
  rw [← Kernel.map_prod_map _ _ measurable_id (MeasurableEquiv.measurable _),
    Kernel.map_id, ← tupleKernel_succ_prod]
  rfl

/-- The next physical measurement uses the original stage history, which
is still present as the first component of the current path coordinates. -/
def advance (κ : Kernel H Ω) (n : ℕ) : Kernel (History H Ω n) (History H Ω (n + 1)) :=
  Kernel.id.prod (κ.comap (initial n) (measurable_initial n))

instance advance_markov (κ : Kernel H Ω) [IsMarkovKernel κ] (n : ℕ) :
    IsMarkovKernel (advance κ n) :=
  Kernel.IsMarkovKernel.prod Kernel.id _

theorem advance_apply (κ : Kernel H Ω) [IsMarkovKernel κ] (n : ℕ)
    (x : History H Ω n) : advance κ n x =
      (Measure.dirac x).prod (κ (initial n x)) := by
  exact (Kernel.prod_apply (Kernel.id : Kernel (History H Ω n) (History H Ω n))
    (κ.comap (initial n) (measurable_initial n)) x).trans (by
      rw [Kernel.id_apply, Kernel.comap_apply])

def pathKernel (κ : Kernel H Ω) (n : ℕ) : Kernel H (History H Ω n) :=
  (jointKernel κ n).map (historyCoordinates n).symm

instance pathKernel_markov (κ : Kernel H Ω) [IsMarkovKernel κ] (n : ℕ) :
    IsMarkovKernel (pathKernel κ n) :=
  Kernel.IsMarkovKernel.map _ (MeasurableEquiv.measurable _)

theorem advance_coordinates (κ : Kernel H Ω) [IsMarkovKernel κ] (n : ℕ) :
    ((advance κ n).comap (historyCoordinates n).symm (MeasurableEquiv.measurable _)).map
      (historyCoordinates (n + 1)) =
      (Kernel.id.prod (κ.prodMkRight (Fin n → Ω))).map (appendCoordinates n) := by
  apply Kernel.ext
  intro x
  apply Measure.ext
  intro S hS
  have hR := Kernel.prod_apply
    (Kernel.id : Kernel (H × (Fin n → Ω)) (H × (Fin n → Ω)))
      (κ.prodMkRight (Fin n → Ω)) x
  have hmapL : ((κ (initial n ((historyCoordinates n).symm x))).map
      (Prod.mk ((historyCoordinates n).symm x)))
        ((historyCoordinates (n + 1)) ⁻¹' S) =
      κ (initial n ((historyCoordinates n).symm x))
        (Prod.mk ((historyCoordinates n).symm x) ⁻¹'
          ((historyCoordinates (n + 1)) ⁻¹' S)) :=
    Measure.map_apply (measurable_const.prodMk measurable_id)
      ((historyCoordinates (n + 1)).measurable hS)
  have hmapR : (((κ.prodMkRight (Fin n → Ω)) x).map (Prod.mk x))
      ((appendCoordinates n) ⁻¹' S) =
      (κ.prodMkRight (Fin n → Ω)) x (Prod.mk x ⁻¹' ((appendCoordinates n) ⁻¹' S)) :=
    Measure.map_apply (measurable_const.prodMk measurable_id)
      ((appendCoordinates n).measurable hS)
  rw [Kernel.map_apply' _ (MeasurableEquiv.measurable _) _ hS, Kernel.comap_apply,
    advance_apply, Measure.dirac_prod]
  erw [hmapL]
  rw [Kernel.map_apply' _ (MeasurableEquiv.measurable _) _ hS,
    hR, Kernel.id_apply, Measure.dirac_prod,
    hmapR, Kernel.prodMkRight_apply]
  simp only [initial, MeasurableEquiv.apply_symm_apply]
  congr 1
  ext y
  change appendCoordinates n (historyCoordinates n ((historyCoordinates n).symm x), y) ∈ S ↔
    appendCoordinates n (x, y) ∈ S
  rw [MeasurableEquiv.apply_symm_apply]

theorem advance_joint (κ : Kernel H Ω) [IsMarkovKernel κ] (n : ℕ) :
    (Kernel.id.prod (κ.prodMkRight (Fin n → Ω))).comp (jointKernel κ n) =
      (jointKernel κ n).prod κ := by
  have he := Kernel.prod_prodMkRight_comp_deterministic_prod (StagePolicy.tupleKernel κ n)
    κ Kernel.id (f := id) measurable_id
  change (Kernel.id.prod (κ.prodMkRight (Fin n → Ω))).comp (jointKernel κ n) =
    (Kernel.id.comp (jointKernel κ n)).prod (κ.comp Kernel.id) at he
  simpa only [Kernel.id_comp, Kernel.comp_id] using he

/-- The full path kernel is obtained by the actual sequential transitions. -/
theorem pathKernel_succ (κ : Kernel H Ω) [IsMarkovKernel κ] (n : ℕ) :
    (advance κ n).comp (pathKernel κ n) = pathKernel κ (n + 1) := by
  apply (Kernel.map_apply_eq_iff_map_symm_apply_eq
    ((advance κ n).comp (pathKernel κ n)) (f := historyCoordinates (n + 1))
      (jointKernel κ (n + 1))).mp
  rw [pathKernel, Kernel.map_comp, Kernel.comp_map _ _ (MeasurableEquiv.measurable _),
    Kernel.comap_map_comm _ (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _),
    advance_coordinates, ← Kernel.map_comp, advance_joint,
    jointKernel_succ]

theorem pathKernel_zero (κ : Kernel H Ω) [IsMarkovKernel κ] : pathKernel κ 0 = Kernel.id := by
  apply Kernel.ext
  intro h
  rw [pathKernel, Kernel.map_apply _ (MeasurableEquiv.measurable _),
    jointKernel, Kernel.prod_apply, Kernel.id_apply]
  change ((Measure.dirac h).prod (Measure.dirac (fun i : Fin 0 => Fin.elim0 i))).map
    (historyCoordinates 0).symm = Measure.dirac h
  rw [Measure.dirac_prod_dirac, Measure.map_dirac (MeasurableEquiv.measurable _)]
  rfl

/-- The exact tuple marginal of the actual block path. -/
theorem pathKernel_samples (κ : Kernel H Ω) [IsMarkovKernel κ] (n : ℕ) (h : H) :
    (pathKernel κ n h).map (samples n) = Measure.pi (fun _ : Fin n => κ h) := by
  rw [pathKernel, Kernel.map_apply _ (MeasurableEquiv.measurable _),
    Measure.map_map (measurable_samples n) (MeasurableEquiv.measurable _)]
  have he : samples (H := H) (Ω := Ω) n ∘ (historyCoordinates n).symm = Prod.snd := by
    funext x
    simp only [Function.comp_apply, samples, MeasurableEquiv.apply_symm_apply]
  rw [he, jointKernel, Kernel.prod_apply, Measure.map_snd_prod, measure_univ, one_smul]
  exact StagePolicy.tupleKernel_apply _ _ _

section Quantum

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- The actual block learner uses one fresh copy at every step, retaining
the initial stage history as its frozen classical measurement parameter. -/
def learner (M : OneCopyStep ι H Ω) (η : Measure H) (hη : IsProbabilityMeasure η)
    (T : Estimator ι (History H Ω N)) : AdaptiveModel.Learner ι H Ω N where
  seed := η
  seed_probability := hη
  step := fun k => StagePolicy.pullbackStep M (initial k.val) (measurable_initial k.val)
  estimator := T

theorem learner_prefixLaw (M : OneCopyStep ι H Ω) (η : Measure H)
    (hη : IsProbabilityMeasure η) (T : Estimator ι (History H Ω N))
    (ρ : Density ι) (k : ℕ) (hk : k ≤ N) :
    (learner M η hη T).prefixLaw ρ k hk = pathKernel (M.bornKernel ρ) k ∘ₘ η := by
  letI := hη
  induction k with
  | zero => rw [pathKernel_zero]; exact Measure.id_comp.symm
  | succ k ih =>
      change ((learner M η hη T).prefixLaw ρ k
        (Nat.le_trans (Nat.le_succ k) hk)).compProd
          ((StagePolicy.pullbackStep M (initial k) (measurable_initial k)).bornKernel ρ) = _
      rw [StagePolicy.pullbackStep_bornKernel, Measure.compProd_eq_comp_prod]
      change advance (M.bornKernel ρ) k ∘ₘ
        (learner M η hη T).prefixLaw ρ k _ = _
      rw [ih _, Measure.comp_assoc, pathKernel_succ]

/-- Conditional on any fixed stage history, the actual learner's new tuple
has the product Born law.  The theorem also covers `N = 0`. -/
theorem learner_tupleLaw (M : OneCopyStep ι H Ω) (h : H)
    (T : Estimator ι (History H Ω N)) (ρ : Density ι) :
    ((learner M (Measure.dirac h) inferInstance T).transcriptLaw ρ).map (samples N) =
      Measure.pi (fun _ : Fin N => M.bornKernel ρ h) := by
  change ((learner M (Measure.dirac h) inferInstance T).prefixLaw ρ N
    (le_refl N)).map (samples N) = _
  rw [learner_prefixLaw, Measure.dirac_bind (Kernel.measurable _) h]
  exact pathKernel_samples _ _ _

end Quantum

section GlobalInterval

variable {Seed : Type u} [MeasurableSpace Seed]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- Regroup an ordinary full transcript into a stage-entry history followed
by the outcomes observed since that boundary. -/
def historyTail (a : ℕ) : (k : ℕ) →
    History Seed Ω (a + k) ≃ᵐ History (History Seed Ω a) Ω k
  | 0 => MeasurableEquiv.refl _
  | k + 1 => (historyTail a k).prodCongr (MeasurableEquiv.refl Ω)

theorem id_prod_conjugate {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (κ : Kernel α Ω) [IsMarkovKernel κ] :
    ((Kernel.id.prod κ).comap e.symm e.symm.measurable).map
      (e.prodCongr (MeasurableEquiv.refl Ω)) =
      Kernel.id.prod (κ.comap e.symm e.symm.measurable) := by
  apply Kernel.ext
  intro x
  rw [Kernel.map_apply _ (MeasurableEquiv.measurable _), Kernel.comap_apply,
    Kernel.prod_apply, Kernel.id_apply, Kernel.prod_apply, Kernel.id_apply,
    Kernel.comap_apply]
  change ((Measure.dirac (e.symm x)).prod (κ (e.symm x))).map (Prod.map e id) = _
  rw [← Measure.map_prod_map _ _ e.measurable measurable_id, Measure.map_id,
    Measure.map_dirac e.measurable, e.apply_symm_apply]

/-- Structural equality of the actual measurement objects on a stage: after
regrouping its history, each copy pulls back the same stage-entry POVM.
This hypothesis specifies reference kernels and matrix effects, not a
probability law or success conclusion. -/
theorem intervalKernel_historyTail (A : AdaptiveModel.Learner ι Seed Ω N)
    (ρ : Density ι) (a K : ℕ) (hK : a + K ≤ N)
    (M : OneCopyStep ι (History Seed Ω a) Ω)
    (hstep : ∀ k (hk : k < K),
      StagePolicy.pullbackStep (A.step ⟨a + k, by omega⟩)
          (historyTail a k).symm (MeasurableEquiv.measurable _) =
        StagePolicy.pullbackStep M (initial k) (measurable_initial k))
    (k : ℕ) (hk : k ≤ K) :
    (OneCopyStageComposition.intervalKernel A ρ a k (by omega)).map (historyTail a k) =
      pathKernel (M.bornKernel ρ) k := by
  induction k with
  | zero =>
      rw [pathKernel_zero]
      exact Kernel.map_id _
  | succ k ih =>
      have hs := hstep k (by omega)
      have hborn : ((A.step ⟨a + k, by omega⟩).bornKernel ρ).comap
          (historyTail a k).symm (MeasurableEquiv.measurable _) =
          (M.bornKernel ρ).comap (initial k) (measurable_initial k) := by
        rw [← StagePolicy.pullbackStep_bornKernel, hs, StagePolicy.pullbackStep_bornKernel]
      have hi := (Kernel.map_apply_eq_iff_map_symm_apply_eq
        (OneCopyStageComposition.intervalKernel A ρ a k (by omega))
        (f := historyTail a k) (pathKernel (M.bornKernel ρ) k)).mp (ih (by omega))
      rw [OneCopyStageComposition.intervalKernel, Kernel.map_comp, hi,
        Kernel.comp_map _ _ (MeasurableEquiv.measurable _),
        Kernel.comap_map_comm _ (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _)]
      change (((Kernel.id.prod ((A.step ⟨a + k, by omega⟩).bornKernel ρ)).comap
        (historyTail a k).symm (MeasurableEquiv.measurable _)).map
          ((historyTail a k).prodCongr (MeasurableEquiv.refl Ω))).comp
            (pathKernel (M.bornKernel ρ) k) = _
      rw [id_prod_conjugate, hborn]
      exact pathKernel_succ _ _

/-- The newly observed tuple in a genuine global protocol interval. -/
def intervalSamples (a k : ℕ) : History Seed Ω (a + k) → (Fin k → Ω) :=
  samples k ∘ historyTail a k

theorem measurable_intervalSamples (a k : ℕ) :
    Measurable (intervalSamples (Seed := Seed) (Ω := Ω) a k) :=
  (measurable_samples k).comp (historyTail a k).measurable

/-- Native conditional IID law at an actual copy boundary.  Its sole
structural premise is the specified repeated actual one-copy measurement. -/
theorem intervalKernel_tupleLaw (A : AdaptiveModel.Learner ι Seed Ω N)
    (ρ : Density ι) (a K : ℕ) (hK : a + K ≤ N)
    (M : OneCopyStep ι (History Seed Ω a) Ω)
    (hstep : ∀ k (hk : k < K),
      StagePolicy.pullbackStep (A.step ⟨a + k, by omega⟩)
          (historyTail a k).symm (MeasurableEquiv.measurable _) =
        StagePolicy.pullbackStep M (initial k) (measurable_initial k))
    (h : History Seed Ω a) :
    (OneCopyStageComposition.intervalKernel A ρ a K hK h).map (intervalSamples a K) =
      Measure.pi (fun _ : Fin K => M.bornKernel ρ h) := by
  have hi := congrArg (fun κ => κ h)
    (intervalKernel_historyTail A ρ a K hK M hstep K (le_refl K))
  dsimp only at hi
  rw [Kernel.map_apply _ (MeasurableEquiv.measurable _)] at hi
  rw [intervalSamples, ← Measure.map_map (measurable_samples K)
    (MeasurableEquiv.measurable _), hi]
  exact pathKernel_samples _ _ _

theorem intervalKernel_failureProbability (A : AdaptiveModel.Learner ι Seed Ω N)
    (ρ : Density ι) (a K : ℕ) (hK : a + K ≤ N)
    (M : OneCopyStep ι (History Seed Ω a) Ω)
    (hstep : ∀ k (hk : k < K),
      StagePolicy.pullbackStep (A.step ⟨a + k, by omega⟩)
          (historyTail a k).symm (MeasurableEquiv.measurable _) =
        StagePolicy.pullbackStep M (initial k) (measurable_initial k))
    (h : History Seed Ω a) (B : Set (Fin K → Ω)) (hB : MeasurableSet B) :
    OneCopyStageComposition.intervalKernel A ρ a K hK h (intervalSamples a K ⁻¹' B) =
      Measure.pi (fun _ : Fin K => M.bornKernel ρ h) B := by
  rw [← intervalKernel_tupleLaw A ρ a K hK M hstep h,
    Measure.map_apply (measurable_intervalSamples a K) hB]

end GlobalInterval

end Paper26.FrozenOneCopyBlock
