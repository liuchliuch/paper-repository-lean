import Paper36.SourceExperiment

/-! Finite marginal laws of the one constructed infinite source execution. -/
namespace Paper36.SourceMarginals
open MeasureTheory ProbabilityTheory Preorder Paper36.SourceExperiment
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 1000000
variable {X : Type*} [MeasurableSpace X]

def iterateKernel (κ : Kernel X X) : ℕ → Kernel X X
  | 0 => Kernel.id
  | n+1 => κ ∘ₖ iterateKernel κ n

instance iterateKernel_markov (κ : Kernel X X) [IsMarkovKernel κ] (n : ℕ) :
    IsMarkovKernel (iterateKernel κ n) := by
  induction n with
  | zero => dsimp [iterateKernel]; infer_instance
  | succ n ih => dsimp [iterateKernel]; infer_instance

private lemma partial_step_last (κ : Kernel X X) [IsMarkovKernel κ] (n : ℕ) :
    (Kernel.partialTraj (X := fun _ => X) (historyKernel κ) n (n+1)).map (last (n+1)) =
      historyKernel κ n := by
  have hm : Measurable (IicProdIoc (X := fun _ => X) n (n+1)) := measurable_IicProdIoc
  have hpi : Measurable (MeasurableEquiv.piSingleton (X := fun _ => X) n) :=
    (MeasurableEquiv.piSingleton n).measurable
  ext x B hB
  have hSet : MeasurableSet (Prod.mk x ⁻¹' (IicProdIoc (X := fun _ => X) n (n+1) ⁻¹'
      (last (X := X) (n+1) ⁻¹' B))) :=
    (hm ((measurable_last (n+1)) hB)).preimage (measurable_const.prodMk measurable_id)
  rw [Kernel.map_apply' _ (measurable_last (n+1)) _ hB,
    Kernel.partialTraj_succ_self, Kernel.map_apply' _ hm _ ((measurable_last (n+1)) hB),
    Kernel.id_prod_apply' _ _ (hm ((measurable_last (n+1)) hB)),
    Kernel.map_apply _ hpi x, Measure.map_apply hpi hSet]
  congr 1
  ext y
  simp [Set.preimage, last, IicProdIoc, MeasurableEquiv.piSingleton]

private lemma comp_comap {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ] (κ : Kernel α β) (η : Kernel β γ)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] (f : δ → α) (hf : Measurable f) :
    η ∘ₖ κ.comap f hf = (η ∘ₖ κ).comap f hf := by
  rw [← Kernel.comp_deterministic_eq_comap κ hf, ← Kernel.comp_assoc,
    Kernel.comp_deterministic_eq_comap]

/-- The last coordinate of each true finite trajectory is the iterated protocol law. -/
theorem partial_last (κ : Kernel X X) [IsMarkovKernel κ] (n : ℕ) :
    (Kernel.partialTraj (X := fun _ => X) (historyKernel κ) 0 n).map (last n) =
      (iterateKernel κ n).comap (last 0) (measurable_last 0) := by
  induction n with
  | zero =>
    rw [Kernel.partialTraj_self, iterateKernel, Kernel.id_map (measurable_last 0)]
    ext x B hB
    rfl
  | succ n ih =>
    rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le n), Kernel.map_comp, partial_step_last]
    change κ.comap (last n) (measurable_last n) ∘ₖ _ = _
    rw [← Kernel.comp_map _ κ (measurable_last n), ih, comp_comap, iterateKernel]

/-- The nth coordinate of the original infinite execution has exactly κ iterated n times. -/
theorem executionKernel_nth (κ : Kernel X X) [IsMarkovKernel κ] (n : ℕ) :
    (executionKernel κ).map (fun x : ℕ → X => x n) = iterateKernel κ n := by
  have hrestrict : Measurable (fun x : ℕ → X => fun i : Finset.Iic n => x i.val) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply i.val
  have he : (fun x : ℕ → X => x n) = last n ∘ (fun x : ℕ → X => fun i : Finset.Iic n => x i.val) := rfl
  rw [he, Kernel.map_comp_right _ hrestrict (measurable_last n), executionKernel_prefix,
    ← Kernel.comap_map_comm _ measurable_seed (measurable_last n), partial_last,
    ← Kernel.comap_comp_right _ measurable_seed (measurable_last 0)]
  change (iterateKernel κ n).comap id measurable_id = iterateKernel κ n
  exact Kernel.comap_id _

/-- The previous finite trajectory together with its next genuine state. -/
def nextPair (n : ℕ) (x : Finset.Iic (n+1) → X) : (Finset.Iic n → X) × X :=
  ((fun i => x ⟨i.val, Finset.mem_Iic.mpr ((Finset.mem_Iic.mp i.property).trans (Nat.le_succ n))⟩), last (n+1) x)

lemma measurable_nextPair (n : ℕ) : Measurable (nextPair (X := X) n) :=
  (measurable_pi_lambda _ fun i => measurable_pi_apply _).prodMk (measurable_last _)

private lemma nextPair_append (n : ℕ) (x : Finset.Iic n → X) (y : X) :
    nextPair n (IicProdIoc (X := fun _ => X) n (n+1) (x,MeasurableEquiv.piSingleton (X := fun _ => X) n y)) = (x,y) := by
  apply Prod.ext
  · funext i
    simp [nextPair, IicProdIoc, Finset.mem_Iic.mp i.property]
  · simp [nextPair, last, IicProdIoc, MeasurableEquiv.piSingleton]

theorem partial_step_pair
    (κ : (n : ℕ) → Kernel (Finset.Iic n → X) X) [∀ n, IsMarkovKernel (κ n)] (n : ℕ) :
    (Kernel.partialTraj (X := fun _ => X) κ n (n+1)).map (nextPair n) = Kernel.id ×ₖ κ n := by
  have hm : Measurable (IicProdIoc (X := fun _ => X) n (n+1)) := measurable_IicProdIoc
  have hpi : Measurable (MeasurableEquiv.piSingleton (X := fun _ => X) n) :=
    (MeasurableEquiv.piSingleton n).measurable
  ext x B hB
  have hSet : MeasurableSet (Prod.mk x ⁻¹' (IicProdIoc (X := fun _ => X) n (n+1) ⁻¹'
      (nextPair (X := X) n ⁻¹' B))) :=
    (hm ((measurable_nextPair n) hB)).preimage (measurable_const.prodMk measurable_id)
  rw [Kernel.map_apply' _ (measurable_nextPair n) _ hB,
    Kernel.partialTraj_succ_self, Kernel.map_apply' _ hm _ ((measurable_nextPair n) hB),
    Kernel.id_prod_apply' _ _ (hm ((measurable_nextPair n) hB)),
    Kernel.map_apply _ hpi x, Measure.map_apply hpi hSet, Kernel.id_prod_apply' _ _ hB]
  congr 1
  ext y
  change (nextPair n (IicProdIoc (X := fun _ => X) n (n+1) (x,MeasurableEquiv.piSingleton (X := fun _ => X) n y)) ∈ B) ↔ ((x,y) ∈ B)
  rw [nextPair_append]

theorem partial_next_pair
    (κ : (n : ℕ) → Kernel (Finset.Iic n → X) X) [∀ n, IsMarkovKernel (κ n)] (n : ℕ) :
    (Kernel.partialTraj (X := fun _ => X) κ 0 (n+1)).map (nextPair n) =
      (Kernel.id ×ₖ κ n) ∘ₖ Kernel.partialTraj (X := fun _ => X) κ 0 n := by
  rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le n), Kernel.map_comp, partial_step_pair]

section Draws
variable {Base D : Type*} [MeasurableSpace Base] [MeasurableSpace D]

def prefixState (n : ℕ) (x : Finset.Iic n → Base × D) : Base × (Fin n → D) :=
  ((x ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩).1, previous n x)

lemma measurable_prefixState (n : ℕ) : Measurable (prefixState (Base := Base) (D := D) n) :=
  (measurable_pi_apply _).fst.prodMk (measurable_previous n)

def appendDraw (n : ℕ) (z : (Base × (Fin n → D)) × D) : Base × (Fin (n+1) → D) :=
  (z.1.1, Fin.lastCases z.2 z.1.2)

lemma measurable_appendDraw (n : ℕ) : Measurable (appendDraw (Base := Base) (D := D) n) := by
  apply measurable_fst.fst.prodMk
  apply measurable_pi_lambda
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.lastCases_last] using (measurable_snd : Measurable (fun z : (Base × (Fin n → D)) × D => z.2))
  · simpa only [Fin.lastCases_castSucc] using ((measurable_pi_apply j).comp measurable_fst.snd : Measurable (fun z : (Base × (Fin n → D)) × D => z.1.2 j))

def nextDrawPair (n : ℕ) (z : (Finset.Iic n → Base × D) × (Base × D)) :
    (Base × (Fin n → D)) × D := (prefixState n z.1,z.2.2)

lemma measurable_nextDrawPair (n : ℕ) : Measurable (nextDrawPair (Base := Base) (D := D) n) :=
  ((measurable_prefixState n).comp measurable_fst).prodMk measurable_snd.snd

theorem drawHistoryKernel_snd
    (κ : (n : ℕ) → Kernel (Base × (Fin n → D)) D) [∀ n, IsMarkovKernel (κ n)] (n : ℕ) :
    (drawHistoryKernel κ n).map Prod.snd = (κ n).comap (prefixState n) (measurable_prefixState n) := by
  ext x B hB
  rw [Kernel.map_apply' _ measurable_snd _ hB, drawHistoryKernel,
    Kernel.map_apply' _ (measurable_drawPair n) _ (measurable_snd hB),
    Kernel.id_prod_apply' _ _ ((measurable_drawPair n) (measurable_snd hB))]
  rfl

theorem draw_step_pair
    (κ : (n : ℕ) → Kernel (Base × (Fin n → D)) D) [∀ n, IsMarkovKernel (κ n)] (n : ℕ) :
    (Kernel.id ×ₖ drawHistoryKernel κ n).map (nextDrawPair n) =
      (Kernel.id ×ₖ κ n).comap (prefixState n) (measurable_prefixState n) := by
  change (Kernel.id ×ₖ drawHistoryKernel κ n).map (Prod.map (prefixState n) Prod.snd) = _
  rw [← Kernel.map_prod_map _ _ (measurable_prefixState n) measurable_snd, drawHistoryKernel_snd,
    Kernel.id_map (measurable_prefixState n), Kernel.comap_prod]
  congr 1

/-- Finite laws of the actual constructed source, retaining the original base. -/
def prefixKernel
    (κ : (n : ℕ) → Kernel (Base × (Fin n → D)) D) [∀ n, IsMarkovKernel (κ n)]
    (dummy : D) (n : ℕ) : Kernel Base (Base × (Fin n → D)) :=
  ((Kernel.partialTraj (X := fun _ => Base × D) (drawHistoryKernel κ) 0 n).map (prefixState n)).comap
    (fun base => seed (base,dummy)) (measurable_seed.comp (measurable_id.prodMk measurable_const))

instance prefixKernel_markov
    (κ : (n : ℕ) → Kernel (Base × (Fin n → D)) D) [∀ n, IsMarkovKernel (κ n)]
    (dummy : D) (n : ℕ) : IsMarkovKernel (prefixKernel κ dummy n) := by
  unfold prefixKernel
  haveI := Kernel.IsMarkovKernel.map
    (Kernel.partialTraj (X := fun _ => Base × D) (drawHistoryKernel κ) 0 n) (measurable_prefixState n)
  infer_instance

/-- The joint finite history and next real learner draw. -/
def nextDrawKernel
    (κ : (n : ℕ) → Kernel (Base × (Fin n → D)) D) [∀ n, IsMarkovKernel (κ n)]
    (dummy : D) (n : ℕ) : Kernel Base ((Base × (Fin n → D)) × D) :=
  ((Kernel.partialTraj (X := fun _ => Base × D) (drawHistoryKernel κ) 0 (n+1)).map
    (nextDrawPair n ∘ nextPair n)).comap
      (fun base => seed (base,dummy)) (measurable_seed.comp (measurable_id.prodMk measurable_const))

/-- The next choice is generated by exactly the original kernel κ(n), given
the retained base and the previous actual draws. -/
theorem nextDrawKernel_eq
    (κ : (n : ℕ) → Kernel (Base × (Fin n → D)) D) [∀ n, IsMarkovKernel (κ n)]
    (dummy : D) (n : ℕ) :
    nextDrawKernel κ dummy n = (Kernel.id ×ₖ κ n) ∘ₖ prefixKernel κ dummy n := by
  have hraw : (Kernel.partialTraj (X := fun _ => Base × D) (drawHistoryKernel κ) 0 (n+1)).map
      (nextDrawPair n ∘ nextPair n) =
      (Kernel.id ×ₖ κ n) ∘ₖ (Kernel.partialTraj (X := fun _ => Base × D) (drawHistoryKernel κ) 0 n).map (prefixState n) := by
    rw [Kernel.map_comp_right _ (measurable_nextPair n) (measurable_nextDrawPair n),
      partial_next_pair, Kernel.map_comp, draw_step_pair, ← Kernel.comp_map _ _ (measurable_prefixState n)]
  unfold nextDrawKernel prefixKernel
  rw [hraw, comp_comap]

lemma prefixState_append (n : ℕ) (x : Finset.Iic (n+1) → Base × D) :
    prefixState (n+1) x = appendDraw n (nextDrawPair n (nextPair n x)) := by
  apply Prod.ext
  · rfl
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [prefixState, previous, appendDraw, nextDrawPair, nextPair,
        Fin.lastCases_last, Fin.val_last, last]
    · simp only [prefixState, previous, appendDraw, nextDrawPair, nextPair,
        Fin.lastCases_castSucc, Fin.coe_castSucc]

theorem prefixKernel_eq_nextDraw_map
    (κ : (n : ℕ) → Kernel (Base × (Fin n → D)) D) [∀ n, IsMarkovKernel (κ n)]
    (dummy : D) (n : ℕ) :
    prefixKernel κ dummy (n+1) = (nextDrawKernel κ dummy n).map (appendDraw n) := by
  have he : prefixState (Base := Base) (D := D) (n+1) =
      appendDraw n ∘ (nextDrawPair n ∘ nextPair n) := funext (prefixState_append n)
  have hs : Measurable (fun base : Base => seed (base,dummy)) :=
    measurable_seed.comp (measurable_id.prodMk measurable_const)
  unfold prefixKernel nextDrawKernel
  rw [he, Kernel.map_comp_right _ ((measurable_nextDrawPair n).comp (measurable_nextPair n))
    (measurable_appendDraw n), Kernel.comap_map_comm _ hs (measurable_appendDraw n)]

def stepDraw (κ : (n : ℕ) → Kernel (Base × (Fin n → D)) D) (n : ℕ) :
    Kernel (Base × (Fin n → D)) (Base × (Fin (n+1) → D)) :=
  (Kernel.id ×ₖ κ n).map (appendDraw n)

instance stepDraw_markov (κ : (n : ℕ) → Kernel (Base × (Fin n → D)) D)
    [∀ n, IsMarkovKernel (κ n)] (n : ℕ) : IsMarkovKernel (stepDraw κ n) :=
  Kernel.IsMarkovKernel.map _ (measurable_appendDraw n)

/-- Exact retained-base finite-prefix recursion for the one actual infinite process. -/
theorem prefixKernel_succ
    (κ : (n : ℕ) → Kernel (Base × (Fin n → D)) D) [∀ n, IsMarkovKernel (κ n)]
    (dummy : D) (n : ℕ) :
    prefixKernel κ dummy (n+1) = stepDraw κ n ∘ₖ prefixKernel κ dummy n := by
  rw [prefixKernel_eq_nextDraw_map, nextDrawKernel_eq, Kernel.map_comp]
  rfl

/-- Forgetting the retained base yields the actual infinite draw sequence prefix. -/
theorem prefixKernel_snd
    (κ : (n : ℕ) → Kernel (Base × (Fin n → D)) D) [∀ n, IsMarkovKernel (κ n)]
    (dummy : D) (n : ℕ) :
    (prefixKernel κ dummy n).snd =
      (drawExecutionKernel κ dummy).map (fun d : ℕ → D => fun i : Fin n => d i.val) := by
  have hs : Measurable (fun base : Base => seed (base,dummy)) :=
    measurable_seed.comp (measurable_id.prodMk measurable_const)
  rw [Kernel.snd_eq, prefixKernel, ← Kernel.comap_map_comm _ hs measurable_snd,
    ← Kernel.map_comp_right _ (measurable_prefixState n) measurable_snd]
  change ((Kernel.partialTraj (X := fun _ => Base × D) (drawHistoryKernel κ) 0 n).map (previous n)).comap
    (fun base => seed (base,dummy)) hs = _
  rw [Kernel.comap_map_comm _ hs (measurable_previous n)]
  exact (drawExecutionKernel_prefix κ dummy n).symm

/-- The base coordinate is exactly the original seed base, at every finite length. -/
theorem prefixKernel_fst
    (κ : (n : ℕ) → Kernel (Base × (Fin n → D)) D) [∀ n, IsMarkovKernel (κ n)]
    (dummy : D) (n : ℕ) : (prefixKernel κ dummy n).fst = Kernel.id := by
  let root : (Finset.Iic 0 → Base × D) → Base := fun x => (x ⟨0, by simp⟩).1
  have hr : Measurable root := (measurable_pi_apply _).fst
  have he : Prod.fst ∘ prefixState (Base := Base) (D := D) n =
      root ∘ frestrictLe₂ (π := fun _ : ℕ => Base × D) (Nat.zero_le n) := rfl
  have hs : Measurable (fun base : Base => seed (base,dummy)) :=
    measurable_seed.comp (measurable_id.prodMk measurable_const)
  have hrestrict : Measurable (frestrictLe₂ (π := fun _ : ℕ => Base × D) (Nat.zero_le n)) :=
    measurable_frestrictLe₂ _
  rw [Kernel.fst_eq, prefixKernel, ← Kernel.comap_map_comm _ hs measurable_fst,
    ← Kernel.map_comp_right _ (measurable_prefixState n) measurable_fst, he,
    Kernel.map_comp_right _ hrestrict hr,
    Kernel.partialTraj_map_frestrictLe₂, Kernel.partialTraj_self, Kernel.id_map hr]
  ext base B hB
  rfl

private theorem eq_id_prod_snd {Y : Type*} [MeasurableSpace Y] [MeasurableSingletonClass Base]
    (η : Kernel Base (Base × Y)) [IsMarkovKernel η] (hfst : η.fst = Kernel.id) :
    η = Kernel.id ×ₖ η.snd := by
  ext base : 1
  have hf : (η base).map Prod.fst = Measure.dirac base := by
    rw [← Kernel.fst_apply, hfst, Kernel.id_apply]
  have hmap : ∀ᵐ b ∂(η base).map Prod.fst, b = base := by
    rw [hf]
    exact (ae_dirac_iff (measurableSet_singleton base)).2 rfl
  have hae : ∀ᵐ z ∂η base, z.1 = base := ae_of_ae_map measurable_fst.aemeasurable hmap
  have he : (fun z : Base × Y => z) =ᵐ[η base] (fun z => (base,z.2)) := by
    filter_upwards [hae] with z hz
    exact Prod.ext hz rfl
  have hmk : Measurable (Prod.mk base : Y → Base × Y) := measurable_const.prodMk measurable_id
  calc
    η base = (η base).map id := Measure.map_id.symm
    _ = (η base).map (fun z => (base,z.2)) := Measure.map_congr he
    _ = ((η base).map Prod.snd).map (Prod.mk base) := by
      rw [Measure.map_map hmk measurable_snd]
      rfl
    _ = (Measure.dirac base).prod ((η base).map Prod.snd) := by rw [Measure.dirac_prod]
    _ = (Kernel.id ×ₖ η.snd) base := by
      rw [Kernel.prod_apply, Kernel.id_apply, Kernel.snd_apply]

/-- The augmented prefix law is the joint law of the retained input base and
the actual finite prefix of the one infinite draw execution. -/
theorem prefixKernel_eq_actual [MeasurableSingletonClass Base]
    (κ : (n : ℕ) → Kernel (Base × (Fin n → D)) D) [∀ n, IsMarkovKernel (κ n)]
    (dummy : D) (n : ℕ) :
    prefixKernel κ dummy n = Kernel.id ×ₖ
      (drawExecutionKernel κ dummy).map (fun d : ℕ → D => fun i : Fin n => d i.val) := by
  rw [eq_id_prod_snd _ (prefixKernel_fst κ dummy n), prefixKernel_snd]

theorem actual_prefix [MeasurableSingletonClass Base]
    (ν : Measure Base) [IsProbabilityMeasure ν]
    (κ : (n : ℕ) → Kernel (Base × (Fin n → D)) D) [∀ n, IsMarkovKernel (κ n)]
    (dummy : D) (n : ℕ) : (ν ⊗ₘ drawExecutionKernel κ dummy).map
      (fun z => (z.1, fun i : Fin n => z.2 i.val)) = prefixKernel κ dummy n ∘ₘ ν := by
  have hp : Measurable (fun d : ℕ → D => fun i : Fin n => d i.val) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply i.val
  have hk : (Kernel.id ×ₖ drawExecutionKernel κ dummy).map
      (fun z => (z.1, fun i : Fin n => z.2 i.val)) =
      Kernel.id ×ₖ (drawExecutionKernel κ dummy).map (fun d : ℕ → D => fun i : Fin n => d i.val) := by
    change (Kernel.id ×ₖ drawExecutionKernel κ dummy).map
      (Prod.map id (fun d : ℕ → D => fun i : Fin n => d i.val)) = _
    rw [← Kernel.map_prod_map _ _ measurable_id hp, Kernel.map_id]
  rw [prefixKernel_eq_actual, Measure.compProd_eq_comp_prod]
  have hm : Measurable (fun z : Base × (ℕ → D) => (z.1, fun i : Fin n => z.2 i.val)) :=
    measurable_fst.prodMk (measurable_pi_lambda _ fun i => measurable_snd.eval)
  exact (Measure.map_comp ν (Kernel.id ×ₖ drawExecutionKernel κ dummy) hm).trans
    (congrArg (fun η : Kernel Base (Base × (Fin n → D)) => η ∘ₘ ν) hk)

/-- The same finite-prefix recurrence, stated directly with the actual source
measure for any base prior; it is ready for episode-by-episode fresh-window induction. -/
theorem actual_prefix_succ [MeasurableSingletonClass Base]
    (ν : Measure Base) [IsProbabilityMeasure ν]
    (κ : (n : ℕ) → Kernel (Base × (Fin n → D)) D) [∀ n, IsMarkovKernel (κ n)]
    (dummy : D) (n : ℕ) :
    (ν ⊗ₘ drawExecutionKernel κ dummy).map
      (fun z => (z.1, fun i : Fin (n+1) => z.2 i.val)) =
      stepDraw κ n ∘ₘ ((ν ⊗ₘ drawExecutionKernel κ dummy).map
        (fun z => (z.1, fun i : Fin n => z.2 i.val))) := by
  rw [actual_prefix ν κ dummy (n+1), prefixKernel_succ, ← Measure.comp_assoc, ← actual_prefix ν κ dummy n]

def splitDraw (n : ℕ) (z : Base × (Fin (n+1) → D)) : (Base × (Fin n → D)) × D :=
  ((z.1,fun i => z.2 i.castSucc),z.2 (Fin.last n))

lemma measurable_splitDraw (n : ℕ) : Measurable (splitDraw (Base := Base) (D := D) n) :=
  (measurable_fst.prodMk (measurable_pi_lambda _ fun i => measurable_snd.eval)).prodMk measurable_snd.eval

lemma splitDraw_appendDraw (n : ℕ) :
    splitDraw (Base := Base) (D := D) n ∘ appendDraw n = id := by
  funext z
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · funext i
      change Fin.lastCases z.2 z.1.2 i.castSucc = z.1.2 i
      exact Fin.lastCases_castSucc i
  · change Fin.lastCases z.2 z.1.2 (Fin.last n) = z.2
    exact Fin.lastCases_last

theorem prefixKernel_splitDraw
    (κ : (n : ℕ) → Kernel (Base × (Fin n → D)) D) [∀ n, IsMarkovKernel (κ n)]
    (dummy : D) (n : ℕ) :
    (prefixKernel κ dummy (n+1)).map (splitDraw n) = nextDrawKernel κ dummy n := by
  rw [prefixKernel_eq_nextDraw_map, ← Kernel.map_comp_right _ (measurable_appendDraw n) (measurable_splitDraw n),
    splitDraw_appendDraw, Kernel.map_id]

/-- The exact actual-source history/next-draw joint law. This derives the
conditional source-generation premise from the constructed infinite process. -/
theorem actual_next_pair [MeasurableSingletonClass Base]
    (ν : Measure Base) [IsProbabilityMeasure ν]
    (κ : (n : ℕ) → Kernel (Base × (Fin n → D)) D) [∀ n, IsMarkovKernel (κ n)]
    (dummy : D) (n : ℕ) :
    (ν ⊗ₘ drawExecutionKernel κ dummy).map
      (fun z => ((z.1, fun i : Fin n => z.2 i.val), z.2 n)) =
      ((ν ⊗ₘ drawExecutionKernel κ dummy).map
        (fun z => (z.1, fun i : Fin n => z.2 i.val))) ⊗ₘ κ n := by
  have he : (fun z : Base × (ℕ → D) => ((z.1, fun i : Fin n => z.2 i.val),z.2 n)) =
      splitDraw n ∘ (fun z => (z.1, fun i : Fin (n+1) => z.2 i.val)) := rfl
  rw [he, ← Measure.map_map (measurable_splitDraw n) (by fun_prop), actual_prefix ν κ dummy (n+1),
    Measure.map_comp _ _ (measurable_splitDraw n), prefixKernel_splitDraw, nextDrawKernel_eq,
    ← Measure.comp_assoc, ← actual_prefix ν κ dummy n, ← Measure.compProd_eq_comp_prod]

end Draws

end
end Paper36.SourceMarginals
