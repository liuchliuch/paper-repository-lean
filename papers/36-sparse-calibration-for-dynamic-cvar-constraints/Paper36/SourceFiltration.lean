import Paper36.SourceSystem

/-! The concrete analyst filtration of the source experiment. Its monotonicity
and physical-path adaptation follow from pure observed-history projections,
with no dynamics, concentration, or performance premise. -/
namespace Paper36.SourceFiltration
noncomputable section
open MeasureTheory ProbabilityTheory Paper36.Trajectories Paper36.SourceReplay
  Paper36.SourceProtocol Paper36.SourceSystem

universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace A] [DiscreteMeasurableSpace A]
  {M Code Meta : Type*} [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M]
  [MeasurableSpace Code] [MeasurableSpace Meta] {T : ℕ}

/-- The finite prefix of an observed history; unused malformed input lengths
are handled by retaining that input history. -/
def cutHistory (j : ℕ) (history : History Meta S A T) : History Meta S A T :=
  if hj : j ≤ history.1 then
    ⟨j,(fun i => history.2.1 ⟨i.val,by omega⟩),fun i => history.2.2 ⟨i.val,by omega⟩⟩
  else history

omit [Nonempty S] [Nonempty A] in
lemma measurable_cutHistory (j : ℕ) :
    Measurable (cutHistory (Meta := Meta) (S := S) (A := A) (T := T) j) := by
  intro B hB
  apply MeasurableSpace.measurableSet_iInf.2
  intro n
  change MeasurableSet ((fun z : (Fin n → Meta) × (Fin n → Trajectory S A T) =>
    cutHistory j ⟨n,z⟩) ⁻¹' B)
  by_cases hj : j ≤ n
  · have hf : Measurable (fun z : (Fin n → Meta) × (Fin n → Trajectory S A T) =>
        ((fun i : Fin j => z.1 ⟨i.val,by omega⟩),fun i : Fin j => z.2 ⟨i.val,by omega⟩)) :=
      (measurable_pi_lambda _ (fun _ => measurable_fst.eval)).prodMk
        (measurable_pi_lambda _ (fun _ => measurable_snd.eval))
    simpa only [cutHistory,dif_pos hj] using ((measurable_history_mk j).comp hf) hB
  · simpa only [cutHistory,dif_neg hj] using (measurable_history_mk (Meta := Meta) (S := S) (A := A) (T := T) n) hB

omit [Nonempty S] [Nonempty A] [MeasurableSpace A] [DiscreteMeasurableSpace A] [MeasurableSpace Meta] in
lemma cutHistory_replay (raw : RawTape S A) (s₀ : S) (draws : ℕ → Draw Meta A T)
    {j k : ℕ} (hjk : j ≤ k) :
    cutHistory j (replayHistory raw s₀ draws k) = replayHistory raw s₀ draws j := by
  unfold cutHistory replayHistory finiteHistory
  rw [dif_pos hjk,finitePaths_eq_episodePath,finitePaths_eq_episodePath]

def historyLength (history : History Meta S A T) : ℕ := history.1

omit [Fintype S] [Fintype A] [Nonempty S] [Nonempty A] [DecidableEq S] [DecidableEq A]
  [MeasurableSpace S] [DiscreteMeasurableSpace S] [MeasurableSpace A] [DiscreteMeasurableSpace A] in
lemma measurable_historyLength :
    Measurable (historyLength (Meta := Meta) (S := S) (A := A) (T := T)) := by
  intro B hB
  apply MeasurableSpace.measurableSet_iInf.2
  intro n
  change MeasurableSet ((fun _ : (Fin n → Meta) × (Fin n → Trajectory S A T) => n) ⁻¹' B)
  exact measurable_const hB

def historyMeta (fallback : Meta) (j : ℕ) (history : History Meta S A T) : Meta :=
  if hj : j < history.1 then history.2.1 ⟨j,hj⟩ else fallback

omit [Fintype S] [Fintype A] [Nonempty S] [Nonempty A] [DecidableEq S] [DecidableEq A]
  [MeasurableSpace S] [DiscreteMeasurableSpace S] [MeasurableSpace A] [DiscreteMeasurableSpace A] in
lemma measurable_historyMeta (fallback : Meta) (j : ℕ) :
    Measurable (historyMeta (S := S) (A := A) (T := T) fallback j) := by
  intro B hB
  apply MeasurableSpace.measurableSet_iInf.2
  intro n
  change MeasurableSet ((fun z : (Fin n → Meta) × (Fin n → Trajectory S A T) =>
    historyMeta fallback j ⟨n,z⟩) ⁻¹' B)
  by_cases hj : j < n
  · have hm : Measurable (fun z : (Fin n → Meta) × (Fin n → Trajectory S A T) => z.1 ⟨j,hj⟩) :=
      (measurable_pi_apply _).comp measurable_fst
    simpa only [historyMeta,dif_pos hj] using hm hB
  · have hm : Measurable (fun _ : (Fin n → Meta) × (Fin n → Trajectory S A T) => fallback) := measurable_const
    simpa only [historyMeta,dif_neg hj] using hm hB

/-- Recover the earlier current metadata from the later recorded history. -/
def recoverInfo (fallback : M × Code) (j : ℕ) (i : Info M Code S A T) : Info M Code S A T :=
  ((i.1.1,cutHistory j i.1.2),
    if j < historyLength i.1.2 then historyMeta fallback j i.1.2 else i.2)

omit [StandardBorelSpace M] [Nonempty M] [Nonempty S] [Nonempty A] in
lemma measurable_recoverInfo (fallback : M × Code) (j : ℕ) :
    Measurable (recoverInfo (S := S) (A := A) (T := T) fallback j) := by
  have hhistory : Measurable (fun i : Info M Code S A T => i.1.2) := measurable_fst.snd
  have hset : MeasurableSet {i : Info M Code S A T | j < historyLength i.1.2} :=
    measurableSet_lt measurable_const (measurable_historyLength.comp hhistory)
  exact (measurable_fst.fst.prodMk ((measurable_cutHistory j).comp hhistory)).prodMk
    (Measurable.ite hset ((measurable_historyMeta fallback j).comp hhistory) measurable_snd)

omit [StandardBorelSpace M] [Nonempty M] [Nonempty S] [Nonempty A]
  [MeasurableSpace A] [DiscreteMeasurableSpace A] [MeasurableSpace M] [MeasurableSpace Code] in
lemma recoverInfo_analystInfo (s₀ : S) (fallback : M × Code) {j k : ℕ} (hjk : j ≤ k)
    (ω : Sample M (M × Code) S A T) :
    recoverInfo fallback j (analystInfo T s₀ k ω) = analystInfo T s₀ j ω := by
  unfold recoverInfo analystInfo SourceProtocol.history
  rw [cutHistory_replay _ _ _ hjk]
  by_cases hlt : j < k
  · simp [historyLength,historyMeta,replayHistory,finiteHistory,hlt]
  · have heq : j = k := by omega
    subst j
    simp [historyLength,replayHistory,finiteHistory]

omit [StandardBorelSpace M] [Nonempty M] [Nonempty S] [Nonempty A] in
/-- The source's actual information sigma fields increase with episode index. -/
theorem info_comap_monotone (s₀ : S) (fallback : M × Code) :
    Monotone (fun k => MeasurableSpace.comap
      (analystInfo (S := S) (A := A) (M := M) (Code := Code) T s₀ k) inferInstance) := by
  intro j k hjk
  have heq : analystInfo (S := S) (A := A) (M := M) (Code := Code) T s₀ j =
      recoverInfo fallback j ∘ analystInfo T s₀ k :=
    funext (fun ω => (recoverInfo_analystInfo s₀ fallback hjk ω).symm)
  change MeasurableSpace.comap (analystInfo T s₀ j) _ ≤ MeasurableSpace.comap (analystInfo T s₀ k) _
  rw [heq,← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_recoverInfo fallback j).comap_le

/-- The native analyst filtration, from the true model, observed past and
current posterior/planner metadata. The fallback is used only off real histories. -/
def naturalFiltration (s₀ : S) (dummy : Draw (M × Code) A T) :
    Filtration ℕ (inferInstance : MeasurableSpace (Sample M (M × Code) S A T)) where
  seq k := MeasurableSpace.comap (analystInfo T s₀ k) inferInstance
  mono' := info_comap_monotone s₀ dummy.1
  le' k := (measurable_analystInfo T s₀ k).comap_le

theorem info_comap (s₀ : S) (dummy : Draw (M × Code) A T) (k : ℕ) :
    MeasurableSpace.comap (analystInfo (S := S) (A := A) (M := M) (Code := Code) T s₀ k) inferInstance =
      naturalFiltration s₀ dummy k := rfl

def historyPath (j : ℕ) (history : History Meta S A T) : Trajectory S A T :=
  if hj : j < history.1 then history.2.2 ⟨j,hj⟩ else Classical.arbitrary _

omit [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  [MeasurableSpace S] [DiscreteMeasurableSpace S] [MeasurableSpace A] [DiscreteMeasurableSpace A] in
lemma measurable_historyPath (j : ℕ) :
    Measurable (historyPath (Meta := Meta) (S := S) (A := A) (T := T) j) := by
  intro B hB
  apply MeasurableSpace.measurableSet_iInf.2
  intro n
  change MeasurableSet ((fun z : (Fin n → Meta) × (Fin n → Trajectory S A T) =>
    historyPath j ⟨n,z⟩) ⁻¹' B)
  by_cases hj : j < n
  · have hm : Measurable (fun z : (Fin n → Meta) × (Fin n → Trajectory S A T) => z.2 ⟨j,hj⟩) :=
      (measurable_pi_apply _).comp measurable_snd
    simpa only [historyPath,dif_pos hj] using hm hB
  · have hm : Measurable (fun _ : (Fin n → Meta) × (Fin n → Trajectory S A T) => Classical.arbitrary (Trajectory S A T)) := measurable_const
    simpa only [historyPath,dif_neg hj] using hm hB

omit [MeasurableSpace A] [DiscreteMeasurableSpace A] [MeasurableSpace M]
  [StandardBorelSpace M] [Nonempty M] [MeasurableSpace Code] in
lemma historyPath_analystInfo (s₀ : S) (k : ℕ) (ω : Sample M (M × Code) S A T) :
    historyPath k (analystInfo T s₀ (k+1) ω).1.2 = SourceProtocol.path s₀ T k ω := by
  unfold analystInfo SourceProtocol.history historyPath replayHistory finiteHistory
  rw [dif_pos (Nat.lt_succ_self k),finitePaths_eq_episodePath]
  rfl

/-- Every complete physical trajectory is measurable at the next native
analyst time. No separate adaptation premise remains for the source certificate. -/
theorem path_measurable (s₀ : S) (dummy : Draw (M × Code) A T) (k : ℕ) :
    Measurable[naturalFiltration s₀ dummy (k+1),inferInstance]
      (SourceProtocol.path (S := S) (A := A) (M := M) (Meta := M × Code) s₀ T k) := by
  have hi : Measurable[naturalFiltration s₀ dummy (k+1),inferInstance]
      (analystInfo (S := S) (A := A) (M := M) (Code := Code) T s₀ (k+1)) :=
    comap_measurable _
  have hp := (measurable_historyPath (Meta := M × Code) (S := S) (A := A) (T := T) k).comp
    (measurable_fst.snd.comp hi)
  convert hp using 1
  funext ω
  exact (historyPath_analystInfo s₀ k ω).symm

end
end Paper36.SourceFiltration
