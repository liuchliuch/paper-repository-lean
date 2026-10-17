import Paper26.MultiscaleUpdate

/-!
# Structural facts of the actual multiscale execution

Every field of `MultiscaleRefinement.StageData` is derived from the finite
recursion in `MultiscaleUpdate.execute`.  No execution certificate, clock
condition, frozen-coordinate invariance or accuracy guarantee is an input.
The recorded block estimates are arbitrary actual PSD matrices.
-/
noncomputable section
open scoped BigOperators Matrix ComplexOrder
open MeasureTheory

namespace Paper26.MultiscaleExecutionFacts
open MultiscaleUpdate MultiscaleRefinement MeasurableSpectralSelection

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Matrices which fix a row/column set continue to fix it after multiplication. -/
theorem fixes_outside_mul (S : Finset ι) (V W : Matrix ι ι ℂ)
    (hV : ∀ i k, i ∉ S ∨ k ∉ S → V i k = (1 : Matrix ι ι ℂ) i k)
    (hW : ∀ i k, i ∉ S ∨ k ∉ S → W i k = (1 : Matrix ι ι ℂ) i k)
    (i k : ι) (h : i ∉ S ∨ k ∉ S) :
    (V * W) i k = (1 : Matrix ι ι ℂ) i k := by
  rcases h with hi | hk
  · have hr : ∀ q, V i q = (1 : Matrix ι ι ℂ) i q := fun q => hV i q (Or.inl hi)
    rw [Matrix.mul_apply]
    simp_rw [hr]
    simpa only [← Matrix.mul_apply, Matrix.one_mul] using hW i k (Or.inl hi)
  · have hc : ∀ q, W q k = (1 : Matrix ι ι ℂ) q k := fun q => hW q k (Or.inr hk)
    rw [Matrix.mul_apply]
    simp_rw [hc]
    simpa only [← Matrix.mul_apply, Matrix.mul_one] using hV i k (Or.inr hk)

section Execution
variable (B : CompactFiberSelectionInput.{u,u}) (L : ℕ) (lower : Fin L → ℝ)
  (F : Fin L → EstimateFamily (ι := ι))

abbrev activeAt (t : ℕ) : Finset ι := (execute B L lower F t).1
abbrev basisAt (t : ℕ) : Matrix.unitaryGroup ι ℂ := (execute B L lower F t).2.1
abbrev frozenAt (t : ℕ) : ι → ℝ := (execute B L lower F t).2.2.1
abbrev clockAt (t : ℕ) : ι → ℕ := (execute B L lower F t).2.2.2

/-- The spectrum actually read from the current active block at stage j. -/
def stageValues (j : Fin L) : ι → ℝ :=
  blockValues (activeAt B L lower F j.val) (F j (activeAt B L lower F j.val))

theorem execute_next_of_ge (t : ℕ) (ht : L ≤ t) :
    execute B L lower F (t + 1) = execute B L lower F t := by
  simp only [execute, dif_neg (by omega : ¬t < L)]

theorem execute_stable (t : ℕ) (ht : L ≤ t) :
    execute B L lower F t = execute B L lower F L := by
  induction t, ht using Nat.le_induction with
  | base => rfl
  | succ t ht ih => rw [execute_next_of_ge B L lower F t ht, ih]

theorem mem_active_next (j : Fin L) (i : ι) :
    i ∈ activeAt B L lower F (j.val + 1) ↔
      i ∈ activeAt B L lower F j.val ∧ stageValues B L lower F j i < lower j := by
  simp only [activeAt, execute, dif_pos j.isLt, step, stepFiber, mem_remaining, stageValues]

theorem basis_next (j : Fin L) :
    basisAt B L lower F (j.val + 1) = basisAt B L lower F j.val *
      selectedUpdate B (activeAt B L lower F j.val) (F j (activeAt B L lower F j.val)) := by
  simp only [basisAt, execute, dif_pos j.isLt, step, stepFiber, activeAt]

theorem frozen_next (j : Fin L) (i : ι) :
    frozenAt B L lower F (j.val + 1) i =
      if i ∈ activeAt B L lower F j.val then
        if lower j ≤ stageValues B L lower F j i then stageValues B L lower F j i else 0
      else frozenAt B L lower F j.val i := by
  simp only [frozenAt, execute, dif_pos j.isLt, step, stepFiber, retained, activeAt, stageValues]

theorem clock_next (j : Fin L) (i : ι) :
    clockAt B L lower F (j.val + 1) i =
      if i ∈ activeAt B L lower F j.val ∧ lower j ≤ stageValues B L lower F j i
        then j.val else clockAt B L lower F j.val i := by
  simp only [clockAt, execute, dif_pos j.isLt, step, stepFiber, activeAt, stageValues]

theorem active_next_subset (t : ℕ) :
    activeAt B L lower F (t + 1) ⊆ activeAt B L lower F t := by
  by_cases ht : t < L
  · intro i hi
    exact ((mem_active_next B L lower F ⟨t, ht⟩ i).mp hi).1
  · exact le_of_eq (congrArg Prod.fst (execute_next_of_ge B L lower F t (by omega)))

theorem active_nested (a b : ℕ) (hab : a ≤ b) :
    activeAt B L lower F b ⊆ activeAt B L lower F a := by
  induction b, hab using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ b hab ih => exact (active_next_subset B L lower F b).trans ih

/-- The clock is terminal exactly on active labels; otherwise it records an
actual earlier stage.  This invariant is proved from the initial state. -/
theorem clock_invariant (t : ℕ) (i : ι) :
    clockAt B L lower F t i ≤ L ∧
      (i ∈ activeAt B L lower F t ↔ clockAt B L lower F t i = L) ∧
      (i ∉ activeAt B L lower F t → clockAt B L lower F t i < t) := by
  induction t with
  | zero => simp [clockAt, activeAt, execute, initial]
  | succ t ih =>
    by_cases ht : t < L
    · let j : Fin L := ⟨t, ht⟩
      have hmem := mem_active_next B L lower F j i
      have hc := clock_next B L lower F j i
      dsimp only [j] at hmem hc
      by_cases hi : i ∈ activeAt B L lower F t
      · by_cases hf : lower j ≤ stageValues B L lower F j i
        · have hn : i ∉ activeAt B L lower F (t + 1) := by
            rw [hmem]
            exact fun hh => (not_lt_of_ge hf) hh.2
          rw [hc, if_pos ⟨hi, hf⟩]
          refine ⟨by omega, iff_of_false hn (by omega), ?_⟩
          intro _
          omega
        · have hn : i ∈ activeAt B L lower F (t + 1) :=
            hmem.mpr ⟨hi, lt_of_not_ge hf⟩
          rw [hc, if_neg (fun hh => hf hh.2)]
          rw [ih.2.1.mp hi]
          exact ⟨le_rfl, iff_of_true hn rfl, fun hh => False.elim (hh hn)⟩
      · have hn : i ∉ activeAt B L lower F (t + 1) := by
          rw [hmem]
          exact fun hh => hi hh.1
        rw [hc, if_neg (fun hh => hi hh.1)]
        refine ⟨ih.1, iff_of_false hn (ih.2.1.not.mp hi), ?_⟩
        intro _
        exact (ih.2.2 hi).trans (Nat.lt_succ_self t)
    · have he := execute_next_of_ge B L lower F t (by omega)
      have ha : activeAt B L lower F (t + 1) = activeAt B L lower F t := congrArg Prod.fst he
      have hc : clockAt B L lower F (t + 1) = clockAt B L lower F t :=
        congrArg (fun st : State (ι := ι) => st.2.2.2) he
      rw [ha, hc]
      exact ⟨ih.1, ih.2.1, fun hi => (ih.2.2 hi).trans (Nat.lt_succ_self t)⟩

theorem clock_stable_of_inactive (a b : ℕ) (hab : a ≤ b) (i : ι)
    (hi : i ∉ activeAt B L lower F a) :
    clockAt B L lower F b i = clockAt B L lower F a i := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    have hib : i ∉ activeAt B L lower F b := fun hb => hi (active_nested B L lower F a b hab hb)
    by_cases hb : b < L
    · rw [clock_next B L lower F ⟨b, hb⟩ i, if_neg (by simp [hib]), ih]
    · have he := execute_next_of_ge B L lower F b (by omega)
      exact (congrArg (fun st : State (ι := ι) => st.2.2.2 i) he).trans ih

theorem frozen_stable_of_inactive (a b : ℕ) (hab : a ≤ b) (i : ι)
    (hi : i ∉ activeAt B L lower F a) :
    frozenAt B L lower F b i = frozenAt B L lower F a i := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    have hib : i ∉ activeAt B L lower F b := fun hb => hi (active_nested B L lower F a b hab hb)
    by_cases hb : b < L
    · rw [frozen_next B L lower F ⟨b, hb⟩ i, if_neg hib, ih]
    · have he := execute_next_of_ge B L lower F b (by omega)
      exact (congrArg (fun st : State (ι := ι) => st.2.2.1 i) he).trans ih

theorem future_clock_ge (a b : ℕ) (ha : a ≤ L) (hab : a ≤ b) (i : ι)
    (hi : i ∈ activeAt B L lower F a) : a ≤ clockAt B L lower F b i := by
  induction b, hab using Nat.le_induction with
  | base => rw [(clock_invariant B L lower F a i).2.1.mp hi]; exact ha
  | succ b hab ih =>
    by_cases hb : b < L
    · rw [clock_next B L lower F ⟨b, hb⟩ i]
      split_ifs
      · exact hab
      · exact ih
    · have he := execute_next_of_ge B L lower F b (by omega)
      have hc : clockAt B L lower F (b + 1) i = clockAt B L lower F b i :=
        congrArg (fun st : State (ι := ι) => st.2.2.2 i) he
      rw [hc]
      exact ih

/-- Before every actual stage, active labels are exactly those whose final
first-freeze time is no earlier than that stage. -/
theorem mem_active_iff_final_clock (t : ℕ) (ht : t ≤ L) (i : ι) :
    i ∈ activeAt B L lower F t ↔ t ≤ clockAt B L lower F L i := by
  constructor
  · exact future_clock_ge B L lower F t L ht ht i
  · intro htime
    by_contra hn
    have he := clock_stable_of_inactive B L lower F t L ht i hn
    have hl := (clock_invariant B L lower F t i).2.2 hn
    rw [← he] at hl
    omega

theorem freeze_time_iff (j : Fin L) (i : ι)
    (hi : i ∈ activeAt B L lower F j.val) :
    clockAt B L lower F L i = j.val ↔ lower j ≤ stageValues B L lower F j i := by
  constructor
  · intro he
    by_contra hn
    have hnext := (mem_active_next B L lower F j i).mpr ⟨hi, lt_of_not_ge hn⟩
    have ht := (mem_active_iff_final_clock B L lower F (j.val + 1) (by omega) i).mp hnext
    omega
  · intro hf
    have hnext : i ∉ activeAt B L lower F (j.val + 1) := by
      rw [mem_active_next]
      exact fun hh => (not_lt_of_ge hf) hh.2
    rw [clock_stable_of_inactive B L lower F (j.val + 1) L (by omega) i hnext,
      clock_next B L lower F j i, if_pos ⟨hi, hf⟩]

theorem frozen_value_at_final (j : Fin L) (i : ι)
    (ht : clockAt B L lower F L i = j.val) :
    frozenAt B L lower F L i = stageValues B L lower F j i := by
  have hi : i ∈ activeAt B L lower F j.val :=
    (mem_active_iff_final_clock B L lower F j.val j.isLt.le i).mpr (by omega)
  have hf := (freeze_time_iff B L lower F j i hi).mp ht
  have hn : i ∉ activeAt B L lower F (j.val + 1) := by
    rw [mem_active_next]
    exact fun hh => (not_lt_of_ge hf) hh.2
  rw [frozen_stable_of_inactive B L lower F (j.val + 1) L (by omega) i hn,
    frozen_next B L lower F j i, if_pos hi, if_pos hf]

/-- The relative basis from any execution prefix to any later prefix fixes
every row or column already outside that prefix's active block. -/
theorem relative_basis_fixes (a b : ℕ) (hab : a ≤ b) (i k : ι)
    (hi : i ∉ activeAt B L lower F a ∨ k ∉ activeAt B L lower F a) :
    (((basisAt B L lower F a : Matrix ι ι ℂ)ᴴ) *
      (basisAt B L lower F b : Matrix ι ι ℂ)) i k = (1 : Matrix ι ι ℂ) i k := by
  induction b, hab using Nat.le_induction generalizing i k with
  | base => rw [PositiveLossBridge.unitary_left]
  | succ b hab ih =>
    by_cases hb : b < L
    · rw [basis_next B L lower F ⟨b, hb⟩]
      change (((basisAt B L lower F a : Matrix ι ι ℂ)ᴴ) *
        ((basisAt B L lower F b : Matrix ι ι ℂ) *
          (selectedUpdate B (activeAt B L lower F b) (F ⟨b, hb⟩ (activeAt B L lower F b)) :
            Matrix ι ι ℂ))) i k = _
      rw [← Matrix.mul_assoc]
      apply fixes_outside_mul (activeAt B L lower F a) _ _ _ _ i k hi
      · intro q r hqr
        exact ih q r hqr
      · intro q r hqr
        apply extendUnitary_outside
        exact hqr.imp
          (fun hq hqb => hq (active_nested B L lower F a b hab hqb))
          (fun hr hrb => hr (active_nested B L lower F a b hab hrb))
    · have he := execute_next_of_ge B L lower F b (by omega)
      have hu : basisAt B L lower F (b + 1) = basisAt B L lower F b :=
        congrArg (fun st : State (ι := ι) => st.2.1) he
      rw [hu]
      exact ih i k hi

variable [NeZero L]

/-- The complete deterministic certificate is constructed from the actual
recorded execution. Its structural fields are all theorems above. -/
def stageData : MultiscaleRefinement.StageData (ι := ι) L lower where
  basis j := basisAt B L lower F (j.val + 1)
  estimateSpectrum := stageValues B L lower F
  estimate_nonneg j i := blockValues_nonneg _ _ i
  freezeTime := clockAt B L lower F L
  time_bound i := (clock_invariant B L lower F L i).1
  threshold_cut j i ht := freeze_time_iff B L lower F j i
    ((mem_active_iff_final_clock B L lower F j.val j.isLt.le i).mpr ht)
  frozen_update j i k ht := by
    have hlast : (MultiscaleRefinement.lastStage L).val + 1 = L := by
      simp only [MultiscaleRefinement.lastStage]
      have := NeZero.pos L
      omega
    change (((basisAt B L lower F (j.val + 1) : Matrix ι ι ℂ)ᴴ) *
      (basisAt B L lower F ((MultiscaleRefinement.lastStage L).val + 1) : Matrix ι ι ℂ)) i k = _
    rw [hlast]
    apply relative_basis_fixes B L lower F (j.val + 1) L (by omega) i k
    exact ht.imp
      (fun hi hm => by
        have h := (mem_active_iff_final_clock B L lower F (j.val + 1) (by omega) i).mp hm
        omega)
      (fun hk hm => by
        have h := (mem_active_iff_final_clock B L lower F (j.val + 1) (by omega) k).mp hm
        omega)

@[simp] theorem stageData_active (j : Fin L) (i : ι) :
    (stageData B L lower F).active j.val i ↔ i ∈ activeAt B L lower F j.val :=
  (mem_active_iff_final_clock B L lower F j.val j.isLt.le i).symm

@[simp] theorem stageData_basis (j : Fin L) :
    (stageData B L lower F).basis j = basisAt B L lower F (j.val + 1) := rfl

@[simp] theorem stageData_spectrum (j : Fin L) :
    (stageData B L lower F).estimateSpectrum j = stageValues B L lower F j := rfl

@[simp] theorem stageData_freezeTime (i : ι) :
    (stageData B L lower F).freezeTime i = clockAt B L lower F L i := rfl

theorem stageData_finalBasis :
    (stageData B L lower F).finalBasis = basisAt B L lower F L := by
  have hlast : (MultiscaleRefinement.lastStage L).val + 1 = L := by
    simp only [MultiscaleRefinement.lastStage]
    have := NeZero.pos L
    omega
  change basisAt B L lower F ((MultiscaleRefinement.lastStage L).val + 1) = _
  rw [hlast]

/-- The shell certificate returns precisely the execution's frozen values
and terminal floor, rather than a different postulated output. -/
theorem stageData_outputSpectrum :
    (stageData B L lower F).outputSpectrum = finalSpectrum B L lower F := by
  funext i
  change (if h : clockAt B L lower F L i < L then
      stageValues B L lower F ⟨clockAt B L lower F L i, h⟩ i
    else lower (MultiscaleRefinement.lastStage L)) =
    if i ∈ activeAt B L lower F L then lower (MultiscaleRefinement.lastStage L)
    else frozenAt B L lower F L i
  by_cases hi : clockAt B L lower F L i < L
  · have hn : i ∉ activeAt B L lower F L := by
      intro hm
      have he := (clock_invariant B L lower F L i).2.1.mp hm
      omega
    rw [dif_pos hi, if_neg hn]
    exact (frozen_value_at_final B L lower F ⟨_, hi⟩ i rfl).symm
  · have he : clockAt B L lower F L i = L := by
      have hb := (clock_invariant B L lower F L i).1
      omega
    have hm := (clock_invariant B L lower F L i).2.1.mpr he
    rw [dif_neg hi, if_pos hm]

theorem stageData_outputMatrix :
    (stageData B L lower F).outputMatrix = finalMatrix B L lower F := by
  unfold MultiscaleRefinement.StageData.outputMatrix MultiscaleUpdate.finalMatrix
  rw [stageData_finalBasis, stageData_outputSpectrum]

end Execution
end Paper26.MultiscaleExecutionFacts
