import Paper02.RecoveryMachine

/-! # Sequential level selection with the actual recovery submachine -/
noncomputable section
attribute [local instance] Classical.propDecidable

namespace Paper02.LevelMachine

open CompactCandidates SparseRecovery Streaming

variable {d U J ℓ K q : ℕ} [Fact q.Prime]

abbrev State (d U J K q : ℕ) [NeZero q] :=
  MachineComposition.State (J + 1) (RecoveryMachine.State d U K q)

def microInit (s : CopyState J K q) (j : Fin (J + 1)) : RecoveryMachine.State d U K q :=
  RecoveryMachine.initial (s j)

def microStep (seed : CopySeed J ℓ q) (s : CopyState J K q)
    (j : Fin (J + 1)) : RecoveryMachine.State d U K q → RecoveryMachine.State d U K q :=
  RecoveryMachine.step (seed.2 j) (s j)

def initial (s : CopyState J K q) : State d U J K q :=
  MachineComposition.start (microInit (d := d) (U := U) s) (.halt none) 0 (by omega)

def step (seed : CopySeed J ℓ q) (s : CopyState J K q) : State d U J K q → State d U J K q :=
  MachineComposition.step (microInit (d := d) (U := U) s) (.halt none) (microStep (d := d) (U := U) seed s) RecoveryMachine.done RecoveryMachine.accept

def Reaches (seed : CopySeed J ℓ q) (s : CopyState J K q) (x y : State d U J K q) : Prop :=
  Relation.ReflTransGen (fun a b => step (d := d) (U := U) seed s a = b) x y

/-- An exact successful run at the least accepted level. -/
theorem machine_some (hdq : d < q) (hUq : 2 * U < q) (seed : CopySeed J ℓ q)
    (s : CopyState J K q) (hex : (acceptedLevels (d := d) U K seed s).Nonempty) :
    ∃ code : CompactCode d U K,
      let j := selectedLevel (d := d) U K seed s
      Reaches (d := d) (U := U) seed s (initial (d := d) (U := U) s) ⟨⟨j.val, by omega⟩, .halt (some code), true⟩ ∧
      decodedAt (d := d) U K seed s j = some (candidateValue code) ∧
      EnumeratingDecoder.Pass (s j).1 code := by
  have recover (j : Fin (J + 1)) := RecoveryMachine.machine_correct hdq hUq (seed.2 j) (s j)
  let out : Fin (J + 1) → Option (CompactCode d U K) := fun j => Classical.choose (recover j)
  have run (j : Fin (J + 1)) := (Classical.choose_spec (recover j)).1
  have spec (j : Fin (J + 1)) := (Classical.choose_spec (recover j)).2.1
  have pass (j : Fin (J + 1)) := (Classical.choose_spec (recover j)).2.2
  let terminal : Fin (J + 1) → RecoveryMachine.State d U K q := fun j => .halt (out j)
  have fixed : ∀ (i : Fin (J + 1)) (x : RecoveryMachine.State d U K q), RecoveryMachine.done x = true → microStep (d := d) (U := U) seed s i x = x :=
    fun i x hx => RecoveryMachine.done_fixed (seed.2 i) (s i) x hx
  have finished : ∀ j : Fin (J + 1), RecoveryMachine.done (terminal j) = true := fun _ => rfl
  let j := selectedLevel (d := d) U K seed s
  have hj : decodedAt (d := d) U K seed s j ≠ none := by
    obtain ⟨a, ha⟩ := hex
    exact (selectedLevel_le seed s a (Finset.mem_filter.mp ha).2).2
  have hout : out j ≠ none := by
    intro h
    have hs := spec j
    change (out j).map candidateValue = _ at hs
    rw [h] at hs
    exact hj hs.symm
  obtain ⟨code, hcode⟩ := Option.ne_none_iff_exists'.mp hout
  have hbefore : ∀ i : Fin (J + 1), i.val < j.val → RecoveryMachine.accept (terminal i) = false := by
    intro i hi
    have hno : decodedAt (d := d) U K seed s i = none := by
      by_contra hnot
      have hle := (selectedLevel_le seed s i hnot).1
      have hval : j.val ≤ i.val := hle
      omega
    have ho : out i = none := by
      have hs := spec i
      change (out i).map candidateValue = _ at hs
      rw [show decodeSummary U K (seed.2 i) (s i) = none from hno] at hs
      exact Option.map_eq_none_iff.mp hs
    simp [terminal, RecoveryMachine.accept, RecoveryMachine.outputCode, ho]
  have hr := MachineComposition.reaches_start (microInit (d := d) (U := U) s) (.halt none) (microStep (d := d) (U := U) seed s)
    RecoveryMachine.done RecoveryMachine.accept fixed terminal run finished j.val j.isLt.le hbefore
  have ha : RecoveryMachine.accept (terminal j) = true := by
    simp [terminal, RecoveryMachine.accept, RecoveryMachine.outputCode, hcode]
  have hf := MachineComposition.reaches_accept (microInit (d := d) (U := U) s) (.halt none) (microStep (d := d) (U := U) seed s)
    RecoveryMachine.done RecoveryMachine.accept fixed terminal run finished j ha
  refine ⟨code, ?_, ?_, pass j code hcode⟩
  · simpa only [terminal, hcode] using hr.trans hf
  · have hs := spec j
    change (out j).map candidateValue = _ at hs
    simpa only [hcode, Option.map_some] using hs.symm

/-- When every level reports dense, the actual numeric loop reaches its end. -/
theorem machine_none (hdq : d < q) (hUq : 2 * U < q) (seed : CopySeed J ℓ q)
    (s : CopyState J K q) (hex : ¬ (acceptedLevels (d := d) U K seed s).Nonempty) :
    Reaches (d := d) (U := U) seed s (initial (d := d) (U := U) s) (MachineComposition.start (microInit (d := d) (U := U) s) (.halt none) (J + 1) le_rfl) ∧
      step (d := d) (U := U) seed s (MachineComposition.start (microInit (d := d) (U := U) s) (.halt none) (J + 1) le_rfl) =
        MachineComposition.start (microInit (d := d) (U := U) s) (.halt none) (J + 1) le_rfl := by
  have recover (j : Fin (J + 1)) := RecoveryMachine.machine_correct hdq hUq (seed.2 j) (s j)
  let out : Fin (J + 1) → Option (CompactCode d U K) := fun j => Classical.choose (recover j)
  let terminal : Fin (J + 1) → RecoveryMachine.State d U K q := fun j => .halt (out j)
  have fixed : ∀ (i : Fin (J + 1)) (x : RecoveryMachine.State d U K q), RecoveryMachine.done x = true → microStep (d := d) (U := U) seed s i x = x :=
    fun i x hx => RecoveryMachine.done_fixed (seed.2 i) (s i) x hx
  have run (j : Fin (J + 1)) := (Classical.choose_spec (recover j)).1
  have finished : ∀ j : Fin (J + 1), RecoveryMachine.done (terminal j) = true := fun _ => rfl
  have hnone : ∀ j, RecoveryMachine.accept (terminal j) = false := by
    intro j
    have hn : decodedAt (d := d) U K seed s j = none := by
      by_contra h
      exact hex ⟨j, by simp [acceptedLevels, h]⟩
    have hs := (Classical.choose_spec (recover j)).2.1
    change (out j).map candidateValue = _ at hs
    rw [show decodeSummary U K (seed.2 j) (s j) = none from hn] at hs
    have ho := Option.map_eq_none_iff.mp hs
    simp [terminal, RecoveryMachine.accept, RecoveryMachine.outputCode, ho]
  exact MachineComposition.search_none (microInit (d := d) (U := U) s) (.halt none) (microStep (d := d) (U := U) seed s)
    RecoveryMachine.done RecoveryMachine.accept fixed terminal run finished hnone

/-- Actual level counter, recovery registers, and acceptance flag. -/
theorem machine_fits : StreamingSpace.FitsBits (State d U J K q)
    (WeightEval.registerBits (J + 2) + RecoveryMachine.machineBits d U K q + 1) :=
  MachineComposition.state_bits _ _ (WeightEval.lt_two_pow_registerBits (J + 2)).le RecoveryMachine.machine_fits

end Paper02.LevelMachine
