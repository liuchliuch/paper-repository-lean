import Paper02.CandidateChecker
import Paper02.MachineComposition

/-! # Actual bounded-state exhaustive recovery

The counter enumerates compact codes in arithmetic order. Each candidate is
loaded and checked by the operational submachine, not by a candidate oracle.
The canonical mathematical decoder is used only as the result specification.
-/
noncomputable section
attribute [local instance] Classical.propDecidable

namespace Paper02.OperationalDecoder

open CompactCandidates EnumeratingDecoder CandidateChecker SparseRecovery

variable {d U K q : ℕ} [Fact q.Prime]

abbrev Count (d U K : ℕ) := (CandidateChecker.base d U) ^ K
abbrev Micro (d U K q : ℕ) [NeZero q] := CandidateChecker.State d U K q
abbrev State (d U K q : ℕ) [NeZero q] := MachineComposition.State (Count d U K) (Micro d U K q)

def defaultMicro : Micro d U K q := .halt (fun _ => none) false

def initial (M : Fin (2 * K) → ZMod q) : State d U K q :=
  MachineComposition.start (fun i => CandidateChecker.initial CandidateIndex.slotDecode i)
    defaultMicro 0 (Nat.zero_le _)

def step (M : Fin (2 * K) → ZMod q) : State d U K q → State d U K q :=
  MachineComposition.step (fun i => CandidateChecker.initial CandidateIndex.slotDecode i)
    defaultMicro (fun _ => CandidateChecker.step CandidateIndex.slotDecode M)
    CandidateChecker.done CandidateChecker.accept

def Reaches (M : Fin (2 * K) → ZMod q) (s t : State d U K q) : Prop :=
  Relation.ReflTransGen (fun x y => step M x = y) s t

def terminal (M : Fin (2 * K) → ZMod q) (i : Fin (Count d U K)) : Micro d U K q :=
  .halt (CandidateIndex.unrank i) (decide (Pass M (CandidateIndex.unrank i)))

def result (s : State d U K q) : Option (Fin d → ℤ) :=
  if s.accepted then some (candidateValue (CandidateChecker.resultCode s.micro)) else none

/-- For every actual stored summary, the explicit finite search reaches the
canonical candidate, or the genuine no-candidate result. -/
theorem machine_correct (hdq : d < q) (hUq : 2 * U < q) (M : Fin (2 * K) → ZMod q) :
    ∃ finish : State d U K q, Reaches M (initial M) finish ∧
      (finish.accepted = true ∨ finish.index.val = Count d U K) ∧
      (finish.accepted = true → Pass M (CandidateChecker.resultCode finish.micro)) ∧
      step M finish = finish ∧ result finish = momentCandidate U K M := by
  let init : Fin (Count d U K) → Micro d U K q :=
    fun i => CandidateChecker.initial CandidateIndex.slotDecode i
  let microStep : Fin (Count d U K) → Micro d U K q → Micro d U K q :=
    fun _ => CandidateChecker.step CandidateIndex.slotDecode M
  have fixed : ∀ i x, CandidateChecker.done x = true → microStep i x = x :=
    fun _ x hx => CandidateChecker.done_fixed CandidateIndex.slotDecode M x hx
  have runs : ∀ i, Relation.ReflTransGen (fun a b => microStep i a = b) (init i) (terminal M i) :=
    fun i => CandidateChecker.concrete_checker_reaches M i
  have finished : ∀ i : Fin (Count d U K), CandidateChecker.done (terminal M i) = true := fun _ => rfl
  cases hc : momentCandidate (d := d) U K M with
  | none =>
    have hnone : ∀ i : Fin (Count d U K), CandidateChecker.accept (terminal M i) = false := by
      intro i
      have hp : ¬ Pass M (CandidateIndex.unrank i) := by
        intro hp
        have hh := momentCandidate_eq_some hdq hUq (pass_is_candidate M _ hp)
        rw [hc] at hh
        contradiction
      simp [terminal, CandidateChecker.accept, hp]
    have hs := MachineComposition.search_none init defaultMicro microStep
      CandidateChecker.done CandidateChecker.accept fixed (terminal M) runs finished hnone
    refine ⟨MachineComposition.start init defaultMicro (Count d U K) le_rfl, hs.1,
      Or.inr rfl, (by simp [MachineComposition.start]), hs.2, ?_⟩
    simp [result, MachineComposition.start, hc]
  | some v =>
    obtain ⟨code, hpass, hvalue⟩ := candidate_has_passing_code M v (momentCandidate_spec hc)
    obtain ⟨i, hi⟩ := CandidateIndex.unrank_surjective d U K code
    have hex : ∃ i : Fin (Count d U K), CandidateChecker.accept (terminal M i) = true := by
      refine ⟨i, ?_⟩
      simp [terminal, CandidateChecker.accept, hi, hpass]
    obtain ⟨j, hj, hreach⟩ := MachineComposition.search_exists init defaultMicro microStep
      CandidateChecker.done CandidateChecker.accept fixed (terminal M) runs finished hex
    let finish : State d U K q := ⟨⟨j.val, by omega⟩, terminal M j, true⟩
    have hp : Pass M (CandidateIndex.unrank j) := by
      simpa [terminal, CandidateChecker.accept] using hj
    have hv : candidateValue (CandidateIndex.unrank j) = v :=
      integerCandidate_unique hdq hUq (pass_is_candidate M _ hp) (momentCandidate_spec hc)
    refine ⟨finish, hreach, Or.inl rfl, (by intro _; exact hp), ?_, ?_⟩
    · exact MachineComposition.accepted_fixed init defaultMicro microStep
        CandidateChecker.done CandidateChecker.accept finish rfl
    · simp [result, finish, terminal, CandidateChecker.resultCode, hv, hc]

/-- The machine's numeric counter, control flag and all actual microregisters
are charged to its working space. -/
theorem machine_fits : StreamingSpace.FitsBits (State d U K q)
    (CandidateChecker.codeBits d U K + CandidateChecker.checkerBits d U K q + 2) := by
  have hn := StreamingSpace.compactCounter_fits d U K
  have hc := CandidateChecker.checker_fits (d := d) (U := U) (K := K) (q := q)
  have hh := MachineComposition.state_bits
    (N := Count d U K) (C := Micro d U K q)
    (CandidateChecker.codeBits d U K + 1) (CandidateChecker.checkerBits d U K q)
    (by simpa [StreamingSpace.FitsBits, CandidateChecker.codeBits, Count, CandidateChecker.base] using hn) hc
  have he : (CandidateChecker.codeBits d U K + 1) + CandidateChecker.checkerBits d U K q + 1 =
      CandidateChecker.codeBits d U K + CandidateChecker.checkerBits d U K q + 2 := by omega
  rw [he] at hh
  exact hh

end Paper02.OperationalDecoder
