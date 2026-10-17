import Paper02.OperationalDecoder
import Paper02.ChecksumMachine

/-! # Sparse recovery including the independent checksum as an actual machine -/
noncomputable section

namespace Paper02.RecoveryMachine

open CompactCandidates CandidateChecker EnumeratingDecoder SparseRecovery

inductive State (d U K q : ℕ) [NeZero q] where
  | recover : OperationalDecoder.State d U K q → State d U K q
  | checksum : CompactCode d U K → ChecksumMachine.State d K q → State d U K q
  | halt : Option (CompactCode d U K) → State d U K q
  deriving Fintype

variable {d U K q : ℕ} [Fact q.Prime]

def checksumInitial : ChecksumMachine.State d K q :=
  ChecksumMachine.registers 0 0 (by omega) (by omega) 1 0

def step (z : ZMod q) (summary : Summary K (ZMod q)) : State d U K q → State d U K q
  | .recover s =>
      if s.accepted then .checksum (CandidateChecker.resultCode s.micro) checksumInitial
      else if s.index.val = OperationalDecoder.Count d U K then .halt none
      else .recover (OperationalDecoder.step summary.1 s)
  | .checksum code s =>
      if s.slot.val < K then .checksum code (ChecksumMachine.step code z s)
      else .halt (if s.accumulator = summary.2 then some code else none)
  | .halt output => .halt output

def Reaches (z : ZMod q) (summary : Summary K (ZMod q)) (s t : State d U K q) : Prop :=
  Relation.ReflTransGen (fun x y => step z summary x = y) s t

def initial (summary : Summary K (ZMod q)) : State d U K q :=
  .recover (OperationalDecoder.initial summary.1)

lemma lift_recovery (z : ZMod q) (summary : Summary K (ZMod q))
    {s t : OperationalDecoder.State d U K q}
    (h : OperationalDecoder.Reaches summary.1 s t) :
    Reaches z summary (.recover s) (.recover t) := by
  apply Relation.ReflTransGen.lift' State.recover _ h
  intro a b hab
  by_cases ha : a.accepted = true
  · have he : a = b := by
      simpa only [OperationalDecoder.step, MachineComposition.step, ha, ↓reduceIte] using hab
    rw [← he]
  · by_cases hi : a.index.val = OperationalDecoder.Count d U K
    · have he : a = b := by
        have hlt : ¬ a.index.val < OperationalDecoder.Count d U K := by omega
        simpa only [OperationalDecoder.step, MachineComposition.step, ha,
          ↓reduceIte, dif_neg hlt] using hab
      rw [← he]
    · apply Relation.ReflTransGen.single
      simpa only [step, ha, ↓reduceIte, if_neg hi] using congrArg State.recover hab

lemma lift_checksum (z : ZMod q) (summary : Summary K (ZMod q)) (code : CompactCode d U K)
    {s t : ChecksumMachine.State d K q} (h : ChecksumMachine.Reaches code z s t) :
    Reaches z summary (.checksum code s) (.checksum code t) := by
  apply Relation.ReflTransGen.lift' (State.checksum code) _ h
  intro a b hab
  by_cases hj : a.slot.val < K
  · exact Relation.ReflTransGen.single (by simpa only [step, if_pos hj] using congrArg (State.checksum code) hab)
  · have he : a = b := by simpa only [ChecksumMachine.step, dif_neg hj] using hab
    rw [← he]

/-- The complete actual recovery algorithm halts with a compact code whose
integer vector is exactly the canonical checksum decoder's answer. Successful
codes retain the coordinate-uniqueness invariant needed for direct evaluation. -/
theorem machine_correct (hdq : d < q) (hUq : 2 * U < q)
    (z : ZMod q) (summary : Summary K (ZMod q)) :
    ∃ out : Option (CompactCode d U K),
      Reaches z summary (initial summary) (.halt out) ∧
      out.map candidateValue = decodeSummary U K z summary ∧
      (∀ code, out = some code → Pass summary.1 code) := by
  obtain ⟨finish, hrun, hterminal, hpass, hfixed, hspec⟩ :=
    OperationalDecoder.machine_correct hdq hUq summary.1
  have hr := lift_recovery z summary hrun
  cases ha : finish.accepted with
  | false =>
    have hi : finish.index.val = OperationalDecoder.Count d U K :=
      hterminal.resolve_left (by simp [ha])
    have hn : momentCandidate (d := d) U K summary.1 = none := by
      simpa [OperationalDecoder.result, ha] using hspec.symm
    refine ⟨none, hr.tail ?_, ?_, ?_⟩
    · simp [step, ha, hi]
    · simp [decodeSummary, hn]
    · simp
  | true =>
    let code := CandidateChecker.resultCode finish.micro
    have hc : Pass summary.1 code := hpass ha
    have hcan : momentCandidate (d := d) U K summary.1 = some (candidateValue code) := by
      simpa [OperationalDecoder.result, ha] using hspec.symm
    have hload : step z summary (.recover finish) = .checksum code checksumInitial := by simp [step, ha, code]
    have hchecksum := lift_checksum z summary code (ChecksumMachine.checker_correct code z).1
    have hall := (hr.tail hload).trans hchecksum
    let out := if checksum (fun i => ((candidateValue code i : ℤ) : ZMod q)) z = summary.2 then some code else none
    refine ⟨out, hall.tail ?_, ?_, ?_⟩
    · simp only [step, ChecksumMachine.registers, lt_self_iff_false, if_false, out]
    · simp only [decodeSummary, hcan, out]
      split_ifs <;> rfl
    · intro c hout
      dsimp [out] at hout
      split_ifs at hout with hsum
      · exact Option.some.inj hout ▸ hc


def done : State d U K q → Bool
  | .halt _ => true
  | _ => false

def outputCode : State d U K q → Option (CompactCode d U K)
  | .halt out => out
  | _ => none

def accept (s : State d U K q) : Bool := (outputCode s).isSome

lemma done_fixed (z : ZMod q) (summary : Summary K (ZMod q))
    (s : State d U K q) (hs : done s = true) : step z summary s = s := by
  cases s <;> simp_all [done, step]

open StreamingSpace WeightEval

def checksumBits (d K q : ℕ) : ℕ :=
  registerBits (K + 1) + registerBits (d + 1) + 2 * registerBits q

def machineBits (d U K q : ℕ) : ℕ :=
  (codeBits d U K + checkerBits d U K q + 2) +
    (codeBits d U K + checksumBits d K q) + (codeBits d U K + 1) + 2

/-- Includes the actual outer counter, both operational submachines, current
compact code, and all control tags. The stored input summary is charged online. -/
theorem machine_fits : FitsBits (State d U K q) (machineBits d U K q) := by
  let e : State d U K q ≃ OperationalDecoder.State d U K q ⊕
      (CompactCode d U K × ChecksumMachine.State d K q) ⊕ Option (CompactCode d U K) :=
    { toFun := fun s => match s with
        | .recover r => .inl r
        | .checksum c k => .inr (.inl (c, k))
        | .halt o => .inr (.inr o)
      invFun := fun s => match s with
        | .inl r => .recover r
        | .inr (.inl ck) => .checksum ck.1 ck.2
        | .inr (.inr o) => .halt o
      left_inv := by intro s; cases s <;> rfl
      right_inv := by intro s; rcases s with r | ck | o <;> rfl }
  have hc := compactCandidate_fits d U K
  have hh := CandidateChecker.sum_fits (OperationalDecoder.machine_fits (d := d) (U := U) (K := K) (q := q))
    (CandidateChecker.sum_fits (prod_fits hc (ChecksumMachine.checker_fits (d := d) (K := K) (q := q))) (option_fits hc))
  unfold FitsBits at *
  rw [Fintype.card_congr e]
  apply hh.trans_eq
  congr 1
  unfold machineBits checksumBits codeBits
  omega

end Paper02.RecoveryMachine
