import Paper02.LevelMachine
import Paper02.GenericWeightMachine

/-! # Actual final decoding and generic bounded-weight evaluation of one sketch copy -/
noncomputable section

namespace Paper02.GenericCopyDecoderMachine

open CompactCandidates SparseRecovery Streaming
open GenericWeightMachine

variable {w : ℤ → ℕ}
local instance evaluatorFintype {U : ℕ} (ev : Evaluator U w) : Fintype ev.Carrier := ev.finite

def outputBound (J K : ℕ) : ℕ := 3 * K * 2 ^ J

inductive State (d U J K q : ℕ) (ev : Evaluator U w) [NeZero q] where
  | levels : LevelMachine.State d U J K q → State d U J K q ev
  | weight : Fin (J + 1) → CompactCode d U K → GenericWeightMachine.State ev K → State d U J K q ev
  | halt : Fin (outputBound J K + 1) → State d U J K q ev
  deriving Fintype

variable {d U J ℓ K q : ℕ} [Fact q.Prime] (ev : Evaluator U w)

def scaled (j : Fin (J + 1)) (s : GenericWeightMachine.State ev K) : Fin (outputBound J K + 1) :=
  ⟨2 ^ j.val * GenericWeightMachine.result s, by
    have hp : 2 ^ j.val ≤ 2 ^ J := Nat.pow_le_pow_right (by decide) (by omega)
    have hs := GenericWeightMachine.result_le ev s
    have hm := Nat.mul_le_mul hp hs
    unfold outputBound
    nlinarith⟩

def step (seed : CopySeed J ℓ q) (s : CopyState J K q) : State d U J K q ev → State d U J K q ev
  | .levels l =>
      if l.accepted then
        if hj : l.index.val < J + 1 then
          match RecoveryMachine.outputCode l.micro with
          | none => .halt 0
          | some code => .weight ⟨l.index.val, hj⟩ code (GenericWeightMachine.initial ev K)
        else .halt 0
      else if l.index.val = J + 1 then .halt 0
      else .levels (LevelMachine.step seed s l)
  | .weight j code w => if GenericWeightMachine.done w then .halt (scaled ev j w)
      else .weight j code (GenericWeightMachine.step ev code w)
  | .halt out => .halt out

def initial (s : CopyState J K q) : State d U J K q ev := .levels (LevelMachine.initial (d := d) (U := U) s)

def Reaches (seed : CopySeed J ℓ q) (s : CopyState J K q) (x y : State d U J K q ev) : Prop :=
  Relation.ReflTransGen (fun a b => step ev seed s a = b) x y

lemma lift_levels (seed : CopySeed J ℓ q) (s : CopyState J K q)
    {x y : LevelMachine.State d U J K q} (h : LevelMachine.Reaches (d := d) (U := U) seed s x y) :
    Reaches ev (d := d) (U := U) seed s (.levels x) (.levels y) := by
  apply Relation.ReflTransGen.lift' State.levels _ h
  intro a b hab
  by_cases ha : a.accepted = true
  · have he : a = b := by
      simpa only [LevelMachine.step, MachineComposition.step, ha, ↓reduceIte] using hab
    rw [← he]
  · by_cases hi : a.index.val = J + 1
    · have he : a = b := by
        have hn : ¬ a.index.val < J + 1 := by omega
        simpa only [LevelMachine.step, MachineComposition.step, ha, ↓reduceIte, dif_neg hn] using hab
      rw [← he]
    · exact Relation.ReflTransGen.single (by
        simpa only [step, ha, ↓reduceIte, if_neg hi] using congrArg State.levels hab)

lemma lift_weight (seed : CopySeed J ℓ q) (s : CopyState J K q)
    (j : Fin (J + 1)) (code : CompactCode d U K)
    {x y : GenericWeightMachine.State ev K} (h : GenericWeightMachine.Reaches ev code x y) :
    Reaches ev (d := d) (U := U) seed s (.weight j code x) (.weight j code y) := by
  apply Relation.ReflTransGen.lift' (State.weight j code) _ h
  intro a b hab
  by_cases ha : GenericWeightMachine.done a = true
  · have he : a = b := hab.symm.trans (GenericWeightMachine.done_fixed ev code a ha) |>.symm
    rw [← he]
  · exact Relation.ReflTransGen.single (by
      simpa only [step, ha, ↓reduceIte] using congrArg (State.weight j code) hab)

/-- The actual decoder returns the paper's specified estimator, including when
all levels reject. All decoding and supplied single-weight evaluation workspace occurs in this state. -/
theorem machine_correct (hdq : d < q) (hUq : 2 * U < q)
    (hw0 : w 0 = 0) (hw3 : ∀ k, w k ≤ 3)
    (seed : CopySeed J ℓ q) (s : CopyState J K q) :
    ∃ out : Fin (outputBound J K + 1),
      Reaches ev (d := d) (U := U) seed s (initial ev (d := d) (U := U) s) (.halt out) ∧
      (out.val : ℝ) = Streaming.output (d := d) (fun k => (w k : ℝ)) U K seed s := by
  by_cases hex : (acceptedLevels (d := d) U K seed s).Nonempty
  · obtain ⟨code, hreach, hdecoded, hpass⟩ := LevelMachine.machine_some hdq hUq seed s hex
    let j := selectedLevel (d := d) U K seed s
    have hlevels := lift_levels ev seed s hreach
    have hlaunch : step ev seed s (.levels ⟨⟨j.val, by omega⟩, .halt (some code), true⟩) =
        .weight j code (GenericWeightMachine.initial ev K) := by
      simp [step, j.isLt, RecoveryMachine.outputCode]
    obtain ⟨finish, hwrun, hdone, hweight⟩ := GenericWeightMachine.machine_complete ev hw3 code
    have hw := lift_weight ev seed s j code hwrun
    refine ⟨scaled ev j finish, ((hlevels.tail hlaunch).trans hw).tail ?_, ?_⟩
    · simp [step, hdone]
    · have hinj := (EnumeratingDecoder.compatible_all_iff code).mp hpass.1
      have hsum := GenericWeightMachine.sum_eq_moment hw0 code hinj
      simp only [Streaming.output, hdecoded]
      change ((2 ^ j.val * GenericWeightMachine.result finish : ℕ) : ℝ) = _
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, hweight, hsum]
      rfl
  · have hr := (LevelMachine.machine_none hdq hUq seed s hex).1
    have hl := lift_levels ev seed s hr
    have hn : ∀ j, decodedAt (d := d) U K seed s j = none := by
      intro j
      by_contra h
      exact hex ⟨j, by simp [acceptedLevels, h]⟩
    refine ⟨0, hl.tail ?_, ?_⟩
    · simp [step, MachineComposition.start]
    · simp [Streaming.output, hn]

def done : State d U J K q ev → Bool
  | .halt _ => true
  | _ => false

def result : State d U J K q ev → Fin (outputBound J K + 1)
  | .halt out => out
  | _ => 0

lemma done_fixed (seed : CopySeed J ℓ q) (s : CopyState J K q)
    (x : State d U J K q ev) (hx : done ev x = true) : step ev seed s x = x := by
  cases x <;> simp_all [done, step]

open WeightEval StreamingSpace

def machineBits (d U J K q : ℕ) : ℕ :=
  (registerBits (J + 2) + RecoveryMachine.machineBits d U K q + 1) +
    (registerBits (J + 1) + CandidateChecker.codeBits d U K + GenericWeightMachine.machineBits ev K) +
    registerBits (outputBound J K + 1) + 2

theorem machine_fits : FitsBits (State d U J K q ev) (machineBits ev d U J K q) := by
  let e : State d U J K q ev ≃ LevelMachine.State d U J K q ⊕
      (Fin (J + 1) × CompactCode d U K × GenericWeightMachine.State ev K) ⊕ Fin (outputBound J K + 1) :=
    { toFun := fun x => match x with
        | .levels l => .inl l
        | .weight j c w => .inr (.inl (j, c, w))
        | .halt out => .inr (.inr out)
      invFun := fun x => match x with
        | .inl l => .levels l
        | .inr (.inl jcw) => .weight jcw.1 jcw.2.1 jcw.2.2
        | .inr (.inr out) => .halt out
      left_inv := by intro x; cases x <;> rfl
      right_inv := by intro x; rcases x with l | jcw | out <;> rfl }
  have hh := CandidateChecker.sum_fits
    (LevelMachine.machine_fits (d := d) (U := U) (J := J) (K := K) (q := q))
    (CandidateChecker.sum_fits
      (prod_fits (fin_fits (J + 1)) (prod_fits (compactCandidate_fits d U K) (GenericWeightMachine.machine_fits ev K)))
      (fin_fits (outputBound J K + 1)))
  unfold FitsBits at *
  rw [Fintype.card_congr e]
  apply hh.trans_eq
  congr 1
  unfold machineBits CandidateChecker.codeBits
  omega

end Paper02.GenericCopyDecoderMachine
