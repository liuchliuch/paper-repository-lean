import Paper02.LevelMachine
import Paper02.WeightMachine

/-! # Actual final decoding and direct weight evaluation of one sketch copy -/
noncomputable section

namespace Paper02.CopyDecoderMachine

open CompactCandidates SparseRecovery Streaming

def outputBound (J K : ℕ) : ℕ := 3 * K * 2 ^ J

inductive State (d U J K q : ℕ) [NeZero q] where
  | levels : LevelMachine.State d U J K q → State d U J K q
  | weight : Fin (J + 1) → CompactCode d U K → WeightMachine.State U K → State d U J K q
  | halt : Fin (outputBound J K + 1) → State d U J K q
  deriving Fintype

variable {d U J ℓ K q : ℕ} [Fact q.Prime]

def scaled (j : Fin (J + 1)) (s : WeightMachine.State U K) : Fin (outputBound J K + 1) :=
  ⟨2 ^ j.val * WeightMachine.result s, by
    have hp : 2 ^ j.val ≤ 2 ^ J := Nat.pow_le_pow_right (by decide) (by omega)
    have hs := WeightMachine.result_le s
    have hm := Nat.mul_le_mul hp hs
    unfold outputBound
    nlinarith⟩

def step (seed : CopySeed J ℓ q) (s : CopyState J K q) : State d U J K q → State d U J K q
  | .levels l =>
      if l.accepted then
        if hj : l.index.val < J + 1 then
          match RecoveryMachine.outputCode l.micro with
          | none => .halt 0
          | some code => .weight ⟨l.index.val, hj⟩ code (WeightMachine.initial U K)
        else .halt 0
      else if l.index.val = J + 1 then .halt 0
      else .levels (LevelMachine.step seed s l)
  | .weight j code w => if WeightMachine.done w then .halt (scaled j w)
      else .weight j code (WeightMachine.step code w)
  | .halt out => .halt out

def initial (s : CopyState J K q) : State d U J K q := .levels (LevelMachine.initial (d := d) (U := U) s)

def Reaches (seed : CopySeed J ℓ q) (s : CopyState J K q) (x y : State d U J K q) : Prop :=
  Relation.ReflTransGen (fun a b => step seed s a = b) x y

lemma lift_levels (seed : CopySeed J ℓ q) (s : CopyState J K q)
    {x y : LevelMachine.State d U J K q} (h : LevelMachine.Reaches (d := d) (U := U) seed s x y) :
    Reaches (d := d) (U := U) seed s (.levels x) (.levels y) := by
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
    {x y : WeightMachine.State U K} (h : WeightMachine.Reaches code x y) :
    Reaches (d := d) (U := U) seed s (.weight j code x) (.weight j code y) := by
  apply Relation.ReflTransGen.lift' (State.weight j code) _ h
  intro a b hab
  by_cases ha : WeightMachine.done a = true
  · have he : a = b := hab.symm.trans (WeightMachine.done_fixed code a ha) |>.symm
    rw [← he]
  · exact Relation.ReflTransGen.single (by
      simpa only [step, ha, ↓reduceIte] using congrArg (State.weight j code) hab)

/-- The actual decoder returns the paper's specified estimator, including when
all levels reject. All decoding and f evaluation workspace occurs in this state. -/
theorem machine_correct (hdq : d < q) (hUq : 2 * U < q)
    (seed : CopySeed J ℓ q) (s : CopyState J K q) :
    ∃ out : Fin (outputBound J K + 1),
      Reaches (d := d) (U := U) seed s (initial (d := d) (U := U) s) (.halt out) ∧
      (out.val : ℝ) = Streaming.output (d := d) f U K seed s := by
  by_cases hex : (acceptedLevels (d := d) U K seed s).Nonempty
  · obtain ⟨code, hreach, hdecoded, hpass⟩ := LevelMachine.machine_some hdq hUq seed s hex
    let j := selectedLevel (d := d) U K seed s
    have hlevels := lift_levels seed s hreach
    have hlaunch : step seed s (.levels ⟨⟨j.val, by omega⟩, .halt (some code), true⟩) =
        .weight j code (WeightMachine.initial U K) := by
      simp [step, j.isLt, RecoveryMachine.outputCode]
    obtain ⟨finish, hwrun, hdone, hweight⟩ := WeightMachine.machine_complete code
    have hw := lift_weight seed s j code hwrun
    refine ⟨scaled j finish, ((hlevels.tail hlaunch).trans hw).tail ?_, ?_⟩
    · simp [step, hdone]
    · have hinj := (EnumeratingDecoder.compatible_all_iff code).mp hpass.1
      have hsum := WeightMachine.sum_eq_moment code hinj
      simp only [Streaming.output, hdecoded]
      change ((2 ^ j.val * WeightMachine.result finish : ℕ) : ℝ) = _
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, hweight, hsum]
      rfl
  · have hr := (LevelMachine.machine_none hdq hUq seed s hex).1
    have hl := lift_levels seed s hr
    have hn : ∀ j, decodedAt (d := d) U K seed s j = none := by
      intro j
      by_contra h
      exact hex ⟨j, by simp [acceptedLevels, h]⟩
    refine ⟨0, hl.tail ?_, ?_⟩
    · simp [step, MachineComposition.start]
    · simp [Streaming.output, hn]

def done : State d U J K q → Bool
  | .halt _ => true
  | _ => false

def result : State d U J K q → Fin (outputBound J K + 1)
  | .halt out => out
  | _ => 0

lemma done_fixed (seed : CopySeed J ℓ q) (s : CopyState J K q)
    (x : State d U J K q) (hx : done x = true) : step seed s x = x := by
  cases x <;> simp_all [done, step]

open WeightEval StreamingSpace

def machineBits (d U J K q : ℕ) : ℕ :=
  (registerBits (J + 2) + RecoveryMachine.machineBits d U K q + 1) +
    (registerBits (J + 1) + CandidateChecker.codeBits d U K + WeightMachine.machineBits U K) +
    registerBits (outputBound J K + 1) + 2

theorem machine_fits : FitsBits (State d U J K q) (machineBits d U J K q) := by
  let e : State d U J K q ≃ LevelMachine.State d U J K q ⊕
      (Fin (J + 1) × CompactCode d U K × WeightMachine.State U K) ⊕ Fin (outputBound J K + 1) :=
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
      (prod_fits (fin_fits (J + 1)) (prod_fits (compactCandidate_fits d U K) (WeightMachine.machine_fits U K)))
      (fin_fits (outputBound J K + 1)))
  unfold FitsBits at *
  rw [Fintype.card_congr e]
  apply hh.trans_eq
  congr 1
  unfold machineBits CandidateChecker.codeBits
  omega

end Paper02.CopyDecoderMachine
