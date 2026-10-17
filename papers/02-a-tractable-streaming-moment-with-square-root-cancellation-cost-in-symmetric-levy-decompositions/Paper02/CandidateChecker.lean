import Paper02.CandidateLoader
import Paper02.CandidateIndex

/-! # Composition of the actual bounded-register candidate checks -/
noncomputable section
attribute [local instance] Classical.propDecidable

namespace Paper02.CandidateChecker

open CompactCandidates EnumeratingDecoder

abbrev Entry (d U : ℕ) := Option (Fin d × Fin (2 * U + 1))
def base (d U : ℕ) : ℕ := 1 + d * (2 * U + 1)

inductive State (d U K q : ℕ) [NeZero q] where
  | load : CandidateLoader.State (Entry d U) K (base d U) → State d U K q
  | validate : CompactCode d U K → BooleanState (K * K) → State d U K q
  | moments : CompactCode d U K → MomentMachine.State K q → State d U K q
  | halt : CompactCode d U K → Bool → State d U K q
  deriving Fintype

variable {d U K q : ℕ} [Fact q.Prime]

def momentInitial : MomentMachine.State K q :=
  MomentMachine.registers 0 0 0 (by omega) (by omega) (by omega) 1 0 true

def step (decode : Fin (base d U) → Entry d U) (M : Fin (2 * K) → ZMod q) :
    State d U K q → State d U K q
  | .load s =>
      if s.position.val < K then .load (CandidateLoader.step (by unfold base; omega) decode s)
      else .validate s.cells ⟨0, true⟩
  | .validate code s =>
      if s.index.val < K * K then .validate code (booleanStep (compatibilityTest code) s)
      else if s.good then .moments code momentInitial else .halt code false
  | .moments code s =>
      if s.moment.val < 2 * K then
        .moments code (MomentMachine.step (fun j => slotNode (code j) q)
          (fun j => slotWeight (code j) q) M s)
      else .halt code s.good
  | .halt code good => .halt code good

def Reaches (decode : Fin (base d U) → Entry d U) (M : Fin (2 * K) → ZMod q)
    (s t : State d U K q) : Prop :=
  Relation.ReflTransGen (fun x y => step decode M x = y) s t

def initial (decode : Fin (base d U) → Entry d U) (i : Fin ((base d U) ^ K)) : State d U K q :=
  .load (CandidateLoader.expected (by unfold base; omega) decode none i 0 (by omega))

lemma lift_loader (decode : Fin (base d U) → Entry d U) (M : Fin (2 * K) → ZMod q)
    {s t : CandidateLoader.State (Entry d U) K (base d U)}
    (h : Relation.ReflTransGen (fun x y => CandidateLoader.step (by unfold base; omega) decode x = y) s t) :
    Reaches decode M (.load s) (.load t) := by
  apply Relation.ReflTransGen.lift' State.load _ h
  intro a b hab
  by_cases hj : a.position.val < K
  · exact Relation.ReflTransGen.single (by simpa only [step, if_pos hj] using congrArg State.load hab)
  · have he : a = b := by simpa only [CandidateLoader.step, dif_neg hj] using hab
    rw [← he]

lemma lift_validation (decode : Fin (base d U) → Entry d U) (M : Fin (2 * K) → ZMod q)
    (code : CompactCode d U K) {s t : BooleanState (K * K)}
    (h : Relation.ReflTransGen (fun x y => booleanStep (compatibilityTest code) x = y) s t) :
    Reaches decode M (.validate code s) (.validate code t) := by
  apply Relation.ReflTransGen.lift' (State.validate code) _ h
  intro a b hab
  by_cases hj : a.index.val < K * K
  · exact Relation.ReflTransGen.single (by simpa only [step, if_pos hj] using congrArg (State.validate code) hab)
  · have he : a = b := by simpa only [booleanStep, dif_neg hj] using hab
    rw [← he]

lemma lift_moments (decode : Fin (base d U) → Entry d U) (M : Fin (2 * K) → ZMod q)
    (code : CompactCode d U K) {s t : MomentMachine.State K q}
    (h : MomentMachine.Reaches (fun j => slotNode (code j) q) (fun j => slotWeight (code j) q) M s t) :
    Reaches decode M (.moments code s) (.moments code t) := by
  apply Relation.ReflTransGen.lift' (State.moments code) _ h
  intro a b hab
  by_cases hj : a.moment.val < 2 * K
  · exact Relation.ReflTransGen.single (by simpa only [step, if_pos hj] using congrArg (State.moments code) hab)
  · have he : a = b := by simpa only [MomentMachine.step, dif_neg hj] using hab
    rw [← he]

lemma validation_flag (code : CompactCode d U K) :
    booleanPrefix (compatibilityTest code) (K * K) =
      decide (∀ j k, compatible code j k = true) := by
  apply Bool.eq_iff_iff.mpr
  have hh := (boolean_checker_correct (compatibilityTest code)).2.2
  simpa only [decide_eq_true_eq] using hh.trans (compatibility_test_iff code)

lemma moment_flag (code : CompactCode d U K) (M : Fin (2 * K) → ZMod q) :
    MomentMachine.goodPrefix (fun j => slotNode (code j) q) (fun j => slotWeight (code j) q) M (2 * K) =
      decide (SparseRecovery.integerMoments K (candidateValue code) = M) := by
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using (compact_moment_checker_correct code M).2

/-- A whole candidate test halts through the loader, index checks and moment
arithmetic, and its flag has the exact mathematical candidate meaning. -/
theorem checker_reaches (decode : Fin (base d U) → Entry d U)
    (M : Fin (2 * K) → ZMod q) (i : Fin ((base d U) ^ K)) :
    let code := CandidateLoader.digits (by unfold base; omega) decode i.val
    Reaches decode M (initial decode i) (.halt code (decide (Pass M code))) := by
  dsimp only
  let hb : 0 < base d U := by unfold base; omega
  let code : CompactCode d U K := CandidateLoader.digits hb decode i.val
  let loaded := CandidateLoader.expected hb decode none i K (le_refl _)
  have hl : Reaches decode M (initial decode i) (.load loaded) :=
    lift_loader decode M (CandidateLoader.loader_reaches hb decode none i K (le_refl _))
  have hload : step decode M (.load loaded) = .validate code ⟨0, true⟩ := by
    simp only [step, loaded, CandidateLoader.expected, lt_self_iff_false, if_false]
    congr 2
    exact (CandidateLoader.loader_correct hb decode none i).2.2
  have hv := lift_validation decode M code (boolean_reaches (compatibilityTest code) (K * K) (le_refl _))
  have hp := (hl.tail hload).trans hv
  let valid := decide (∀ j k, compatible code j k = true)
  have hvflag := validation_flag code
  change Reaches decode M _ (.halt code (decide (Pass M code)))
  by_cases hc : ∀ j k, compatible code j k = true
  · have hm := lift_moments decode M code (compact_moment_checker_correct code M).1
    have hgo : step decode M (.validate code
        ⟨⟨K * K, by omega⟩, booleanPrefix (compatibilityTest code) (K * K)⟩) =
          .moments code momentInitial := by simp [step, hvflag, hc]
    have hfinish := (hp.tail hgo).trans hm
    apply hfinish.tail
    simp [step, MomentMachine.registers, moment_flag, Pass, hc]
  · apply hp.tail
    simp [step, hvflag, hc, Pass]

def done : State d U K q → Bool
  | .halt _ _ => true
  | _ => false

def accept : State d U K q → Bool
  | .halt _ good => good
  | _ => false

def resultCode : State d U K q → CompactCode d U K
  | .load s => s.cells
  | .validate code _ => code
  | .moments code _ => code
  | .halt code _ => code

lemma done_fixed (decode : Fin (base d U) → Entry d U) (M : Fin (2 * K) → ZMod q)
    (s : State d U K q) (hs : done s = true) : step decode M s = s := by
  cases s <;> simp_all [done, step]


/-- The loader's arithmetic digits are the explicit finite-base enumeration. -/
lemma digits_eq_unrank (i : Fin ((base d U) ^ K)) :
    CandidateLoader.digits (K := K) (by unfold CandidateIndex.base; omega)
      (CandidateIndex.slotDecode (d := d) (U := U)) i.val = CandidateIndex.unrank i := rfl

/-- Concrete input-independent enumeration of all compact candidates. -/
theorem concrete_checker_reaches (M : Fin (2 * K) → ZMod q)
    (i : Fin ((base d U) ^ K)) :
    Reaches CandidateIndex.slotDecode M (initial CandidateIndex.slotDecode i)
      (.halt (CandidateIndex.unrank i) (decide (Pass M (CandidateIndex.unrank i)))) := by
  simpa only [digits_eq_unrank] using checker_reaches CandidateIndex.slotDecode M i

open StreamingSpace WeightEval

def codeBits (d U K : ℕ) : ℕ :=
  K * (registerBits (d + 1) + registerBits (2 * U + 1) + 1)

def loaderBits (d U K : ℕ) : ℕ :=
  (codeBits d U K + 1) + registerBits (K + 1) + codeBits d U K

def boolBits (K : ℕ) : ℕ := registerBits (K * K + 1) + 1

def momentBits (K q : ℕ) : ℕ :=
  2 * registerBits (2 * K + 1) + registerBits (K + 1) + 2 * registerBits q + 1

def checkerBits (d U K q : ℕ) : ℕ :=
  loaderBits d U K + (codeBits d U K + boolBits K) +
    (codeBits d U K + momentBits K q) + (codeBits d U K + 1) + 3

lemma sum_fits {A B : Type*} [Fintype A] [Fintype B] {a b : ℕ}
    (hA : FitsBits A a) (hB : FitsBits B b) : FitsBits (A ⊕ B) (a + b + 1) := by
  unfold FitsBits at *
  rw [Fintype.card_sum, pow_succ]
  have ha := hA.trans (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_add_right a b))
  have hb := hB.trans (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_add_left b a))
  omega

lemma loader_fits : FitsBits (CandidateLoader.State (Entry d U) K (base d U)) (loaderBits d U K) := by
  let e : CandidateLoader.State (Entry d U) K (base d U) ≃
      Fin ((base d U) ^ K + 1) × Fin (K + 1) × CompactCode d U K :=
    { toFun := fun s => (s.quotient, s.position, s.cells)
      invFun := fun s => ⟨s.1, s.2.1, s.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold FitsBits
  rw [Fintype.card_congr e]
  have h := prod_fits (compactCounter_fits d U K)
    (prod_fits (fin_fits (K + 1)) (compactCandidate_fits d U K))
  simpa only [FitsBits, loaderBits, codeBits, base, Nat.add_assoc] using h

/-- This cardinal bound counts the actual state of the loader and both checking
loops, rather than a workspace type unrelated to the decoder's execution. -/
theorem checker_fits : FitsBits (State d U K q) (checkerBits d U K q) := by
  let Code := CompactCode d U K
  let L := CandidateLoader.State (Entry d U) K (base d U)
  let V := Code × BooleanState (K * K)
  let P := Code × MomentMachine.State K q
  let H := Code × Bool
  let e : State d U K q ≃ L ⊕ V ⊕ P ⊕ H :=
    { toFun := fun s => match s with
        | .load l => .inl l
        | .validate c v => .inr (.inl (c, v))
        | .moments c p => .inr (.inr (.inl (c, p)))
        | .halt c h => .inr (.inr (.inr (c, h)))
      invFun := fun s => match s with
        | .inl l => .load l
        | .inr (.inl v) => .validate v.1 v.2
        | .inr (.inr (.inl p)) => .moments p.1 p.2
        | .inr (.inr (.inr h)) => .halt h.1 h.2
      left_inv := by intro s; cases s <;> rfl
      right_inv := by intro s; rcases s with l | v | p | h <;> rfl }
  have hc : FitsBits Code (codeBits d U K) := compactCandidate_fits d U K
  have hv : FitsBits V (codeBits d U K + boolBits K) :=
    prod_fits hc (boolean_space_bound (K * K))
  have hp : FitsBits P (codeBits d U K + momentBits K q) :=
    prod_fits hc MomentMachine.checker_space_bound
  have hh : FitsBits H (codeBits d U K + 1) := prod_fits hc (by simp [FitsBits])
  have ht := sum_fits (loader_fits (d := d) (U := U) (K := K)) (sum_fits hv (sum_fits hp hh))
  unfold FitsBits at *
  rw [Fintype.card_congr e]
  convert ht using 1 <;> simp only [checkerBits] <;> congr 1 <;> omega

end Paper02.CandidateChecker
