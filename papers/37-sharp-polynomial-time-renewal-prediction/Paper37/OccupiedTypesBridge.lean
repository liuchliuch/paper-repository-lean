import Paper37.Adaptive
import Paper37.RenewalOccupancy
import Mathlib.Data.List.Infix

/-! The source parse-based `V_N` is exactly the stationary occupied-gap
count used in the expectation bounds, rather than a surrogate statistic. -/
namespace Paper37.OccupiedTypesBridge
open scoped BigOperators
open Paper37.Renewal Paper37.Prediction Paper37.RenewalOccupancy

def zeroOne (g : ℕ) : List Bool := List.replicate g false ++ [true]

def visibleGaps (x : List Bool) : List ℕ :=
  match firstSuffix x with
  | none => []
  | some z => gapsFrom 0 z

lemma gapPattern_succ (g : ℕ) : gapPattern (g+1) = true :: zeroOne g := by
  simp [gapPattern, zeroOne]

@[simp] lemma zeroOne_prefix_true (g : ℕ) (x : List Bool) :
    (zeroOne g).IsPrefix (true::x) ↔ g = 0 := by
  cases g <;> simp [zeroOne, List.replicate_succ]

@[simp] lemma zeroOne_succ_prefix_false (g : ℕ) (x : List Bool) :
    (zeroOne (g+1)).IsPrefix (false::x) ↔ (zeroOne g).IsPrefix x := by
  simp [zeroOne, List.replicate_succ]

/-- Every parser output is either the first completed gap from the supplied
initial age or a fully internal visible renewal pattern. -/
lemma mem_gapsFrom_iff (a g : ℕ) (x : List Bool) :
    g ∈ gapsFrom a x ↔
      (a ≤ g ∧ (zeroOne (g-a)).IsPrefix x) ∨ (gapPattern (g+1)).IsInfix x := by
  induction x generalizing a with
  | nil => simp [gapsFrom, zeroOne, gapPattern]
  | cons b x ih =>
    cases b with
    | false =>
      rw [gapsFrom, ih]
      by_cases ha : a+1 ≤ g
      · have ha' : a ≤ g := by omega
        have he : g-a = g-(a+1)+1 := by omega
        simp [ha, ha', he, List.infix_cons_iff, gapPattern_succ]
      · by_cases ha' : a ≤ g
        · have he : g = a := by omega
          simp [he, List.infix_cons_iff, gapPattern_succ, zeroOne]
        · simp [ha, ha', List.infix_cons_iff, gapPattern_succ]
    | true =>
      rw [gapsFrom, List.mem_cons, ih 0]
      simp only [Nat.zero_le, Nat.sub_zero, true_and, List.infix_cons_iff,
        gapPattern_succ, List.cons_prefix_cons, true_and, zeroOne_prefix_true]
      have he : (a ≤ g ∧ g-a=0) ↔ g=a := by omega
      rw [he]

/-- An internal completed gap in the source first-renewal parse is precisely
a fully observed binary pattern with its two renewal endpoints. -/
theorem mem_visibleGaps_iff (g : ℕ) (x : List Bool) :
    g ∈ visibleGaps x ↔ (gapPattern (g+1)).IsInfix x := by
  induction x with
  | nil => simp [visibleGaps, firstSuffix, gapPattern]
  | cons b x ih =>
    cases b with
    | false => simpa [visibleGaps, firstSuffix, List.infix_cons_iff, gapPattern_succ] using ih
    | true =>
      simp only [visibleGaps, firstSuffix]
      rw [mem_gapsFrom_iff]
      simp [List.infix_cons_iff, gapPattern_succ]

/-- A positive occurrence count is equivalent to a genuine fully contained
substring; the count definition's finite range is exactly the valid range. -/
theorem completedGapCount_pos_iff {N d : ℕ} {x : List Bool}
    (hx : x.length = N) (hd : 1 ≤ d) :
    0 < completedGapCount N d x ↔ (gapPattern d).IsInfix x := by
  constructor
  · intro hc
    obtain ⟨i, hi, hpos⟩ := Finset.sum_pos_iff.mp hc
    have hpat : (x.drop i).take (d+1) = gapPattern d := by
      split_ifs at hpos with h
      · exact h
      · simp at hpos
    refine ⟨x.take i, x.drop (i+(d+1)), ?_⟩
    rw [← hpat, List.append_assoc, List.drop_take_append_drop, List.take_append_drop]
  · rintro ⟨a,b,hab⟩
    have hlen := congrArg List.length hab
    simp only [List.length_append, gapPattern_length hd] at hlen
    have hi : a.length ∈ Finset.range (N-d) := by
      apply Finset.mem_range.mpr
      omega
    have hpat : (x.drop a.length).take (d+1) = gapPattern d := by
      rw [← hab, List.append_assoc, List.drop_left, ← gapPattern_length hd, List.take_left]
    unfold completedGapCount
    apply Finset.sum_pos_iff.mpr
    exact ⟨a.length, hi, by simp [hpat]⟩

lemma visibleGaps_card (x : List Bool) :
    Paper37.Adaptive.visibleTypes x = (visibleGaps x).toFinset.card := by
  unfold Paper37.Adaptive.visibleTypes visibleGaps
  cases firstSuffix x <;> simp [Paper37.Adaptive.nu]

/-- Exact source `V_N` identification needed to average the adaptive oracle. -/
theorem visibleTypes_eq_occupiedTypes {N : ℕ} (x : List Bool) (hx : x.length = N) :
    Paper37.Adaptive.visibleTypes x = occupiedTypes N x := by
  have hset : (Finset.Ico 1 N).filter (fun d => 0 < completedGapCount N d x) =
      (visibleGaps x).toFinset.image (fun g => g+1) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_image, List.mem_toFinset]
    constructor
    · rintro ⟨⟨hd,hdN⟩,hc⟩
      refine ⟨d-1, ?_, by omega⟩
      rw [mem_visibleGaps_iff]
      have he : d-1+1 = d := by omega
      rw [he]
      exact (completedGapCount_pos_iff hx hd).mp hc
    · rintro ⟨g,hg,rfl⟩
      have hinf := (mem_visibleGaps_iff g x).mp hg
      have hlen := hinf.length_le
      rw [gapPattern_length (by omega)] at hlen
      rw [hx] at hlen
      exact ⟨⟨by omega,by omega⟩, (completedGapCount_pos_iff hx (by omega)).mpr hinf⟩
  rw [occupiedTypes_eq_card, hset, Finset.card_image_of_injective _ (by intro a b h; simpa using h),
    visibleGaps_card]

end Paper37.OccupiedTypesBridge
