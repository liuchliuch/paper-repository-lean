import Paper37.RenewalLikelihood
import Paper37.AnalyticBounds
import Mathlib.Data.List.TakeDrop

/-! Stationary cylinder probabilities and occupied-gap counts for the actual
binary renewal block law. Positive gap lengths are used throughout. -/
noncomputable section
namespace Paper37.RenewalOccupancy
open scoped BigOperators
open Paper37.Renewal

lemma wordSum_eq_sum (n : ℕ) (f : List Bool → ℝ) :
    wordSum n f = ∑ x ∈ (words n).toFinset, f x := by
  exact (List.sum_toFinset f (words_nodup n)).symm

lemma wordSum_congr (n : ℕ) {f g : List Bool → ℝ}
    (h : ∀ x, x.length = n → f x = g x) : wordSum n f = wordSum n g := by
  rw [wordSum_eq_sum, wordSum_eq_sum]
  apply Finset.sum_congr rfl
  intro x hx
  exact h x ((mem_words n x).mp (List.mem_toFinset.mp hx))

@[simp] lemma wordSum_zero_fun (n : ℕ) : wordSum n (fun _ => (0:ℝ)) = 0 := by
  simp [wordSum]

lemma wordSum_add (n : ℕ) (f g : List Bool → ℝ) :
    wordSum n (fun x => f x + g x) = wordSum n f + wordSum n g := by
  simp only [wordSum_eq_sum, Finset.sum_add_distrib]

lemma wordSum_finset_sum {α : Type*} (n : ℕ) (s : Finset α) (f : α → List Bool → ℝ) :
    wordSum n (fun x => ∑ a ∈ s, f a x) = ∑ a ∈ s, wordSum n (f a) := by
  simp only [wordSum_eq_sum]
  rw [Finset.sum_comm]

lemma wordSum_append_marginal (μ : Law) (n : ℕ) (a : List Bool) :
    wordSum n (fun x => blockMass μ (a ++ x)) = blockMass μ a := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [wordSum_step]
    have h0 := ih (a ++ [false])
    have h1 := ih (a ++ [true])
    simp only [List.append_assoc, List.singleton_append] at h0 h1
    rw [h0, h1]
    exact (blockMass_right_consistency μ a).symm

/-- Summing all continuations of an exact observed prefix gives its true mass. -/
lemma prefix_cylinder_mass (μ : Law) (a p : List Bool) (r : ℕ) :
    wordSum (p.length+r) (fun x =>
      if x.take p.length = p then blockMass μ (a ++ x) else 0) =
        blockMass μ (a ++ p) := by
  induction p generalizing a with
  | nil => simpa using wordSum_append_marginal μ r a
  | cons b p ih =>
    rw [List.length_cons, Nat.add_right_comm, wordSum_step]
    cases b with
    | false =>
      simp only [List.take_succ_cons, List.cons.injEq, Bool.true_eq_false, false_and, true_and, ↓reduceIte]
      have h := ih (a ++ [false])
      simp only [List.append_assoc, List.singleton_append] at h
      simpa using h
    | true =>
      simp only [List.take_succ_cons, List.cons.injEq, Bool.false_eq_true, false_and, true_and, ↓reduceIte]
      have h := ih (a ++ [true])
      simp only [List.append_assoc, List.singleton_append] at h
      simpa using h

/-- Every fully contained substring has the same cylinder mass, proved from
left and right consistency of the constructed stationary block law. -/
theorem substring_cylinder_mass (μ : Law) (p : List Bool) (i r : ℕ) :
    wordSum (i+p.length+r) (fun x =>
      if (x.drop i).take p.length = p then blockMass μ x else 0) = blockMass μ p := by
  induction i with
  | zero => simpa using prefix_cylinder_mass μ [] p r
  | succ i ih =>
    rw [Nat.succ_add, Nat.succ_add, wordSum_step]
    calc
      wordSum (i+p.length+r) (fun x =>
          if ((false::x).drop (i+1)).take p.length = p then blockMass μ (false::x) else 0) +
        wordSum (i+p.length+r) (fun x =>
          if ((true::x).drop (i+1)).take p.length = p then blockMass μ (true::x) else 0) =
          wordSum (i+p.length+r) (fun x =>
            if (x.drop i).take p.length = p then blockMass μ x else 0) := by
        rw [← wordSum_add]
        apply wordSum_congr
        intro x hx
        simp only [List.drop_succ_cons]
        split_ifs with h
        · exact (blockMass_left_consistency μ x).symm
        · simp
      _ = blockMass μ p := ih

/-- A completed gap of positive length `d` is exactly this visible pattern. -/
def gapPattern (d : ℕ) : List Bool :=
  true :: (List.replicate (d-1) false ++ [true])

lemma gapPattern_length {d : ℕ} (hd : 1 ≤ d) : (gapPattern d).length = d+1 := by
  simp [gapPattern]
  omega

theorem gapPattern_mass (μ : Law) (d : ℕ) :
    blockMass μ (gapPattern d) = μ.mass (d-1) / mean μ := by
  unfold gapPattern blockMass
  simp only [stationaryNumerator, tail_zero, one_mul]
  rw [ordinary_prefix_zeros_one]
  simp [ordinary, tail_zero]

/-- Count the completed gaps of length `d` contained in the `N`-bit word.
The possible left renewal positions are exactly `0,...,N-d-1`. -/
def completedGapCount (N d : ℕ) (x : List Bool) : ℕ :=
  ∑ i ∈ Finset.range (N-d),
    if (x.drop i).take (d+1) = gapPattern d then 1 else 0

/-- Exact count moment from stationary substring probabilities, equation (E.12)'s
preceding display. Both stationary boundary censoring factors are retained. -/
theorem expected_completedGapCount (μ : Law) (N d : ℕ) (hd : 1 ≤ d) (hdN : d < N) :
    wordSum N (fun x => blockMass μ x * (completedGapCount N d x : ℝ)) =
      ((N-d:ℕ):ℝ) * μ.mass (d-1) / mean μ := by
  have hcast (x : List Bool) :
      (completedGapCount N d x : ℝ) =
        ∑ i ∈ Finset.range (N-d),
          if (x.drop i).take (d+1) = gapPattern d then (1:ℝ) else 0 := by
    simp [completedGapCount]
  simp_rw [hcast, Finset.mul_sum]
  rw [wordSum_finset_sum]
  have hterm : ∀ i ∈ Finset.range (N-d),
      wordSum N (fun x => blockMass μ x *
        (if (x.drop i).take (d+1) = gapPattern d then (1:ℝ) else 0)) =
          μ.mass (d-1) / mean μ := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hlen : i+(gapPattern d).length+(N-i-(d+1)) = N := by
      rw [gapPattern_length hd]
      omega
    have hc := substring_cylinder_mass μ (gapPattern d) i (N-i-(d+1))
    rw [hlen, gapPattern_mass μ d] at hc
    simpa only [gapPattern_length hd, mul_ite, mul_one, mul_zero] using hc
  calc
    (∑ i ∈ Finset.range (N-d), wordSum N (fun x => blockMass μ x *
        (if (x.drop i).take (d+1) = gapPattern d then (1:ℝ) else 0))) =
        ∑ _i ∈ Finset.range (N-d), μ.mass (d-1) / mean μ := by
      apply Finset.sum_congr rfl
      exact hterm
    _ = _ := by simp; ring

/-- Number of distinct positive completed-gap lengths occurring in the block. -/
def occupiedTypes (N : ℕ) (x : List Bool) : ℕ :=
  ∑ d ∈ Finset.Ico 1 N, if 0 < completedGapCount N d x then 1 else 0

lemma occupiedTypes_eq_card (N : ℕ) (x : List Bool) :
    occupiedTypes N x = ((Finset.Ico 1 N).filter (fun d => 0 < completedGapCount N d x)).card := by
  simp [occupiedTypes, Finset.sum_boole]

lemma occupiedTypes_le_horizon (N : ℕ) (x : List Bool) : occupiedTypes N x ≤ N-1 := by
  rw [occupiedTypes_eq_card]
  simpa using Finset.card_filter_le (Finset.Ico 1 N) (fun d => 0 < completedGapCount N d x)

abbrev BlockWord (N : ℕ) := {x : List Bool // x ∈ (words N).toFinset}

lemma wordSum_eq_fintype (N : ℕ) (f : List Bool → ℝ) :
    wordSum N f = ∑ x : BlockWord N, f x.val := by
  rw [wordSum_eq_sum, Finset.sum_coe_sort]

/-- Actual stationary expected occupied-type bound (E.12), instantiated from
its indicator/Markov inequality with the exact renewal count moment above. -/
theorem expected_occupiedTypes_le (μ : Law) (N : ℕ) :
    wordSum N (fun x => blockMass μ x * (occupiedTypes N x : ℝ)) ≤
      Paper37.AnalyticBounds.occupiedComplexity N (fun d => μ.mass (d-1)) (mean μ) := by
  let w : BlockWord N → ℝ := fun x => blockMass μ x.val
  let C : BlockWord N → ℕ → ℕ := fun x d => completedGapCount N d x.val
  have hw : ∀ x, 0 ≤ w x := fun x => blockMass_nonneg μ x.val
  have hwsum : ∑ x, w x = 1 := by
    change (∑ x : BlockWord N, blockMass μ x.val) = 1
    rw [← wordSum_eq_fintype]
    exact blockMass_normalized μ N
  have hm : ∀ d ∈ Finset.Ico 1 N, (∑ x, w x * (C x d : ℝ)) =
      ((N-d:ℕ):ℝ) * μ.mass (d-1) / mean μ := by
    intro d hd
    change (∑ x : BlockWord N, blockMass μ x.val * (completedGapCount N d x.val : ℝ)) = _
    simpa only [wordSum_eq_fintype] using
      expected_completedGapCount μ N d (Finset.mem_Ico.mp hd).1 (Finset.mem_Ico.mp hd).2
  have h := Paper37.AnalyticBounds.expectedDistinct_le_complexity
    N w C (fun d => μ.mass (d-1)) (mean μ) hw hwsum hm
  rw [wordSum_eq_fintype]
  convert h using 1
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  simp [occupiedTypes, C]


/-- Stationary averaging of the actual occupied-type oracle branch. This
combines the cylinder-derived occupancy moment with the finite oracle lemma. -/
theorem expected_adaptiveOracle_le (μ : Law) {N : ℕ} (hN : 1 ≤ N) :
    wordSum N (fun x => blockMass μ x *
      min (Paper37.AnalyticBounds.redundancyBound N)
        ((2*((max 1 (occupiedTypes N x):ℕ):ℝ)+2)*Real.log ((N:ℝ)+1) +
          2*Real.log (((max 1 (occupiedTypes N x):ℕ):ℝ)+1))) ≤
      min (Paper37.AnalyticBounds.redundancyBound N)
        ((2*Paper37.AnalyticBounds.occupiedComplexity N
          (fun d => μ.mass (d-1)) (mean μ)+6)*Real.log ((N:ℝ)+1)) := by
  let w : BlockWord N → ℝ := fun x => blockMass μ x.val
  let V : BlockWord N → ℕ := fun x => occupiedTypes N x.val
  have hw : ∀ x, 0 ≤ w x := fun x => blockMass_nonneg μ x.val
  have hwsum : ∑ x, w x = 1 := by
    change (∑ x : BlockWord N, blockMass μ x.val) = 1
    rw [← wordSum_eq_fintype]
    exact blockMass_normalized μ N
  have hV : ∀ x, V x ≤ N-1 := fun x => occupiedTypes_le_horizon N x.val
  have hv : (∑ x, w x * (V x:ℝ)) ≤
      Paper37.AnalyticBounds.occupiedComplexity N (fun d => μ.mass (d-1)) (mean μ) := by
    change (∑ x : BlockWord N, blockMass μ x.val * (occupiedTypes N x.val:ℝ)) ≤ _
    simpa only [wordSum_eq_fintype] using expected_occupiedTypes_le μ N
  have h := Paper37.AnalyticBounds.expectedOracle_le hN w V
    (Paper37.AnalyticBounds.occupiedComplexity N (fun d => μ.mass (d-1)) (mean μ))
    hw hwsum hV hv
  rw [wordSum_eq_fintype]
  exact h

end Paper37.RenewalOccupancy
