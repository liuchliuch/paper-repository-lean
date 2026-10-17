import PsgEst.ProbabilityThinning

/-! Exact shifted and offset-thinned laws on the finite Markov path space. -/

open Matrix BigOperators Real Finset Classical
namespace PsgEst

/-- The actual law after `r` transitions, with no positivity restriction on its support. -/
noncomputable def shiftedLaw {d : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (mu : Fin d → ℝ) (r : ℕ) : Fin d → ℝ := fun j => ∑ i, mu i * (P ^ r) i j

lemma shiftedLaw_nonneg {d : ℕ} (S : Stoch d) (mu : Fin d → ℝ)
    (hmu : ∀ i, 0 ≤ mu i) (r : ℕ) : ∀ j, 0 ≤ shiftedLaw S.P mu r j := by
  intro j
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hmu i) (S.pow_nonneg r i j)

lemma shiftedLaw_sum {d : ℕ} (S : Stoch d) (mu : Fin d → ℝ)
    (hsum : ∑ i, mu i = 1) (r : ℕ) : ∑ j, shiftedLaw S.P mu r j = 1 := by
  unfold shiftedLaw
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, S.pow_row_stoch, mul_one]
  exact hsum

/-- Integrating one-observation paths is the same as summing their sole state. -/
lemma sum_single_path {d : ℕ} (f : (Fin 1 → Fin d) → ℝ) :
    (∑ Y : Fin 1 → Fin d, f Y) = ∑ x : Fin d, f (fun _ => x) := by
  exact (Equiv.sum_comp (Equiv.funUnique (Fin 1) (Fin d)).symm f).symm

/-- Marginalizing a Markov path at its terminal state gives `mu P^r`. -/
theorem pathLast_sum {d : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (mu : Fin d → ℝ) (r : ℕ) (g : Fin d → ℝ) :
    (∑ X : Fin (r + 1) → Fin d, pathProb P mu X * g (X (Fin.last r))) =
      ∑ x : Fin d, shiftedLaw P mu r x * g x := by
  have hb := pathBlock_sum (m := 0) P mu r (fun _ x => g x)
  rw [sum_single_path] at hb
  have hzero (x : Fin d) : pathProb P mu (fun _ : Fin 1 => x) = mu x := by
    simp [pathProb]
  simp only [hzero] at hb
  generalize hR : 0 + r = r0 at hb
  have hr0 : r0 = r := hR.symm.trans (Nat.zero_add r)
  clear hR
  subst r0
  rw [hb]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [shiftedLaw, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Discard the first `r` transitions and retain the following `m+1` observations. -/
def pathShift {d m : ℕ} (r : ℕ) (X : Fin (r + m + 1) → Fin d) :
    Fin (m + 1) → Fin d := fun t => X ⟨r + t.val, by have ht := t.isLt; omega⟩

@[simp] lemma pathShift_last {d m : ℕ} (r : ℕ) (X : Fin (r + m + 1) → Fin d) :
    pathShift (m := m) r X (Fin.last m) = X (Fin.last (r + m)) := rfl

lemma pathShift_snoc {d m : ℕ} (r : ℕ) (Y : Fin (r + m + 1) → Fin d) (x : Fin d) :
    pathShift (m := m + 1) r (pathSnoc Y x) = pathSnoc (pathShift (m := m) r Y) x := by
  funext i
  by_cases hi : i.val < m + 1
  · have hri : r + i.val < r + m + 1 := by omega
    simp only [pathShift, pathSnoc, Nat.add_eq, dif_pos hi, dif_pos hri]
  · have hri : ¬r + i.val < r + m + 1 := by omega
    simp only [pathShift, pathSnoc, Nat.add_eq, dif_neg hi, dif_neg hri]

/-- Exact law of a suffix, proved by terminal extension of its retained path. -/
theorem pathShift_sum {d : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (mu : Fin d → ℝ) (r m : ℕ) (f : (Fin (m + 1) → Fin d) → ℝ) :
    (∑ X : Fin (r + m + 1) → Fin d, pathProb P mu X * f (pathShift (m := m) r X)) =
      ∑ Y : Fin (m + 1) → Fin d, pathProb P (shiftedLaw P mu r) Y * f Y := by
  induction m with
  | zero =>
    have hs (X : Fin (r + 0 + 1) → Fin d) :
        pathShift (m := 0) r X = fun _ => X (Fin.last r) := by
      funext i
      have hi : i = 0 := Fin.ext (by omega)
      subst i
      rfl
    simp_rw [hs]
    rw [pathLast_sum P mu r (fun x => f (fun _ => x)), sum_single_path]
    simp [pathProb]
  | succ m ih =>
    have hsnoc := sum_path_snoc (n := r + m) (fun X =>
      pathProb P mu X * f (pathShift (m := m + 1) r X))
    convert hsnoc.trans ?_ using 1
    simp_rw [pathProb_snoc, pathShift_snoc, ← pathShift_last (m := m) r, mul_assoc]
    simp_rw [← Finset.mul_sum]
    rw [ih (fun Z => ∑ x, P (Z (Fin.last m)) x * f (pathSnoc Z x))]
    rw [sum_path_snoc (n := m)]
    apply Finset.sum_congr rfl
    intro Y _
    simp_rw [pathProb_snoc, mul_assoc, Finset.mul_sum]

/-- Select every `b`th observation after an arbitrary initial offset `r`. -/
def offsetBlockSkip {d : ℕ} (r b m : ℕ) (X : Fin (r + b * m + 1) → Fin d) :
    Fin (m + 1) → Fin d := blockSkip (pathShift (m := b * m) r X)

lemma offsetBlockSkip_apply {d : ℕ} (r b m : ℕ)
    (X : Fin (r + b * m + 1) → Fin d) (t : Fin (m + 1)) :
    offsetBlockSkip r b m X t = X ⟨r + b * t.val, by
      have hh := Nat.mul_le_mul_left b (Nat.le_of_lt_succ t.isLt)
      omega⟩ := rfl

/-- Offset thinning has the genuine `P^b` path law with initial distribution `mu P^r`. -/
theorem offsetBlockSkip_sum {d : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (mu : Fin d → ℝ) (r b m : ℕ) (f : (Fin (m + 1) → Fin d) → ℝ) :
    (∑ X : Fin (r + b * m + 1) → Fin d,
      pathProb P mu X * f (offsetBlockSkip r b m X)) =
      ∑ Y : Fin (m + 1) → Fin d, pathProb (P ^ b) (shiftedLaw P mu r) Y * f Y := by
  unfold offsetBlockSkip
  rw [pathShift_sum P mu r (b * m) (fun Y => f (blockSkip Y))]
  exact blockSkip_sum P (shiftedLaw P mu r) b m f

/-- Offset thinning inside a longer path, with unused terminal steps discarded. -/
def offsetSkip {d n : ℕ} (r b m : ℕ) (h : r + b * m ≤ n)
    (X : Fin (n + 1) → Fin d) : Fin (m + 1) → Fin d :=
  offsetBlockSkip r b m (pathPrefix h X)

/-- Full marginalization theorem for arbitrary offset and lag, without assumptions
on the starting support. -/
theorem offsetSkip_sum {d n : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (mu : Fin d → ℝ) (hrow : ∀ i, ∑ j, P i j = 1)
    (r b m : ℕ) (h : r + b * m ≤ n) (f : (Fin (m + 1) → Fin d) → ℝ) :
    (∑ X : Fin (n + 1) → Fin d, pathProb P mu X * f (offsetSkip r b m h X)) =
      ∑ Y : Fin (m + 1) → Fin d, pathProb (P ^ b) (shiftedLaw P mu r) Y * f Y := by
  unfold offsetSkip
  rw [pathPrefix_sum_of_le P mu hrow h (fun Y => f (offsetBlockSkip r b m Y))]
  exact offsetBlockSkip_sum P mu r b m f

/-- Event-probability form of the offset thinning law. -/
theorem offsetSkip_measure {d n : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (mu : Fin d → ℝ) (hrow : ∀ i, ∑ j, P i j = 1)
    (r b m : ℕ) (h : r + b * m ≤ n) (E : Finset (Fin (m + 1) → Fin d)) :
    pathMeasure P mu (Finset.univ.filter (fun X => offsetSkip r b m h X ∈ E)) =
      pathMeasure (P ^ b) (shiftedLaw P mu r) E := by
  have hh := offsetSkip_sum P mu hrow r b m h (fun Y => if Y ∈ E then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero] at hh
  simpa only [pathMeasure, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.filter_univ_mem] using hh

end PsgEst
