import PsgEst.ProbabilityChain
import PsgEst.Estimator

/-!
# Prefix marginalization and subsampling of finite Markov trajectories
-/

open Matrix BigOperators Real Finset Classical

namespace PsgEst

/-- Restrict a trajectory to its first `m+1` observations. -/
def pathPrefix {d m n : ℕ} (h : m ≤ n) (X : Fin (n + 1) → Fin d) :
    Fin (m + 1) → Fin d := fun t => X ⟨t.val, by omega⟩

@[simp] lemma pathPrefix_refl {d n : ℕ} (X : Fin (n + 1) → Fin d) :
    pathPrefix (le_refl n) X = X := by funext i; rfl

lemma pathPrefix_snoc {d m n : ℕ} (h : m ≤ n)
    (Y : Fin (n + 1) → Fin d) (x : Fin d) :
    pathPrefix (h.trans (Nat.le_succ n)) (pathSnoc Y x) = pathPrefix h Y := by
  funext i
  have hi := i.isLt
  exact pathSnoc_castSucc Y x ⟨i.val, by omega⟩

/-- Integrating away any unused terminal part leaves the prefix path law. -/
theorem pathPrefix_sum {d m : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (mu0 : Fin d → ℝ) (hrow : ∀ i, ∑ j, P i j = 1)
    (k : ℕ) (f : (Fin (m + 1) → Fin d) → ℝ) :
    (∑ X : Fin (m + k + 1) → Fin d,
      pathProb P mu0 X * f (pathPrefix (Nat.le_add_right m k) X)) =
    ∑ Y : Fin (m + 1) → Fin d, pathProb P mu0 Y * f Y := by
  induction k with
  | zero => simp
  | succ k ih =>
    refine (sum_path_snoc (d := d) (n := m + k)
      (fun X => pathProb P mu0 X * f (pathPrefix (Nat.le_add_right m (k + 1)) X))).trans ?_
    have hpref (Y : Fin (m + k + 1) → Fin d) (x : Fin d) :
        pathPrefix (Nat.le_add_right m (k + 1)) (pathSnoc Y x) =
          pathPrefix (Nat.le_add_right m k) Y := by
      exact pathPrefix_snoc (Nat.le_add_right m k) Y x
    simp_rw [pathProb_snoc, hpref]
    have hin (Y : Fin (m + k + 1) → Fin d) :
        (∑ x : Fin d, pathProb P mu0 Y * P (Y (Fin.last (m + k))) x *
          f (pathPrefix (Nat.le_add_right m k) Y)) =
          pathProb P mu0 Y * f (pathPrefix (Nat.le_add_right m k) Y) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, hrow, mul_one]
    simp_rw [hin]
    exact ih

/-- Integrate a block of `k` transitions, retaining its endpoint as well as the
whole preceding path.  The block contributes exactly the entry of `P^k`. -/
theorem pathBlock_sum {d m : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (mu0 : Fin d → ℝ) (k : ℕ)
    (f : (Fin (m + 1) → Fin d) → Fin d → ℝ) :
    (∑ X : Fin (m + k + 1) → Fin d, pathProb P mu0 X *
      f (pathPrefix (Nat.le_add_right m k) X) (X (Fin.last (m + k)))) =
    ∑ Y : Fin (m + 1) → Fin d, pathProb P mu0 Y *
      ∑ x : Fin d, (P ^ k) (Y (Fin.last m)) x * f Y x := by
  induction k generalizing f with
  | zero =>
    simp [Matrix.one_apply]
  | succ k ih =>
    refine (sum_path_snoc (d := d) (n := m + k)
      (fun X => pathProb P mu0 X * f (pathPrefix (Nat.le_add_right m (k + 1)) X)
        (X (Fin.last (m + k + 1))))).trans ?_
    have hpref (Y : Fin (m + k + 1) → Fin d) (x : Fin d) :
        pathPrefix (Nat.le_add_right m (k + 1)) (pathSnoc Y x) =
          pathPrefix (Nat.le_add_right m k) Y := by
      exact pathPrefix_snoc (Nat.le_add_right m k) Y x
    simp_rw [pathProb_snoc, hpref, pathSnoc_last, mul_assoc]
    simp_rw [← Finset.mul_sum]
    rw [ih (fun Y z => ∑ x : Fin d, P z x * f Y x)]
    apply Finset.sum_congr rfl
    intro Y _
    congr 1
    rw [pow_succ]
    simp_rw [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring

/-- Prefix marginalization with an arbitrary length comparison. -/
theorem pathPrefix_sum_of_le {d m n : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (mu0 : Fin d → ℝ) (hrow : ∀ i, ∑ j, P i j = 1) (h : m ≤ n)
    (f : (Fin (m + 1) → Fin d) → ℝ) :
    (∑ X : Fin (n + 1) → Fin d, pathProb P mu0 X * f (pathPrefix h X)) =
      ∑ Y : Fin (m + 1) → Fin d, pathProb P mu0 Y * f Y := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h
  exact pathPrefix_sum P mu0 hrow r f

/-- Take every `k`th observation when the total number of transitions is `k*m`. -/
def blockSkip {d k m : ℕ} (X : Fin (k * m + 1) → Fin d) :
    Fin (m + 1) → Fin d := fun t => X ⟨k * t.val, by
      have ht := Nat.mul_le_mul_left k (Nat.le_of_lt_succ t.isLt)
      omega⟩

@[simp] lemma blockSkip_last {d k m : ℕ} (X : Fin (k * m + 1) → Fin d) :
    blockSkip X (Fin.last m) = X (Fin.last (k * m)) := rfl

@[simp] lemma blockSkip_zero {d k : ℕ} (X : Fin (k * 0 + 1) → Fin d) :
    blockSkip (m := 0) X = X := by
  funext i
  have hi : i = 0 := Fin.ext (by omega)
  subst i
  rfl

lemma blockSkip_succ {d k m : ℕ} (X : Fin (k * (m + 1) + 1) → Fin d) :
    blockSkip X = pathSnoc
      (blockSkip (pathPrefix (Nat.mul_le_mul_left k (Nat.le_succ m)) X))
      (X (Fin.last (k * (m + 1)))) := by
  funext i
  unfold blockSkip pathSnoc pathPrefix
  split_ifs with h
  · rfl
  · congr 1
    apply Fin.ext
    have hi : i.val = m + 1 := by omega
    simp [hi]

/-- Exact subsampling law for a path consisting of complete blocks. -/
theorem blockSkip_sum {d : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (mu0 : Fin d → ℝ) (k m : ℕ)
    (f : (Fin (m + 1) → Fin d) → ℝ) :
    (∑ X : Fin (k * m + 1) → Fin d, pathProb P mu0 X * f (blockSkip X)) =
      ∑ Y : Fin (m + 1) → Fin d, pathProb (P ^ k) mu0 Y * f Y := by
  induction m with
  | zero => simp [pathProb]
  | succ m ih =>
    simp_rw [blockSkip_succ]
    have hb := pathBlock_sum P mu0 k
      (fun Y : Fin (k * m + 1) → Fin d => fun x => f (pathSnoc (blockSkip Y) x))
    simp only [← blockSkip_last] at hb
    have hb' : (∑ X : Fin (k * (m + 1) + 1) → Fin d, pathProb P mu0 X *
        f (pathSnoc (blockSkip (pathPrefix
          (Nat.mul_le_mul_left k (Nat.le_succ m)) X)) (X (Fin.last (k * (m + 1)))))) =
        ∑ Y : Fin (k * m + 1) → Fin d, pathProb P mu0 Y *
          ∑ x : Fin d, (P ^ k) (blockSkip Y (Fin.last m)) x *
            f (pathSnoc (blockSkip Y) x) := by
      simpa only [Nat.mul_succ] using hb
    rw [hb', ih (fun Z => ∑ x : Fin d, (P ^ k) (Z (Fin.last m)) x *
      f (pathSnoc Z x))]
    rw [sum_path_snoc (n := m)]
    apply Finset.sum_congr rfl
    intro Y _
    simp_rw [pathProb_snoc, mul_assoc, Finset.mul_sum]

lemma skipPath_eq_blockSkip_prefix {d n : ℕ} (X : Fin (n + 1) → Fin d) (k : ℕ) :
    skipPath X k = blockSkip (pathPrefix (Nat.mul_div_le n k) X) := by
  funext t
  unfold skipPath blockSkip pathPrefix
  congr 1
  apply Fin.ext
  exact Nat.mul_comm t.val k

/-- Subsampling at lag `k` pushes the original trajectory law forward to the
trajectory law with transition matrix `P^k`, discarding the unused terminal steps. -/
theorem skipPath_sum {d n : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (mu0 : Fin d → ℝ) (hrow : ∀ i, ∑ j, P i j = 1) (k : ℕ)
    (f : (Fin (n / k + 1) → Fin d) → ℝ) :
    (∑ X : Fin (n + 1) → Fin d, pathProb P mu0 X * f (skipPath X k)) =
      ∑ Y : Fin (n / k + 1) → Fin d, pathProb (P ^ k) mu0 Y * f Y := by
  simp_rw [skipPath_eq_blockSkip_prefix]
  rw [pathPrefix_sum_of_le P mu0 hrow (Nat.mul_div_le n k) (fun Y => f (blockSkip Y))]
  exact blockSkip_sum P mu0 k (n / k) f

/-- Event-probability form of the lagged trajectory distribution. -/
theorem skipPath_measure {d n : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (mu0 : Fin d → ℝ) (hrow : ∀ i, ∑ j, P i j = 1) (k : ℕ)
    (E : Finset (Fin (n / k + 1) → Fin d)) :
    pathMeasure P mu0 (Finset.univ.filter (fun X => skipPath X k ∈ E)) =
      pathMeasure (P ^ k) mu0 E := by
  have h := skipPath_sum P mu0 hrow k (fun Y => if Y ∈ E then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero] at h
  simpa only [pathMeasure, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.filter_univ_mem] using h

end PsgEst
