import PsgEst.Probability

/-!
# Finite path chain rule

A finite path sum decomposes by its prefix and final state.  Applying this
bijection to relative entropy gives its one-step chain rule, including an
initial law with zeros (and hence a point mass initial law).
-/

open Matrix BigOperators Real Finset Classical

namespace PsgEst

/-- Decompose a sum over paths into a sum over their prefix and last state. -/
lemma sum_path_snoc {d n : ℕ} (f : (Fin (n + 2) → Fin d) → ℝ) :
    ∑ X, f X = ∑ Y : Fin (n + 1) → Fin d, ∑ x : Fin d, f (pathSnoc Y x) := by
  conv_rhs => rw [← Fintype.sum_prod_type']
  refine Finset.sum_bij
    (fun X _ => ((fun t => X (Fin.castSucc t)), X (Fin.last (n + 1))))
    (fun _ _ => by simp) ?_ ?_ ?_
  · intro X₁ _ X₂ _ h
    have h1 : (fun t => X₁ (Fin.castSucc t)) = (fun t => X₂ (Fin.castSucc t)) :=
      congrArg Prod.fst h
    have h2 : X₁ (Fin.last (n + 1)) = X₂ (Fin.last (n + 1)) :=
      congrArg Prod.snd h
    have hs1 := pathSnoc_init_last X₁
    have hs2 := pathSnoc_init_last X₂
    rw [h1, h2] at hs1
    exact hs1.symm.trans hs2
  · rintro ⟨Y, x⟩ _
    refine ⟨pathSnoc Y x, by simp, ?_⟩
    simp only [Prod.mk.injEq]
    constructor
    · funext t
      exact pathSnoc_castSucc Y x t
    · exact pathSnoc_last Y x
  · intro X _
    rw [pathSnoc_init_last]

/-- The zero branch in finite relative entropy is already encoded by multiplication. -/
lemma pathKL_eq_sum {d n : ℕ} (P Q : Matrix (Fin d) (Fin d) ℝ)
    (mu0 nu0 : Fin d → ℝ) :
    pathKL (n := n) P Q mu0 nu0 = ∑ X : Fin (n + 1) → Fin d,
      pathProb P mu0 X * log (pathProb P mu0 X / pathProb Q nu0 X) := by
  unfold pathKL
  apply Finset.sum_congr rfl
  intro X _
  dsimp
  split_ifs with h
  · simp [h]
  · rfl

lemma pathProb_ne_zero_of_initial_ne_zero {d n : ℕ}
    (P : Matrix (Fin d) (Fin d) ℝ) (mu0 : Fin d → ℝ)
    (hP : ∀ i j, 0 < P i j) (X : Fin (n + 1) → Fin d)
    (hmu : mu0 (X 0) ≠ 0) : pathProb P mu0 X ≠ 0 := by
  unfold pathProb
  apply mul_ne_zero hmu
  exact Finset.prod_ne_zero_iff.mpr fun t _ => ne_of_gt (hP _ _)

/-- With a shared initial law and positive transitions, the two path laws have the
same support. -/
lemma pathProb_ne_zero_iff {d n : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (mu0 : Fin d → ℝ) (hP : ∀ i j, 0 < P i j)
    (X : Fin (n + 1) → Fin d) :
    pathProb P mu0 X ≠ 0 ↔ mu0 (X 0) ≠ 0 := by
  constructor
  · intro h hz
    apply h
    simp [pathProb, hz]
  · exact pathProb_ne_zero_of_initial_ne_zero P mu0 hP X

/-- Pointwise entropy increment for one final transition. -/
lemma pathKL_snoc_term {d n : ℕ} (P Q : Matrix (Fin d) (Fin d) ℝ)
    (mu0 : Fin d → ℝ) (hP : ∀ i j, 0 < P i j) (hQ : ∀ i j, 0 < Q i j)
    (Y : Fin (n + 1) → Fin d) (x : Fin d) :
    pathProb P mu0 (pathSnoc Y x) *
        log (pathProb P mu0 (pathSnoc Y x) / pathProb Q mu0 (pathSnoc Y x)) =
      pathProb P mu0 Y * P (Y (Fin.last n)) x *
        log (pathProb P mu0 Y / pathProb Q mu0 Y) +
      pathProb P mu0 Y * (P (Y (Fin.last n)) x *
        log (P (Y (Fin.last n)) x / Q (Y (Fin.last n)) x)) := by
  rw [pathProb_snoc, pathProb_snoc]
  by_cases hp : pathProb P mu0 Y = 0
  · simp [hp]
  · have hmu := (pathProb_ne_zero_iff P mu0 hP Y).mp hp
    have hq := pathProb_ne_zero_of_initial_ne_zero Q mu0 hQ Y hmu
    have hratio : pathProb P mu0 Y * P (Y (Fin.last n)) x /
        (pathProb Q mu0 Y * Q (Y (Fin.last n)) x) =
        (pathProb P mu0 Y / pathProb Q mu0 Y) *
        (P (Y (Fin.last n)) x / Q (Y (Fin.last n)) x) := by ring
    rw [hratio, Real.log_mul (div_ne_zero hp hq)
      (div_ne_zero (ne_of_gt (hP _ _)) (ne_of_gt (hQ _ _)))]
    ring

/-- One-step chain rule for the relative entropy of finite Markov trajectories.
The initial distribution may contain zero masses. -/
theorem pathKL_succ {d n : ℕ} (P Q : Matrix (Fin d) (Fin d) ℝ)
    (mu0 : Fin d → ℝ) (hP : ∀ i j, 0 < P i j) (hQ : ∀ i j, 0 < Q i j)
    (hrow : ∀ i, ∑ j, P i j = 1) :
    pathKL (n := n + 1) P Q mu0 mu0 = pathKL (n := n) P Q mu0 mu0 +
      ∑ Y : Fin (n + 1) → Fin d, pathProb P mu0 Y *
        ∑ x : Fin d, P (Y (Fin.last n)) x *
          log (P (Y (Fin.last n)) x / Q (Y (Fin.last n)) x) := by
  rw [pathKL_eq_sum, pathKL_eq_sum, sum_path_snoc]
  simp_rw [pathKL_snoc_term P Q mu0 hP hQ]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro Y _
  rw [Finset.sum_add_distrib]
  congr 1
  · calc
      (∑ x : Fin d, pathProb P mu0 Y * P (Y (Fin.last n)) x *
          log (pathProb P mu0 Y / pathProb Q mu0 Y)) =
          pathProb P mu0 Y * (∑ x : Fin d, P (Y (Fin.last n)) x) *
          log (pathProb P mu0 Y / pathProb Q mu0 Y) := by
        rw [Finset.mul_sum, Finset.sum_mul]
      _ = _ := by rw [hrow, mul_one]
  · rw [Finset.mul_sum]

/-- Identical initial laws have zero relative entropy before the first transition. -/
@[simp] theorem pathKL_zero {d : ℕ} (P Q : Matrix (Fin d) (Fin d) ℝ)
    (mu0 : Fin d → ℝ) : pathKL (n := 0) P Q mu0 mu0 = 0 := by
  rw [pathKL_eq_sum]
  apply Finset.sum_eq_zero
  intro X _
  by_cases h : mu0 (X 0) = 0
  · simp [pathProb, h]
  · simp [pathProb, h]

/-- The trajectory KL is the sum of the expected one-step row divergences.
Each expectation is taken over the prefix ending at that time. -/
theorem pathKL_chain_rule {d n : ℕ} (P Q : Matrix (Fin d) (Fin d) ℝ)
    (mu0 : Fin d → ℝ) (hP : ∀ i j, 0 < P i j) (hQ : ∀ i j, 0 < Q i j)
    (hrow : ∀ i, ∑ j, P i j = 1) :
    pathKL (n := n) P Q mu0 mu0 =
      ∑ t : Fin n, ∑ Y : Fin (t.val + 1) → Fin d, pathProb P mu0 Y *
        ∑ x : Fin d, P (Y (Fin.last t.val)) x *
          log (P (Y (Fin.last t.val)) x / Q (Y (Fin.last t.val)) x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pathKL_succ P Q mu0 hP hQ hrow, Fin.sum_univ_castSucc]
    exact congrArg (fun z : ℝ => z + _) ih

end PsgEst
