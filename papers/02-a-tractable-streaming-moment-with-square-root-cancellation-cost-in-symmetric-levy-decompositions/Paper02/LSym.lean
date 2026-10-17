import Paper02.Basic
import Paper02.RudinShapiro
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Corollary 2.2: dual inequality (Gaussian + finite atomic jump parts)

If `|∑ a_k cos(k t)| ≤ M` for all `t`, then
`|∑ a_k D h(k)| ≤ s(1) * M` for `h` a difference of such exponents.
-/

noncomputable section

namespace Paper02.LSym

open Paper02 Real

lemma secondDiff_finset_sum {J : Type} [Fintype J] (f : J → ℤ → ℝ) (k : ℤ) :
    secondDiff (fun x => ∑ j, f j x) k = ∑ j, secondDiff (f j) k := by
  classical
  simp only [secondDiff_eq]
  have h2 : (2:ℝ) * (∑ j, f j k) = ∑ j, 2 * f j k := Finset.mul_sum _ _ _
  have e1 : (∑ j, f j (k + 1)) - 2 * (∑ j, f j k) + (∑ j, f j (k - 1))
      = ∑ j, (f j (k + 1) - 2 * f j k + f j (k - 1)) := by
    rw [h2, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  have e2 : (∑ j, (f j (k + 1) - 2 * f j k + f j (k - 1))) / 2
      = ∑ j, (f j (k + 1) - 2 * f j k + f j (k - 1)) / 2 :=
    Finset.sum_div _ _ _
  rw [e1, e2]

lemma secondDiff_jump_atom (c s : ℝ) (k : ℤ) :
    secondDiff (fun x : ℤ => c * (1 - Real.cos ((x : ℝ) * s))) k
      = c * (1 - Real.cos s) * Real.cos ((k : ℝ) * s) := by
  have h := Paper02.secondDiff_smul c (fun x : ℤ => 1 - Real.cos ((x : ℝ) * s)) k
  have hcos := Paper02.secondDiff_cos s k
  rw [h, hcos]
  ring

lemma secondDiff_jump_sum {J : Type} [Fintype J] (c : J → ℝ) (s : J → ℝ) (k : ℤ) :
    secondDiff (fun x : ℤ => ∑ j, c j * (1 - Real.cos ((x : ℝ) * s j))) k
      = ∑ j, c j * (1 - Real.cos (s j)) * Real.cos ((k : ℝ) * s j) := by
  rw [secondDiff_finset_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  exact secondDiff_jump_atom (c j) (s j) k

/-- **Corollary 2.2 (Gaussian part).** -/
lemma dual_gaussian {ι : Type} [Fintype ι] (a : ι → ℝ) (k : ι → ℤ) (A : ℝ)
    (hA : 0 ≤ A) (M : ℝ) (hM : ∀ t : ℝ, |∑ i, a i * Real.cos ((k i : ℝ) * t)| ≤ M) :
    |∑ i, a i * secondDiff (fun x : ℤ => A * (x : ℝ) ^ 2) (k i)| ≤ A * M := by
  have hD : ∀ i, secondDiff (fun x : ℤ => A * (x : ℝ) ^ 2) (k i) = A :=
    fun i => Paper02.secondDiff_gaussian A (k i)
  have hsum : ∑ i, a i * secondDiff (fun x : ℤ => A * (x : ℝ) ^ 2) (k i)
      = (∑ i, a i) * A := by
    have hkey : ∀ i : ι, secondDiff (fun x : ℤ => A * (x : ℝ) ^ 2) (k i) = A := hD
    simp_rw [hkey]
    show (∑ i, a i * A) = (∑ i, a i) * A
    rw [Finset.sum_mul]
  have hs : |(∑ i, a i) * A| = |∑ i, a i| * A := by
    rw [abs_mul, abs_of_nonneg hA]
  rw [hsum, hs]
  have h0 : |∑ i, a i| ≤ M := by
    have := hM 0
    simpa using this
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) h0
  nlinarith [abs_nonneg (∑ i, a i)]

/-- **Corollary 2.2 (finite atomic jump part).**
Mass is `∑ c_j (1-cos s_j) = g(1)`. -/
lemma dual_atomic {ι J : Type} [Fintype ι] [Fintype J]
    (a : ι → ℝ) (k : ι → ℤ) (c : J → ℝ) (hc : ∀ j, 0 ≤ c j) (s : J → ℝ)
    (M : ℝ) (hM : ∀ t : ℝ, |∑ i, a i * Real.cos ((k i : ℝ) * t)| ≤ M) :
    |∑ i, a i * secondDiff
        (fun x : ℤ => ∑ j, c j * (1 - Real.cos ((x : ℝ) * s j))) (k i)|
      ≤ (∑ j, c j * (1 - Real.cos (s j))) * M := by
  have hD : ∀ i,
      secondDiff (fun x : ℤ => ∑ j, c j * (1 - Real.cos ((x : ℝ) * s j))) (k i)
        = ∑ j, c j * (1 - Real.cos (s j)) * Real.cos ((k i : ℝ) * s j) :=
    fun i => secondDiff_jump_sum c s (k i)
  set w : J → ℝ := fun j => c j * (1 - Real.cos (s j))
  have hw : ∀ j, 0 ≤ w j := by
    intro j
    have h1 : 0 ≤ c j := hc j
    have h2 : 0 ≤ (1:ℝ) - Real.cos (s j) := by
      have := Real.cos_le_one (s j); linarith
    positivity
  have hre : (∑ i, a i * secondDiff
        (fun x : ℤ => ∑ j, c j * (1 - Real.cos ((x : ℝ) * s j))) (k i))
      = ∑ i, ∑ j, a i * (w j * Real.cos ((k i : ℝ) * s j)) := by
    simp_rw [hD, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have : a i * (c j * (1 - Real.cos (s j)) * Real.cos ((k i : ℝ) * s j))
        = a i * (w j * Real.cos ((k i : ℝ) * s j)) := by
      unfold w; ring
    exact this
  rw [hre, Finset.sum_comm]
  have hswap : (∑ j, ∑ i, a i * (w j * Real.cos ((k i : ℝ) * s j)))
      = ∑ j, w j * ∑ i, a i * Real.cos ((k i : ℝ) * s j) := by
    apply Finset.sum_congr rfl
    intro j _
    have h : ∀ i, a i * (w j * Real.cos ((k i : ℝ) * s j))
        = w j * (a i * Real.cos ((k i : ℝ) * s j)) := by
      intro i; ring
    simp_rw [h, Finset.mul_sum]
  rw [hswap]
  have hle : |∑ j, w j * ∑ i, a i * Real.cos ((k i : ℝ) * s j)|
      ≤ ∑ j, |w j * ∑ i, a i * Real.cos ((k i : ℝ) * s j)| :=
    Finset.abs_sum_le_sum_abs _ _
  have hcs : ∀ j, |w j * ∑ i, a i * Real.cos ((k i : ℝ) * s j)| ≤ w j * M := by
    intro j
    have h1 : 0 ≤ w j := hw j
    have h3 : |∑ i, a i * Real.cos ((k i : ℝ) * s j)| ≤ M := hM (s j)
    have h4 : 0 ≤ M := le_trans (abs_nonneg _) h3
    rw [abs_mul, abs_of_nonneg h1]
    nlinarith
  have hsum : (∑ j, w j * M) = (∑ j, w j) * M := by
    rw [Finset.sum_mul]
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hA := le_trans hle (Finset.sum_le_sum fun j _ => hcs j)
  rw [hsum] at hA
  -- `w j = c j * (1-cos s j)`
  have hkey : (∑ j, w j) = ∑ j, c j * (1 - Real.cos (s j)) := rfl
  rw [hkey]
  exact hA

end Paper02.LSym
