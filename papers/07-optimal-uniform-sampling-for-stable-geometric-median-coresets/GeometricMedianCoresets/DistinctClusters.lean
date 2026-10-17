import GeometricMedianCoresets.ClusterCosts
import GeometricMedianCoresets.UniformMajority

/-! Explicit distinct points in two small clusters, with the required rounded imbalance. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace GeometricMedianCoresets.LowerBound

/-- The two-cluster lower-bound population is genuinely a set of distinct real points. -/
theorem exists_distinct_clusters {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1/100) (m : ℕ) :
    ∃ (n : ℕ) (mark : Fin n → Bool) (P : Dataset ℝ n) (θ : ℝ),
      0 < n ∧ m ≤ n ∧ 20 * (m:ℝ)^2 ≤ n ∧ Function.Injective P ∧
      10 * ε ≤ θ ∧ θ ≤ 11 * ε ∧
      ((((Finset.univ : Finset (Fin n)).filter (fun i => mark i = true)).card : ℝ) / n) =
        (1 - θ) / 2 ∧
      (∀ i, |P i - base mark i| ≤ ε ^ 2 / 100) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max (2 / ε) (max (20 * (m:ℝ)^2) (m:ℝ)))
  have hnε : 2 / ε ≤ (n:ℝ) := (le_max_left _ _).trans hn.le
  have hnlarge : 20 * (m:ℝ)^2 ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn.le)
  have hmnR : (m:ℝ) ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn.le)
  have hmn : m ≤ n := by exact_mod_cast hmnR
  have hnR : (0:ℝ) < n := lt_of_lt_of_le (by positivity : (0:ℝ) < 2 / ε) hnε
  have hnN : 0 < n := by exact_mod_cast hnR
  have hεn : 2 ≤ ε * n := by
    have h := (div_le_iff₀ hε).1 hnε
    nlinarith
  let a : ℕ := ⌊(1 - 10 * ε) * n / 2⌋₊
  have hnonneg : 0 ≤ (1 - 10 * ε) * n / 2 := by
    have hscale : 0 ≤ 1 - 10 * ε := by linarith
    exact div_nonneg (mul_nonneg hscale hnR.le) (by norm_num)
  have hfloor : (a:ℝ) ≤ (1 - 10 * ε) * n / 2 := Nat.floor_le hnonneg
  have hfloor' : (1 - 10 * ε) * n / 2 < (a:ℝ) + 1 := Nat.lt_floor_add_one _
  have ha : a < n := (Nat.floor_lt hnonneg).2 (by nlinarith)
  let mark : Fin n → Bool := fun i => decide (i.val < a)
  have hcard : ((Finset.univ : Finset (Fin n)).filter (fun i => mark i = true)).card = a := by
    let b : Fin n := ⟨a, ha⟩
    have heq : (Finset.univ.filter (fun i : Fin n => mark i = true)) = Finset.Iio b := by
      ext i
      simp [mark, b, Fin.lt_def]
    rw [heq, Fin.card_Iio]
  let θ : ℝ := 1 - 2 * (a:ℝ) / n
  have hphi : (a:ℝ) / n ≤ (1 - 10 * ε) / 2 := (div_le_iff₀ hnR).2 (by nlinarith)
  have hplo : (1 - 11 * ε) / 2 ≤ (a:ℝ) / n := (le_div_iff₀ hnR).2 (by nlinarith)
  have hθlo : 10 * ε ≤ θ := by dsimp [θ]; rw [mul_div_assoc]; linarith
  have hθhi : θ ≤ 11 * ε := by dsimp [θ]; rw [mul_div_assoc]; linarith
  let ρ : ℝ := ε ^ 2 / 100
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  let offset : Fin n → ℝ := fun i => ρ * (i.val + 1) / ((n:ℝ) + 1)
  let P : Dataset ℝ n := fun i => base mark i + offset i
  have hoff : ∀ i, 0 ≤ offset i ∧ offset i < ρ := by
    intro i
    constructor
    · dsimp [offset]; positivity
    · dsimp [offset]
      apply (div_lt_iff₀ (by linarith : (0:ℝ) < n + 1)).2
      have hi : (i.val:ℝ) < n := by exact_mod_cast i.isLt
      nlinarith
  have hmonoBase : Monotone (base mark) := by
    intro i j hij
    have hle : i.val ≤ j.val := hij
    simp only [base, mark, decide_eq_true_eq]
    split_ifs <;> norm_num <;> omega
  have hmonoOff : StrictMono offset := by
    intro i j hij
    dsimp [offset]
    apply div_lt_div_of_pos_right _ (by linarith : (0:ℝ) < n + 1)
    apply mul_lt_mul_of_pos_left _ hρ
    exact_mod_cast Nat.add_lt_add_right hij 1
  have hinj : Function.Injective P :=
    (show StrictMono P from fun i j hij => add_lt_add_of_le_of_lt (hmonoBase hij.le) (hmonoOff hij)).injective
  refine ⟨n, mark, P, θ, hnN, hmn, hnlarge, hinj, hθlo, hθhi, ?_, ?_⟩
  · rw [hcard]
    dsimp [θ]
    ring
  · intro i
    have heq : P i - base mark i = offset i := by dsimp [P]; ring
    rw [heq, abs_of_nonneg (hoff i).1]
    exact (hoff i).2.le

end GeometricMedianCoresets.LowerBound
