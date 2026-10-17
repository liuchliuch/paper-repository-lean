import Paper08.ZeroFreeMarginal
import Paper08.CubeWeighted

/-! # Logarithmic derivative bounds from smaller-marginal phase control -/
noncomputable section
open scoped BigOperators
namespace Paper08.ZeroFreeInduction
open Integral CubeMarginal ComplexSector

variable {n m r c : ℕ} {q θ : ℝ} {z : ℂ}

/-- The scoped weighted integral is controlled by the already proved marginal
 norm-loss inequality. The denominator's nonzero premise is supplied by the
 earlier uniform nonzero step of the same induction. -/
theorem weighted_ratio_le {k : ℕ} (ih : Good n m r c q z θ k)
    (hq : 0 ≤ q) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hpow : (1 : ℝ)/2 ≤ Real.cos θ ^ (r-1))
    (M : Model n m r c q) (S J : Finset (Fin n)) (hS : S.card ≤ k+1)
    (hJ : J.card ≤ r-1) {δ : (Fin n → ℝ) → ℝ}
    (hδcont : ContinuousOn δ (cube n)) (hδ : ∀ y ∈ cube n, |δ y| ≤ q)
    (hdep : ∀ x ∈ cube n, ∀ y ∈ cube n, (∀ i ∈ J, x i = y i) → δ x = δ y)
    {x : Fin n → ℝ} (hx : x ∈ cube n) (hnz : M.partial S z x ≠ 0) :
    ‖(z * avg S (fun y => (δ y : ℂ) * M.exponential z y) x) / M.partial S z x‖ ≤
      2 * ‖z‖ * q := by
  let T := S ∩ J
  let R := realAvg T (fun y => ‖avg (S \ T) (M.exponential z) y‖) x
  have hR : 0 ≤ R := realAvg_nonneg T (fun y _ => norm_nonneg _) hx
  have hcos0 : 0 ≤ Real.cos θ := (ComplexSector.cos_pos hθ0 hθ1).le
  have hTcard : T.card ≤ r-1 := (Finset.card_le_card Finset.inter_subset_right).trans hJ
  have hpower : (1 : ℝ)/2 ≤ Real.cos θ ^ T.card :=
    hpow.trans (pow_le_pow_of_le_one hcos0 (Real.cos_le_one θ) hTcard)
  have hstep := stepLower_of_good ih hθ1 M S hS
  have hloss := CubeNormLoss.subset (M.continuous_exponential z) hcos0 hstep
    (Finset.inter_subset_left : T ⊆ S) hx
  have hRle : R ≤ 2 * ‖M.partial S z x‖ := by
    change Real.cos θ ^ T.card * R ≤ ‖M.partial S z x‖ at hloss
    nlinarith
  have hweight := CubeWeighted.weighted_avg_norm_le S J (M.continuous_exponential z)
    hδcont hδ hdep hx
  change ‖avg S (fun y => (δ y : ℂ) * M.exponential z y) x‖ ≤ q * R at hweight
  have hnum : ‖z * avg S (fun y => (δ y : ℂ) * M.exponential z y) x‖ ≤
      (2 * ‖z‖ * q) * ‖M.partial S z x‖ := by
    rw [norm_mul]
    calc
      ‖z‖ * ‖avg S (fun y => (δ y : ℂ) * M.exponential z y) x‖ ≤ ‖z‖ * (q * R) :=
        mul_le_mul_of_nonneg_left hweight (norm_nonneg z)
      _ ≤ ‖z‖ * (q * (2 * ‖M.partial S z x‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hRle hq) (norm_nonneg z)
      _ = _ := by ring
  rw [norm_div]
  exact (div_le_iff₀ (norm_pos_iff.mpr hnz)).mpr hnum

end Paper08.ZeroFreeInduction
