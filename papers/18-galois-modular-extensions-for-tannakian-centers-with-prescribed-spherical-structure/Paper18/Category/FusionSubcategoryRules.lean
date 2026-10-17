import Paper18.Fusion.Basic

/-!
# Dual closure of finite tensor-closed collections

A collection of simple labels containing the unit and every constituent of
products is automatically closed under duals. Positivity of FP dimensions
provides the finite stationary measure; dual closure is proved, not assumed.
-/
noncomputable section
open Classical
open scoped BigOperators
universe w
namespace Paper18.FusionBasis
variable {ι : Type w} [Fintype ι] (B : FusionBasis ι)

/-- Finite tensor and summand closure imply dual closure. -/
lemma dual_closed_of_tensor_closed (p : ι → Prop) (hone : p B.one)
    (hprod : ∀ i j k, p i → p j → B.N i j k ≠ 0 → p k)
    (i : ι) (hi : p i) : p (B.dual i) := by
  let s : Finset ι := Finset.univ.filter p
  have hmem (k : ι) : k ∈ s ↔ p k := by simp [s]
  have hrow (k : ι) (hk : k ∈ s) :
      ∑ j ∈ s, (B.N i k j : ℝ) * B.fpdim j = B.fpdim i * B.fpdim k := by
    rw [← B.fpdim_mul i k]
    apply Finset.sum_subset (Finset.subset_univ s)
    intro j _ hj
    have hz : B.N i k j = 0 := by
      by_contra hn
      exact hj ((hmem j).mpr (hprod i k j hi ((hmem k).mp hk) hn))
    simp [hz]
  have hcol (j : ι) :
      ∑ k ∈ s, (B.N i k j : ℝ) * B.fpdim k ≤ B.fpdim i * B.fpdim j := by
    have hall : ∑ k, (B.N i k j : ℝ) * B.fpdim k = B.fpdim i * B.fpdim j := by
      simp_rw [B.N_dual i]
      rw [B.fpdim_mul, B.fpdim_dual]
    rw [← hall]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      (fun k _ _ => mul_nonneg (Nat.cast_nonneg _) (B.fpdim_pos k).le)
  have hbalance :
      (∑ j ∈ s, B.fpdim j * (∑ k ∈ s, (B.N i k j : ℝ) * B.fpdim k)) =
        ∑ j ∈ s, B.fpdim j * (B.fpdim i * B.fpdim j) := by
    calc
      _ = ∑ k ∈ s, B.fpdim k * (∑ j ∈ s, (B.N i k j : ℝ) * B.fpdim j) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hrow k hk]
  have heq : ∀ j ∈ s,
      B.fpdim j * (∑ k ∈ s, (B.N i k j : ℝ) * B.fpdim k) =
        B.fpdim j * (B.fpdim i * B.fpdim j) :=
    (Finset.sum_eq_sum_iff_of_le
      (fun j _ => mul_le_mul_of_nonneg_left (hcol j) (B.fpdim_pos j).le)).mp hbalance
  have hunit := heq B.one ((hmem _).mpr hone)
  have hdualCoeff (k : ι) : B.N i k B.one = if B.dual i = k then 1 else 0 := by
    rw [B.N_dual, B.N_one_right]
  by_contra hno
  have hz : ∑ k ∈ s, (B.N i k B.one : ℝ) * B.fpdim k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [hdualCoeff]
    have hne : B.dual i ≠ k := by
      intro h
      exact hno (h ▸ ((hmem k).mp hk))
    simp [hne]
  rw [hz, B.fpdim_one] at hunit
  have := B.fpdim_pos i
  nlinarith

end Paper18.FusionBasis
