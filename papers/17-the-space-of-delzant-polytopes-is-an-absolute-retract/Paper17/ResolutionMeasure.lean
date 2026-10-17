import Paper17.ConeComplex
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# A strictly decreasing global resolution measure

Use the natural-number weight `(n+1)^multiplicity` for each maximal cone.
Replacing a cone by at most `n` cones of smaller positive multiplicity strictly
reduces its contribution. Summing over all simultaneously affected cones and
removing duplicate new cells can only decrease the total further.
-/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace Paper17
section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The sum over affected stellar pieces is indexed exactly by the chosen face. -/
theorem sum_starCellValid_of_subset (I s : Finset ι) (hIs : I ⊆ s)
    (f : Option ι → ℕ) :
    ∑ q ∈ Finset.univ.filter (starCellValid I s), f q = ∑ i ∈ I, f (some i) := by
  classical
  simp only [Finset.sum_filter, Fintype.sum_option, starCellValid, hIs, not_true_eq_false,
    if_false, true_and, zero_add]
  trans (∑ x, if x ∈ I then f (some x) else 0)
  · apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ I <;> simp [hi]
  calc (∑ x, if x ∈ I then f (some x) else 0) =
        ∑ x ∈ I, if x ∈ I then f (some x) else 0 :=
          (Finset.sum_subset (Finset.subset_univ I) (fun i _ hi => if_neg hi)).symm
    _ = ∑ i ∈ I, f (some i) := Finset.sum_congr rfl (fun i hi => if_pos hi)

theorem sum_starCellValid_of_not_subset (I s : Finset ι) (hIs : ¬ I ⊆ s)
    (f : Option ι → ℕ) :
    ∑ q ∈ Finset.univ.filter (starCellValid I s), f q = f none := by
  classical
  simp [Finset.sum_filter, Fintype.sum_option, starCellValid, hIs]

/-- At most `n` children of smaller multiplicity outweigh strictly less than
the old cone under base `n+1`. -/
theorem stellar_power_branch_lt (n m : ℕ) (I s : Finset ι) (hI : I.Nonempty)
    (hIs : I ⊆ s) (hs : s.card ≤ n) (d : Option ι → ℕ)
    (hd : ∀ i ∈ I, d (some i) < m) :
    (∑ q ∈ Finset.univ.filter (starCellValid I s), (n + 1) ^ d q) < (n + 1) ^ m := by
  classical
  rw [sum_starCellValid_of_subset I s hIs]
  have hm : 0 < m := (Nat.zero_le (d (some hI.choose))).trans_lt (hd hI.choose hI.choose_spec)
  have hcard : I.card ≤ n := (Finset.card_le_card hIs).trans hs
  have hpow : 0 < (n + 1) ^ (m - 1) := pow_pos (by omega) _
  calc (∑ i ∈ I, (n + 1) ^ d (some i))
      ≤ ∑ _i ∈ I, (n + 1) ^ (m - 1) := by
        apply Finset.sum_le_sum
        intro i hi
        exact Nat.pow_le_pow_right (by omega) (by have := hd i hi; omega)
    _ = I.card * (n + 1) ^ (m - 1) := by simp
    _ ≤ n * (n + 1) ^ (m - 1) := Nat.mul_le_mul_right _ hcard
    _ < (n + 1) * (n + 1) ^ (m - 1) := Nat.mul_lt_mul_of_pos_right (by omega) hpow
    _ = (n + 1) ^ m := by rw [mul_comm, ← pow_succ]; congr 1; omega

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The actual finite set of new geometric cells has smaller total weight.
Only row multiplicity descent and the combinatorial branch bound are inputs;
no global termination conclusion is assumed. -/
theorem SimplicialConeComplex.stellar_weight_lt {v : ι → E}
    (K : SimplicialConeComplex v) (n : ℕ) (I : Finset ι) (hI : I.Nonempty)
    (hface : ∃ s ∈ K.facets, I ⊆ s) (hcard : ∀ s ∈ K.facets, s.card ≤ n)
    (μ : Finset ι → ℕ) (ν : Finset (Option ι) → ℕ)
    (hkeep : ∀ s ∈ K.facets, ¬ I ⊆ s → ν (starCellGenerators s none) = μ s)
    (hdrop : ∀ s ∈ K.facets, I ⊆ s → ∀ i ∈ I, ν (starCellGenerators s (some i)) < μ s) :
    (∑ s ∈ K.starFacets I, (n + 1) ^ ν s) < ∑ s ∈ K.facets, (n + 1) ^ μ s := by
  classical
  let T := (K.facets.product (Finset.univ : Finset (Option ι))).filter
    (fun p : Finset ι × Option ι => starCellValid I p.1 p.2)
  have hdup : (∑ s ∈ K.starFacets I, (n + 1) ^ ν s) ≤
      ∑ p ∈ T, (n + 1) ^ ν (starCellGenerators p.1 p.2) := by
    change (∑ s ∈ T.image (fun p => starCellGenerators p.1 p.2), (n + 1) ^ ν s) ≤ _
    exact Finset.sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _)
  have hsum : (∑ p ∈ T, (n + 1) ^ ν (starCellGenerators p.1 p.2)) =
      ∑ s ∈ K.facets, ∑ q ∈ Finset.univ.filter (starCellValid I s),
        (n + 1) ^ ν (starCellGenerators s q) := by
    simp only [T, Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]
  have hle : ∀ s ∈ K.facets,
      (∑ q ∈ Finset.univ.filter (starCellValid I s), (n + 1) ^ ν (starCellGenerators s q)) ≤
        (n + 1) ^ μ s := by
    intro s hs
    by_cases hIs : I ⊆ s
    · exact (stellar_power_branch_lt n (μ s) I s hI hIs (hcard s hs)
        (fun q => ν (starCellGenerators s q)) (hdrop s hs hIs)).le
    · rw [sum_starCellValid_of_not_subset I s hIs, hkeep s hs hIs]
  have hlt : ∃ s ∈ K.facets,
      (∑ q ∈ Finset.univ.filter (starCellValid I s), (n + 1) ^ ν (starCellGenerators s q)) <
        (n + 1) ^ μ s := by
    obtain ⟨s, hs, hIs⟩ := hface
    exact ⟨s, hs, stellar_power_branch_lt n (μ s) I s hI hIs (hcard s hs)
      (fun q => ν (starCellGenerators s q)) (hdrop s hs hIs)⟩
  exact hdup.trans_lt (hsum ▸ Finset.sum_lt_sum hle hlt)

end
end Paper17
