import Paper14.Basic
import Mathlib.Data.Set.SymmDiff
/-!
# Theorem 4: mixing from excess returns

Paper anchors: Thmtheorem4, E9–E11 (two decompositions, finite invariant measure,
positive-excess components are product).

Proved here: combinatorial almost-invariance of level sets, nonnegativity of the
E7 tail factor, boundedness of weighted partial sums `∑ j p_j`, and elementary
product/marginal facts. The full measure-theoretic decompositions are proved
in `ExcessDecomposition`, and the criterion is assembled in `ExcessCriterionProof`.
-/
open MeasureTheory Filter Topology Set
open scoped symmDiff

namespace Paper14

/-- Theorem 4 is `Theorem4Statement` from `Paper14.Basic`. -/
def Theorem4Claim : Prop :=
  ∀ {α : Type*} [MeasurableSpace α] [MetricSpace α]
      [CompactSpace α] [BorelSpace α]
    (T : α → α) (μ : Measure α) (Y : ℕ → ℝ → Set α) (φ : ℕ → ℝ → α → α)
    (ρ : ℕ → ℝ → ℝ), Theorem4Statement T μ Y φ ρ

/-! ## Almost invariance of level sets (paper E8, combinatorial form) -/

/-- For any set `E`, the symmetric difference `E ∆ T⁻¹' E` sits inside the set
where membership in `E` changes along `T`. -/
theorem symmDiff_preimage_subset_change {α : Type*} (T : α → α) (E : Set α) :
    E ∆ (T ⁻¹' E) ⊆ {y | (y ∈ E ∧ T y ∉ E) ∨ (T y ∈ E ∧ y ∉ E)} := by
  intro y hy
  simp only [Set.mem_symmDiff, mem_preimage] at hy
  simp only [mem_setOf_eq]
  exact hy

/-- Level set form: for `E = {y | f y = j}`,
`E ∆ T⁻¹' E ⊆ {y | f y ≠ f (T y)}`. -/
theorem symmDiff_level_subset {α : Type*} (T : α → α) (f : α → ℕ) (j : ℕ) :
    {y | f y = j} ∆ (T ⁻¹' {y | f y = j}) ⊆ {y | f y ≠ f (T y)} := by
  intro y hy
  simp only [Set.mem_symmDiff, mem_preimage, mem_setOf_eq] at hy
  simp only [mem_setOf_eq]
  rcases hy with ⟨hyj, hyN⟩ | ⟨hyj, hyN⟩
  · -- f y = j, f (T y) ≠ j
    intro heq
    apply hyN
    rw [← heq]
    exact hyj
  · -- f (T y) = j, f y ≠ j
    intro heq
    apply hyN
    rw [heq]
    exact hyj

/-- Pointwise form of level-set almost invariance. -/
theorem ne_of_mem_symmDiff_level {α : Type*} {T : α → α} {f : α → ℕ} {j : ℕ} {y : α}
    (hy : y ∈ ({z | f z = j} : Set α) ∆ (T ⁻¹' {z | f z = j})) :
    f y ≠ f (T y) :=
  symmDiff_level_subset T f j hy

/-- A level set is contained in the pullback of itself whenever `f` is
`T`-invariant at that point. -/
theorem mem_preimage_of_level_of_eq {α : Type*} {T : α → α} {f : α → ℕ} {j : ℕ} {y : α}
    (hy : f y = j) (heq : f (T y) = f y) : T y ∈ ({z | f z = j} : Set α) := by
  simp only [mem_setOf_eq]
  rw [heq, hy]

/-- Membership in the level set is preserved by `T` when `f` does not change. -/
theorem level_mem_of_eq_on {α : Type*} {T : α → α} {f : α → ℕ} {j : ℕ}
    (h : ∀ y, f (T y) = f y) (y : α) (hy : y ∈ ({z | f z = j} : Set α)) :
    T y ∈ ({z | f z = j} : Set α) := by
  rw [mem_setOf_eq] at hy ⊢
  rw [h y, hy]

/-! ## Tail factor of paper E7 -/

/-- Paper E7 scale: `C/(J+1) ≥ 0` for `C, J ≥ 0`. -/
theorem excess_tail_factor_nonneg {C J : ℝ} (hC : 0 ≤ C) (hJ : 0 ≤ J) :
    0 ≤ C / (J + 1) :=
  div_nonneg hC (by linarith)

/-- The denominator `J+1` is strictly positive for `J ≥ 0`. -/
theorem excess_tail_factor_denom_pos {J : ℝ} (hJ : 0 ≤ J) : (0:ℝ) < J + 1 := by
  linarith

/-- Trivial upper bound of the tail factor by `C` when `J ≥ 0` and `C ≥ 0`. -/
theorem excess_tail_factor_le {C J : ℝ} (hC : 0 ≤ C) (hJ : 0 ≤ J) :
    C / (J + 1) ≤ C := by
  have ha : (0:ℝ) < J + 1 := by linarith
  have h1 : (1:ℝ) ≤ J + 1 := by linarith
  have h2 : (J + 1 : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ ha).mpr h1
  calc C / (J + 1) = C * (J + 1 : ℝ)⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left h2 hC
    _ = C := by ring

/-! ## Weighted partial sums (paper E6 / E7 real analysis) -/

/-- Partial sums of `j * p_j` are bounded by `C` when every partial sum is. -/
theorem weighted_partial_le {p : ℕ → ℝ} {C : ℝ}
    (h : ∀ n : ℕ, (∑ j ∈ Finset.range n, (j : ℝ) * p j) ≤ C) (n : ℕ) :
    (∑ j ∈ Finset.range n, (j : ℝ) * p j) ≤ C :=
  h n

/-- Partial sums of `j * p_j` are monotone when `p ≥ 0`. -/
theorem weighted_partial_mono {p : ℕ → ℝ} (hp : ∀ j, 0 ≤ p j) :
    Monotone (fun n : ℕ => ∑ j ∈ Finset.range n, (j : ℝ) * p j) := by
  intro m n hmn
  exact Finset.sum_mono_set_of_nonneg
    (fun j => mul_nonneg (Nat.cast_nonneg j) (hp j))
    (Finset.range_subset_range.mpr hmn)

/-- If `∑ j * p_j ≤ C` (all partial sums) and `p ≥ 0`, then `∑ p_j ≤ C + p 0`. -/
theorem sum_p_le_of_weighted_sum_le {p : ℕ → ℝ} {C : ℝ} (hp : ∀ j, 0 ≤ p j)
    (h : ∀ n : ℕ, (∑ j ∈ Finset.range n, (j : ℝ) * p j) ≤ C) (n : ℕ) :
    (∑ j ∈ Finset.range n, p j) ≤ C + p 0 := by
  have hterm : ∀ j ∈ Finset.range n,
      p j ≤ (j : ℝ) * p j + (if j = 0 then p j else 0) := by
    intro j hj
    by_cases hj0 : j = 0
    · subst hj0
      simp
    · have hj1 : (1:ℝ) ≤ j := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj0
      have hpj : 0 ≤ p j := hp j
      simp only [hj0, ite_false, add_zero]
      nlinarith
  calc (∑ j ∈ Finset.range n, p j)
      ≤ ∑ j ∈ Finset.range n, ((j : ℝ) * p j + (if j = 0 then p j else 0)) :=
        Finset.sum_le_sum hterm
    _ = ∑ j ∈ Finset.range n, (j : ℝ) * p j
          + ∑ j ∈ Finset.range n, (if j = 0 then p j else 0) :=
        Finset.sum_add_distrib
    _ = ∑ j ∈ Finset.range n, (j : ℝ) * p j
          + (if 0 ∈ Finset.range n then p 0 else 0) := by
        rw [Finset.sum_ite_eq']
    _ ≤ ∑ j ∈ Finset.range n, (j : ℝ) * p j + p 0 := by
        split_ifs with hmem
        · exact le_rfl
        · exact add_le_add_left (hp 0) _
    _ ≤ C + p 0 := add_le_add_right (h n) _

/-- Immediate consequence: `∑_{j=1}^{n-1} p_j ≤ C` when `p ≥ 0` and
`∑ j * p_j ≤ C`, since `p_j ≤ j * p_j` for `j ≥ 1`. -/
theorem sum_p_pos_le_of_weighted_sum_le {p : ℕ → ℝ} {C : ℝ} (hp : ∀ j, 0 ≤ p j)
    (h : ∀ n : ℕ, (∑ j ∈ Finset.range n, (j : ℝ) * p j) ≤ C) (n : ℕ) :
    (∑ j ∈ Finset.range n, (if j = 0 then 0 else p j)) ≤ C := by
  have hterm : ∀ j ∈ Finset.range n,
      (if j = 0 then 0 else p j) ≤ (j : ℝ) * p j := by
    intro j hj
    by_cases hj0 : j = 0
    · subst hj0
      simp
    · have hj1 : (1:ℝ) ≤ j := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj0
      have hpj : 0 ≤ p j := hp j
      simp only [hj0, ite_false]
      nlinarith
  calc (∑ j ∈ Finset.range n, (if j = 0 then 0 else p j))
      ≤ ∑ j ∈ Finset.range n, (j : ℝ) * p j := Finset.sum_le_sum hterm
    _ ≤ C := h n

/-! ## Product sets and marginals -/

/-- Membership in a product set is exactly membership in the two marginals. -/
theorem mem_prod_iff' {α : Type*} {β : Type*} {s : Set α} {t : Set β} {x : α × β} :
    x ∈ s ×ˢ t ↔ x.1 ∈ s ∧ x.2 ∈ t :=
  Iff.rfl

/-- First marginal of a product set. -/
theorem fst_mem_of_mem_prod {α : Type*} {β : Type*} {s : Set α} {t : Set β}
    {x : α × β} (h : x ∈ s ×ˢ t) : x.1 ∈ s :=
  h.1

/-- Second marginal of a product set. -/
theorem snd_mem_of_mem_prod {α : Type*} {β : Type*} {s : Set α} {t : Set β}
    {x : α × β} (h : x ∈ s ×ˢ t) : x.2 ∈ t :=
  h.2

/-- Both marginals of a product set. -/
theorem mem_prod_of_mem {α : Type*} {β : Type*} {s : Set α} {t : Set β}
    {x : α × β} (h1 : x.1 ∈ s) (h2 : x.2 ∈ t) : x ∈ s ×ˢ t :=
  ⟨h1, h2⟩

/-- Preimage of `s` under `fst` is `s ×ˢ univ`. -/
theorem preimage_fst_prod {α : Type*} {β : Type*} {s : Set α} :
    (Prod.fst : α × β → α) ⁻¹' s = s ×ˢ (univ : Set β) := by
  ext x
  simp

/-- Preimage of `t` under `snd` is `univ ×ˢ t`. -/
theorem preimage_snd_prod {α : Type*} {β : Type*} {t : Set β} :
    (Prod.snd : α × β → β) ⁻¹' t = (univ : Set α) ×ˢ t := by
  ext x
  simp

/-- Finite product cardinality. -/
theorem card_product' {α : Type*} {β : Type*} (s : Finset α) (t : Finset β) :
    (s ×ˢ t).card = s.card * t.card :=
  Finset.card_product s t

/-- Product of two level sets is the level set of the pair of coordinates. -/
theorem prod_level_eq {α : Type*} {β : Type*} {f : α → ℕ} {g : β → ℕ} {j k : ℕ} :
    ({x | f x = j} : Set α) ×ˢ {y | g y = k}
      = {z : α × β | f z.1 = j ∧ g z.2 = k} := by
  ext z
  simp

/-- A product of two excess levels is contained in the set where both
coordinates lie in their respective levels. -/
theorem prod_excessLevel_subset {α : Type*} {T : α → α} {Y : Set α} {n j m k : ℕ} :
    (excessLevel T Y n j) ×ˢ (excessLevel T Y m k)
      ⊆ {z : α × α | z.1 ∈ Y ∧ z.2 ∈ Y
        ∧ excessDn T Y n z.1 = j ∧ excessDn T Y m z.2 = k} := by
  intro z hz
  have h1 := hz.1
  have h2 := hz.2
  exact ⟨h1.1, h2.1, h1.2, h2.2⟩

/-- Combinatorial analogue of a decomposition: any `ℕ`-valued function
partitions the domain into its level sets. -/
theorem level_union {α : Type*} (f : α → ℕ) :
    (⋃ j : ℕ, {y | f y = j}) = univ := by
  ext y
  simp

/-- Distinct excess levels intersect trivially. -/
theorem excessLevel_inter_eq_empty {α : Type*} {T : α → α} {Y : Set α} {n j j' : ℕ}
    (h : j ≠ j') : excessLevel T Y n j ∩ excessLevel T Y n j' = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  intro y hy
  have h1 : excessDn T Y n y = j := hy.1.2
  have h2 : excessDn T Y n y = j' := hy.2.2
  exact h (h1.symm.trans h2)

/-- Distinct excess levels are disjoint. -/
theorem disjoint_excessLevel {α : Type*} {T : α → α} {Y : Set α} {n j j' : ℕ}
    (h : j ≠ j') :
    Disjoint (excessLevel T Y n j) (excessLevel T Y n j') := by
  rw [disjoint_iff_inter_eq_empty]
  exact excessLevel_inter_eq_empty h

end Paper14
