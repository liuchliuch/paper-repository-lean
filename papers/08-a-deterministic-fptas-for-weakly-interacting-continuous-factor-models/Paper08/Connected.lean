import Paper08.Enumeration
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Connected-support counts (2.10)–(2.12)

All counts below are cardinalities of explicitly defined finite enumerations.
The graph bound comes from the proved forest encoding in `Paper08.Enumeration`.
-/
noncomputable section
open scoped BigOperators
namespace Paper08.Connected

/-- The paper's constant `A₀ = 8 max{1,D}`. -/
def A₀ (D : ℕ) : ℕ := 8 * max 1 D

lemma A₀_pos (D : ℕ) : 1 ≤ A₀ D := by
  unfold A₀
  omega

/-- An actual count of the possible ordered forest shapes. -/
lemma tree_shape_bound (a : ℕ) :
    (Tree.treesOfNumNodesEq (a - 1)).card ≤ 4 ^ (a - 1) := by
  rw [Tree.treesOfNumNodesEq_card_eq_catalan]
  exact Enumeration.catalan_le_four_pow _

/-- Each forest edge has at most `max{1,D}` neighbour labels. -/
lemma neighbour_choice_count (D : ℕ) (t : Tree Unit) :
    (Enumeration.labelings (max 1 D) t).card = (max 1 D) ^ t.numNodes :=
  Enumeration.card_labelings _ _

/-- The connected vertex-set count asserted immediately after (2.10). -/
lemma connected_count {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D a : ℕ)
    (hdeg : ∀ v, G.degree v ≤ D) :
    (Enumeration.connectedSets G a).card ≤ Fintype.card V * (4 * max 1 D) ^ (a - 1) :=
  Enumeration.card_connectedSets_le G D a hdeg

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- All `(A,B)` pairs with `A` connected of cardinality `a` and `B ⊆ A`. -/
def pairsOfSize (G : SimpleGraph V) (a : ℕ) : Finset (Finset V × Finset V) :=
  (Enumeration.connectedSets G a).biUnion fun A => A.powerset.image (fun B => (A, B))

lemma mem_pairsOfSize (G : SimpleGraph V) (a : ℕ) (A B : Finset V) :
    (A, B) ∈ pairsOfSize G a ↔
      A.card = a ∧ (G.induce (A : Set V)).Connected ∧ B ⊆ A := by
  classical
  simp only [pairsOfSize, Enumeration.connectedSets, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_powerset, Finset.subset_univ, true_and, Finset.mem_image, Prod.mk.injEq]
  aesop

lemma card_pairsOfSize_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (D a : ℕ) (hdeg : ∀ v, G.degree v ≤ D) :
    (pairsOfSize G a).card ≤ Fintype.card V * (4 * max 1 D) ^ (a - 1) * 2 ^ a := by
  classical
  calc
    (pairsOfSize G a).card ≤
        ∑ A ∈ Enumeration.connectedSets G a,
          (A.powerset.image (fun B => (A, B))).card := Finset.card_biUnion_le
    _ ≤ ∑ A ∈ Enumeration.connectedSets G a, A.powerset.card :=
      Finset.sum_le_sum fun A _ => Finset.card_image_le
    _ = (Enumeration.connectedSets G a).card * 2 ^ a := by
      rw [← Finset.sum_const_nat]
      intro A hA
      rw [Finset.card_powerset, (Finset.mem_filter.mp hA).2.1]
    _ ≤ Fintype.card V * (4 * max 1 D) ^ (a - 1) * 2 ^ a :=
      Nat.mul_le_mul_right _ (connected_count G D a hdeg)

/-- Enumerate nonempty connected supports through order `s`, together with every subset. -/
def pairsUpTo (G : SimpleGraph V) (s : ℕ) : Finset (Finset V × Finset V) :=
  (Finset.Icc 1 s).biUnion (pairsOfSize G)

lemma mem_pairsUpTo (G : SimpleGraph V) (s : ℕ) (A B : Finset V) :
    (A, B) ∈ pairsUpTo G s ↔
      A.Nonempty ∧ A.card ≤ s ∧ (G.induce (A : Set V)).Connected ∧ B ⊆ A := by
  simp only [pairsUpTo, Finset.mem_biUnion, Finset.mem_Icc, mem_pairsOfSize]
  constructor
  · rintro ⟨a, ⟨ha, has⟩, hcard, hc, hb⟩
    exact ⟨Finset.card_pos.mp (by omega), by omega, hc, hb⟩
  · rintro ⟨hne, has, hc, hb⟩
    exact ⟨A.card, ⟨Finset.card_pos.mpr hne, has⟩, rfl, hc, hb⟩

lemma two_mul_sum_range_pow_le (x s : ℕ) (hx : 3 ≤ x) :
    2 * (∑ k ∈ Finset.range s, x ^ k) ≤ x ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, pow_succ]
    nlinarith [Nat.mul_le_mul_right (x ^ s) hx]

/-- The finite geometric estimate used in the pair count. -/
lemma geom_series_pair_count_nat (m D s : ℕ) :
    (∑ a ∈ Finset.Icc 1 s, m * (4 * max 1 D) ^ (a - 1) * 2 ^ a) ≤ m * A₀ D ^ s := by
  have hreindex :
      (∑ a ∈ Finset.Icc 1 s, m * (4 * max 1 D) ^ (a - 1) * 2 ^ a) =
      ∑ k ∈ Finset.range s, m * 2 * A₀ D ^ k := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_right]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Nat.add_sub_cancel_left, A₀]
    rw [Nat.add_comm 1 k, pow_succ]
    rw [show 8 * max 1 D = (4 * max 1 D) * 2 by omega]
    simp only [mul_pow]
    ring
  rw [hreindex, ← Finset.mul_sum]
  have hx : 3 ≤ A₀ D := by unfold A₀; omega
  calc
    m * 2 * (∑ k ∈ Finset.range s, A₀ D ^ k) =
        m * (2 * (∑ k ∈ Finset.range s, A₀ D ^ k)) := by ring
    _ ≤ m * A₀ D ^ s := Nat.mul_le_mul_left _ (two_mul_sum_range_pow_le _ _ hx)

/-- The real-valued form of the same estimate. -/
lemma geom_series_pair_count (m D s : ℕ) :
    (∑ a ∈ Finset.Icc 1 s,
      (m : ℝ) * (4 * max 1 D) ^ (a - 1) * 2 ^ a) ≤ (m : ℝ) * (8 * max 1 D) ^ s := by
  exact_mod_cast geom_series_pair_count_nat m D s

/-- Number of `(A,B)` pairs: the full cardinality assertion preceding (2.12). -/
lemma pair_count (G : SimpleGraph V) [DecidableRel G.Adj] (D s : ℕ)
    (hdeg : ∀ v, G.degree v ≤ D) :
    (pairsUpTo G s).card ≤ Fintype.card V * A₀ D ^ s := by
  calc
    (pairsUpTo G s).card ≤ ∑ a ∈ Finset.Icc 1 s, (pairsOfSize G a).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ a ∈ Finset.Icc 1 s,
        Fintype.card V * (4 * max 1 D) ^ (a - 1) * 2 ^ a :=
      Finset.sum_le_sum fun a _ => card_pairsOfSize_le G D a hdeg
    _ ≤ Fintype.card V * A₀ D ^ s := geom_series_pair_count_nat _ _ _

/-- The actual occurrences of local coefficients `d_p(B)` in (2.10), recording
`A` as well so repeated uses of the same `(p,B)` are counted separately. -/
def localCoefficients (G : SimpleGraph V) (s : ℕ) : Finset (ℕ × (Finset V × Finset V)) :=
  ((Finset.Icc 1 s) ×ˢ pairsUpTo G s).filter fun x => x.2.1.card ≤ x.1

lemma mem_localCoefficients (G : SimpleGraph V) (s p : ℕ) (A B : Finset V) :
    (p, A, B) ∈ localCoefficients G s ↔
      1 ≤ p ∧ p ≤ s ∧ A.Nonempty ∧ A.card ≤ p ∧
      (G.induce (A : Set V)).Connected ∧ B ⊆ A := by
  simp only [localCoefficients, Finset.mem_filter, Finset.mem_product,
    Finset.mem_Icc, mem_pairsUpTo]
  constructor
  · rintro ⟨⟨⟨hp, hps⟩, hne, hAs, hc, hB⟩, hAp⟩
    exact ⟨hp, hps, hne, hAp, hc, hB⟩
  · rintro ⟨hp, hps, hne, hAp, hc, hB⟩
    exact ⟨⟨⟨hp, hps⟩, hne, hAp.trans hps, hc, hB⟩, hAp⟩

/-- Equation (2.12), counted with precisely the multiplicities of (2.10). -/
lemma local_coeff_count (G : SimpleGraph V) [DecidableRel G.Adj] (D s : ℕ)
    (hdeg : ∀ v, G.degree v ≤ D) :
    (localCoefficients G s).card ≤ s * Fintype.card V * A₀ D ^ s := by
  calc
    (localCoefficients G s).card ≤ ((Finset.Icc 1 s) ×ˢ pairsUpTo G s).card :=
      Finset.card_filter_le _ _
    _ = s * (pairsUpTo G s).card := by simp [Nat.card_Icc]
    _ ≤ s * (Fintype.card V * A₀ D ^ s) := Nat.mul_le_mul_left _ (pair_count G D s hdeg)
    _ = s * Fintype.card V * A₀ D ^ s := by ring

end Paper08.Connected
