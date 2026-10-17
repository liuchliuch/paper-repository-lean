import UniformBorderRank.LocalMaps
import UniformBorderRank.Comb

/-! Expansion over the original anchor factors.  A coordinate slice is
regarded as a tensor on all sites, constant along the frozen sites.  The
coordinate masks selecting the frozen sites are products, so multiplying
by these masks preserves each summand's border-rank bound. -/
noncomputable section
namespace UniformBorderRank
open Finset

/-- Pointwise multiplication by a product of local coefficient functions. -/
def productMask {N : ℕ} {d : Fin N → ℕ}
    (v : ∀ i, Fin (d i) → ℂ) (T : Coeffs d) : Coeffs d :=
  fun u => (∏ i, v i (u i)) * T u

lemma isProduct_productMask {N : ℕ} {d : Fin N → ℕ}
    (v : ∀ i, Fin (d i) → ℂ) {T : Coeffs d} (hT : isProduct T) :
    isProduct (productMask v T) := by
  obtain ⟨w, hw⟩ := hT
  refine ⟨fun i x => v i x * w i x, ?_⟩
  intro u
  simp only [productMask, hw, prod_mul_distrib]

lemma cpRankLe_productMask {N : ℕ} {d : Fin N → ℕ}
    (v : ∀ i, Fin (d i) → ℂ) {T : Coeffs d} {b : ℕ}
    (hT : cpRankLe T b) : cpRankLe (productMask v T) b := by
  obtain ⟨w, hw, hs⟩ := hT
  refine ⟨fun j => productMask v (w j), fun j => isProduct_productMask v (hw j), ?_⟩
  intro u
  simp only [productMask, hs, mul_sum]

lemma borderRankLe_productMask {N : ℕ} {d : Fin N → ℕ}
    (v : ∀ i, Fin (d i) → ℂ) {T : Coeffs d} {b : ℕ}
    (hT : borderRankLe T b) : borderRankLe (productMask v T) b := by
  obtain ⟨w, hw, hl⟩ := hT
  exact ⟨fun n => productMask v (w n), fun n => cpRankLe_productMask v (hw n),
    fun u => (hl u).const_mul _⟩

/-- Replace the coordinates at the chosen anchor sites by an assignment. -/
def freezeCoordinates {N : ℕ} {d : Fin N → ℕ} (K : Finset (Fin N))
    (gamma : ∀ i : K, Fin (d i)) (u : ∀ i, Fin (d i)) : ∀ i, Fin (d i) :=
  fun i => if hi : i ∈ K then gamma ⟨i, hi⟩ else u i

/-- The original tensor with the anchor coordinates frozen; its values at
these sites are constant. -/
def coefficientSlice {N : ℕ} {d : Fin N → ℕ} (K : Finset (Fin N))
    (gamma : ∀ i : K, Fin (d i)) (T : Coeffs d) : Coeffs d :=
  fun u => T (freezeCoordinates K gamma u)

/-- Product coordinate mask supported at one assignment of the anchor sites. -/
def anchorMask {N : ℕ} {d : Fin N → ℕ} (K : Finset (Fin N))
    (gamma : ∀ i : K, Fin (d i)) (i : Fin N) (x : Fin (d i)) : ℂ :=
  if hi : i ∈ K then (if x = gamma ⟨i, hi⟩ then 1 else 0) else 1

lemma anchorMask_self {N : ℕ} {d : Fin N → ℕ} (K : Finset (Fin N))
    (u : ∀ i, Fin (d i)) :
    (∏ i, anchorMask K (fun i => u i) i (u i)) = 1 := by
  classical
  apply prod_eq_one
  intro i _
  simp [anchorMask]

lemma anchorMask_ne {N : ℕ} {d : Fin N → ℕ} (K : Finset (Fin N))
    (u : ∀ i, Fin (d i)) (gamma : ∀ i : K, Fin (d i))
    (hne : gamma ≠ fun i : K => u i) :
    (∏ i, anchorMask K gamma i (u i)) = 0 := by
  classical
  have hex : ∃ i : K, gamma i ≠ u i := by
    simpa only [ne_eq, funext_iff, not_forall] using hne
  obtain ⟨i, hi⟩ := hex
  apply prod_eq_zero (mem_univ i.val)
  simp [anchorMask, i.property, Ne.symm hi]

/-- The actual coordinate expansion of a tensor along an arbitrary set of
original factors.  No rank or reconstruction hypothesis is used. -/
theorem anchor_factor_expansion {N : ℕ} {d : Fin N → ℕ}
    (K : Finset (Fin N)) (T : Coeffs d) :
    T = ∑ gamma : (∀ i : K, Fin (d i)),
      productMask (anchorMask K gamma) (coefficientSlice K gamma T) := by
  classical
  ext u
  rw [sum_apply, sum_eq_single (fun i : K => u i)]
  · simp only [productMask, anchorMask_self, one_mul, coefficientSlice]
    congr 1
    ext i
    simp [freezeCoordinates]
  · intro gamma _ hne
    simp only [productMask, anchorMask_ne K u gamma hne, zero_mul]
  · simp

/-- If every actual coordinate slice has border rank at most `b`, expansion
along the anchor factors costs exactly the number of anchor assignments. -/
theorem borderRankLe_anchor_expansion {N : ℕ} {d : Fin N → ℕ}
    (K : Finset (Fin N)) (T : Coeffs d) (b : ℕ)
    (h : ∀ gamma : (∀ i : K, Fin (d i)), borderRankLe (coefficientSlice K gamma T) b) :
    borderRankLe T (Fintype.card (∀ i : K, Fin (d i)) * b) := by
  classical
  have hb := borderRankLe_finset_sum univ
    (fun gamma : (∀ i : K, Fin (d i)) =>
      productMask (anchorMask K gamma) (coefficientSlice K gamma T))
    (fun _ => b) (fun gamma _ => borderRankLe_productMask _ (h gamma))
  rw [← anchor_factor_expansion K T] at hb
  simpa only [sum_const, card_univ, smul_eq_mul] using hb

lemma anchor_assignment_card_le {N r : ℕ} {d : Fin N → ℕ}
    (K : Finset (Fin N)) (hd : ∀ i ∈ K, d i ≤ r) :
    Fintype.card (∀ i : K, Fin (d i)) ≤ r ^ K.card := by
  classical
  rw [Fintype.card_pi]
  calc
    _ ≤ ∏ _i : K, r := prod_le_prod (fun _ _ => Nat.zero_le _)
      (fun i _ => by simpa using hd i i.property)
    _ = _ := by simp

/-- Uniform local dimensions turn the cost of the actual anchor expansion
into `r` to the number of anchor factors. -/
theorem borderRankLe_anchor_expansion_pow {N r : ℕ} {d : Fin N → ℕ}
    (hN : 0 < N) (K : Finset (Fin N)) (T : Coeffs d) (b : ℕ)
    (hd : ∀ i ∈ K, d i ≤ r)
    (h : ∀ gamma : (∀ i : K, Fin (d i)), borderRankLe (coefficientSlice K gamma T) b) :
    borderRankLe T (r ^ K.card * b) :=
  borderRankLe_mono hN (Nat.mul_le_mul_right b (anchor_assignment_card_le K hd))
    (borderRankLe_anchor_expansion K T b h)

/-- Substituting the normalized-core bound after expanding at most
`2*r-2` original factors gives precisely the exponent of Theorem 1.1. -/
theorem borderRankLe_anchor_expansion_mainExponent {N r : ℕ} {d : Fin N → ℕ}
    (hN : 0 < N) (hr : 1 ≤ r) (K : Finset (Fin N)) (T : Coeffs d)
    (hd : ∀ i ∈ K, d i ≤ r) (hK : K.card ≤ 2 * r - 2)
    (h : ∀ gamma : (∀ i : K, Fin (d i)),
      borderRankLe (coefficientSlice K gamma T) (r ^ (r ^ 2 - 1) * F (r ^ 2))) :
    borderRankLe T (r ^ (r ^ 2 + 2 * r - 3) * F (r ^ 2)) := by
  have hexp : K.card + (r ^ 2 - 1) ≤ r ^ 2 + 2 * r - 3 := by
    have hr2 : 1 ≤ r ^ 2 := by nlinarith
    omega
  have hb : r ^ K.card * (r ^ (r ^ 2 - 1) * F (r ^ 2)) ≤
      r ^ (r ^ 2 + 2 * r - 3) * F (r ^ 2) := by
    rw [← mul_assoc, ← pow_add]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hr hexp)
  exact borderRankLe_mono hN hb
    (borderRankLe_anchor_expansion_pow hN K T _ hd h)

end UniformBorderRank
