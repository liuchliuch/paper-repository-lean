import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Data.Finsupp.Weight
import Paper08.Basic

/-!
# Lemma 2.3 — Boolean-lattice and formal-series support extraction

* Alternating binomial sum `∑_{k=0}^n (-1)^{n-k} C(n,k) = [n = 0]`
  (the multiplier of (2.8) once supports are identified with subsets).
* Inclusion–exclusion multipliers of (2.8)–(2.9).
* Degree bound: a monomial of degree `p` has support of size at most `p`.
-/

noncomputable section

open scoped Real BigOperators

namespace Paper08
namespace Support

/-- Alternating binomial sum `∑_{k=0}^{n} (-1)^{n-k} C(n,k) = [n = 0]`. -/
lemma sum_choose_alternating (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), ((-1 : ℤ) ^ (n - k) * (n.choose k : ℤ)))
      = if n = 0 then 1 else 0 := by
  have h := Commute.add_pow (show Commute (1:ℤ) (-1) by simp) n
  -- h : (1 + -1) ^ n = ∑ m ∈ range (n+1), 1 ^ m * (-1) ^ (n-m) * ↑(n.choose m)
  simp only [one_pow] at h
  have h0 : (1 + (-1:ℤ)) = 0 := by ring
  rw [h0] at h
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  · have hn' : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
    rw [zero_pow hn'] at h
    have hif : (if n = 0 then (1:ℤ) else 0) = 0 := if_neg hn'
    rw [hif]
    have h1 : (∑ k ∈ Finset.range (n + 1), ((-1 : ℤ) ^ (n - k) * (n.choose k : ℤ)))
        = (∑ k ∈ Finset.range (n + 1), (1 * (-1 : ℤ) ^ (n - k) * (n.choose k : ℤ))) := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [h1]
    exact h.symm

/-- The multiplier of a monomial of support `S` under (2.8):
`∑_{B : S ⊆ B ⊆ A} (-1)^{|A|-|B|}`. -/
def ieMultiplier {α : Type*} [DecidableEq α] (A S : Finset α) : ℤ :=
  ∑ B ∈ A.powerset, if S ⊆ B then (-1 : ℤ) ^ (A.card - B.card) else 0

/-- When `S = A` the multiplier is `1`. -/
lemma ie_multiplier_self {α : Type*} [DecidableEq α] (A : Finset α) :
    ieMultiplier A A = 1 := by
  unfold ieMultiplier
  rw [Finset.sum_eq_single A]
  · simp
  · intro B hB hne
    by_cases hsub : A ⊆ B
    · have h1 : B ⊆ A := Finset.mem_powerset.mp hB
      exact absurd (Finset.Subset.antisymm hsub h1).symm hne
    · rw [if_neg hsub]
  · intro h
    exact absurd (Finset.mem_powerset_self A) h

/-- When `A = ∅` the multiplier of the empty support is `1`. -/
lemma ie_multiplier_empty {α : Type*} [DecidableEq α] :
    ieMultiplier (∅ : Finset α) ∅ = 1 := by
  simp [ieMultiplier]

/-- Degree bound: if every exponent is at least `1` and they sum to `p`,
the support has size at most `p`. -/
lemma support_card_le_degree {α : Type*} [Fintype α]
    (S : Finset α) (exps : S → ℕ) (hp : ∀ i, 1 ≤ exps i)
    (p : ℕ) (hsum : (∑ i, exps i) = p) : S.card ≤ p := by
  have h2 : (S.card : ℕ) ≤ ∑ i, exps i := by
    have : (∑ i, (1:ℕ)) ≤ ∑ i, exps i := Finset.sum_le_sum (fun i _ => hp i)
    simpa using this
  omega

/-! ## Möbius extraction on the Boolean lattice -/

/-- The actual finite alternating transform in (2.8). -/
def mobius {α R : Type*} [DecidableEq α] [CommRing R]
    (F : Finset α → R) (A : Finset α) : R :=
  ∑ B ∈ A.powerset, (-1 : R) ^ (A.card - B.card) * F B

/-- Inserting a new index replaces a set function by its finite difference. -/
lemma mobius_insert {α R : Type*} [DecidableEq α] [CommRing R]
    (F : Finset α → R) (A : Finset α) (a : α) (ha : a ∉ A) :
    mobius F (insert a A) =
      mobius (fun B => F (insert a B)) A - mobius F A := by
  unfold mobius
  rw [Finset.sum_powerset_insert ha]
  have hleft :
      (∑ B ∈ A.powerset, (-1 : R) ^ ((insert a A).card - B.card) * F B) =
        -(∑ B ∈ A.powerset, (-1 : R) ^ (A.card - B.card) * F B) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro B hB
    have hcard := Finset.card_le_card (Finset.mem_powerset.mp hB)
    rw [Finset.card_insert_of_notMem ha,
      show A.card + 1 - B.card = (A.card - B.card) + 1 by omega, pow_succ]
    ring
  have hright :
      (∑ B ∈ A.powerset,
        (-1 : R) ^ ((insert a A).card - (insert a B).card) * F (insert a B)) =
      ∑ B ∈ A.powerset, (-1 : R) ^ (A.card - B.card) * F (insert a B) := by
    apply Finset.sum_congr rfl
    intro B hB
    have hab : a ∉ B := fun h => ha ((Finset.mem_powerset.mp hB) h)
    rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem hab]
    simp
  rw [hleft, hright]
  ring

/-- An index on which a set function does not depend causes exact cancellation. -/
lemma mobius_eq_zero_of_invariant {α R : Type*} [DecidableEq α] [CommRing R]
    (F : Finset α → R) (A : Finset α) (a : α) (ha : a ∈ A)
    (hinv : ∀ B ⊆ A.erase a, F (insert a B) = F B) :
    mobius F A = 0 := by
  rw [← Finset.insert_erase ha, mobius_insert F (A.erase a) a (Finset.notMem_erase a A)]
  have h : mobius (fun B => F (insert a B)) (A.erase a) = mobius F (A.erase a) := by
    unfold mobius
    exact Finset.sum_congr rfl (fun B hB => by simp only [hinv B (Finset.mem_powerset.mp hB)])
  rw [h, sub_self]

/-- Complete inclusion–exclusion multiplier, including all off-diagonal cases. -/
lemma mobius_indicator {α R : Type*} [DecidableEq α] [CommRing R]
    (A S : Finset α) (r : R) :
    mobius (fun B => if S ⊆ B then r else 0) A = if S = A then r else 0 := by
  by_cases hSA : S = A
  · subst S
    unfold mobius
    rw [Finset.sum_eq_single A]
    · simp
    · intro B hB hne
      have hnot : ¬ A ⊆ B := fun h => hne
        (Finset.Subset.antisymm (Finset.mem_powerset.mp hB) h)
      simp [hnot]
    · simp
  · rw [if_neg hSA]
    by_cases hsub : S ⊆ A
    · have hproper : ¬ A ⊆ S := fun h => hSA (Finset.Subset.antisymm hsub h)
      obtain ⟨a, haA, haS⟩ := Finset.not_subset.mp hproper
      apply mobius_eq_zero_of_invariant _ A a haA
      intro B _
      simp only [Finset.subset_insert_iff_of_notMem haS]
    · unfold mobius
      apply Finset.sum_eq_zero
      intro B hB
      have hnot : ¬ S ⊆ B := fun h => hsub (h.trans (Finset.mem_powerset.mp hB))
      simp [hnot]

lemma ie_multiplier {α : Type*} [DecidableEq α] (A S : Finset α) :
    ieMultiplier A S = if S = A then 1 else 0 := by
  simpa [ieMultiplier, mobius, mul_ite] using mobius_indicator A S (1 : ℤ)

/-- Boolean-lattice inversion, with no assumptions on the input set function. -/
lemma sum_mobius {α R : Type*} [DecidableEq α] [CommRing R]
    (F : Finset α → R) (E : Finset α) :
    (∑ A ∈ E.powerset, mobius F A) = F E := by
  induction E using Finset.induction_on generalizing F with
  | empty => simp [mobius]
  | @insert a E ha ih =>
    rw [Finset.sum_powerset_insert ha, ih F]
    have h : (∑ A ∈ E.powerset, mobius F (insert a A)) =
        ∑ A ∈ E.powerset,
          (mobius (fun B => F (insert a B)) A - mobius F A) := by
      apply Finset.sum_congr rfl
      intro A hA
      exact mobius_insert F A a (fun h => ha ((Finset.mem_powerset.mp hA) h))
    rw [h, Finset.sum_sub_distrib, ih, ih]
    ring

/-! ## Multivariate formal series, coefficient by coefficient -/

/-- Set every variable outside `B` to zero. This is the coefficient definition of
restriction to a coordinate subspace, valid also for infinitely many variables. -/
def restrictSeries {α R : Type*} [DecidableEq α] [CommRing R]
    (B : Finset α) (G : MvPowerSeries α R) : MvPowerSeries α R :=
  fun d => if d.support ⊆ B then MvPowerSeries.coeff d G else 0

@[simp] lemma coeff_restrictSeries {α R : Type*} [DecidableEq α] [CommRing R]
    (B : Finset α) (G : MvPowerSeries α R) (d : α →₀ ℕ) :
    MvPowerSeries.coeff d (restrictSeries B G) =
      if d.support ⊆ B then MvPowerSeries.coeff d G else 0 := rfl

/-- The alternating transform of coordinate restrictions in (2.8). -/
def supportSeries {α R : Type*} [DecidableEq α] [CommRing R]
    (A : Finset α) (G : MvPowerSeries α R) : MvPowerSeries α R :=
  ∑ B ∈ A.powerset,
    MvPowerSeries.C ((-1 : R) ^ (A.card - B.card)) * restrictSeries B G

/-- Equation (2.9): the alternating transform retains exactly the monomials
whose support equals `A`. No convergence assumption is involved. -/
lemma coeff_supportSeries {α R : Type*} [DecidableEq α] [CommRing R]
    (A : Finset α) (G : MvPowerSeries α R) (d : α →₀ ℕ) :
    MvPowerSeries.coeff d (supportSeries A G) =
      if d.support = A then MvPowerSeries.coeff d G else 0 := by
  simp only [supportSeries, map_sum, MvPowerSeries.coeff_C_mul, coeff_restrictSeries]
  exact mobius_indicator A d.support (MvPowerSeries.coeff d G)

/-- The inversion identity following (2.9), as equality of formal power series. -/
lemma sum_supportSeries {α R : Type*} [DecidableEq α] [CommRing R]
    (E : Finset α) (G : MvPowerSeries α R) :
    (∑ A ∈ E.powerset, supportSeries A G) = restrictSeries E G := by
  ext d
  simp only [map_sum, coeff_restrictSeries]
  have h := sum_mobius
    (fun B => if d.support ⊆ B then MvPowerSeries.coeff d G else 0) E
  simpa only [coeff_supportSeries, mobius_indicator] using h

/-- A nonzero exponent contributes at least one to the total degree. -/
lemma finsupp_support_card_le_degree {α : Type*} (d : α →₀ ℕ) :
    d.support.card ≤ d.degree := by
  classical
  change d.support.card ≤ ∑ i ∈ d.support, d i
  calc
    d.support.card = ∑ _i ∈ d.support, 1 := by simp
    _ ≤ ∑ i ∈ d.support, d i := Finset.sum_le_sum fun i hi =>
      Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)

/-- The degree-vanishing assertion of Lemma 2.3 for every multi-index. -/
lemma coeff_supportSeries_eq_zero_of_degree_lt {α R : Type*} [DecidableEq α]
    [CommRing R] (A : Finset α) (G : MvPowerSeries α R) (d : α →₀ ℕ)
    (hdeg : d.degree < A.card) :
    MvPowerSeries.coeff d (supportSeries A G) = 0 := by
  rw [coeff_supportSeries, if_neg]
  intro h
  have hc := finsupp_support_card_le_degree d
  rw [h] at hc
  omega

/-- The empty support vanishes when the original series has constant term zero. -/
lemma supportSeries_empty {α R : Type*} [DecidableEq α] [CommRing R]
    (G : MvPowerSeries α R) (hG : MvPowerSeries.constantCoeff G = 0) :
    supportSeries ∅ G = 0 := by
  ext d
  rw [coeff_supportSeries]
  by_cases hd : d = 0
  · subst d
    simpa only [Finsupp.support_zero, if_pos rfl, map_zero,
      MvPowerSeries.coeff_zero_eq_constantCoeff] using hG
  · have hs : d.support ≠ ∅ := fun hs => hd (Finsupp.support_eq_empty.mp hs)
    simp [hs]

/-- If a series uses only variables in a proper subset of `A`, its extracted
`A`-part is zero. This is the algebraic cancellation used for independent components. -/
lemma supportSeries_eq_zero_of_supportedOn {α R : Type*} [DecidableEq α] [CommRing R]
    (A C : Finset α) (G : MvPowerSeries α R) (hproper : ¬ A ⊆ C)
    (hG : ∀ d : α →₀ ℕ, ¬ d.support ⊆ C → MvPowerSeries.coeff d G = 0) :
    supportSeries A G = 0 := by
  ext d
  rw [coeff_supportSeries]
  by_cases hd : d.support = A
  · simp only [hd, map_zero]
    exact hG d (by simpa only [hd] using hproper)
  · simp [hd]

/-- Additive decomposition over proper coordinate groups has no full-support
monomial. This covers any number of disconnected components, not just two. -/
lemma supportSeries_component_sum {α R ι : Type*} [DecidableEq α] [CommRing R]
    (A : Finset α) (I : Finset ι) (C : ι → Finset α)
    (G : ι → MvPowerSeries α R) (hproper : ∀ i ∈ I, ¬ A ⊆ C i)
    (hG : ∀ i ∈ I, ∀ d : α →₀ ℕ, ¬ d.support ⊆ C i →
      MvPowerSeries.coeff d (G i) = 0) :
    supportSeries A (∑ i ∈ I, G i) = 0 := by
  ext d
  rw [coeff_supportSeries]
  by_cases hd : d.support = A
  · simp only [hd, map_sum, map_zero]
    exact Finset.sum_eq_zero (fun i hi => hG i hi d (by simpa only [hd] using hproper i hi))
  · simp [hd]

end Support
end Paper08
