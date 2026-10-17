/-
Copyright (c) 2026. Actual local-chain approximation errors charge block volume.
-/
import Paper09.Coupling
import Paper09.Markov

open Finset BigOperators Classical Real
noncomputable section
namespace Paper09.LocalSimulation
variable {V : Type*} [Fintype V]

/-- A law actually keeps the exterior spins fixed. -/
def FrozenOutside (B : Finset V) (τ : Config V) (p : FinProb (Config V)) : Prop :=
  ∀ η, p.w η ≠ 0 → ∀ x, x ∉ B → η x = τ x

/-- Hamming cost restricted to a physical block. -/
def localHamming (B : Finset V) (η ξ : Config V) : ℝ :=
  ∑ x ∈ B, if η x = ξ x then (0:ℝ) else 1

theorem localHamming_self (B : Finset V) (η : Config V) : localHamming B η η = 0 := by
  simp [localHamming]

theorem localHamming_le_card (B : Finset V) (η ξ : Config V) :
    localHamming B η ξ ≤ B.card := by
  calc localHamming B η ξ ≤ ∑ _x ∈ B, (1:ℝ) := by
         apply sum_le_sum
         intro x _
         split_ifs <;> norm_num
    _ = _ := by simp

theorem hamming_eq_local (B : Finset V) (η ξ : Config V)
    (hext : ∀ x, x ∉ B → η x = ξ x) : hammingR η ξ = localHamming B η ξ := by
  rw [hammingR_eq_sum]
  symm
  apply Finset.sum_subset (subset_univ B)
  intro x _ hx
  simp [hext x hx]

theorem coupling_cost_local {B : Finset V} {τ : Config V} {p q : FinProb (Config V)}
    (hp : FrozenOutside B τ p) (hq : FrozenOutside B τ q) (c : Coupling p q) :
    c.cost hammingR = c.cost (localHamming B) := by
  unfold Coupling.cost
  apply sum_congr rfl
  intro η _
  apply sum_congr rfl
  intro ξ _
  by_cases hc : c.mass η ξ = 0
  · simp [hc]
  · have hpw : p.w η ≠ 0 := fun hz => hc (c.mass_eq_zero_of_row hz ξ)
    have hqw : q.w ξ ≠ 0 := fun hz => hc (c.mass_eq_zero_of_col hz η)
    rw [hamming_eq_local B η ξ (fun x hx => (hp η hpw x hx).trans (hq ξ hqw x hx).symm)]

/-- Maximal coupling of a local output and its equilibrium sample costs only
`|B| * TV`, proved from their actual frozen-exterior supports. -/
theorem wasserstein_le_block_tv {B : Finset V} {τ : Config V}
    {p q : FinProb (Config V)} (hp : FrozenOutside B τ p) (hq : FrozenOutside B τ q) :
    hammingWasserstein p q ≤ (B.card : ℝ) * tvDist p q := by
  calc hammingWasserstein p q ≤ (Coupling.maximal p q).cost hammingR :=
         Wasserstein.le_cost hammingR_nonneg _
    _ = (Coupling.maximal p q).cost (localHamming B) := coupling_cost_local hp hq _
    _ ≤ _ := Coupling.maximal_cost_le p q (localHamming B) B.card
      (localHamming_self B) (localHamming_le_card B)

/-- The two real local approximation couplings can be glued to the Gibbs
influence coupling, incurring `2|B|δ` rather than the ambient volume. -/
theorem block_simulation_gluing (B : Finset V) (τ τ' : Config V)
    (p q pEq qEq : FinProb (Config V)) (δp δq : ℝ)
    (hp : FrozenOutside B τ p) (hpe : FrozenOutside B τ pEq)
    (hq : FrozenOutside B τ' q) (hqe : FrozenOutside B τ' qEq)
    (htvp : tvDist p pEq ≤ δp) (htvq : tvDist qEq q ≤ δq) :
    hammingWasserstein p q ≤ hammingWasserstein pEq qEq + (B.card : ℝ)*(δp+δq) := by
  have hpw := (wasserstein_le_block_tv hp hpe).trans
    (mul_le_mul_of_nonneg_left htvp (Nat.cast_nonneg B.card))
  have hqw := (wasserstein_le_block_tv hqe hq).trans
    (mul_le_mul_of_nonneg_left htvq (Nat.cast_nonneg B.card))
  have ht₁ : hammingWasserstein p q ≤ hammingWasserstein p pEq + hammingWasserstein pEq q :=
    Wasserstein.triangle hammingR_nonneg hammingR_triangle
  have ht₂ : hammingWasserstein pEq q ≤ hammingWasserstein pEq qEq + hammingWasserstein qEq q :=
    Wasserstein.triangle hammingR_nonneg hammingR_triangle
  nlinarith

end Paper09.LocalSimulation
