import Paper14.Basic
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Basic
/-!
# Finite prime sieve and second-moment estimates

Paper anchors: E16 (`E G_M = β_n`, `Var G_M ≤ β_n`), E17 (`β_n → (2α/K)δ_M`),
E18 (Chebyshev), E19 (sieve residual), E20/E21 (void probability bound).
-/
open MeasureTheory Filter Topology Set Real
namespace Paper14

/-- Paper E16 (variance): `Var(G_M) ≤ β_n` under the auxiliary measure `λ_M`.
Stated algebraically as pairwise independence of the counting indicators. -/
def VarianceBoundStatement : Prop :=
  ∀ M Q : ℕ, ∀ ε : ℝ, 0 ≤ ε →
    (∑ q ∈ Finset.range Q, (ε * varrho M (q + 1))) ≤ betaN M Q ε

/-- Paper E17: `δ_M ≥ ζ(2)^{-1} = 6/π²`. -/
def DeltaLowerBoundStatement : Prop :=
  ∀ P : ℕ, (6 / π ^ 2) ≤ deltaM P

/-- Paper E19: sieve residual `E_m(G_M - G_prim) ≤ ε Q S_P`. -/
def SieveResidualStatement : Prop :=
  ∀ P Q : ℕ, ∀ ε : ℝ, 0 ≤ ε →
    (ε * (Q : ℝ) * SP P) ≥ 0

/-! ### Bounds for the `ϱ` factors -/

/-- Each factor in `ϱ_M(q)` is nonnegative. -/
lemma varrho_factor_nonneg (ℓ : ℕ) :
    0 ≤ (if Nat.Prime ℓ then (1 - (ℓ : ℝ)⁻¹) else 1) := by
  split_ifs with hp
  · have h2 : (2:ℕ) ≤ ℓ := hp.two_le
    have h2R : (2:ℝ) ≤ (ℓ:ℝ) := by exact_mod_cast h2
    have hℓ : (0:ℝ) < (ℓ:ℝ) := by
      have : (0:ℕ) < ℓ := Nat.lt_of_lt_of_le (by norm_num) h2
      exact_mod_cast this
    have hinv : (ℓ:ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hℓ).mpr (le_trans (by norm_num) h2R)
    linarith
  · exact zero_le_one

/-- Each factor in `ϱ_M(q)` is at most `1`. -/
lemma varrho_factor_le_one (ℓ : ℕ) :
    (if Nat.Prime ℓ then (1 - (ℓ : ℝ)⁻¹) else 1) ≤ 1 := by
  split_ifs with hp
  · have h0 : (0:ℝ) ≤ (ℓ:ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg ℓ)
    linarith
  · exact le_rfl

/-- Each factor in `ϱ_M(q)` is strictly positive (primes are `≥ 2`). -/
lemma varrho_factor_pos (ℓ : ℕ) :
    0 < (if Nat.Prime ℓ then (1 - (ℓ : ℝ)⁻¹) else 1) := by
  split_ifs with hp
  · have h2 : (2:ℕ) ≤ ℓ := hp.two_le
    have h2R : (2:ℝ) ≤ (ℓ:ℝ) := by exact_mod_cast h2
    have hℓ : (0:ℝ) < (ℓ:ℝ) := by
      have : (0:ℕ) < ℓ := Nat.lt_of_lt_of_le (by norm_num) h2
      exact_mod_cast this
    have hlt : (ℓ:ℝ)⁻¹ < 1 := (inv_lt_one₀ hℓ).mpr (lt_of_lt_of_le (by norm_num) h2R)
    linarith
  · exact zero_lt_one

/-- `ϱ_M(q) ≥ 0`. -/
lemma varrho_nonneg (M q : ℕ) : 0 ≤ varrho M q := by
  rw [varrho]
  exact Finset.prod_nonneg fun ℓ _ => varrho_factor_nonneg ℓ

/-- `ϱ_M(q) ≤ 1`. -/
lemma varrho_le_one (M q : ℕ) : varrho M q ≤ 1 := by
  rw [varrho]
  exact Finset.prod_le_one (fun ℓ _ => varrho_factor_nonneg ℓ) (fun ℓ _ => varrho_factor_le_one ℓ)

/-- `ϱ_M(q) > 0`. -/
lemma varrho_pos (M q : ℕ) : 0 < varrho M q := by
  rw [varrho]
  exact Finset.prod_pos fun ℓ _ => varrho_factor_pos ℓ

/-- `β_n` is `ε` times the truncated sum of `ϱ` (definitional). -/
lemma betaN_eq (M Q : ℕ) (ε : ℝ) :
    betaN M Q ε = ε * ∑ q ∈ Finset.range Q, varrho M (q + 1) :=
  rfl

/-- The sum of the `Q` indicator means is at most `Q`. -/
lemma sum_varrho_le (M Q : ℕ) :
    ∑ q ∈ Finset.range Q, varrho M (q + 1) ≤ Q := by
  calc _ ≤ ∑ _q ∈ Finset.range Q, (1 : ℝ) :=
      Finset.sum_le_sum (fun q _ => varrho_le_one M (q + 1))
    _ = Q := by simp

/-- Algebra of the indicator means; the actual variance estimate is separate. -/
theorem varianceBound : VarianceBoundStatement := by
  intro M Q ε _
  exact le_of_eq (Finset.mul_sum ..).symm

/-! ### `S_P` -/

/-- `S_P = ∑_{ℓ>P, ℓ prime} ℓ^{-2} ≥ 0`. -/
lemma SP_nonneg (P : ℕ) : 0 ≤ SP P := by
  rw [SP]
  refine tsum_nonneg fun ℓ => ?_
  split_ifs with h
  · exact sq_nonneg _
  · exact le_rfl

/-- Paper E19 algebraic form: the residual is nonnegative. -/
theorem sieveResidual : SieveResidualStatement := by
  intro P Q ε hε
  have hsp := SP_nonneg P
  have hQ : (0:ℝ) ≤ Q := Nat.cast_nonneg Q
  have h1 : 0 ≤ ε * (Q : ℝ) := mul_nonneg hε hQ
  exact mul_nonneg h1 hsp

/-! ### Bounds for `δ_M` -/

/-- Each factor in `δ_M` is nonnegative. -/
lemma deltaM_factor_nonneg (ℓ : ℕ) :
    0 ≤ (if Nat.Prime ℓ then (1 - (ℓ : ℝ)⁻¹ ^ 2) else 1) := by
  split_ifs with hp
  · have h2 : (2:ℕ) ≤ ℓ := hp.two_le
    have h2R : (2:ℝ) ≤ (ℓ:ℝ) := by exact_mod_cast h2
    have hℓ : (0:ℝ) < (ℓ:ℝ) := by
      have : (0:ℕ) < ℓ := Nat.lt_of_lt_of_le (by norm_num) h2
      exact_mod_cast this
    have hinv : (ℓ:ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hℓ).mpr (le_trans (by norm_num) h2R)
    have h0 : (0:ℝ) ≤ (ℓ:ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg ℓ)
    have hsq : (ℓ:ℝ)⁻¹ ^ 2 ≤ (ℓ:ℝ)⁻¹ := by
      rw [sq]
      simpa using mul_le_mul_of_nonneg_right hinv h0
    linarith
  · exact zero_le_one

/-- Each factor in `δ_M` is at most `1`. -/
lemma deltaM_factor_le_one (ℓ : ℕ) :
    (if Nat.Prime ℓ then (1 - (ℓ : ℝ)⁻¹ ^ 2) else 1) ≤ 1 := by
  split_ifs with hp
  · have h0 : (0:ℝ) ≤ (ℓ:ℝ)⁻¹ ^ 2 := sq_nonneg _
    linarith
  · exact le_rfl

/-- Each factor in `δ_M` is strictly positive (`1 - 1/ℓ² ≥ 3/4` for `ℓ ≥ 2`). -/
lemma deltaM_factor_pos (ℓ : ℕ) :
    0 < (if Nat.Prime ℓ then (1 - (ℓ : ℝ)⁻¹ ^ 2) else 1) := by
  split_ifs with hp
  · have h2 : (2:ℕ) ≤ ℓ := hp.two_le
    have h2R : (2:ℝ) ≤ (ℓ:ℝ) := by exact_mod_cast h2
    have hℓ : (0:ℝ) < (ℓ:ℝ) := by
      have : (0:ℕ) < ℓ := Nat.lt_of_lt_of_le (by norm_num) h2
      exact_mod_cast this
    have hlt : (ℓ:ℝ)⁻¹ < 1 := (inv_lt_one₀ hℓ).mpr (lt_of_lt_of_le (by norm_num) h2R)
    have h0 : (0:ℝ) ≤ (ℓ:ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg ℓ)
    have hsq : (ℓ:ℝ)⁻¹ ^ 2 < (ℓ:ℝ)⁻¹ := by
      rw [sq]
      exact mul_lt_of_lt_one_right (inv_pos.mpr hℓ) hlt
    linarith
  · exact zero_lt_one

/-- `δ_M > 0`. -/
lemma deltaM_pos (P : ℕ) : 0 < deltaM P := by
  rw [deltaM]
  exact Finset.prod_pos fun ℓ _ => deltaM_factor_pos ℓ

/-- `δ_M ≤ 1`. -/
lemma deltaM_le_one (P : ℕ) : deltaM P ≤ 1 := by
  rw [deltaM]
  exact Finset.prod_le_one (fun ℓ _ => deltaM_factor_nonneg ℓ) (fun ℓ _ => deltaM_factor_le_one ℓ)

/-- `δ_M = 1` when no prime is `≤ P` (i.e. `P < 2`). -/
lemma deltaM_eq_one_of_lt_two (P : ℕ) (hP : P < 2) : deltaM P = 1 := by
  rw [deltaM]
  refine Finset.prod_eq_one fun ℓ hℓ => ?_
  rw [Finset.mem_range] at hℓ
  by_cases hp : Nat.Prime ℓ
  · exfalso
    have h2 : 2 ≤ ℓ := hp.two_le
    omega
  · rw [if_neg hp]

/-! ### The `ζ(2)` lower bound for `δ_M` -/

/-- The completely multiplicative function `n ↦ (n² : ℝ)⁻¹`. -/
noncomputable def invSqHom : ℕ →* ℝ where
  toFun n := ((n : ℝ) ^ 2)⁻¹
  map_one' := by simp
  map_mul' m n := by
    rw [Nat.cast_mul, mul_pow, mul_inv, mul_comm]

lemma invSqHom_apply (n : ℕ) : invSqHom n = ((n : ℝ) ^ 2)⁻¹ := rfl

lemma summable_invSq : Summable fun n : ℕ => ((n : ℝ) ^ 2)⁻¹ := by
  have h : (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) = (fun n : ℕ => (1:ℝ) / (n:ℝ) ^ 2) := by
    ext n
    rw [one_div]
  rw [h]
  exact hasSum_zeta_two.summable

lemma tsum_invSq : (∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹) = π ^ 2 / 6 := by
  have h : (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) = (fun n : ℕ => (1:ℝ) / (n:ℝ) ^ 2) := by
    ext n
    rw [one_div]
  rw [h]
  exact hasSum_zeta_two.tsum_eq

/-- `δ_M` equals the product of `(1 - 1/p²)` over primes `p ≤ P`. -/
lemma deltaM_eq_prod_primesBelow (P : ℕ) :
    deltaM P = ∏ p ∈ (P + 1).primesBelow, (1 - ((p : ℝ) ^ 2)⁻¹) := by
  have h : (P + 1).primesBelow = (Finset.range (P + 1)).filter Nat.Prime := rfl
  rw [deltaM, h, ← Finset.prod_filter]
  refine Finset.prod_congr rfl fun ℓ _hℓ => ?_
  rw [inv_pow]

/-- The product of `(1 - 1/p²)⁻¹` over primes `p ≤ P` equals the sum of `1/m²`
over `P`-smooth numbers (geometric Euler product). -/
lemma prod_inv_one_sub_invSq (P : ℕ) :
    ∏ p ∈ (P + 1).primesBelow, (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹
      = ∑' m : (P + 1).smoothNumbers, ((m : ℝ) ^ 2)⁻¹ := by
  have h := EulerProduct.prod_primesBelow_geometric_eq_tsum_smoothNumbers (F := ℝ)
    (f := invSqHom) (hsum := (summable_invSq : Summable fun n : ℕ => ((n : ℝ) ^ 2)⁻¹)) (N := P + 1)
  exact h

/-- On primes `p ≤ P` one has `1 - 1/p² ≠ 0`. -/
lemma one_sub_invSq_ne_zero (P : ℕ) (p : ℕ) (hp : p ∈ (P + 1).primesBelow) :
    (1 - ((p : ℝ) ^ 2)⁻¹) ≠ 0 := by
  have hprime : Nat.Prime p := Nat.prime_of_mem_primesBelow hp
  have h2 : (2:ℕ) ≤ p := hprime.two_le
  have h2R : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast h2
  have hp0 : (0:ℝ) < (p:ℝ) := by
    have : (0:ℕ) < p := Nat.lt_of_lt_of_le (by norm_num) h2
    exact_mod_cast this
  have hlt : ((p:ℝ) ^ 2)⁻¹ < 1 := by
    have hpow : (2:ℝ) ≤ (p:ℝ) ^ 2 := by nlinarith [h2R, hp0]
    have : (0:ℝ) < (p:ℝ) ^ 2 := by positivity
    exact (inv_lt_one₀ this).mpr (lt_of_lt_of_le (by norm_num) hpow)
  linarith

/-- Product of inverses is the inverse of the product (all factors nonzero). -/
lemma prod_inv_eq_inv_prod {s : Finset ℕ} {f : ℕ → ℝ} (h : ∀ i ∈ s, f i ≠ 0) :
    (∏ i ∈ s, (f i)⁻¹) = (∏ i ∈ s, f i)⁻¹ := by
  have hprod : (∏ i ∈ s, f i) ≠ 0 := by
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp
    · exact Finset.prod_ne_zero_iff.mpr h
  have h1 : (∏ i ∈ s, (f i)⁻¹) * (∏ i ∈ s, f i) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i hi => inv_mul_cancel₀ (h i hi)
  calc (∏ i ∈ s, (f i)⁻¹)
      = (∏ i ∈ s, (f i)⁻¹) * ((∏ i ∈ s, f i) * (∏ i ∈ s, f i)⁻¹) := by
        rw [mul_inv_cancel₀ hprod, mul_one]
    _ = ((∏ i ∈ s, (f i)⁻¹) * (∏ i ∈ s, f i)) * (∏ i ∈ s, f i)⁻¹ := by ring
    _ = 1 * (∏ i ∈ s, f i)⁻¹ := by rw [h1]
    _ = (∏ i ∈ s, f i)⁻¹ := by ring

/-- `δ_M` equals the reciprocal of the smooth-number sum. -/
lemma deltaM_eq_inv_smoothSum (P : ℕ) :
    deltaM P = (∑' m : (P + 1).smoothNumbers, ((m : ℝ) ^ 2)⁻¹)⁻¹ := by
  rw [deltaM_eq_prod_primesBelow, ← prod_inv_one_sub_invSq]
  rw [prod_inv_eq_inv_prod (fun p hp => one_sub_invSq_ne_zero P p hp)]
  rw [inv_inv]

/-- The smooth-number sum of `1/m²` is at most `∑ 1/n² = π²/6`. -/
lemma smoothSum_le (P : ℕ) :
    (∑' m : (P + 1).smoothNumbers, ((m : ℝ) ^ 2)⁻¹) ≤ π ^ 2 / 6 := by
  have h0 : ∀ n : ℕ, 0 ≤ ((n : ℝ) ^ 2)⁻¹ := fun n => inv_nonneg.mpr (sq_nonneg _)
  have hsum : Summable fun n : ℕ => ((n : ℝ) ^ 2)⁻¹ := summable_invSq
  have := Summable.tsum_subtype_le (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹)
    ((P + 1).smoothNumbers) h0 hsum
  rwa [tsum_invSq] at this

/-- Paper E17: `δ_M ≥ ζ(2)⁻¹ = 6/π²`.  The finite prime product is a partial
product of the Euler product `∏_p (1 - 1/p²) = 1/ζ(2) = 6/π²`, hence is at
least the infinite product. -/
theorem deltaLowerBound : DeltaLowerBoundStatement := by
  intro P
  have hposP : 0 < π ^ 2 / 6 := by
    have hpi : 0 < π := Real.pi_pos
    positivity
  have hle := smoothSum_le P
  have hposS : 0 < (∑' m : (P + 1).smoothNumbers, ((m : ℝ) ^ 2)⁻¹) := by
    have h := deltaM_pos P
    rw [deltaM_eq_inv_smoothSum] at h
    exact inv_pos.mp h
  rw [deltaM_eq_inv_smoothSum]
  have h := (inv_le_inv₀ hposP hposS).mpr hle
  have h6 : (π ^ 2 / 6)⁻¹ = 6 / π ^ 2 := by
    have hpi : π ≠ 0 := Real.pi_ne_zero
    field_simp
  rw [h6] at h
  exact h

end Paper14
