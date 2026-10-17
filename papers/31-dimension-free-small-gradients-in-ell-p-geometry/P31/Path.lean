import P31.Transport
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The summable path bound (paper Lemma 4.2)

The proof uses actual distances between the computed points and the exact
minimizers.  It holds in every seminormed additive group, so the vector and
matrix geometries can use the same argument after supplying Lemma 4.1.
-/

namespace P31

noncomputable section

variable {E : Type*} [SeminormedAddCommGroup E]

/-- The constant in the paper's path estimate, for any base ratio `ρ > 1`. -/
def pathConstant (ρ : ℝ) : ℝ := (ρ + 1) / (ρ - 1)

theorem one_le_pathConstant {ρ : ℝ} (hρ : 1 < ρ) : 1 ≤ pathConstant ρ := by
  unfold pathConstant
  apply (le_div_iff₀ (by linarith : 0 < ρ - 1)).2
  linarith

theorem pathConstant_step {ρ : ℝ} (hρ : 1 < ρ) :
    (pathConstant ρ + 1) / ρ + 1 = pathConstant ρ := by
  unfold pathConstant
  have hρ0 : ρ ≠ 0 := ne_of_gt (lt_trans zero_lt_one hρ)
  have hρ1 : ρ - 1 ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

/-- The computed step estimate (4.3), obtained by passing through the exact
minimizer of the new stage. -/
theorem computed_step_bound (x exactMin : ℕ → E) (δ : ℕ → ℝ) (k : ℕ)
    (hContract : ‖x (k + 1) - exactMin (k + 1)‖ ≤ δ (k + 1))
    (hTransport : ‖exactMin (k + 1) - x k‖ ≤ δ k) :
    ‖x (k + 1) - x k‖ ≤ δ (k + 1) + δ k := by
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    (add_le_add hContract hTransport)

/-- Local form of the path argument.  There are `n` computed steps after the
historical center `x i`, followed by the last transport step. -/
theorem path_bound_local
    (x exactMin : ℕ → E) (δ : ℕ → ℝ) (ρ : ℝ) (hρ : 1 < ρ)
    (hδ : ∀ k, 0 ≤ δ k)
    (hRatio : ∀ k, δ (k + 1) = δ k / ρ)
    (i n : ℕ)
    (hTransport : ∀ k, i ≤ k → k ≤ i + n →
      ‖exactMin (k + 1) - x k‖ ≤ δ k)
    (hContract : ∀ k, i < k → k ≤ i + n →
      ‖x k - exactMin k‖ ≤ δ k) :
    ‖exactMin (i + n + 1) - x i‖ ≤ pathConstant ρ * δ i := by
  induction n generalizing i with
  | zero =>
      have ht := hTransport i le_rfl (by omega)
      simp only [Nat.add_zero] at ht ⊢
      exact ht.trans (le_mul_of_one_le_left (hδ i) (one_le_pathConstant hρ))
  | succ n ih =>
      have hTail : ‖exactMin ((i + 1) + n + 1) - x (i + 1)‖ ≤
          pathConstant ρ * δ (i + 1) := by
        apply ih (i + 1)
        · intro k hk hk'
          exact hTransport k (by omega) (by omega)
        · intro k hk hk'
          exact hContract k (by omega) (by omega)
      have hStep : ‖x (i + 1) - x i‖ ≤ δ (i + 1) + δ i :=
        computed_step_bound x exactMin δ i
          (hContract (i + 1) (by omega) (by omega))
          (hTransport i le_rfl (by omega))
      have hIndices : i + (n + 1) + 1 = (i + 1) + n + 1 := by omega
      rw [hIndices]
      calc
        ‖exactMin ((i + 1) + n + 1) - x i‖ ≤
            ‖exactMin ((i + 1) + n + 1) - x (i + 1)‖ + ‖x (i + 1) - x i‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ pathConstant ρ * δ (i + 1) + (δ (i + 1) + δ i) :=
          add_le_add hTail hStep
        _ = ((pathConstant ρ + 1) / ρ + 1) * δ i := by rw [hRatio]; ring
        _ = pathConstant ρ * δ i := by rw [pathConstant_step hρ]

/-- Lemma 4.2, in its original finite stage indexing.  The hypotheses are the
two conclusions of Lemma 4.1 at each stage and the geometric radius ratio. -/
theorem path_bound
    (x exactMin : ℕ → E) (δ : ℕ → ℝ) (ρ : ℝ) (S : ℕ)
    (hρ : 1 < ρ) (hδ : ∀ k, 0 ≤ δ k)
    (hRatio : ∀ k, δ (k + 1) = δ k / ρ)
    (hTransport : ∀ s, 1 ≤ s → s ≤ S →
      ‖exactMin s - x (s - 1)‖ ≤ δ (s - 1))
    (hContract : ∀ s, 1 ≤ s → s ≤ S →
      ‖x s - exactMin s‖ ≤ δ s)
    (i : ℕ) (hi : 1 ≤ i) (hiS : i ≤ S) :
    ‖exactMin S - x (i - 1)‖ ≤ pathConstant ρ * δ (i - 1) := by
  have hIndex : i - 1 + (S - i) + 1 = S := by omega
  rw [← hIndex]
  apply path_bound_local x exactMin δ ρ hρ hδ hRatio (i - 1) (S - i)
  · intro k hk hk'
    have ht := hTransport (k + 1) (by omega) (by omega)
    simpa only [Nat.add_sub_cancel] using ht
  · intro k hk hk'
    exact hContract k (by omega) (by omega)

/-- The radii `δₖ = R ρ⁻ᵏ`, written with a natural denominator power. -/
def geometricRadius (R ρ : ℝ) (k : ℕ) : ℝ := R / ρ ^ k

theorem geometricRadius_nonneg {R ρ : ℝ} (hR : 0 ≤ R) (hρ : 0 ≤ ρ) (k : ℕ) :
    0 ≤ geometricRadius R ρ k := by
  unfold geometricRadius
  positivity

theorem geometricRadius_ratio {R ρ : ℝ} (k : ℕ) :
    geometricRadius R ρ (k + 1) = geometricRadius R ρ k / ρ := by
  unfold geometricRadius
  rw [pow_succ, div_mul_eq_div_div]

/-- Lemma 4.2 with the paper's actual geometric radius formula substituted. -/
theorem geometric_path_bound
    (x exactMin : ℕ → E) (R ρ : ℝ) (S : ℕ)
    (hR : 0 ≤ R) (hρ : 1 < ρ)
    (hTransport : ∀ s, 1 ≤ s → s ≤ S →
      ‖exactMin s - x (s - 1)‖ ≤ geometricRadius R ρ (s - 1))
    (hContract : ∀ s, 1 ≤ s → s ≤ S →
      ‖x s - exactMin s‖ ≤ geometricRadius R ρ s)
    (i : ℕ) (hi : 1 ≤ i) (hiS : i ≤ S) :
    ‖exactMin S - x (i - 1)‖ ≤ pathConstant ρ * (R / ρ ^ (i - 1)) := by
  exact path_bound x exactMin (geometricRadius R ρ) ρ S hρ
    (geometricRadius_nonneg hR (le_of_lt (lt_trans zero_lt_one hρ)))
    geometricRadius_ratio
    hTransport hContract i hi hiS

/-- The fixed schedule in the paper uses `ρ = 2` and hence `U = 3`. -/
theorem geometric_path_bound_two
    (x exactMin : ℕ → E) (R : ℝ) (S : ℕ) (hR : 0 ≤ R)
    (hTransport : ∀ s, 1 ≤ s → s ≤ S →
      ‖exactMin s - x (s - 1)‖ ≤ geometricRadius R 2 (s - 1))
    (hContract : ∀ s, 1 ≤ s → s ≤ S →
      ‖x s - exactMin s‖ ≤ geometricRadius R 2 s)
    (i : ℕ) (hi : 1 ≤ i) (hiS : i ≤ S) :
    ‖exactMin S - x (i - 1)‖ ≤ 3 * (R / 2 ^ (i - 1)) := by
  simpa only [pathConstant, show (2 + 1 : ℝ) / (2 - 1) = 3 by norm_num] using
    geometric_path_bound x exactMin R 2 S hR (by norm_num) hTransport hContract i hi hiS

end

end P31
