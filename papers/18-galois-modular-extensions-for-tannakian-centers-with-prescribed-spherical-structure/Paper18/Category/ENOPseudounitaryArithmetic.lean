import Paper18.Results.Integrality
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # The algebraic-norm step of ENO Proposition 8.24 -/

noncomputable section
open Classical
open scoped BigOperators
universe u
namespace Paper18

/-- A totally positive algebraic integer whose conjugates are at most one
is one. This is the finite norm-product argument in ENO Proposition 8.24. -/
theorem algebraicInteger_eq_one_of_conjugates_pos_le_one
    {K : Type u} [Field K] [NumberField K] (a : K) (ha : IsIntegral ℤ a)
    (h : ∀ σ : K →ₐ[ℚ] ℂ, 0 < (σ a).re ∧ (σ a).re ≤ 1 ∧ (σ a).im = 0) : a = 1 := by
  letI : Nonempty (K →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  let p : ℝ := ∏ σ : K →ₐ[ℚ] ℂ, (σ a).re
  have hp : 0 < p := Finset.prod_pos (fun σ _ => (h σ).1)
  have hp1 : p ≤ 1 := Finset.prod_le_one (fun σ _ => (h σ).1.le) (fun σ _ => (h σ).2.1)
  have hn : ((Algebra.norm ℚ a : ℚ) : ℝ) = p := by
    have hc := Algebra.norm_eq_prod_embeddings ℚ ℂ a
    have he : (∏ σ : K →ₐ[ℚ] ℂ, σ a) = (p : ℂ) := by
      rw [Complex.ofReal_prod]
      apply Finset.prod_congr rfl
      intro σ _
      exact Complex.ext rfl (by simpa using (h σ).2.2)
    rw [he] at hc
    have hr := congrArg Complex.re hc
    simpa using hr
  have hi : IsIntegral ℤ (Algebra.norm ℚ a) := Algebra.isIntegral_norm ℚ ha
  obtain ⟨n, hn'⟩ := (rat_integral_iff (Algebra.norm ℚ a)).mp hi
  have hnR : p = (n : ℝ) := by rw [← hn, hn']; norm_cast
  have hnpos : (0 : ℤ) < n := by exact_mod_cast (hnR ▸ hp)
  have hnle : n ≤ (1 : ℤ) := by exact_mod_cast (hnR ▸ hp1)
  have hn1 : n = 1 := by omega
  have hp_eq : p = 1 := by simpa [hn1] using hnR
  have hσ (σ : K →ₐ[ℚ] ℂ) : (σ a).re = 1 := by
    have he := Finset.prod_erase_mul (s := Finset.univ)
      (f := fun τ : K →ₐ[ℚ] ℂ => (τ a).re) (Finset.mem_univ σ)
    have herase : (∏ τ ∈ Finset.univ.erase σ, (τ a).re) ≤ 1 :=
      Finset.prod_le_one (fun τ _ => (h τ).1.le) (fun τ _ => (h τ).2.1)
    have hb : p ≤ (σ a).re := by
      dsimp only [p]
      rw [← he]
      exact (mul_le_mul_of_nonneg_right herase (h σ).1.le).trans_eq (one_mul _)
    rw [hp_eq] at hb
    exact le_antisymm (h σ).2.1 hb
  let σ : K →ₐ[ℚ] ℂ := Classical.choice inferInstance
  apply σ.injective
  rw [map_one]
  exact Complex.ext (hσ σ) (by simpa using (h σ).2.2)

end Paper18
