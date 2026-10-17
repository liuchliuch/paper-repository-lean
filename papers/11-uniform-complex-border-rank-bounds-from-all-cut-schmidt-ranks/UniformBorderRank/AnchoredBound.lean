import UniformBorderRank.RawCoreRanks

/-! The normalized core bound with all normalization and support assumptions
proved from the actual full-rank contracted coefficient core. -/
noncomputable section
namespace UniformBorderRank
open Finset

/-- A full-rank product-contracted core and the raw anchored cut bounds imply
the uniform border-rank bound for every actual anchor coefficient tensor. -/
theorem borderRankLe_anchored_coefficients {N r : ℕ} {d : Fin N → ℕ}
    {I J : Type*} [Fintype I] [Fintype J]
    (hN : 0 < N) (hr : 1 ≤ r) (hd : ∀ i, d i ≤ r)
    (H : I → J → Coeffs d) (b : ∀ i, Fin (d i) → ℂ)
    (hcore : Module.finrank ℂ (Submodule.span ℂ (Set.range
      (fun a c => ∑ u, H a c u * ∏ i, b i (u i)))) = r)
    (hcut : ∀ S, Module.finrank ℂ (Submodule.span ℂ (Set.range (anchoredCut H S))) ≤ r) :
    ∀ a c, borderRankLe (H a c) (r ^ (r ^ 2 - 1) * F (r ^ 2)) := by
  classical
  let w (u : ∀ i, Fin (d i)) := ∏ i, b i (u i)
  let M (a : I) (c : J) := ∑ u, H a c u * w u
  obtain ⟨X, Y, L, R, hXY, hLM, hYR⟩ :=
    exists_normalized_rank_factorization M r hcore
  have hMR (a : I) (i : Fin r) : (∑ c, M a c * R c i) = X a i := by
    simp only [hXY, sum_mul]
    rw [sum_comm]
    simp only [mul_assoc, ← mul_sum, hYR, mul_ite, mul_one, mul_zero]
    simp
  have hLX (i j : Fin r) : (∑ a, L i a * X a j) = if i = j then 1 else 0 := by
    calc
      _ = ∑ a, L i a * (∑ c, M a c * R c j) := by simp only [hMR]
      _ = ∑ c, (∑ a, L i a * M a c) * R c j := by
        simp only [mul_sum, sum_mul, mul_assoc]
        rw [sum_comm]
      _ = _ := by simp only [hLM, hYR]
  let Phi := anchorMultilinear H L R
  have hPhi : Phi b = 1 := by
    apply anchorMultilinear_core
    intro i j
    change (∑ a, ∑ c, L i a * M a c * R c j) = _
    rw [sum_comm]
    simp only [← sum_mul, hLM, hYR]
  have hblocks := anchorMultilinear_cut_rank H L R b hcut
  have hleft (a : I) (i : Fin r) :
      (∑ c, ∑ u, H a c u * w u * R c i) = X a i := by
    simpa only [M, sum_mul] using hMR a i
  have hright (c : J) (j : Fin r) :
      (∑ a, ∑ u, L j a * H a c u * w u) = Y j c := by
    simpa only [M, mul_sum, mul_assoc] using hLM j c
  have hrow := (boundary_row_rank_le_anchoredCut_empty H).trans (hcut ∅)
  have hcol := (boundary_column_rank_le_anchoredCut_univ H).trans (hcut univ)
  have hrec := anchored_coefficient_reconstruction H w r X Y L R
    hleft hright hLX hYR hrow hcol
  intro a c
  let ell : EndMat r →ₗ[ℂ] ℂ :=
    { toFun := fun A => ∑ i, ∑ j, X a i * A i j * Y j c
      map_add' := by intros; simp [Matrix.add_apply, mul_add, add_mul, sum_add_distrib]
      map_smul' := by intros; simp [Matrix.smul_apply, smul_eq_mul, mul_left_comm,
        mul_assoc, mul_sum] }
  have hb := borderRankLe_normalized_core hN hr hd Phi b hPhi hblocks ell
  have heq : (fun u => ell (Phi (fun i => Pi.single (u i) 1))) = H a c := by
    funext u
    change ell (coefficientMultilinear (normalizedCoefficients H L R)
      (fun i => Pi.single (u i) 1)) = _
    rw [coefficientMultilinear_basis]
    exact (hrec a c u).symm
  rwa [heq] at hb

end UniformBorderRank
