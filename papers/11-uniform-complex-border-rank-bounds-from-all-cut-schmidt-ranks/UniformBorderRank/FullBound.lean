import UniformBorderRank.AnchoredBound
import UniformBorderRank.AnchorSlice
import UniformBorderRank.LocalSupports
import UniformBorderRank.UniformBound
import UniformBorderRank.ProjectiveSecant

/-! The original all-cut uniform bound and its projective secant consequence. -/
noncomputable section
namespace UniformBorderRank
open Finset

/-- With local supports already reduced, the actual retained anchor
construction and reconstruction yield the complete exponent of Theorem 1.1. -/
theorem borderRankLe_maxSchmidtRank_of_local_dims {N : ℕ} (d : Fin N → ℕ)
    (hN : 2 ≤ N) (T : Coeffs d) (hT : T ≠ 0)
    (hr : 2 ≤ maxSchmidtRank d T) (hd : ∀ i, d i ≤ maxSchmidtRank d T) :
    borderRankLe T ((maxSchmidtRank d T) ^
      ((maxSchmidtRank d T) ^ 2 + 2 * maxSchmidtRank d T - 3) *
        F ((maxSchmidtRank d T) ^ 2)) := by
  classical
  let r := maxSchmidtRank d T
  have hr' : 1 ≤ r := by dsimp [r]; omega
  have hcut : allCutLe d T r := allCutLe_of_maxSchmidtRank_le T r (le_refl r)
  obtain ⟨L, R, q, hL, hR, hLR, hcL, hcR, hcore⟩ :=
    exists_original_anchor_core d hN T hT hr
  let e := anchorOutsideDim d L R
  let H := anchorTensor d T L R
  let b := anchorOutsideBase d L R q
  have he : ∀ i, e i ≤ r := by
    intro i
    dsimp [e, anchorOutsideDim]
    split_ifs
    · exact hr'
    · exact hd i
  have hcore' : Module.finrank ℂ (Submodule.span ℂ (Set.range
      (fun a c => ∑ u, H a c u * ∏ i, b i (u i)))) = r := by
    have hm : (fun a c => ∑ u, H a c u * ∏ i, b i (u i)) =
        anchorContract d T L R q := by
      funext a c
      exact anchorTensor_core_eq d T L R hLR q a c
    rw [hm]
    exact hcore
  have hc : ∀ S, Module.finrank ℂ (Submodule.span ℂ (Set.range (anchoredCut H S))) ≤ r := by
    intro S
    exact anchorTensorCut_rank_le d T L R hL hR hLR r hcut S
  have hs := borderRankLe_anchored_coefficients (by omega : 0 < N) hr' he H b hcore' hc
  apply borderRankLe_anchor_expansion_mainExponent (by omega : 0 < N) hr' (L ∪ R) T
  · intro i _
    exact hd i
  · have hcU := card_union_le L R
    dsimp [r] at hr' ⊢
    omega
  · intro gamma
    exact borderRankLe_coefficientSlice_of_anchorTensor d T L R gamma _
      (hs (anchorSliceLeft L R gamma) (anchorSliceRight L R gamma))

/-- The complete higher-rank branch of Theorem 1.1, for arbitrary original
local dimensions. The local support reduction preserves every Schmidt rank
and transports the resulting border-rank bound back to the original tensor. -/
theorem borderRankLe_maxSchmidtRank {N : ℕ} (d : Fin N → ℕ)
    (hN : 2 ≤ N) (T : Coeffs d) (hT : T ≠ 0) (hr : 2 ≤ maxSchmidtRank d T) :
    borderRankLe T ((maxSchmidtRank d T) ^
      ((maxSchmidtRank d T) ^ 2 + 2 * maxSchmidtRank d T - 3) *
        F ((maxSchmidtRank d T) ^ 2)) := by
  let r := maxSchmidtRank d T
  have hcut : allCutLe d T r := allCutLe_of_maxSchmidtRank_le T r (le_refl r)
  obtain ⟨e, U, A, B, he, hU, _, _, hflat, hborder⟩ :=
    exists_local_support_reduction hN T hT r hcut
  have hm : maxSchmidtRank e U = maxSchmidtRank d T := by
    simp only [maxSchmidtRank, hflat]
  have hb := borderRankLe_maxSchmidtRank_of_local_dims e hN U hU
    (by rwa [hm]) (by rwa [hm])
  rw [hm] at hb
  exact (hborder _).mp hb

/-- Both branches of Theorem 1.1, with the original maximal flattening rank. -/
theorem uniform_border_rank_bound {N : ℕ} (d : Fin N → ℕ)
    (hN : 2 ≤ N) (T : Coeffs d) (hT : T ≠ 0) :
    (maxSchmidtRank d T = 1 → isProduct T) ∧
    (2 ≤ maxSchmidtRank d T → borderRankLe T
      ((maxSchmidtRank d T) ^ ((maxSchmidtRank d T) ^ 2 +
        2 * maxSchmidtRank d T - 3) * F ((maxSchmidtRank d T) ^ 2))) := by
  exact ⟨isProduct_of_maxSchmidtRank_one hN T hT,
    borderRankLe_maxSchmidtRank d hN T hT⟩

/-- The original all-cut hypothesis implies the explicit uniform numerical
bound, with no normalized representation or support hypothesis. -/
theorem borderRankLe_of_allCutLe {N D : ℕ} (d : Fin N → ℕ)
    (hN : 2 ≤ N) (hD : 1 ≤ D) (T : Coeffs d) (hT : T ≠ 0)
    (hcut : allCutLe d T D) : borderRankLe T (Bhat D) := by
  have hrpos := maxSchmidtRank_pos hN T hT
  have hrle : maxSchmidtRank d T ≤ D := by
    obtain ⟨S, hSe, hSu, hS⟩ := maxSchmidtRank_attained hN T hT
    rw [← hS]
    exact hcut S hSe hSu
  have hb : borderRankLe T (Bhat (maxSchmidtRank d T)) := by
    by_cases hr1 : maxSchmidtRank d T = 1
    · rw [hr1, Bhat_one]
      exact borderRankLe_of_cpRankLe (cpRankLe_one_of_isProduct
        (isProduct_of_maxSchmidtRank_one hN T hT hr1))
    · rw [Bhat_of_two_le (by omega)]
      exact borderRankLe_maxSchmidtRank d hN T hT (by omega)
  exact borderRankLe_mono (by omega) (Bhat_mono hrle) hb

/-- Corollary 1.2 as membership in the actual projective Zariski closure of
spans of at most `Bhat D` Segre points. -/
theorem allCut_mem_projectiveSecant {N D : ℕ} (d : Fin N → ℕ)
    (hN : 2 ≤ N) (hD : 1 ≤ D) (T : Coeffs d) (hT : T ≠ 0)
    (hcut : allCutLe d T D) :
    Projectivization.mk ℂ T hT ∈ projectiveSecant d (Bhat D) := by
  exact borderRankLe_mem_projectiveSecant (by omega) hT
    (borderRankLe_of_allCutLe d hN hD T hT hcut)

end UniformBorderRank
