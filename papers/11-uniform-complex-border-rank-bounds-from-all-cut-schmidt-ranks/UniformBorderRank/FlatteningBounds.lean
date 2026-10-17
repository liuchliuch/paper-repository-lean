import UniformBorderRank.LocalMaps
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! The actual Schmidt-rank lower bound for complex CP border rank. -/
noncomputable section
namespace UniformBorderRank
open Finset Filter
open scoped Topology

/-- The rank of the actual row space is lower semicontinuous in matrix entries. -/
theorem rowSpan_finrank_eventually_ge {I J : Type*} [Fintype I] [Fintype J]
    (M : I → J → ℂ) :
    ∀ᶠ A in nhds M, Module.finrank ℂ (Submodule.span ℂ (Set.range M)) ≤
      Module.finrank ℂ (Submodule.span ℂ (Set.range A)) := by
  classical
  have he (A : I → J → ℂ) :
      Submodule.span ℂ (Set.range A) = LinearMap.range (Matrix.vecMulLinear A) :=
    (range_vecMulLinear A).symm
  have hself : (Module.finrank ℂ (Submodule.span ℂ (Set.range M)) : Cardinal) ≤
      (Matrix.vecMulLinear M).rank := by
    rw [he, LinearMap.rank, Module.finrank_eq_rank]
  obtain ⟨s, hs, hli⟩ := LinearMap.le_rank_iff_exists_linearIndependent_finset.mp hself
  have hc : Continuous (fun A : I → J → ℂ => fun x : (s : Set (I → ℂ)) =>
      Matrix.vecMulLinear A x) := by
    change Continuous (fun A : I → J → ℂ => fun x : (s : Set (I → ℂ)) =>
      fun j => ∑ i, x.val i * A i j)
    fun_prop
  filter_upwards [hc.tendsto M hli.eventually] with A hA
  have h := LinearMap.le_rank_iff_exists_linearIndependent_finset.mpr ⟨s, hs, hA⟩
  rw [LinearMap.rank, ← he, ← Module.finrank_eq_rank] at h
  exact_mod_cast h

/-- Every actual flattening rank is bounded by the number of CP summands. -/
theorem schmidtRank_le_of_cpRankLe {N b : ℕ} {d : Fin N → ℕ} {T : Coeffs d}
    (hT : cpRankLe T b) (S : Finset (Fin N)) : schmidtRank d T S ≤ b := by
  classical
  obtain ⟨k, hk, hsum⟩ := hT
  choose v hv using hk
  let L (x : ∀ i ∈ S, Fin (d i)) (j : Fin b) :=
    ∏ i, if hi : i ∈ S then v j i (x i hi) else 1
  let R (j : Fin b) (y : ∀ i ∈ Sᶜ, Fin (d i)) :=
    ∏ i, if hi : i ∈ Sᶜ then v j i (y i hi) else 1
  have hm : (fun x y => flatCoeff d T S x y) =
      fun x y => ∑ i : Fin b, ∑ j : Fin b,
        L x i * (if i = j then 1 else 0) * R j y := by
    funext x y
    simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, sum_ite_eq, sum_ite_eq', mem_univ,
      if_true]
    change T ((flatIndexEquiv d S).symm (x,y)) = _
    rw [hsum]
    apply sum_congr rfl
    intro j _
    rw [hv]
    dsimp only [L, R]
    rw [← prod_mul_distrib]
    apply prod_congr rfl
    intro i _
    by_cases hi : i ∈ S <;> simp [flatIndexEquiv, hi]
  change Module.finrank ℂ (Submodule.span ℂ (Set.range _)) ≤ b
  rw [hm]
  exact (rowSpan_finrank_transform_le (fun i j : Fin b => if i = j then 1 else 0)
    L R).trans (by simpa using
      (Submodule.finrank_le (Submodule.span ℂ (Set.range
        (fun i j : Fin b => if i = j then (1 : ℂ) else 0)))))

/-- Every Schmidt rank is a lower bound for complex border rank. -/
theorem schmidtRank_le_of_borderRankLe {N b : ℕ} {d : Fin N → ℕ} {T : Coeffs d}
    (hT : borderRankLe T b) (S : Finset (Fin N)) : schmidtRank d T S ≤ b := by
  obtain ⟨s, hs, ht⟩ := hT
  have hm : Tendsto (fun n x y => flatCoeff d (s n) S x y) atTop
      (nhds (fun x y => flatCoeff d T S x y)) := by
    apply tendsto_pi_nhds.mpr
    intro x
    apply tendsto_pi_nhds.mpr
    intro y
    exact ht _
  have hnear := hm.eventually (rowSpan_finrank_eventually_ge
    (fun x y => flatCoeff d T S x y))
  obtain ⟨n, hn⟩ := hnear.exists
  exact hn.trans (schmidtRank_le_of_cpRankLe (hs n) S)

end UniformBorderRank
