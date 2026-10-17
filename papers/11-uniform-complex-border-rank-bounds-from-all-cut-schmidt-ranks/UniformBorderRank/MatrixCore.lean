import UniformBorderRank.Anchored
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! A rank factorization with left and right normalizers, requiring no
assumed invertible minor. Used to normalize a retained anchor core. -/
noncomputable section
namespace UniformBorderRank
open Finset Module

/-- Every finite matrix of row rank `r` has a rank factorization `X*Y`,
and linear normalizers `L` and `R` satisfying `L*M=Y`, `Y*R=I`. -/
theorem exists_normalized_rank_factorization {I J : Type*} [Fintype I] [Fintype J]
    (M : I → J → ℂ) (r : ℕ)
    (hr : Module.finrank ℂ (Submodule.span ℂ (Set.range M)) = r) :
    ∃ (X : I → Fin r → ℂ) (Y : Fin r → J → ℂ)
      (L : Fin r → I → ℂ) (R : J → Fin r → ℂ),
      (∀ i j, M i j = ∑ a, X i a * Y a j) ∧
      (∀ a j, ∑ i, L a i * M i j = Y a j) ∧
      (∀ a b, ∑ j, Y a j * R j b = if a = b then 1 else 0) := by
  classical
  let W := Submodule.span ℂ (Set.range M)
  let B : Basis (Fin r) ℂ W := (Module.finBasis ℂ W).reindex (finCongr hr)
  let row (i : I) : W := ⟨M i, Submodule.subset_span ⟨i, rfl⟩⟩
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective W.subtype W.ker_subtype
  have hL : ∀ a : Fin r, ∃ c : I → ℂ, ∑ i, c i • M i = (B a).val := by
    intro a
    exact (Submodule.mem_span_range_iff_exists_fun ℂ).mp (B a).property
  choose L hL using hL
  refine ⟨fun i a => B.repr (row i) a, fun a j => (B a).val j,
    L, fun j b => B.coord b (p (Pi.single j 1)), ?_, ?_, ?_⟩
  · intro i j
    have hs := congrArg (fun x : W => x.val j) (B.sum_repr (row i))
    simpa only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, row] using hs.symm
  · intro a j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun (hL a) j
  · intro a b
    let f : (J → ℂ) →ₗ[ℂ] ℂ := (B.coord b).comp p
    have he (y : J → ℂ) : (∑ j, y j * f (Pi.single j 1)) = f y := by
      calc
        _ = f (∑ j, y j • (Pi.single j (1 : ℂ) : J → ℂ)) := by simp [map_sum]
        _ = f y := by
          congr 1
          ext j
          simp [Pi.single_apply, mul_ite]
    have hpB : p (B a).val = B a := LinearMap.congr_fun hp (B a)
    have hh := he (B a).val
    change (∑ j, (B a).val j * f (Pi.single j 1)) = _
    rw [hh]
    simp [f, hpB, Finsupp.single_apply]

end UniformBorderRank
