import UniformBorderRank.RankOps
import UniformBorderRank.Anchored

/-! Local linear maps on coefficient tensors. -/
noncomputable section
namespace UniformBorderRank
open Finset

/-- Apply an arbitrary linear map at every tensor factor. -/
def tensorMap {N : ℕ} {d e : Fin N → ℕ}
    (A : ∀ i, Fin (e i) → Fin (d i) → ℂ) (T : Coeffs d) : Coeffs e :=
  fun u => ∑ v, T v * ∏ i, A i (u i) (v i)

lemma tensorMap_add {N : ℕ} {d e : Fin N → ℕ}
    (A : ∀ i, Fin (e i) → Fin (d i) → ℂ) (T U : Coeffs d) :
    tensorMap A (T + U) = tensorMap A T + tensorMap A U := by
  ext u
  simp [tensorMap, add_mul, sum_add_distrib]

lemma tensorMap_smul {N : ℕ} {d e : Fin N → ℕ}
    (A : ∀ i, Fin (e i) → Fin (d i) → ℂ) (c : ℂ) (T : Coeffs d) :
    tensorMap A (c • T) = c • tensorMap A T := by
  ext u
  simp [tensorMap, mul_assoc, mul_sum]

def tensorLinearMap {N : ℕ} {d e : Fin N → ℕ}
    (A : ∀ i, Fin (e i) → Fin (d i) → ℂ) : Coeffs d →ₗ[ℂ] Coeffs e where
  toFun := tensorMap A
  map_add' := tensorMap_add A
  map_smul' := tensorMap_smul A

lemma isProduct_tensorMap {N : ℕ} {d e : Fin N → ℕ}
    (A : ∀ i, Fin (e i) → Fin (d i) → ℂ) {T : Coeffs d} (hT : isProduct T) :
    isProduct (tensorMap A T) := by
  classical
  obtain ⟨v, hv⟩ := hT
  refine ⟨fun i a => ∑ x, v i x * A i a x, ?_⟩
  intro u
  unfold tensorMap
  simp_rw [hv, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => v i x * A i (u i) x)).symm

lemma cpRankLe_tensorMap {N : ℕ} {d e : Fin N → ℕ}
    (A : ∀ i, Fin (e i) → Fin (d i) → ℂ) {T : Coeffs d} {b : ℕ}
    (hT : cpRankLe T b) : cpRankLe (tensorMap A T) b := by
  classical
  obtain ⟨v, hv, hs⟩ := hT
  refine ⟨fun j => tensorMap A (v j), fun j => isProduct_tensorMap A (hv j), ?_⟩
  intro u
  unfold tensorMap
  simp_rw [hs, Finset.sum_mul]
  exact Finset.sum_comm

lemma borderRankLe_tensorMap {N : ℕ} {d e : Fin N → ℕ}
    (A : ∀ i, Fin (e i) → Fin (d i) → ℂ) {T : Coeffs d} {b : ℕ}
    (hT : borderRankLe T b) : borderRankLe (tensorMap A T) b := by
  classical
  obtain ⟨v, hv, hl⟩ := hT
  refine ⟨fun n => tensorMap A (v n), fun n => cpRankLe_tensorMap A (hv n), ?_⟩
  intro u
  exact tendsto_finset_sum _ (fun x _ => (hl x).mul_const (∏ i, A i (u i) (x i)))

def flatIndexEquiv {N : ℕ} (d : Fin N → ℕ) (S : Finset (Fin N)) :
    (∀ i, Fin (d i)) ≃ (∀ i ∈ S, Fin (d i)) × (∀ i ∈ Sᶜ, Fin (d i)) where
  toFun u := (fun i _ => u i, fun i _ => u i)
  invFun u i := if h : i ∈ S then u.1 i h else u.2 i (mem_compl.mpr h)
  left_inv u := by funext i; dsimp; split_ifs <;> rfl
  right_inv u := by
    apply Prod.ext
    · funext i hi; exact dif_pos hi
    · funext i hi; exact dif_neg (mem_compl.mp hi)

/-- Local linear maps cannot increase any flattening rank. -/
theorem schmidtRank_tensorMap_le {N : ℕ} {d e : Fin N → ℕ}
    (A : ∀ i, Fin (e i) → Fin (d i) → ℂ) (T : Coeffs d) (S : Finset (Fin N)) :
    schmidtRank e (tensorMap A T) S ≤ schmidtRank d T S := by
  classical
  let L (x : ∀ i ∈ S, Fin (e i)) (y : ∀ i ∈ S, Fin (d i)) : ℂ :=
    ∏ i, if h : i ∈ S then A i (x i h) (y i h) else 1
  let R (y : ∀ i ∈ Sᶜ, Fin (d i)) (x : ∀ i ∈ Sᶜ, Fin (e i)) : ℂ :=
    ∏ i, if h : i ∈ Sᶜ then A i (x i h) (y i h) else 1
  have hm : (fun x y => flatCoeff e (tensorMap A T) S x y) =
      (fun x y => ∑ u, ∑ v, L x u * flatCoeff d T S u v * R v y) := by
    funext x y
    let w := (flatIndexEquiv e S).symm (x, y)
    have hweight (u : ∀ i ∈ S, Fin (d i)) (v : ∀ i ∈ Sᶜ, Fin (d i)) :
        (∏ i, A i (w i) ((flatIndexEquiv d S).symm (u, v) i)) = L x u * R v y := by
      dsimp only [L, R]
      rw [← prod_mul_distrib]
      apply prod_congr rfl
      intro i _
      by_cases hi : i ∈ S
      · simp [w, flatIndexEquiv, hi]
      · simp [w, flatIndexEquiv, hi]
    change (∑ u, T u * ∏ i, A i (w i) (u i)) = _
    rw [← (flatIndexEquiv d S).symm.sum_comp]
    simp only [Fintype.sum_prod_type]
    apply sum_congr rfl
    intro u _
    apply sum_congr rfl
    intro v _
    rw [hweight]
    change T ((flatIndexEquiv d S).symm (u, v)) * (L x u * R v y) =
      L x u * T ((flatIndexEquiv d S).symm (u, v)) * R v y
    ring
  change Module.finrank ℂ (Submodule.span ℂ (Set.range (fun x y =>
      flatCoeff e (tensorMap A T) S x y))) ≤ _
  rw [hm]
  exact rowSpan_finrank_transform_le (fun x y => flatCoeff d T S x y) L R

lemma allCutLe_tensorMap {N : ℕ} {d e : Fin N → ℕ}
    (A : ∀ i, Fin (e i) → Fin (d i) → ℂ) (T : Coeffs d) (D : ℕ)
    (h : allCutLe d T D) : allCutLe e (tensorMap A T) D := by
  intro S he hu
  exact (schmidtRank_tensorMap_le A T S).trans (h S he hu)

end UniformBorderRank
