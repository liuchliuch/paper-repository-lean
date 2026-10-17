import UniformBorderRank.AnchoredRepresentation
import UniformBorderRank.LocalMaps

/-! Normalization of an actual coefficient tensor with two retained anchors. -/
noncomputable section
namespace UniformBorderRank
open Finset

variable {N r : ℕ} {d : Fin N → ℕ} {I J : Type*} [Fintype I] [Fintype J]

/-- The raw anchored matrix for a cut of the remaining sites. -/
def anchoredCut (H : I → J → Coeffs d) (S : Finset (Fin N)) :
    (I × (∀ i ∈ S, Fin (d i))) → (J × (∀ i ∈ Sᶜ, Fin (d i))) → ℂ :=
  fun a b => H a.1 b.1 ((flatIndexEquiv d S).symm (a.2,b.2))

/-- The coefficientwise left and right normalization of the original core. -/
def normalizedCoefficients (H : I → J → Coeffs d)
    (L : Fin r → I → ℂ) (R : J → Fin r → ℂ) (u : ∀ i, Fin (d i)) : EndMat r :=
  fun i j => ∑ a, ∑ b, L i a * H a b u * R b j

/-- Contract a coefficient tensor against one covector per remaining site. -/
def coefficientMultilinear (C : (∀ i, Fin (d i)) → EndMat r) :
    MultilinearMap ℂ (fun i => Fin (d i) → ℂ) (EndMat r) :=
  ∑ u, (MultilinearMap.mkPiRing ℂ (Fin N) (C u)).compLinearMap
    (fun i => LinearMap.proj (u i))

lemma coefficientMultilinear_apply (C : (∀ i, Fin (d i)) → EndMat r)
    (x : ∀ i, Fin (d i) → ℂ) (a b : Fin r) :
    coefficientMultilinear C x a b = ∑ u, C u a b * ∏ i, x i (u i) := by
  classical
  simp [coefficientMultilinear, Finset.sum_apply, MultilinearMap.mkPiRing_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_comm]

/-- The actual normalized multilinear core. -/
def anchorMultilinear (H : I → J → Coeffs d)
    (L : Fin r → I → ℂ) (R : J → Fin r → ℂ) :=
  coefficientMultilinear (normalizedCoefficients H L R)

lemma anchorMultilinear_apply (H : I → J → Coeffs d)
    (L : Fin r → I → ℂ) (R : J → Fin r → ℂ)
    (x : ∀ i, Fin (d i) → ℂ) (i j : Fin r) :
    anchorMultilinear H L R x i j =
      ∑ a, ∑ b, ∑ u, L i a * H a b u * R b j * ∏ k, x k (u k) := by
  classical
  simp only [anchorMultilinear, coefficientMultilinear_apply, normalizedCoefficients,
    sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  rw [sum_comm]

lemma anchorMultilinear_core (H : I → J → Coeffs d)
    (L : Fin r → I → ℂ) (R : J → Fin r → ℂ)
    (b : ∀ i, Fin (d i) → ℂ)
    (h : ∀ i j, ∑ a, ∑ c, L i a *
      (∑ u, H a c u * ∏ k, b k (u k)) * R c j = if i = j then 1 else 0) :
    anchorMultilinear H L R b = 1 := by
  ext i j
  rw [anchorMultilinear_apply]
  change _ = if i = j then 1 else 0
  rw [← h]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro c _
  simp only [mul_sum, sum_mul]
  apply sum_congr rfl
  intro u _
  ring

def anchorCutLeftWeight (L : Fin r → I → ℂ)
    (b x : ∀ i, Fin (d i) → ℂ) (S : Finset (Fin N))
    (p : Fin 2 × Fin r) (a : I × (∀ i ∈ S, Fin (d i))) : ℂ :=
  L p.2 a.1 * ∏ i, if hi : i ∈ S then
    (if p.1 = 0 then b i else x i) (a.2 i hi) else 1

def anchorCutRightWeight (R : J → Fin r → ℂ)
    (b x : ∀ i, Fin (d i) → ℂ) (S : Finset (Fin N))
    (a : J × (∀ i ∈ Sᶜ, Fin (d i))) (q : Fin 2 × Fin r) : ℂ :=
  R a.1 q.2 * ∏ i, if hi : i ∈ Sᶜ then
    (if q.1 = 0 then b i else x i) (a.2 i hi) else 1

/-- Evaluated blocks are actual two-sided linear transformations of the raw
anchored flattening. -/
theorem anchorMultilinear_cut_transform (H : I → J → Coeffs d)
    (L : Fin r → I → ℂ) (R : J → Fin r → ℂ)
    (b x : ∀ i, Fin (d i) → ℂ) (S : Finset (Fin N)) :
    evaluatedCutBlocks (anchorMultilinear H L R) b x S =
      fun p q => ∑ a, ∑ c, anchorCutLeftWeight L b x S p a *
        anchoredCut H S a c * anchorCutRightWeight R b x S c q := by
  classical
  funext p q
  let z : ∀ i, Fin (d i) → ℂ := fun i => if i ∈ S then
    (if p.1 = 0 then b i else x i) else (if q.1 = 0 then b i else x i)
  have hweight (u : ∀ i ∈ S, Fin (d i)) (v : ∀ i ∈ Sᶜ, Fin (d i)) :
      (∏ i, z i ((flatIndexEquiv d S).symm (u,v) i)) =
        (∏ i, if hi : i ∈ S then (if p.1 = 0 then b i else x i) (u i hi) else 1) *
        (∏ i, if hi : i ∈ Sᶜ then (if q.1 = 0 then b i else x i) (v i hi) else 1) := by
    rw [← prod_mul_distrib]
    apply prod_congr rfl
    intro i _
    by_cases hi : i ∈ S
    · simp [z, flatIndexEquiv, hi]
    · simp [z, flatIndexEquiv, hi]
  have hsum (a : I) (c : J) :
      (∑ u, L p.2 a * H a c u * R c q.2 * ∏ i, z i (u i)) =
        ∑ u : (∀ i ∈ S, Fin (d i)), ∑ v : (∀ i ∈ Sᶜ, Fin (d i)),
          anchorCutLeftWeight L b x S p (a,u) * anchoredCut H S (a,u) (c,v) *
            anchorCutRightWeight R b x S (c,v) q := by
    rw [← (flatIndexEquiv d S).symm.sum_comp]
    simp only [Fintype.sum_prod_type]
    apply sum_congr rfl
    intro u _
    apply sum_congr rfl
    intro v _
    rw [hweight]
    dsimp only [anchorCutLeftWeight, anchorCutRightWeight, anchoredCut]
    ring
  change anchorMultilinear H L R z p.2 q.2 = _
  rw [anchorMultilinear_apply]
  simp_rw [hsum]
  simp only [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro a _
  rw [sum_comm]

/-- Every block rank bound required by the normalized matrix-product argument
follows from the ranks of the original anchored flattenings. -/
theorem anchorMultilinear_cut_rank (H : I → J → Coeffs d)
    (L : Fin r → I → ℂ) (R : J → Fin r → ℂ)
    (b : ∀ i, Fin (d i) → ℂ)
    (hcut : ∀ S, Module.finrank ℂ (Submodule.span ℂ (Set.range (anchoredCut H S))) ≤ r) :
    ∀ x S, Module.finrank ℂ (Submodule.span ℂ (Set.range
      (evaluatedCutBlocks (anchorMultilinear H L R) b x S))) ≤ r := by
  intro x S
  rw [anchorMultilinear_cut_transform]
  exact (rowSpan_finrank_transform_le (anchoredCut H S)
    (anchorCutLeftWeight L b x S) (anchorCutRightWeight R b x S)).trans (hcut S)

/-- Covectors of the standard coordinate basis extract the actual coefficient. -/
lemma coefficientMultilinear_basis (C : (∀ i, Fin (d i)) → EndMat r)
    (u : ∀ i, Fin (d i)) :
    coefficientMultilinear C (fun i => Pi.single (u i) 1) = C u := by
  classical
  have hw (v : ∀ i, Fin (d i)) :
      (∏ i, (Pi.single (u i) (1 : ℂ) : Fin (d i) → ℂ) (v i)) = if v = u then 1 else 0 := by
    by_cases hv : v = u
    · subst v; simp
    · rw [if_neg hv]
      obtain ⟨i, hi⟩ : ∃ i, v i ≠ u i := by
        simpa only [ne_eq, funext_iff, not_forall] using hv
      apply prod_eq_zero (mem_univ i)
      simp [Pi.single_apply, Ne.symm hi]
  ext a b
  rw [coefficientMultilinear_apply]
  simp only [hw, mul_ite, mul_one, mul_zero]
  simp

end UniformBorderRank
