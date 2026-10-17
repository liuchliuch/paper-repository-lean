import UniformBorderRank.ArtinProduct
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Scheme-theoretic spans on a product affine chart

Fixing a nonzero homogeneous coordinate in every factor gives the usual
product affine chart of a Segre variety. Its coordinate ring is a polynomial
ring in the remaining coordinates. An ideal in this ring specifies a closed
subscheme, including its nilpotent structure. We define its linear span by
the linear sections which vanish in its coordinate ring, and prove that this
span is the image of the dual of restriction. Proposition 3.2 then bounds
every tensor in the span of a finite subscheme.

This file treats subschemes contained in one specified product chart. The
global statement that an arbitrary finite projective subscheme admits such a
chart is a separate geometric assertion.
-/

noncomputable section
namespace UniformBorderRank
open Finset Module

variable {N : ℕ} {d : Fin N → ℕ}

/-- Affine coordinates after fixing the distinguished homogeneous coordinate
`b i` in every projective factor. -/
abbrev SegreChartVar (d : Fin N → ℕ) (b : ∀ i, Fin (d i)) :=
  Σ i, {j : Fin (d i) // j ≠ b i}

/-- The actual polynomial coordinate algebra of the product affine chart. -/
abbrev SegreChartRing (d : Fin N → ℕ) (b : ∀ i, Fin (d i)) :=
  MvPolynomial (SegreChartVar d b) ℂ

/-- The restriction of the `j`-th homogeneous coordinate divided by the
distinguished coordinate at the `i`-th factor. -/
def segreChartCoordinate (b : ∀ i, Fin (d i)) (i : Fin N) (j : Fin (d i)) :
    SegreChartRing d b :=
  if h : j = b i then 1 else MvPolynomial.X ⟨i, ⟨j, h⟩⟩

@[simp] theorem segreChartCoordinate_base (b : ∀ i, Fin (d i)) (i : Fin N) :
    segreChartCoordinate b i (b i) = 1 := by
  simp [segreChartCoordinate]

/-- Restriction of a global section of multidegree `(1,...,1)` to the
product affine chart, using the trivialization by the distinguished product
coordinate. -/
def segreChartSection (b : ∀ i, Fin (d i)) : Coeffs d →ₗ[ℂ] SegreChartRing d b where
  toFun s := ∑ u, s u • ∏ i, segreChartCoordinate b i (u i)
  map_add' s t := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c s := by simp [Finset.smul_sum, smul_smul]

@[simp] theorem segreChartSection_single (b : ∀ i, Fin (d i))
    (u : ∀ i, Fin (d i)) :
    segreChartSection b (Pi.single u 1) = ∏ i, segreChartCoordinate b i (u i) := by
  classical
  simp [segreChartSection]

/-- Restriction of global sections to the closed subscheme defined by `I`.
No radical is taken: vanishing is scheme theoretic. -/
def segreSubschemeRestriction (b : ∀ i, Fin (d i))
    (I : Ideal (SegreChartRing d b)) : Coeffs d →ₗ[ℂ] SegreChartRing d b ⧸ I :=
  (Ideal.Quotient.mkₐ ℂ I).toLinearMap.comp (segreChartSection b)

@[simp] theorem segreSubschemeRestriction_eq_zero_iff (b : ∀ i, Fin (d i))
    (I : Ideal (SegreChartRing d b)) (s : Coeffs d) :
    segreSubschemeRestriction b I s = 0 ↔ segreChartSection b s ∈ I :=
  Ideal.Quotient.eq_zero_iff_mem

/-- The coefficient pairing between tensors and linear forms on the ambient
Segre tensor space. -/
def coefficientFunctional (T : Coeffs d) : Coeffs d →ₗ[ℂ] ℂ where
  toFun s := ∑ u, s u * T u
  map_add' s t := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c s := by simp [Finset.mul_sum, mul_assoc]

@[simp] theorem coefficientFunctional_single (T : Coeffs d)
    (u : ∀ i, Fin (d i)) : coefficientFunctional T (Pi.single u 1) = T u := by
  classical
  change (∑ v, (Pi.single u (1 : ℂ) : Coeffs d) v * T v) = T u
  rw [Finset.sum_eq_single u]
  · simp
  · intro v _ hv
    rw [Pi.single_eq_of_ne hv]
    simp
  · simp

/-- The affine cone over the scheme-theoretic linear span of the closed
subscheme `I`: a tensor satisfies every ambient linear equation whose section
vanishes in the quotient algebra. -/
def segreSubschemeSpan (b : ∀ i, Fin (d i))
    (I : Ideal (SegreChartRing d b)) : Set (Coeffs d) :=
  {T | ∀ s, segreChartSection b s ∈ I → coefficientFunctional T s = 0}

/-- Scheme-theoretic span is exactly the image of the dual section
restriction. The existence of the functional is proved from the vanishing
ideal condition, rather than included in the definition of the span. -/
theorem mem_segreSubschemeSpan_iff_dual_image (b : ∀ i, Fin (d i))
    (I : Ideal (SegreChartRing d b)) (T : Coeffs d) :
    T ∈ segreSubschemeSpan b I ↔
      ∃ ell : (SegreChartRing d b ⧸ I) →ₗ[ℂ] ℂ,
        coefficientFunctional T = ell.comp (segreSubschemeRestriction b I) := by
  have hdual := LinearMap.range_dualMap_eq_dualAnnihilator_ker
    (segreSubschemeRestriction b I)
  constructor
  · intro hT
    have hmem : coefficientFunctional T ∈
        (LinearMap.ker (segreSubschemeRestriction b I)).dualAnnihilator := by
      apply (Submodule.mem_dualAnnihilator _).mpr
      intro s hs
      exact hT s ((segreSubschemeRestriction_eq_zero_iff b I s).mp hs)
    rw [← hdual] at hmem
    obtain ⟨ell, hell⟩ := hmem
    exact ⟨ell, hell.symm⟩
  · rintro ⟨ell, hell⟩ s hs
    rw [hell]
    change ell (segreSubschemeRestriction b I s) = 0
    rw [(segreSubschemeRestriction_eq_zero_iff b I s).mpr hs, map_zero]

/-- Local coordinate restrictions into the actual quotient algebra. -/
def segreSubschemeCoordinate (b : ∀ i, Fin (d i))
    (I : Ideal (SegreChartRing d b)) (i : Fin N) (j : Fin (d i)) :
    SegreChartRing d b ⧸ I :=
  Ideal.Quotient.mk I (segreChartCoordinate b i j)

/-- Every tensor in the scheme-theoretic span is an algebra product in the
coordinate algebra of the given subscheme. -/
theorem mem_segreSubschemeSpan_iff_product (b : ∀ i, Fin (d i))
    (I : Ideal (SegreChartRing d b)) (T : Coeffs d) :
    T ∈ segreSubschemeSpan b I ↔
      ∃ ell : (SegreChartRing d b ⧸ I) →ₗ[ℂ] ℂ,
        ∀ u, T u = ell (∏ i, segreSubschemeCoordinate b I i (u i)) := by
  constructor
  · intro hT
    obtain ⟨ell, hell⟩ := (mem_segreSubschemeSpan_iff_dual_image b I T).mp hT
    refine ⟨ell, fun u => ?_⟩
    have h := DFunLike.congr_fun hell (Pi.single u 1)
    rw [coefficientFunctional_single] at h
    change T u = ell ((Ideal.Quotient.mk I) (segreChartSection b (Pi.single u 1))) at h
    rw [segreChartSection_single, map_prod] at h
    exact h
  · rintro ⟨ell, hell⟩
    apply (mem_segreSubschemeSpan_iff_dual_image b I T).mpr
    refine ⟨ell, ?_⟩
    apply LinearMap.ext
    intro s
    change (∑ u, s u * T u) =
      ell ((Ideal.Quotient.mkₐ ℂ I) (∑ u, s u • ∏ i, segreChartCoordinate b i (u i)))
    simp only [map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro u _
    rw [hell u]
    simp [segreSubschemeCoordinate, map_prod]

/-- Cactus-to-border-rank bound for the span of an actual finite closed
subscheme of a product affine chart. Its length is the vector-space
dimension of its quotient algebra, with all nilpotents retained. -/
theorem borderRankLe_segreSubschemeSpan (hN : 0 < N)
    (b : ∀ i, Fin (d i)) (I : Ideal (SegreChartRing d b))
    [FiniteDimensional ℂ (SegreChartRing d b ⧸ I)]
    [Nontrivial (SegreChartRing d b ⧸ I)] {T : Coeffs d}
    (hT : T ∈ segreSubschemeSpan b I) :
    borderRankLe T (F (Module.finrank ℂ (SegreChartRing d b ⧸ I))) := by
  obtain ⟨ell, hell⟩ := (mem_segreSubschemeSpan_iff_product b I T).mp hT
  have he : T = (fun u => ell (∏ i, segreSubschemeCoordinate b I i (u i))) :=
    funext hell
  rw [he]
  exact borderRankLe_algebra_product hN (segreSubschemeCoordinate b I) ell

/-- The uniform length-`m` version, obtained from the quotient length rather
than from a prescribed algebra-product representation. -/
theorem borderRankLe_segreSubschemeSpan_of_length_le (hN : 0 < N)
    (b : ∀ i, Fin (d i)) (I : Ideal (SegreChartRing d b))
    [FiniteDimensional ℂ (SegreChartRing d b ⧸ I)]
    [Nontrivial (SegreChartRing d b ⧸ I)] {m : ℕ}
    (hm : Module.finrank ℂ (SegreChartRing d b ⧸ I) ≤ m) {T : Coeffs d}
    (hT : T ∈ segreSubschemeSpan b I) : borderRankLe T (F m) :=
  borderRankLe_mono hN (F_mono Module.finrank_pos hm)
    (borderRankLe_segreSubschemeSpan hN b I hT)

end UniformBorderRank
