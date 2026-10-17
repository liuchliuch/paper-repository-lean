import Paper18.Fusion.TensorFunctor
import Paper18.Results.PF
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.NumberTheory.Niven
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Tactic

/-!
# Lemma 3.1 — integrality under dominant tensor functors and equivariantization

*The target of a dominant tensor functor from an integral fusion category is
integral. If a finite group `H` acts on a fusion category `C`, then `C^H` is
integral if and only if `C` is integral.*

The direct proof uses the image of the source FP-weighted regular element.
Its coefficients are positive integers when the source is integral. Tensor
compatibility and Frobenius reciprocity make it a positive eigenvector of
the same strictly positive matrix as the target FP dimensions. PF uniqueness
therefore gives rational target dimensions after normalization at the unit.
Their algebraic integrality is proved from integer fusion-matrix
characteristic polynomials, so they are integers. The actual-category bridge
and the equivariant simple-object classification are not asserted here.
-/

noncomputable section

open Classical

universe u v

open scoped BigOperators Matrix

namespace Paper18

/-! ## Rational algebraic integers are integers -/

/-- A real number that is both rational and integral over `ℤ` is an integer. -/
lemma real_rat_integral_eq_int {x : ℝ} (hrat : ∃ q : ℚ, x = q)
    (hint : IsIntegral ℤ x) : ∃ n : ℤ, x = n := by
  obtain ⟨q, hq⟩ := hrat
  subst hq
  exact IsIntegral.exists_int_iff_exists_rat hint |>.mp ⟨q, rfl⟩

/-- On `ℚ`, integrality over `ℤ` is just being an integer. -/
lemma rat_integral_iff (q : ℚ) : IsIntegral ℤ q ↔ ∃ n : ℤ, q = n := by
  constructor
  · intro h
    have h2 := IsIntegrallyClosed.algebraMap_eq_of_integral (R := ℤ) (K := ℚ) h
    obtain ⟨n, hn⟩ := h2
    exact ⟨n, hn.symm⟩
  · intro ⟨n, hn⟩
    rw [hn]
    -- `(n : ℚ)` is the image of an integer, hence integral over `ℤ`.
    refine ⟨_, Polynomial.monic_X_sub_C (R := ℤ) n, ?_⟩
    simp [Polynomial.X]

/-! ## PF integrality transfer -/

/-- Packaged integrality transfer: positive numbers that are rational and
integral over `ℤ` are natural numbers. -/
theorem integrality_of_PF_model {n : ℕ} [NeZero n]
    (d : Fin n → ℝ)
    (hd_pos : ∀ i, 0 < d i)
    (hRat : ∀ i, ∃ q : ℚ, d i = q)
    (hInt : ∀ i, IsIntegral ℤ (d i)) :
    ∀ i, ∃ m : ℕ, d i = m := by
  intro i
  obtain ⟨n0, hn0⟩ := real_rat_integral_eq_int (hRat i) (hInt i)
  have hpos : (0:ℤ) < n0 := by
    have := hd_pos i
    rw [hn0] at this
    exact_mod_cast this
  refine ⟨n0.natAbs, ?_⟩
  have hnn : (n0.natAbs : ℤ) = n0 := Int.natAbs_of_nonneg (le_of_lt hpos)
  rw [hn0, ← hnn]
  simp

/-- Uniqueness of the normalized positive eigenvector of a strictly positive
matrix (PF uniqueness). -/
theorem unique_normalized_pos_eigenvector
    {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (lam : ℝ)
    (hA : ∀ i j, 0 < A i j)
    (v w : Fin n → ℝ)
    (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (hve : ∀ i, ∑ j, A i j * v j = lam * v i)
    (hwe : ∀ i, ∑ j, A i j * w j = lam * w i)
    (hv0 : v 0 = 1) (hw0 : w 0 = 1) :
    ∀ i, v i = w i := by
  obtain ⟨c, _hc_pos, hprop⟩ :=
    posMatrix_positive_eigenspace_one_dim A lam hA v w hv hw hve hwe
  have h1 : v 0 = c * w 0 := hprop 0
  have hc1 : c = 1 := by
    rw [hv0, hw0, mul_one] at h1
    linarith
  intro i
  rw [hprop i, hc1, one_mul]

/-! ## Regular-element proof of rationality -/

namespace FusionBasis

/-- The dimension-weighted regular vector is a common eigenvector for left
multiplication. This follows from rigidity and dimension multiplicativity. -/
lemma regular_eigen {ι : Type u} [Fintype ι] (B : FusionBasis ι) (x z : ι) :
    ∑ y, B.fpdim y * (B.N x y z : ℝ) = B.fpdim x * B.fpdim z := by
  calc
    _ = ∑ y, (B.N (B.dual x) z y : ℝ) * B.fpdim y := by
      apply Finset.sum_congr rfl
      intro y _
      rw [B.N_dual x y z]
      ring
    _ = _ := by simpa using B.fpdim_mul (B.dual x) z

/-- Each FP dimension is an algebraic integer, using the monic characteristic
polynomial of its integer fusion matrix. -/
lemma fpdim_isIntegral {ι : Type u} [Fintype ι] (B : FusionBasis ι) (x : ι) :
    IsIntegral ℤ (B.fpdim x) := by
  let L : Matrix ι ι ℤ := fun i j => B.N x i j
  let Lr : Matrix ι ι ℝ := L.map (Int.castRingHom ℝ)
  have hker : (Matrix.scalar ι (B.fpdim x) - Lr) *ᵥ B.fpdim = 0 := by
    ext i
    simp only [Matrix.sub_mulVec, Matrix.scalar_apply, Matrix.mulVec_diagonal, Pi.sub_apply,
      Pi.zero_apply]
    change B.fpdim x * B.fpdim i - ∑ j, (B.N x i j : ℝ) * B.fpdim j = 0
    rw [B.fpdim_mul]
    ring
  have hne : B.fpdim ≠ 0 := by
    intro h
    have := congrFun h B.one
    simp at this
  have hdet : (Matrix.scalar ι (B.fpdim x) - Lr).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨B.fpdim, hne, hker⟩
  refine ⟨L.charpoly, L.charpoly_monic, ?_⟩
  rw [← Polynomial.eval_map, ← Matrix.charpoly_map, Matrix.eval_charpoly]
  exact hdet

end FusionBasis

namespace FusionMap

variable {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
  {U : FusionBasis ι} {V : FusionBasis κ} (F : FusionMap U V)

/-- Coefficients of the image of the source's FP-weighted regular element. -/
def regularImage (i : κ) : ℝ := ∑ x, U.fpdim x * (F.imageCoeff x i : ℝ)

/-- Left fusion matrix of the image of the sum of all source simples. -/
def dominantMatrix : Matrix κ κ ℝ :=
  fun i j => ∑ x, ∑ a, (F.imageCoeff x a : ℝ) * (V.N a j i : ℝ)

lemma regularImage_pos (i : κ) : 0 < F.regularImage i := by
  obtain ⟨x, hx⟩ := F.dominant i
  exact Finset.sum_pos' (fun z _ => mul_nonneg (U.fpdim_pos z).le (Nat.cast_nonneg _))
    ⟨x, Finset.mem_univ _, mul_pos (U.fpdim_pos x) (by exact_mod_cast hx)⟩

lemma dominantMatrix_pos (i j : κ) : 0 < F.dominantMatrix i j := by
  obtain ⟨a, ha⟩ := V.exists_left_multiplier i j
  obtain ⟨x, hx⟩ := F.dominant a
  apply Finset.sum_pos' (fun z _ => Finset.sum_nonneg (fun b _ =>
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
  refine ⟨x, Finset.mem_univ _, ?_⟩
  apply Finset.sum_pos' (fun b _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  exact ⟨a, Finset.mem_univ _, mul_pos (by exact_mod_cast hx) (by exact_mod_cast ha)⟩

lemma dominantMatrix_fpdim (i : κ) :
    ∑ j, F.dominantMatrix i j * V.fpdim j =
      (∑ x, U.fpdim x) * V.fpdim i := by
  have hreg (a : κ) : ∑ j, (V.N a j i : ℝ) * V.fpdim j =
      V.fpdim a * V.fpdim i := by
    simpa only [mul_comm] using V.regular_eigen a i
  calc
    _ = ∑ x, ∑ a, (F.imageCoeff x a : ℝ) *
        (∑ j, (V.N a j i : ℝ) * V.fpdim j) := by
      simp only [dominantMatrix, Finset.sum_mul, Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm]
      congr 1; ext x
      rw [Finset.sum_comm]
    _ = _ := by
      simp_rw [hreg, ← mul_assoc, ← Finset.sum_mul, F.fpdim_preserved]

lemma tensor_coeff_real (x w : ι) (i : κ) :
    ∑ z, (U.N x w z : ℝ) * (F.imageCoeff z i : ℝ) =
      ∑ a, ∑ b, (F.imageCoeff x a : ℝ) * (F.imageCoeff w b : ℝ) * (V.N a b i : ℝ) := by
  exact_mod_cast F.tensor_coeff x w i

lemma dominantMatrix_regularImage (i : κ) :
    ∑ j, F.dominantMatrix i j * F.regularImage j =
      (∑ x, U.fpdim x) * F.regularImage i := by
  have hx (x : ι) :
      ∑ j, (∑ a, (F.imageCoeff x a : ℝ) * (V.N a j i : ℝ)) *
        F.regularImage j = U.fpdim x * F.regularImage i := by
    calc
      _ = ∑ w, U.fpdim w * (∑ a, ∑ j,
          (F.imageCoeff x a : ℝ) * (F.imageCoeff w j : ℝ) * (V.N a j i : ℝ)) := by
        simp only [regularImage, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro w _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro a _
        apply Finset.sum_congr rfl; intro j _; ring
      _ = ∑ w, U.fpdim w * (∑ z,
          (U.N x w z : ℝ) * (F.imageCoeff z i : ℝ)) := by
        simp_rw [← F.tensor_coeff_real]
      _ = ∑ z, (∑ w, U.fpdim w * (U.N x w z : ℝ)) *
          (F.imageCoeff z i : ℝ) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro z _
        apply Finset.sum_congr rfl; intro w _; ring
      _ = _ := by
        simp_rw [U.regular_eigen, mul_assoc, ← Finset.mul_sum]
        rfl
  calc
    _ = ∑ x, ∑ j, (∑ a, (F.imageCoeff x a : ℝ) * (V.N a j i : ℝ)) *
        F.regularImage j := by
      simp only [dominantMatrix, Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = _ := by simp_rw [hx, ← Finset.sum_mul]

/-- The image of the source regular element has integer coefficients when
source FP dimensions are integers. -/
lemma regularImage_integer (hU : U.Integral) (i : κ) :
    ∃ n : ℤ, F.regularImage i = n := by
  choose n hn using hU
  refine ⟨∑ x, n x * (F.imageCoeff x i : ℤ), ?_⟩
  simp [regularImage, hn]

/-- Rationality is derived from dominance, tensor compatibility and source
integrality, using two positive eigenvectors of the dominant matrix. -/
lemma fpdim_rational (F : FusionMap U V) (hU : U.Integral) (i : κ) :
    ∃ q : ℚ, V.fpdim i = q := by
  letI : Nonempty κ := ⟨V.one⟩
  obtain ⟨c, hc, he⟩ := posMatrix_positive_eigenspace_one_dim
    F.dominantMatrix (∑ x, U.fpdim x) F.dominantMatrix_pos
    V.fpdim F.regularImage V.fpdim_pos F.regularImage_pos
    F.dominantMatrix_fpdim F.dominantMatrix_regularImage
  obtain ⟨ni, hni⟩ := F.regularImage_integer hU i
  obtain ⟨n1, hn1⟩ := F.regularImage_integer hU V.one
  have he1 := he V.one
  rw [V.fpdim_one, hn1] at he1
  have hn1r : (n1 : ℝ) ≠ 0 := by
    have := F.regularImage_pos V.one
    rw [hn1] at this
    exact ne_of_gt this
  refine ⟨(ni : ℚ) / (n1 : ℚ), ?_⟩
  rw [he i, hni]
  push_cast
  apply (eq_div_iff hn1r).mpr
  calc
    c * (ni : ℝ) * (n1 : ℝ) = (c * (n1 : ℝ)) * (ni : ℝ) := by ring
    _ = (ni : ℝ) := by rw [← he1, one_mul]

end FusionMap

/-- Lemma 3.1 at the based fusion-ring level. No rationality or
algebraic-integrality premise is supplied by the caller. The connection
of this based-ring statement to actual fusion categories remains separate. -/
theorem lemma3_1_dominant {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    {U : FusionBasis ι} {V : FusionBasis κ}
    (F : FusionMap U V) (hU : U.Integral) : V.Integral := by
  intro y
  exact real_rat_integral_eq_int (F.fpdim_rational hU y) (V.fpdim_isIntegral y)


/-- Any tensor functor into an integral fusion category has integral source:
its simple images have integer dimension as sums of integral target simples. -/
theorem FusionRuleMap.integral_of_target_integral
    {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    {U : FusionBasis ι} {V : FusionBasis κ}
    (F : FusionRuleMap U V) (hV : V.Integral) : U.Integral := by
  choose n hn using hV
  intro x
  refine ⟨∑ y, (F.imageCoeff x y : ℤ) * n y, ?_⟩
  rw [← F.fpdim_preserved x]
  simp [hn]

/-- Integrality is equivalent across a dominant tensor functor. This proves
the equivariantization step once the actual dominant forgetful functor is
constructed; no orbit or projective-representation classification is needed. -/
theorem FusionMap.integral_iff
    {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    {U : FusionBasis ι} {V : FusionBasis κ}
    (F : FusionMap U V) : U.Integral ↔ V.Integral :=
  ⟨lemma3_1_dominant F, F.toFusionRuleMap.integral_of_target_integral⟩

/-- **Lemma 3.1, second assertion** (equivariantization).
If `C` is integral, every FP dimension is a natural number. -/
theorem lemma3_1_equivariant_forward
    {ι : Type u} [Fintype ι] {C : FusionBasis ι}
    (hC : C.Integral) :
    ∀ x : ι, ∃ m : ℕ, C.fpdim x = m :=
  C.integral_iff_fpdim_nat.mp hC

/-- Integrality of `C` implies integrality of the scaled FP-dimension formula
`FPdim(Y) · [H : H_Y] · dim(π)` used for equivariant simples. -/
theorem equivariant_dim_integral
    {ι : Type u} [Fintype ι] {C : FusionBasis ι}
    (hC : C.Integral) (x : ι) (index dpi : ℕ) :
    ∃ m : ℕ, C.fpdim x * (index * dpi) = m := by
  obtain ⟨n, hn⟩ := C.integral_iff_fpdim_nat.mp hC x
  exact ⟨n * (index * dpi), by simp [hn]⟩

/-- Both directions of Lemma 3.1 for an equivariant dimension model. -/
theorem EquivariantDimensionModel.integral_iff
    {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    {C : FusionBasis ι} {E : FusionBasis κ}
    (M : EquivariantDimensionModel C E) : E.Integral ↔ C.Integral :=
  M.forget.integral_iff

/-- Algebraic-integrality packaging: FP dimensions are integral over `ℤ`
when they are PF eigenvalues of integer fusion matrices. -/
def IsAlgIntFPdim {ι : Type u} [Fintype ι] (B : FusionBasis ι) : Prop :=
  ∀ x : ι, IsIntegral ℤ (B.fpdim x)

/-- Under algebraic integrality and PF rationality, a fusion basis is integral. -/
theorem integral_of_algInt_rat {ι : Type u} [Fintype ι]
    {B : FusionBasis ι}
    (hRat : ∀ x : ι, ∃ q : ℚ, B.fpdim x = q)
    (hInt : IsAlgIntFPdim B) :
    B.Integral := by
  intro x
  exact real_rat_integral_eq_int (hRat x) (hInt x)

end Paper18
