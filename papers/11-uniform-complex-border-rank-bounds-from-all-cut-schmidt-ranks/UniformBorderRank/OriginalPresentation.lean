import UniformBorderRank.AnchoredBound
import UniformBorderRank.AnchorTensor
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Data.Matrix.Basis

/-! Proposition 2.2 for the original tensor.  The supports are ranges of
split injective coordinate maps and hence have dimension `r`; their tensor
product is identified with the normalized matrix coordinates. -/
noncomputable section
namespace UniformBorderRank
open Finset Module
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

variable {r : ℕ} {I J : Type*} [Fintype I] [Fintype J]

/-- The left retained support, with its actual inclusion in anchor coefficients. -/
def anchorLeftSupport (X : I → Fin r → ℂ) : Submodule ℂ (I → ℂ) :=
  LinearMap.range (Matrix.mulVecLin X)

/-- The right retained support, with its actual inclusion in anchor coefficients. -/
def anchorRightSupport (Y : Fin r → J → ℂ) : Submodule ℂ (J → ℂ) :=
  LinearMap.range (Matrix.vecMulLinear Y)

lemma anchorLeft_injective (X : I → Fin r → ℂ) (L : Fin r → I → ℂ)
    (hLX : ∀ i j, ∑ a, L i a * X a j = if i = j then 1 else 0) :
    Function.Injective (Matrix.mulVecLin X) := by
  classical
  have hleft : Function.LeftInverse (Matrix.mulVecLin L) (Matrix.mulVecLin X) := by
    intro v
    funext i
    change (∑ a, L i a * ∑ j, X a j * v j) = v i
    simp only [mul_sum]
    rw [sum_comm]
    simp only [← mul_assoc, ← sum_mul, hLX]
    simp [ite_mul]
  exact hleft.injective

lemma anchorRight_injective (Y : Fin r → J → ℂ) (R : J → Fin r → ℂ)
    (hYR : ∀ i j, ∑ b, Y i b * R b j = if i = j then 1 else 0) :
    Function.Injective (Matrix.vecMulLinear Y) := by
  classical
  have hleft : Function.LeftInverse (Matrix.vecMulLinear R) (Matrix.vecMulLinear Y) := by
    intro v
    funext i
    change (∑ b, (∑ j, v j * Y j b) * R b i) = v i
    simp only [sum_mul]
    rw [sum_comm]
    simp only [mul_assoc, ← mul_sum, hYR]
    simp [mul_ite]
  exact hleft.injective

lemma anchorLeftSupport_finrank (X : I → Fin r → ℂ) (L : Fin r → I → ℂ)
    (hLX : ∀ i j, ∑ a, L i a * X a j = if i = j then 1 else 0) :
    Module.finrank ℂ (anchorLeftSupport X) = r := by
  rw [anchorLeftSupport, LinearMap.finrank_range_of_inj (anchorLeft_injective X L hLX)]
  simp

lemma anchorRightSupport_finrank (Y : Fin r → J → ℂ) (R : J → Fin r → ℂ)
    (hYR : ∀ i j, ∑ b, Y i b * R b j = if i = j then 1 else 0) :
    Module.finrank ℂ (anchorRightSupport Y) = r := by
  rw [anchorRightSupport, LinearMap.finrank_range_of_inj (anchorRight_injective Y R hYR)]
  simp

/-- A canonical matrix/tensor identification, sending the `(i,j)` matrix
coordinate to the tensor product of the `i` and `j` coordinate vectors. -/
def matrixTensorEquiv (r : ℕ) :
    EndMat r ≃ₗ[ℂ] (Fin r → ℂ) ⊗[ℂ] (Fin r → ℂ) :=
  (Matrix.transposeLinearEquiv (Fin r) (Fin r) ℂ ℂ).trans
    (TensorProduct.piScalarRight ℂ ℂ (Fin r → ℂ) (Fin r)).symm

lemma matrixTensorEquiv_single (i j : Fin r) :
    matrixTensorEquiv r (Matrix.single i j 1) =
      (Pi.single i 1) ⊗ₜ[ℂ] (Pi.single j 1) := by
  classical
  change (TensorProduct.piScalarRight ℂ ℂ (Fin r → ℂ) (Fin r)).symm
    (Matrix.of.symm (Matrix.transpose (Matrix.single i j (1 : ℂ)))) = _
  rw [Matrix.transpose_single, Matrix.of_symm_single, TensorProduct.piScalarRight_symm_single]

/-- The actual support coordinate equivalences coming from split injections. -/
def anchorLeftEquiv (X : I → Fin r → ℂ) (L : Fin r → I → ℂ)
    (hLX : ∀ i j, ∑ a, L i a * X a j = if i = j then 1 else 0) :
    (Fin r → ℂ) ≃ₗ[ℂ] anchorLeftSupport X :=
  LinearEquiv.ofInjective (Matrix.mulVecLin X) (anchorLeft_injective X L hLX)

def anchorRightEquiv (Y : Fin r → J → ℂ) (R : J → Fin r → ℂ)
    (hYR : ∀ i j, ∑ b, Y i b * R b j = if i = j then 1 else 0) :
    (Fin r → ℂ) ≃ₗ[ℂ] anchorRightSupport Y :=
  LinearEquiv.ofInjective (Matrix.vecMulLinear Y) (anchorRight_injective Y R hYR)

/-- The paper's identification `Theta : End(C^r) ≃ U ⊗ W`, with actual
support subspaces of the original retained anchor spaces. -/
def originalAnchorTheta (X : I → Fin r → ℂ) (Y : Fin r → J → ℂ)
    (L : Fin r → I → ℂ) (R : J → Fin r → ℂ)
    (hLX : ∀ i j, ∑ a, L i a * X a j = if i = j then 1 else 0)
    (hYR : ∀ i j, ∑ b, Y i b * R b j = if i = j then 1 else 0) :
    EndMat r ≃ₗ[ℂ] (anchorLeftSupport X) ⊗[ℂ] (anchorRightSupport Y) :=
  (matrixTensorEquiv r).trans
    (TensorProduct.congr (anchorLeftEquiv X L hLX) (anchorRightEquiv Y R hYR))

lemma originalAnchorTheta_single (X : I → Fin r → ℂ) (Y : Fin r → J → ℂ)
    (L : Fin r → I → ℂ) (R : J → Fin r → ℂ)
    (hLX : ∀ i j, ∑ a, L i a * X a j = if i = j then 1 else 0)
    (hYR : ∀ i j, ∑ b, Y i b * R b j = if i = j then 1 else 0)
    (i j : Fin r) :
    originalAnchorTheta X Y L R hLX hYR (Matrix.single i j 1) =
      anchorLeftEquiv X L hLX (Pi.single i 1) ⊗ₜ[ℂ]
        anchorRightEquiv Y R hYR (Pi.single j 1) := by
  simp [originalAnchorTheta, matrixTensorEquiv_single, TensorProduct.congr_tmul]

/-- The support identification has exactly the explicit double-sum expansion
in Proposition 2.2, rather than being an unspecified equivalence. -/
theorem originalAnchorTheta_expansion (X : I → Fin r → ℂ) (Y : Fin r → J → ℂ)
    (L : Fin r → I → ℂ) (R : J → Fin r → ℂ)
    (hLX : ∀ i j, ∑ a, L i a * X a j = if i = j then 1 else 0)
    (hYR : ∀ i j, ∑ b, Y i b * R b j = if i = j then 1 else 0) (Z : EndMat r) :
    originalAnchorTheta X Y L R hLX hYR Z =
      ∑ i, ∑ j, Z i j •
        (anchorLeftEquiv X L hLX (Pi.single i 1) ⊗ₜ[ℂ]
          anchorRightEquiv Y R hYR (Pi.single j 1)) := by
  classical
  have he : Z = ∑ i, ∑ j, Z i j • (Matrix.single i j (1 : ℂ)) := by
    simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using Matrix.matrix_eq_sum_single Z
  calc
    _ = originalAnchorTheta X Y L R hLX hYR
        (∑ i, ∑ j, Z i j • (Matrix.single i j (1 : ℂ))) := congrArg _ he
    _ = _ := by simp only [map_sum, map_smul, originalAnchorTheta_single]

/-- Coefficients of an actual tensor in two retained support subspaces. -/
def supportTensorCoefficients (U : Submodule ℂ (I → ℂ)) (W : Submodule ℂ (J → ℂ)) :
    U ⊗[ℂ] W →ₗ[ℂ] (I → J → ℂ) :=
  TensorProduct.lift {
    toFun := fun u => {
      toFun := fun w => fun a b => u.val a * w.val b
      map_add' := by intro w z; ext a b; simp [mul_add]
      map_smul' := by intro c w; ext a b; simp [mul_left_comm, mul_assoc] }
    map_add' := by intro u v; ext w a b; simp [add_mul]
    map_smul' := by intro c u; ext w a b; simp [mul_assoc] }

@[simp] lemma supportTensorCoefficients_tmul
    (U : Submodule ℂ (I → ℂ)) (W : Submodule ℂ (J → ℂ))
    (u : U) (w : W) (a : I) (b : J) :
    supportTensorCoefficients U W (u ⊗ₜ[ℂ] w) a b = u.val a * w.val b := by
  simp [supportTensorCoefficients]

lemma anchorLeftEquiv_basis_val (X : I → Fin r → ℂ) (L : Fin r → I → ℂ)
    (hLX : ∀ i j, ∑ a, L i a * X a j = if i = j then 1 else 0) (i : Fin r) (a : I) :
    (anchorLeftEquiv X L hLX (Pi.single i 1)).val a = X a i := by
  change (∑ j, X a j * (Pi.single i (1 : ℂ) : Fin r → ℂ) j) = X a i
  simp [Pi.single_apply]

lemma anchorRightEquiv_basis_val (Y : Fin r → J → ℂ) (R : J → Fin r → ℂ)
    (hYR : ∀ i j, ∑ b, Y i b * R b j = if i = j then 1 else 0) (j : Fin r) (b : J) :
    (anchorRightEquiv Y R hYR (Pi.single j 1)).val b = Y j b := by
  change (∑ i, (Pi.single j (1 : ℂ) : Fin r → ℂ) i * Y i b) = Y j b
  simp [Pi.single_apply]

/-- The tensor-product identification embeds into the original anchor
coefficient spaces by the actual two support matrices. -/
theorem originalAnchorTheta_coefficients (X : I → Fin r → ℂ) (Y : Fin r → J → ℂ)
    (L : Fin r → I → ℂ) (R : J → Fin r → ℂ)
    (hLX : ∀ i j, ∑ a, L i a * X a j = if i = j then 1 else 0)
    (hYR : ∀ i j, ∑ b, Y i b * R b j = if i = j then 1 else 0)
    (Z : EndMat r) (a : I) (b : J) :
    supportTensorCoefficients (anchorLeftSupport X) (anchorRightSupport Y)
      (originalAnchorTheta X Y L R hLX hYR Z) a b =
        ∑ i, ∑ j, X a i * Z i j * Y j b := by
  rw [originalAnchorTheta_expansion]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    supportTensorCoefficients_tmul, anchorLeftEquiv_basis_val, anchorRightEquiv_basis_val]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring

/-- Constructed data for the original anchored matrix-product form.  The
normalizers, support dimensions, and reconstruction equalities are proved
fields, not additional hypotheses on the original tensor. -/
structure OriginalAnchoredPresentation {N : ℕ} (d : Fin N → ℕ) (T : Coeffs d) (r : ℕ) where
  L : Finset (Fin N)
  R : Finset (Fin N)
  q : FiniteSites.Covectors d
  left_nonempty : L.Nonempty
  right_nonempty : R.Nonempty
  disjoint : Disjoint L R
  left_card : L.card ≤ r - 1
  right_card : R.card ≤ r - 1
  X : FiniteSites.RetainedIndex d L → Fin r → ℂ
  Y : Fin r → FiniteSites.RetainedIndex d R → ℂ
  Lnorm : Fin r → FiniteSites.RetainedIndex d L → ℂ
  Rnorm : FiniteSites.RetainedIndex d R → Fin r → ℂ
  left_normalized : ∀ i j, ∑ a, Lnorm i a * X a j = if i = j then 1 else 0
  right_normalized : ∀ i j, ∑ c, Y i c * Rnorm c j = if i = j then 1 else 0
  left_support_dimension : Module.finrank ℂ (anchorLeftSupport X) = r
  right_support_dimension : Module.finrank ℂ (anchorRightSupport Y) = r
  coefficient_reconstruction : ∀ a c u, anchorTensor d T L R a c u =
    ∑ i, ∑ j, X a i * normalizedCoefficients (anchorTensor d T L R) Lnorm Rnorm u i j * Y j c
  core : anchorMultilinear (anchorTensor d T L R) Lnorm Rnorm
    (anchorOutsideBase d L R q) = 1
  cut_factorization : ∀ x S,
    anchorMultilinear (anchorTensor d T L R) Lnorm Rnorm x =
      anchorMultilinear (anchorTensor d T L R) Lnorm Rnorm (mixArguments x (anchorOutsideBase d L R q) S) *
        anchorMultilinear (anchorTensor d T L R) Lnorm Rnorm (mixArguments (anchorOutsideBase d L R q) x S)
  site_base : ∀ i, (anchorMultilinear (anchorTensor d T L R) Lnorm Rnorm).toLinearMap
    (anchorOutsideBase d L R q) i (anchorOutsideBase d L R q i) = 1
  cross_commute : ∀ i j, i ≠ j →
    ∀ (x : Fin (anchorOutsideDim d L R i) → ℂ) (y : Fin (anchorOutsideDim d L R j) → ℂ),
    (anchorMultilinear (anchorTensor d T L R) Lnorm Rnorm).toLinearMap (anchorOutsideBase d L R q) i x *
      (anchorMultilinear (anchorTensor d T L R) Lnorm Rnorm).toLinearMap (anchorOutsideBase d L R q) j y =
    (anchorMultilinear (anchorTensor d T L R) Lnorm Rnorm).toLinearMap (anchorOutsideBase d L R q) j y *
      (anchorMultilinear (anchorTensor d T L R) Lnorm Rnorm).toLinearMap (anchorOutsideBase d L R q) i x
  any_order : ∀ (x : ∀ i, Fin (anchorOutsideDim d L R i) → ℂ) (order : List (Fin N)),
    order.Nodup → order.toFinset = univ →
    anchorMultilinear (anchorTensor d T L R) Lnorm Rnorm x =
      (order.map (fun i =>
        (anchorMultilinear (anchorTensor d T L R) Lnorm Rnorm).toLinearMap
          (anchorOutsideBase d L R q) i (x i))).prod

/-- Proposition 2.2, with all data and all normalization/reconstruction
properties constructed from the original maximal all-cut Schmidt rank. -/
theorem exists_original_anchored_presentation {N : ℕ} (d : Fin N → ℕ) (hN : 2 ≤ N)
    (T : Coeffs d) (hT : T ≠ 0) (hr : 2 ≤ maxSchmidtRank d T) :
    Nonempty (OriginalAnchoredPresentation d T (maxSchmidtRank d T)) := by
  classical
  let r := maxSchmidtRank d T
  have hcut : allCutLe d T r := allCutLe_of_maxSchmidtRank_le T r (le_refl r)
  obtain ⟨L, R, q, hL, hR, hLR, hcL, hcR, hcore⟩ :=
    exists_original_anchor_core d hN T hT hr
  let H := anchorTensor d T L R
  let b := anchorOutsideBase d L R q
  let w (u : ∀ i, Fin (anchorOutsideDim d L R i)) := ∏ i, b i (u i)
  let M (a : FiniteSites.RetainedIndex d L) (c : FiniteSites.RetainedIndex d R) :=
    ∑ u, H a c u * w u
  have hM : Module.finrank ℂ (Submodule.span ℂ (Set.range M)) = r := by
    have hm : M = anchorContract d T L R q := by
      funext a c
      exact anchorTensor_core_eq d T L R hLR q a c
    rw [hm]
    exact hcore
  have hc : ∀ S, Module.finrank ℂ (Submodule.span ℂ (Set.range (anchoredCut H S))) ≤ r := by
    intro S
    exact anchorTensorCut_rank_le d T L R hL hR hLR r hcut S
  obtain ⟨X, Y, Ln, Rn, hXY, hLM, hYR⟩ := exists_normalized_rank_factorization M r hM
  have hMR (a : FiniteSites.RetainedIndex d L) (i : Fin r) :
      (∑ c, M a c * Rn c i) = X a i := by
    simp only [hXY, sum_mul]
    rw [sum_comm]
    simp only [mul_assoc, ← mul_sum, hYR, mul_ite, mul_one, mul_zero]
    simp
  have hLX (i j : Fin r) : (∑ a, Ln i a * X a j) = if i = j then 1 else 0 := by
    calc
      _ = ∑ a, Ln i a * (∑ c, M a c * Rn c j) := by simp only [hMR]
      _ = ∑ c, (∑ a, Ln i a * M a c) * Rn c j := by
        simp only [mul_sum, sum_mul, mul_assoc]
        rw [sum_comm]
      _ = _ := by simp only [hLM, hYR]
  let Phi := anchorMultilinear H Ln Rn
  have hPhi : Phi b = 1 := by
    apply anchorMultilinear_core
    intro i j
    change (∑ a, ∑ c, Ln i a * M a c * Rn c j) = _
    rw [sum_comm]
    simp only [← sum_mul, hLM, hYR]
  have hblocks := anchorMultilinear_cut_rank H Ln Rn b hc
  have hleft (a : FiniteSites.RetainedIndex d L) (i : Fin r) :
      (∑ c, ∑ u, H a c u * w u * Rn c i) = X a i := by
    simpa only [M, sum_mul] using hMR a i
  have hright (c : FiniteSites.RetainedIndex d R) (j : Fin r) :
      (∑ a, ∑ u, Ln j a * H a c u * w u) = Y j c := by
    simpa only [M, mul_sum, mul_assoc] using hLM j c
  have hrow := (boundary_row_rank_le_anchoredCut_empty H).trans (hc ∅)
  have hcol := (boundary_column_rank_le_anchoredCut_univ H).trans (hc univ)
  have hrec := anchored_coefficient_reconstruction H w r X Y Ln Rn
    hleft hright hLX hYR hrow hcol
  have hform := normalized_matrix_product_form Phi b hPhi hblocks
  refine ⟨{
    L := L, R := R, q := q, left_nonempty := hL, right_nonempty := hR,
    disjoint := hLR, left_card := hcL, right_card := hcR,
    X := X, Y := Y, Lnorm := Ln, Rnorm := Rn,
    left_normalized := hLX, right_normalized := hYR,
    left_support_dimension := anchorLeftSupport_finrank X Ln hLX,
    right_support_dimension := anchorRightSupport_finrank Y Rn hYR,
    coefficient_reconstruction := hrec,
    core := hPhi, cut_factorization := normalized_cut_identity Phi b hPhi hblocks,
    site_base := hform.1, cross_commute := hform.2.1,
    any_order := hform.2.2 }⟩

namespace OriginalAnchoredPresentation

variable {N : ℕ} {d : Fin N → ℕ} {T : Coeffs d} {r : ℕ}

/-- The actual normalized multilinear map, not an additional chosen function. -/
def Phi (P : OriginalAnchoredPresentation d T r) :=
  anchorMultilinear (anchorTensor d T P.L P.R) P.Lnorm P.Rnorm

/-- The actual remaining-site base covectors. -/
def base (P : OriginalAnchoredPresentation d T r) := anchorOutsideBase d P.L P.R P.q

/-- The linear map attached to an actual local remaining-site variable. -/
def siteMap (P : OriginalAnchoredPresentation d T r) (i : Fin N) := P.Phi.toLinearMap P.base i

/-- The paper's support-tensor identification. -/
def Theta (P : OriginalAnchoredPresentation d T r) :
    EndMat r ≃ₗ[ℂ] (anchorLeftSupport P.X) ⊗[ℂ] (anchorRightSupport P.Y) :=
  originalAnchorTheta P.X P.Y P.Lnorm P.Rnorm P.left_normalized P.right_normalized

/-- The explicit original support bases in the identification `Theta`. -/
def leftBasis (P : OriginalAnchoredPresentation d T r) :
    Basis (Fin r) ℂ (anchorLeftSupport P.X) :=
  (Pi.basisFun ℂ (Fin r)).map (anchorLeftEquiv P.X P.Lnorm P.left_normalized)

def rightBasis (P : OriginalAnchoredPresentation d T r) :
    Basis (Fin r) ℂ (anchorRightSupport P.Y) :=
  (Pi.basisFun ℂ (Fin r)).map (anchorRightEquiv P.Y P.Rnorm P.right_normalized)

/-- `Theta` uses precisely the double sum of the two actual support bases. -/
theorem Theta_expansion (P : OriginalAnchoredPresentation d T r) (Z : EndMat r) :
    P.Theta Z = ∑ i, ∑ j, Z i j • (P.leftBasis i ⊗ₜ[ℂ] P.rightBasis j) := by
  simpa [Theta, leftBasis, rightBasis, Pi.basisFun_apply] using
    originalAnchorTheta_expansion P.X P.Y P.Lnorm P.Rnorm
      P.left_normalized P.right_normalized Z

/-- Source equation (6) over exactly the complementary sites `C`. Dummy
anchor positions are held at their base covectors, and are omitted from the
product, including the empty-complement case. -/
theorem outside_any_order_product (P : OriginalAnchoredPresentation d T r)
    (x : ∀ i, Fin (anchorOutsideDim d P.L P.R i) → ℂ)
    (hx : ∀ i ∈ P.L ∪ P.R, x i = P.base i)
    (order : List (Fin N)) (hn : order.Nodup)
    (hcover : order.toFinset = (P.L ∪ P.R)ᶜ) :
    P.Phi x = (order.map (fun i => P.siteMap i (x i))).prod := by
  have hh := normalized_any_order_product P.Phi P.base P.core P.cut_factorization x order hn
  have he : mixArguments x P.base order.toFinset = x := by
    funext i
    rw [hcover]
    change (if i ∈ (P.L ∪ P.R)ᶜ then x i else P.base i) = x i
    by_cases hi : i ∈ P.L ∪ P.R
    · rw [if_neg (fun hc => (mem_compl.mp hc) hi), ← hx i hi]
    · rw [if_pos (mem_compl.mpr hi)]
  rw [he] at hh
  exact hh

/-- The actual original coefficient array is reconstructed through the two
retained supports and the normalized matrix coefficient. -/
theorem original_coefficient_reconstruction (P : OriginalAnchoredPresentation d T r)
    (w : FiniteSites.TensorIndex d) :
    T w = ∑ i, ∑ j, P.X (FiniteSites.restrictIndex P.L w) i *
      normalizedCoefficients (anchorTensor d T P.L P.R) P.Lnorm P.Rnorm
        (outsideAnchorIndex d P.L P.R w) i j * P.Y j (FiniteSites.restrictIndex P.R w) := by
  simpa only [anchorTensor, assemble_outsideAnchorIndex] using
    P.coefficient_reconstruction (FiniteSites.restrictIndex P.L w)
      (FiniteSites.restrictIndex P.R w) (outsideAnchorIndex d P.L P.R w)

/-- Coefficients of `Theta` in the original anchor spaces. -/
theorem Theta_coefficients (P : OriginalAnchoredPresentation d T r) (Z : EndMat r)
    (a : FiniteSites.RetainedIndex d P.L) (c : FiniteSites.RetainedIndex d P.R) :
    supportTensorCoefficients (anchorLeftSupport P.X) (anchorRightSupport P.Y)
      (P.Theta Z) a c = ∑ i, ∑ j, P.X a i * Z i j * P.Y j c :=
  originalAnchorTheta_coefficients P.X P.Y P.Lnorm P.Rnorm
    P.left_normalized P.right_normalized Z a c

/-- Each original remaining-coordinate tensor belongs to the actual tensor
product of the two `r`-dimensional retained supports. -/
theorem coefficient_in_supports (P : OriginalAnchoredPresentation d T r)
    (u : FiniteSites.TensorIndex (anchorOutsideDim d P.L P.R)) :
    supportTensorCoefficients (anchorLeftSupport P.X) (anchorRightSupport P.Y)
      (P.Theta (normalizedCoefficients (anchorTensor d T P.L P.R) P.Lnorm P.Rnorm u)) =
        fun a c => anchorTensor d T P.L P.R a c u := by
  funext a c
  rw [P.Theta_coefficients]
  exact (P.coefficient_reconstruction a c u).symm

/-- The matrix-valued multilinear map is precisely `Theta` coordinates of
the actual product contractions of the original tensor. -/
theorem contraction_in_supports (P : OriginalAnchoredPresentation d T r)
    (x : ∀ i, Fin (anchorOutsideDim d P.L P.R i) → ℂ)
    (a : FiniteSites.RetainedIndex d P.L) (c : FiniteSites.RetainedIndex d P.R) :
    supportTensorCoefficients (anchorLeftSupport P.X) (anchorRightSupport P.Y)
      (P.Theta (P.Phi x)) a c =
        ∑ u, anchorTensor d T P.L P.R a c u * ∏ i, x i (u i) := by
  rw [P.Theta_coefficients]
  simp only [Phi, anchorMultilinear, coefficientMultilinear_apply]
  calc
    _ = ∑ u, (∑ i, ∑ j, P.X a i *
        normalizedCoefficients (anchorTensor d T P.L P.R) P.Lnorm P.Rnorm u i j * P.Y j c) *
          ∏ k, x k (u k) := by
      simp only [mul_sum, sum_mul]
      symm
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro u _
      ring
    _ = _ := by
      apply sum_congr rfl
      intro u _
      rw [← P.coefficient_reconstruction]

end OriginalAnchoredPresentation
end UniformBorderRank
