import Paper28.FoldingDifferential
import Paper28.DimensionReduction
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Determinant

/-! The genuine n-dimensional Jacobian, sqrt(det(D*D)), and the passage
from a nonradial two-plane to the full n-plane. The only explicit external
input is the classical multi-block Fischer determinant inequality, specialized
to one two-by-two principal block and singleton blocks. See Pate (1997),
DOI 10.1016/S0024-3795(96)00044-4, and Blekherman et al., IMRN (2023),
Corollary 4.5. It is a universal PSD-matrix inequality, not a folding or
current estimate. No new axiom is declared. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open scoped InnerProductSpace
open WithLp

/-- Exact disclosed classical Fischer input for a two-point block and all
remaining singleton blocks. The product over an empty complement is one. -/
def FischerInput : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (a : Fin 2 ↪ Fin n),
    M.PosSemidef → M.det ≤ (M.submatrix a a).det *
      ∏ i ∈ Finset.univ.filter (fun i => ∀ j : Fin 2, a j ≠ i), M i i

section Generic
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- The original basis-independent linear Jacobian, with domain E. -/
irreducible_def linearJacobian (D : E →ₗ[ℝ] F) : ℝ :=
  Real.sqrt (LinearMap.det (D.adjoint.comp D))

theorem gram_eq_adjoint_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : E →ₗ[ℝ] F) (b : OrthonormalBasis ι ℝ E) :
    Matrix.gram ℝ (fun i => D (b i)) =
      LinearMap.toMatrix b.toBasis b.toBasis (D.adjoint.comp D) := by
  ext i j
  simp only [Matrix.gram_apply, LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, LinearMap.comp_apply, LinearMap.adjoint_inner_right]

theorem linearJacobian_eq_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : E →ₗ[ℝ] F) (b : OrthonormalBasis ι ℝ E) :
    linearJacobian D = Real.sqrt (Matrix.gram ℝ (fun i => D (b i))).det := by
  rw [gram_eq_adjoint_matrix, LinearMap.det_toMatrix, linearJacobian_def]

/-- The first two indices in an n-element index type. -/
def twoFrameEmbedding {n : ℕ} (hn : 2 ≤ n) : Fin 2 ↪ Fin n where
  toFun i := ⟨i.val, lt_of_lt_of_le i.isLt hn⟩
  inj' i j h := Fin.ext (congrArg (fun x : Fin n => x.val) h)

/-- Extend any two orthonormal vectors to an actual orthonormal basis,
retaining their indices. -/
theorem extend_two_frame (e : Fin 2 → E) (he : Orthonormal ℝ e)
    (hn : 2 ≤ Module.finrank ℝ E) :
    ∃ b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E,
      ∀ i, b (twoFrameEmbedding hn i) = e i := by
  classical
  let w : Fin (Module.finrank ℝ E) → E :=
    fun i => if hi : i.val < 2 then e ⟨i.val, hi⟩ else 0
  let s : Set (Fin (Module.finrank ℝ E)) := {i | i.val < 2}
  let f : s → Fin 2 := fun i => ⟨i.val.val, i.property⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply Fin.ext
    exact congrArg (fun x : Fin 2 => x.val) hij
  have hw : Orthonormal ℝ (s.restrict w) := by
    convert he.comp f hf using 1
    ext i
    change (if hi : i.val.val < 2 then e ⟨i.val.val, hi⟩ else 0) = e ⟨i.val.val, i.property⟩
    rw [dif_pos (show i.val.val < 2 from i.property)]
  obtain ⟨b, hb⟩ := hw.exists_orthonormalBasis_extension_of_card_eq (by simp)
  refine ⟨b, fun i => ?_⟩
  rw [hb (twoFrameEmbedding hn i) (show twoFrameEmbedding hn i ∈ s from i.isLt)]
  simp [w, twoFrameEmbedding, i.isLt]

/-- Classical Fischer compression, instantiated with the actual Gram matrix
of a contraction. All diagonal and complement-product bounds are proved here. -/
theorem linearJacobian_le_two_frame (hFischer : FischerInput) (D : E →ₗ[ℝ] F)
    (hD : ∀ v, ‖D v‖ ≤ ‖v‖) (e : Fin 2 → E) (he : Orthonormal ℝ e)
    (hn : 2 ≤ Module.finrank ℝ E) :
    linearJacobian D ≤ Real.sqrt (Matrix.gram ℝ (fun i => D (e i))).det := by
  classical
  obtain ⟨b, hb⟩ := extend_two_frame e he hn
  let M := Matrix.gram ℝ (fun i => D (b i))
  let a := twoFrameEmbedding hn
  have hM : M.PosSemidef := Matrix.posSemidef_gram _ _
  have hminor : M.submatrix a a = Matrix.gram ℝ (fun i => D (e i)) := by
    ext i j
    simp [M, a, Matrix.submatrix, hb]
  have hdiag (i : Fin (Module.finrank ℝ E)) : 0 ≤ M i i ∧ M i i ≤ 1 := by
    have hnrm := hD (b i)
    rw [b.orthonormal.norm_eq_one i] at hnrm
    change 0 ≤ ⟪D (b i), D (b i)⟫_ℝ ∧ ⟪D (b i), D (b i)⟫_ℝ ≤ 1
    rw [real_inner_self_eq_norm_sq]
    constructor
    · positivity
    · nlinarith [norm_nonneg (D (b i))]
  have hprod : (∏ i ∈ Finset.univ.filter (fun i => ∀ j : Fin 2, a j ≠ i), M i i) ≤ 1 :=
    Finset.prod_le_one (fun i _ => (hdiag i).1) (fun i _ => (hdiag i).2)
  have hminorNonneg : 0 ≤ (M.submatrix a a).det := (hM.submatrix a).det_nonneg
  have hdet := (hFischer _ M a hM).trans
    (show (M.submatrix a a).det * _ ≤ (M.submatrix a a).det by
      nlinarith [mul_nonneg hminorNonneg (sub_nonneg.mpr hprod)])
  rw [linearJacobian_eq_gram D b]
  change Real.sqrt M.det ≤ _
  rw [← hminor]
  exact Real.sqrt_le_sqrt hdet

omit [FiniteDimensional ℝ F] in
/-- The same intrinsic Jacobian through the finite-dimensional image.
This avoids assuming finite dimension of the ambient target space. -/
def nJacobian (D : E →ₗ[ℝ] F) : ℝ := linearJacobian D.rangeRestrict

omit [FiniteDimensional ℝ F] in
theorem nJacobian_eq_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : E →ₗ[ℝ] F) (b : OrthonormalBasis ι ℝ E) :
    nJacobian D = Real.sqrt (Matrix.gram ℝ (fun i => D (b i))).det := by
  exact linearJacobian_eq_gram D.rangeRestrict b

theorem nJacobian_eq_linearJacobian (D : E →ₗ[ℝ] F) : nJacobian D = linearJacobian D := by
  rw [nJacobian_eq_gram D (stdOrthonormalBasis ℝ E), linearJacobian_eq_gram D (stdOrthonormalBasis ℝ E)]

omit [FiniteDimensional ℝ F] in
theorem nJacobian_le_two_frame (hFischer : FischerInput) (D : E →ₗ[ℝ] F)
    (hD : ∀ v, ‖D v‖ ≤ ‖v‖) (e : Fin 2 → E) (he : Orthonormal ℝ e)
    (hn : 2 ≤ Module.finrank ℝ E) :
    nJacobian D ≤ Real.sqrt (Matrix.gram ℝ (fun i => D (e i))).det := by
  exact linearJacobian_le_two_frame hFischer D.rangeRestrict hD e he hn

/-- The n-Jacobian of a linear isometric embedding is exactly one. -/
theorem linearJacobian_of_isometry (D : E →ₗ[ℝ] F) (hD : ∀ v, ‖D v‖ = ‖v‖) :
    linearJacobian D = 1 := by
  classical
  let f : E →ₗᵢ[ℝ] F := { toLinearMap := D, norm_map' := hD }
  let b := stdOrthonormalBasis ℝ E
  have hM : Matrix.gram ℝ (fun i => D (b i)) = 1 := by
    ext i j
    change ⟪f (b i), f (b j)⟫_ℝ = _
    rw [f.inner_map_map]
    exact orthonormal_iff_ite.mp b.orthonormal i j
  rw [linearJacobian_eq_gram D b, hM, Matrix.det_one, Real.sqrt_one]

/-- Zero maps have zero Jacobian in positive domain dimension. -/
theorem linearJacobian_zero (hE : 0 < Module.finrank ℝ E) :
    linearJacobian (0 : E →ₗ[ℝ] F) = 0 := by
  classical
  let b := stdOrthonormalBasis ℝ E
  haveI : Nonempty (Fin (Module.finrank ℝ E)) := ⟨⟨0, hE⟩⟩
  rw [linearJacobian_eq_gram (0 : E →ₗ[ℝ] F) b]
  change Real.sqrt (Matrix.gram ℝ (0 : Fin (Module.finrank ℝ E) → F)).det = 0
  rw [Matrix.gram_zero, Matrix.det_zero inferInstance, Real.sqrt_zero]

end Generic

section Frames
variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ U]

/-- Gram congruence under an arbitrary real coefficient matrix. -/
theorem gram_linear_combinations {n : ℕ} (v : Fin n → V) (C : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.gram ℝ (fun j => ∑ i, C i j • v i) = C.transpose * Matrix.gram ℝ v * C := by
  ext j k
  simp only [Matrix.gram_apply, Matrix.mul_apply, Matrix.transpose_apply, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- A transparent finite-sum linearity condition, used to avoid choosing
unnecessary target-space adjoints. -/
def PreservesFrameSums (f : U → V) : Prop :=
  ∀ (v : Fin (Module.finrank ℝ U) → U) (a : Fin (Module.finrank ℝ U) → ℝ),
    f (∑ i, a i • v i) = ∑ i, a i • f (v i)

/-- Genuine full-dimensional Gram Jacobian in a canonical orthonormal basis.
The next theorem proves independence of that basis. -/
def frameJacobian (f : U → V) : ℝ :=
  Real.sqrt (Matrix.gram ℝ (fun i => f (stdOrthonormalBasis ℝ U i))).det

theorem frameJacobian_eq_gram (f : U → V) (hf : PreservesFrameSums f)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ U)) ℝ U) :
    frameJacobian f = Real.sqrt (Matrix.gram ℝ (fun i => f (b i))).det := by
  classical
  let c := stdOrthonormalBasis ℝ U
  let C := c.toBasis.toMatrix b
  have hv (j) : (∑ i, C i j • c i) = b j := by
    exact c.toBasis.sum_repr (b j)
  have heq : (fun j => f (b j)) = fun j => ∑ i, C i j • f (c i) := by
    funext j
    rw [← hf (fun i => c i) (fun i => C i j), hv]
  have hdet : (Matrix.gram ℝ (fun i => f (b i))).det =
      (Matrix.gram ℝ (fun i => f (c i))).det := by
    rw [heq, gram_linear_combinations, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    have hsign : C.det = 1 ∨ C.det = -1 := c.det_to_matrix_orthonormalBasis_real b
    rcases hsign with h | h <;> rw [h] <;> ring
  exact congrArg Real.sqrt hdet.symm

theorem frameJacobian_le_two_frame (hFischer : FischerInput) (f : U → V)
    (hf : PreservesFrameSums f) (hnorm : ∀ v, ‖f v‖ ≤ ‖v‖)
    (e : Fin 2 → U) (he : Orthonormal ℝ e) (hn : 2 ≤ Module.finrank ℝ U) :
    frameJacobian f ≤ Real.sqrt (Matrix.gram ℝ (fun i => f (e i))).det := by
  classical
  obtain ⟨b, hb⟩ := extend_two_frame e he hn
  let M := Matrix.gram ℝ (fun i => f (b i))
  let a := twoFrameEmbedding hn
  have hM : M.PosSemidef := Matrix.posSemidef_gram _ _
  have hminor : M.submatrix a a = Matrix.gram ℝ (fun i => f (e i)) := by
    ext i j
    simp [M, a, Matrix.submatrix, hb]
  have hdiag (i : Fin (Module.finrank ℝ U)) : 0 ≤ M i i ∧ M i i ≤ 1 := by
    have hnrm := hnorm (b i)
    rw [b.orthonormal.norm_eq_one i] at hnrm
    change 0 ≤ ⟪f (b i), f (b i)⟫_ℝ ∧ ⟪f (b i), f (b i)⟫_ℝ ≤ 1
    rw [real_inner_self_eq_norm_sq]
    constructor
    · positivity
    · nlinarith [norm_nonneg (f (b i))]
  have hprod : (∏ i ∈ Finset.univ.filter (fun i => ∀ j : Fin 2, a j ≠ i), M i i) ≤ 1 :=
    Finset.prod_le_one (fun i _ => (hdiag i).1) (fun i _ => (hdiag i).2)
  have hminorNonneg : 0 ≤ (M.submatrix a a).det := (hM.submatrix a).det_nonneg
  have hdet := (hFischer _ M a hM).trans
    (show (M.submatrix a a).det * _ ≤ (M.submatrix a a).det by
      nlinarith [mul_nonneg hminorNonneg (sub_nonneg.mpr hprod)])
  rw [frameJacobian_eq_gram f hf b]
  change Real.sqrt M.det ≤ _
  rw [← hminor]
  exact Real.sqrt_le_sqrt hdet

/-- Agreement with the source's adjoint-determinant formula whenever
the target is finite dimensional. -/
theorem frameJacobian_eq_linearJacobian [FiniteDimensional ℝ V] (D : U →ₗ[ℝ] V) :
    frameJacobian D = linearJacobian D := by
  exact (linearJacobian_eq_gram D (stdOrthonormalBasis ℝ U)).symm

theorem frameJacobian_of_inner_isometry (f : U → V)
    (hf : ∀ v w, ⟪f v, f w⟫_ℝ = ⟪v, w⟫_ℝ) : frameJacobian f = 1 := by
  classical
  let b := stdOrthonormalBasis ℝ U
  have hM : Matrix.gram ℝ (fun i => f (b i)) = 1 := by
    ext i j
    rw [Matrix.gram_apply, hf]
    exact orthonormal_iff_ite.mp b.orthonormal i j
  change Real.sqrt (Matrix.gram ℝ (fun i => f (b i))).det = 1
  rw [hM, Matrix.det_one, Real.sqrt_one]

theorem frameJacobian_of_zero (f : U → V) (hf : ∀ v, f v = 0)
    (hn : 0 < Module.finrank ℝ U) : frameJacobian f = 0 := by
  classical
  have hM : Matrix.gram ℝ (fun i => f (stdOrthonormalBasis ℝ U i)) = 0 := by
    ext i j
    simp [Matrix.gram_apply, hf]
  unfold frameJacobian
  rw [hM, Matrix.det_zero ⟨⟨0, hn⟩⟩, Real.sqrt_zero]

end Frames

section Foldings
variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
  [FiniteDimensional ℝ H₁] [FiniteDimensional ℝ H₂]

/-- Two radial constraints suffice inside the sphere tangent space. -/
def lowRadialVectors (u : Triple H₁ H₂) : Fin 2 → Triple H₁ H₂ :=
  ![toLp 2 (u.fst, toLp 2 (0, 0)), toLp 2 (0, toLp 2 (1, 0))]

def lowRadialSpace (u : Triple H₁ H₂) : Submodule ℝ (Triple H₁ H₂) :=
  Submodule.span ℝ (Set.range (lowRadialVectors u))

theorem lowRadialSpace_dim (u : Triple H₁ H₂) :
    Module.finrank ℝ (lowRadialSpace u) ≤ 2 := by
  simpa [lowRadialSpace] using (finrank_range_le_card (R := ℝ) (lowRadialVectors u))

/-- A genuine two-frame in E satisfying both nonradial constraints. No
adapted frame is assumed as an extra hypothesis of the folding estimate. -/
theorem exists_common_nonradial_frame (u : Triple H₁ H₂)
    (S : Submodule ℝ (Triple H₁ H₂)) (hS : 4 ≤ Module.finrank ℝ S) :
    ∃ e : Fin 2 → S, Orthonormal ℝ e ∧
      (∀ i, ⟪u.fst, (e i).val.fst⟫_ℝ = 0) ∧
      (∀ i, (e i).val.snd.fst = 0) := by
  let N := S ⊓ (lowRadialSpace u)ᗮ
  have hN : 2 ≤ Module.finrank ℝ N :=
    orthogonal_slice_dim S (lowRadialSpace u) hS (lowRadialSpace_dim u)
  let b := stdOrthonormalBasis ℝ N
  let a := twoFrameEmbedding hN
  let f : N →ₗᵢ[ℝ] S :=
    { toLinearMap := Submodule.inclusion (show N ≤ S from inf_le_left)
      norm_map' := fun _ => rfl }
  let e : Fin 2 → S := fun i => f (b (a i))
  have he : Orthonormal ℝ e := by
    rw [orthonormal_iff_ite]
    intro i j
    change ⟪b (a i), b (a j)⟫_ℝ = _
    rw [orthonormal_iff_ite.mp b.orthonormal]
    simp only [a.injective.eq_iff]
  refine ⟨e, he, ?_, ?_⟩
  · intro i
    have hn : (b (a i)).val ∈ (lowRadialSpace u)ᗮ := (b (a i)).property.2
    have hx := (lowRadialSpace u).inner_right_of_mem_orthogonal
      (Submodule.subset_span (Set.mem_range_self (0 : Fin 2))) hn
    simpa [lowRadialVectors, e, f, WithLp.prod_inner_apply] using hx
  · intro i
    have hn : (b (a i)).val ∈ (lowRadialSpace u)ᗮ := (b (a i)).property.2
    have hz := (lowRadialSpace u).inner_right_of_mem_orthogonal
      (Submodule.subset_span (Set.mem_range_self (1 : Fin 2))) hn
    simpa [lowRadialVectors, e, f, WithLp.prod_inner_apply] using hz

/-- Genuine full-n Jacobian estimate at every regular folding point and
for every n-dimensional sphere-tangent plane with n >= 4. -/
theorem two_foldings_nJacobian_regular (hFischer : FischerInput)
    (u : Triple H₁ H₂) (S : Submodule ℝ (Triple H₁ H₂))
    (hS : 4 ≤ Module.finrank ℝ S)
    (hTan : ∀ v : S, ⟪u, v.val⟫_ℝ = 0)
    (hL : u.snd ≠ 0) (hR : (reverseTriple u).snd ≠ 0) :
    frameJacobian (fun v : S => normFoldDerivative u v.val) +
      frameJacobian (fun v : S => rightFoldDerivative u v.val) ≤ 1 := by
  obtain ⟨e, he, hx, hz⟩ := exists_common_nonradial_frame u S hS
  have hn : 2 ≤ Module.finrank ℝ S := by omega
  have hfL : PreservesFrameSums (fun v : S => normFoldDerivative u v.val) := by
    intro v a
    simp [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]
  have hfR : PreservesFrameSums (fun v : S => rightFoldDerivative u v.val) := by
    intro v a
    simp [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]
  have hRc : ∀ v : S, ‖rightFoldDerivative u v.val‖ ≤ ‖v‖ := by
    intro v
    change ‖normFoldDerivative (reverseTriple u) (reverseTriple v.val)‖ ≤ ‖v‖
    exact (normFoldDerivative_norm_le _ _ hR).trans_eq (reverseTriple_norm v.val)
  have hLe := frameJacobian_le_two_frame hFischer _ hfL
    (fun v : S => normFoldDerivative_norm_le u v.val hL) e he hn
  have hRe := frameJacobian_le_two_frame hFischer _ hfR hRc e he hn
  let ea : Fin 2 → Triple H₁ H₂ := fun i => (e i).val
  have hea : Orthonormal ℝ ea := he.comp_linearIsometry S.subtypeₗᵢ
  have htwo := folding_differential_two_area_le_one u ea hea (fun i => hTan (e i)) hx hz
  exact (add_le_add hLe hRe).trans htwo

/-- On the stratum where the folded left block vanishes, the left map
is isometric on the tangent plane and the right map is constant there. -/
theorem two_foldings_nJacobian_left_zero_stratum
    (u : Triple H₁ H₂) (S : Submodule ℝ (Triple H₁ H₂))
    (hPos : 0 < Module.finrank ℝ S) (hTan : ∀ v : S, ⟪u, v.val⟫_ℝ = 0)
    (hStrat : ∀ v : S, v.val.snd = 0) :
    frameJacobian (fun v : S => normFoldDerivative u v.val) = 1 ∧
      frameJacobian (fun v : S => rightFoldDerivative u v.val) = 0 := by
  constructor
  · apply frameJacobian_of_inner_isometry
    intro v w
    change ⟪normFoldDerivative u v.val, normFoldDerivative u w.val⟫_ℝ = ⟪v.val, w.val⟫_ℝ
    rw [normFoldDerivative_orthogonal u v.val (by simp [hStrat v]),
      normFoldDerivative_orthogonal u w.val (by simp [hStrat w])]
    simp [prod_inner_apply, hStrat v, hStrat w]
  · refine frameJacobian_of_zero (U := S) (V := WithLp 2 (H₂ × ℝ))
      (fun v : S => rightFoldDerivative u v.val) ?_ hPos
    intro v
    have hx := hTan v
    rw [prod_inner_apply] at hx
    simp only [ofLp_fst, ofLp_snd, hStrat v, inner_zero_right, add_zero] at hx
    have hr : ⟪(reverseTriple u).snd, (reverseTriple v.val).snd⟫_ℝ = 0 := by
      simp [reverseTriple, prod_inner_apply, hStrat v, hx]
    change normFoldDerivative (reverseTriple u) (reverseTriple v.val) = 0
    rw [normFoldDerivative_orthogonal _ _ hr]
    simp [reverseTriple, hStrat v]

/-- Symmetric zero-block stratum. -/
theorem two_foldings_nJacobian_right_zero_stratum
    (u : Triple H₁ H₂) (S : Submodule ℝ (Triple H₁ H₂))
    (hPos : 0 < Module.finrank ℝ S) (hTan : ∀ v : S, ⟪u, v.val⟫_ℝ = 0)
    (hStrat : ∀ v : S, (reverseTriple v.val).snd = 0) :
    frameJacobian (fun v : S => normFoldDerivative u v.val) = 0 ∧
      frameJacobian (fun v : S => rightFoldDerivative u v.val) = 1 := by
  constructor
  · refine frameJacobian_of_zero (U := S) (V := WithLp 2 (H₁ × ℝ))
      (fun v : S => normFoldDerivative u v.val) ?_ hPos
    intro v
    have hvx : v.val.fst = 0 := by
      have h := congrArg (fun q : WithLp 2 (ℝ × H₁) => q.snd) (hStrat v)
      simpa [reverseTriple] using h
    have hv := hTan v
    rw [prod_inner_apply] at hv
    simp only [ofLp_fst, ofLp_snd, hvx, inner_zero_right, zero_add] at hv
    change normFoldDerivative u v.val = 0
    rw [normFoldDerivative_orthogonal _ _ hv]
    simp [hvx]
  · apply frameJacobian_of_inner_isometry
    intro v w
    change ⟪normFoldDerivative (reverseTriple u) (reverseTriple v.val),
      normFoldDerivative (reverseTriple u) (reverseTriple w.val)⟫_ℝ = ⟪v.val, w.val⟫_ℝ
    rw [normFoldDerivative_orthogonal _ _ (by simp [hStrat v]),
      normFoldDerivative_orthogonal _ _ (by simp [hStrat w])]
    rw [← reverseTriple_inner v.val w.val]
    simp [prod_inner_apply, hStrat v, hStrat w]

/-- The full pointwise Jacobian estimate on every coordinate stratum.
The two kernel conditions are precisely generic tangent locality on zero
level sets; they are not a Jacobian or folding estimate. -/
theorem two_foldings_nJacobian_stratified (hFischer : FischerInput)
    (u : Triple H₁ H₂) (S : Submodule ℝ (Triple H₁ H₂))
    (hS : 4 ≤ Module.finrank ℝ S) (hTan : ∀ v : S, ⟪u, v.val⟫_ℝ = 0)
    (hStratL : u.snd = 0 → ∀ v : S, v.val.snd = 0)
    (hStratR : (reverseTriple u).snd = 0 → ∀ v : S, (reverseTriple v.val).snd = 0) :
    frameJacobian (fun v : S => normFoldDerivative u v.val) +
      frameJacobian (fun v : S => rightFoldDerivative u v.val) ≤ 1 := by
  classical
  have hp : 0 < Module.finrank ℝ S := by omega
  by_cases hL : u.snd = 0
  · obtain ⟨hl, hr⟩ := two_foldings_nJacobian_left_zero_stratum u S hp hTan (hStratL hL)
    rw [hl, hr]
    norm_num
  · by_cases hR : (reverseTriple u).snd = 0
    · obtain ⟨hl, hr⟩ := two_foldings_nJacobian_right_zero_stratum u S hp hTan (hStratR hR)
      rw [hl, hr]
      norm_num
    · exact two_foldings_nJacobian_regular hFischer u S hS hTan hL hR

end Foldings
end Paper28
