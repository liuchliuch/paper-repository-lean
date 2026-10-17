import Paper17.IntegerConeGenerators

/-! Rational inequalities for actual faces of integral nonsingular basis cones. -/
noncomputable section
open scoped BigOperators Matrix
namespace Paper17

/-- A finite homogeneous rational presentation with trivial common kernel.
The latter expresses that the actual cone contains no line. -/
structure RationalConePresentation {n : ℕ} (K : Set (V n)) where
  index : Type
  [indexFintype : Fintype index]
  [indexDecidableEq : DecidableEq index]
  normals : index → Fin n → ℚ
  carrier_eq : rationalInequalityCone normals = K
  kernel : ∀ x : V n, (∀ i, dot (ratVector (normals i)) x = 0) → x = 0

attribute [instance] RationalConePresentation.indexFintype RationalConePresentation.indexDecidableEq

/-- A pointed rational H-presentation supplies genuine integer generators. -/
theorem RationalConePresentation.integer_generators {n : ℕ} {K : Set (V n)}
    (H : RationalConePresentation K) :
    ∃ m : ℕ, ∃ rays : Fin m → Fin n → ℤ,
      K = {x | ∃ c : Fin m → ℝ, (∀ i, 0 ≤ c i) ∧ x = ∑ i, c i • realRays rays i} := by
  rw [← H.carrier_eq]
  exact rationalCone_integer_generators H.normals H.kernel

/-- Intersections retain actual rational inequalities and pointedness. -/
def RationalConePresentation.inter {n : ℕ} {K L : Set (V n)}
    (H : RationalConePresentation K) (J : RationalConePresentation L) :
    RationalConePresentation (K ∩ L) where
  index := H.index ⊕ J.index
  normals := Sum.elim H.normals J.normals
  carrier_eq := by
    ext x
    simp only [rationalInequalityCone, Set.mem_setOf_eq, Set.mem_inter_iff, Sum.forall,
      Sum.elim_inl, Sum.elim_inr, ← H.carrier_eq, ← J.carrier_eq]
  kernel := by
    intro x hx
    exact H.kernel x (fun i => hx (.inl i))

def realBasisMatrix {n : ℕ} (A : Fin n → Fin n → ℤ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (A i j : ℝ)

def rationalBasisMatrix {n : ℕ} (A : Fin n → Fin n → ℤ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => (A i j : ℚ)

def rationalBasisInverse {n : ℕ} (A : Fin n → Fin n → ℤ) : Matrix (Fin n) (Fin n) ℚ :=
  (rationalBasisMatrix A)⁻¹

/-- Rational dual coordinate rows of an actual integral basis. -/
def rationalBasisDual {n : ℕ} (A : Fin n → Fin n → ℤ) : Fin n → Fin n → ℚ :=
  fun i j => rationalBasisInverse A j i

private theorem rationalBasis_inverse {n : ℕ} (A : Fin n → Fin n → ℤ)
    (hd : (Matrix.det (realRays A)) ≠ 0) :
    realBasisMatrix A * (rationalBasisInverse A).map (Rat.castHom ℝ) = 1 ∧
      (rationalBasisInverse A).map (Rat.castHom ℝ) * realBasisMatrix A = 1 := by
  let M := rationalBasisMatrix A
  have hcast : M.map (Rat.castHom ℝ) = realBasisMatrix A := by
    ext i j
    simp [M, rationalBasisMatrix, realBasisMatrix]
  have hMd : M.det ≠ 0 := by
    intro hz
    apply hd
    change (realBasisMatrix A).det = 0
    rw [← hcast]
    change (M.map (fun q : ℚ => (q : ℝ))).det = 0
    rw [← Rat.cast_det, hz, Rat.cast_zero]
  have h1 : (1 : Matrix (Fin n) (Fin n) ℚ).map (Rat.castHom ℝ) = 1 := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  constructor
  · have hh := congrArg (fun N : Matrix (Fin n) (Fin n) ℚ => N.map (Rat.castHom ℝ))
      (Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hMd))
    simpa only [Matrix.map_mul, hcast, h1, rationalBasisInverse, M] using hh
  · have hh := congrArg (fun N : Matrix (Fin n) (Fin n) ℚ => N.map (Rat.castHom ℝ))
      (Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hMd))
    simpa only [Matrix.map_mul, hcast, h1, rationalBasisInverse, M] using hh

def rationalBasisCoordinates {n : ℕ} (A : Fin n → Fin n → ℤ) (x : V n) : V n :=
  fun i => dot (ratVector (rationalBasisDual A i)) x

private theorem rationalBasisCoordinates_vecMul {n : ℕ} (A : Fin n → Fin n → ℤ) (x : V n) :
    rationalBasisCoordinates A x = x ᵥ* (rationalBasisInverse A).map (Rat.castHom ℝ) := by
  ext i
  simp only [rationalBasisCoordinates, rationalBasisDual, dot, ratVector, Matrix.vecMul,
    dotProduct, Matrix.map_apply, Rat.coe_castHom, mul_comm]

private theorem basis_synthesis_vecMul {n : ℕ} (A : Fin n → Fin n → ℤ) (c : V n) :
    (∑ i, c i • realRays A i) = c ᵥ* realBasisMatrix A := by
  ext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct, realRays, realBasisMatrix]

theorem rationalBasisCoordinates_synthesis {n : ℕ} (A : Fin n → Fin n → ℤ)
    (hd : (Matrix.det (realRays A)) ≠ 0) (c : V n) :
    rationalBasisCoordinates A (∑ i, c i • realRays A i) = c := by
  rw [rationalBasisCoordinates_vecMul, basis_synthesis_vecMul,
    Matrix.vecMul_vecMul, (rationalBasis_inverse A hd).1, Matrix.vecMul_one]

theorem synthesis_rationalBasisCoordinates {n : ℕ} (A : Fin n → Fin n → ℤ)
    (hd : (Matrix.det (realRays A)) ≠ 0) (x : V n) :
    ∑ i, rationalBasisCoordinates A x i • realRays A i = x := by
  rw [basis_synthesis_vecMul, rationalBasisCoordinates_vecMul, Matrix.vecMul_vecMul,
    (rationalBasis_inverse A hd).2, Matrix.vecMul_one]

/-- Actual coefficient conditions for a coordinate face of the basis cone. -/
theorem mem_basisFace_iff {n : ℕ} (A : Fin n → Fin n → ℤ)
    (hd : (Matrix.det (realRays A)) ≠ 0) (I : Finset (Fin n)) (x : V n) :
    x ∈ raySpan (realRays A) I ↔
      (∀ i, 0 ≤ rationalBasisCoordinates A x i) ∧
        (∀ i, i ∉ I → rationalBasisCoordinates A x i = 0) := by
  constructor
  · rintro ⟨c, hc, hs, rfl⟩
    rw [rationalBasisCoordinates_synthesis A hd c]
    exact ⟨hc, hs⟩
  · rintro ⟨hc, hs⟩
    exact ⟨rationalBasisCoordinates A x, hc, hs, (synthesis_rationalBasisCoordinates A hd x).symm⟩

/-- Every coordinate face has explicit finite rational inequalities, including
both signs of each coordinate that must vanish. -/
def basisFacePresentation {n : ℕ} (A : Fin n → Fin n → ℤ)
    (hd : (Matrix.det (realRays A)) ≠ 0) (I : Finset (Fin n)) :
    RationalConePresentation (raySpan (realRays A) I) where
  index := Fin n ⊕ Fin n
  normals := Sum.elim (rationalBasisDual A)
    (fun i => if i ∈ I then 0 else -rationalBasisDual A i)
  carrier_eq := by
    classical
    ext x
    rw [mem_basisFace_iff A hd I x]
    constructor
    · intro hx
      refine ⟨fun i => hx (.inl i), ?_⟩
      intro i hi
      have hh := hx (.inr i)
      change 0 ≤ dot (ratVector (if i ∈ I then 0 else -rationalBasisDual A i)) x at hh
      rw [if_neg hi, ratVector_neg] at hh
      have hn : dot (-ratVector (rationalBasisDual A i)) x =
          -rationalBasisCoordinates A x i := by
        simpa only [neg_one_smul, neg_one_mul, rationalBasisCoordinates] using
          dot_smul_left (-1) (ratVector (rationalBasisDual A i)) x
      rw [hn] at hh
      exact le_antisymm (neg_nonneg.mp hh) (hx (.inl i))
    · rintro ⟨hx, hz⟩ (i | i)
      · exact hx i
      · change 0 ≤ dot (ratVector (if i ∈ I then 0 else -rationalBasisDual A i)) x
        by_cases hi : i ∈ I
        · simp [hi, ratVector, dot]
        · rw [if_neg hi, ratVector_neg]
          have hn : dot (-ratVector (rationalBasisDual A i)) x =
              -rationalBasisCoordinates A x i := by
            simpa only [neg_one_smul, neg_one_mul, rationalBasisCoordinates] using
              dot_smul_left (-1) (ratVector (rationalBasisDual A i)) x
          rw [hn, hz i hi]
          simp
  kernel := by
    intro x hx
    have hz : rationalBasisCoordinates A x = 0 := by
      funext i
      exact hx (.inl i)
    rw [← synthesis_rationalBasisCoordinates A hd x, hz]
    simp

end Paper17
