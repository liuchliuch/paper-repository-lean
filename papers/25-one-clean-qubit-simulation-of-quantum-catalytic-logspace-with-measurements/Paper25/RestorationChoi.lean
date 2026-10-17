import Paper25.Restoration
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Matrix.Basis

/-! The positivity step in Lemma 2: a positive matrix with a pure marginal
has product form. The Choi application below derives the basis hypothesis in
`lemma_2_product_form` from restoration of all density operators. -/

noncomputable section
set_option maxHeartbeats 1000000
open scoped ComplexOrder ComplexConjugate
open Matrix
namespace Paper25

/-- Trace out the first register. -/
def workPartialTrace {W V : Type*} [Fintype W]
    (A : Matrix (W × V) (W × V) ℂ) : Matrix V V ℂ :=
  fun i j => ∑ w, A (w, i) (w, j)

/-- A positive operator of trace one. -/
def IsDensity {V : Type*} [Fintype V] (ρ : Matrix V V ℂ) : Prop :=
  ρ.PosSemidef ∧ Matrix.trace ρ = 1

/-- A rank-one marginal confines every block of a positive operator to the
same one-dimensional support. The anchor is useful for the unnormalized Choi
vector, whose nonzero coordinates are all one. -/
theorem psd_pure_marginal_product {W V : Type*} [Fintype W] [Fintype V]
    [DecidableEq W] [DecidableEq V]
    (A : Matrix (W × V) (W × V) ℂ) (hA : A.PosSemidef)
    (z : V → ℂ) (a : V) (ha : z a = 1)
    (hm : workPartialTrace A = Matrix.vecMulVec z (star z)) :
    ∃ η : Matrix W W ℂ, IsDensity η ∧
      ∀ w w' i j, A (w, i) (w', j) = η w w' * (z i * star (z j)) := by
  classical
  let η : Matrix W W ℂ := A.submatrix (fun w => (w, a)) (fun w => (w, a))
  have hη : η.PosSemidef := hA.submatrix _
  have htη : Matrix.trace η = 1 := by
    have ht := congrFun (congrFun hm a) a
    simpa [η, Matrix.trace, workPartialTrace, Matrix.vecMulVec, ha] using ht
  have hcol : ∀ w j r, A r (w, j) = star (z j) * A r (w, a) := by
    intro w j r
    let x : W → (W × V → ℂ) := fun v =>
      (Pi.single (v, j) (1 : ℂ) : W × V → ℂ) -
        star (z j) • (Pi.single (v, a) (1 : ℂ) : W × V → ℂ)
    have hnonneg : ∀ v, 0 ≤ star (x v) ⬝ᵥ (A *ᵥ x v) := fun v => hA.2 (x v)
    have hcell : ∀ v, star (x v) ⬝ᵥ (A *ᵥ x v) =
        A (v,j) (v,j) - star (z j) * A (v,j) (v,a) -
        z j * A (v,a) (v,j) + z j * star (z j) * A (v,a) (v,a) := by
      intro v
      simp [x, Matrix.mulVec_sub, Matrix.mulVec_smul, star_sub, star_smul,
        Matrix.mulVec_single_one, sub_dotProduct, dotProduct_sub,
        smul_dotProduct, dotProduct_smul, ← Pi.single_star, Matrix.col_apply]
      <;> ring
    have hsum : (∑ v, star (x v) ⬝ᵥ (A *ᵥ x v)) = 0 := by
      simp_rw [hcell]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
      change workPartialTrace A j j - star (z j) * workPartialTrace A j a -
        z j * workPartialTrace A a j + (z j * star (z j)) * workPartialTrace A a a = 0
      rw [hm]
      simp [Matrix.vecMulVec, ha]
      ring
    have hzero : star (x w) ⬝ᵥ (A *ᵥ x w) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => hnonneg v)).mp hsum w (Finset.mem_univ w)
    have hk := (hA.dotProduct_mulVec_zero_iff (x w)).mp hzero
    have hkr := congrFun hk r
    simpa [x, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_single_one,
      Matrix.col_apply, sub_eq_zero, mul_comm] using hkr
  refine ⟨η, ⟨hη, htη⟩, ?_⟩
  intro w w' i j
  have hr : A (w,i) (w',a) = z i * A (w,a) (w',a) := by
    have h := congrArg star (hcol w i (w', a))
    have hh (p q : W × V) : star (A p q) = A q p := by
      exact congrFun (congrFun hA.1 q) p
    simpa only [StarMul.star_mul, star_star, hh, mul_comm] using h
  rw [hcol w' j (w,i), hr]
  dsimp [η]
  ring

end Paper25

namespace Paper25

/-- Density operators span the complex operator space. This is stated as an
identity principle for linear maps and proved by normalization and polarization. -/
theorem linearMap_eq_zero_of_density {V : Type*} [Fintype V] [DecidableEq V]
    {M : Type*} [AddCommGroup M]
    [Module ℂ M]
    (L : Matrix (V) (V) ℂ →ₗ[ℂ] M)
    (h : ∀ ρ, IsDensity ρ → L ρ = 0) : ∀ X, L X = 0 := by
  classical
  have hpos : ∀ P : Matrix (V) (V) ℂ, P.PosSemidef → L P = 0 := by
    intro P hP
    let t : ℝ := (Matrix.trace P).re
    have ht : 0 ≤ t := (Complex.nonneg_iff.mp hP.trace_nonneg).1
    have heq : Matrix.trace P = (t : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa using (Complex.nonneg_iff.mp hP.trace_nonneg).2.symm
    by_cases ht0 : t = 0
    · have hP0 : P = 0 := hP.trace_eq_zero_iff.mp (by simpa [ht0] using heq)
      simp [hP0]
    · let ρ : Matrix (V) (V) ℂ := (t⁻¹ : ℂ) • P
      have hρ : IsDensity ρ := by
        refine ⟨hP.smul (by exact_mod_cast (inv_nonneg.mpr ht)), ?_⟩
        simp [ρ, Matrix.trace_smul, heq, ht0]
      have hv := h ρ hρ
      have htC : (t⁻¹ : ℂ) ≠ 0 := by exact_mod_cast inv_ne_zero ht0
      have hv' : (t⁻¹ : ℂ) • L P = 0 := by simpa [ρ] using hv
      exact (smul_eq_zero.mp hv').resolve_left htC
  have hrank (x : V → ℂ) : L (Matrix.vecMulVec x (star x)) = 0 :=
    hpos _ (Matrix.posSemidef_vecMulVec_self_star x)
  have hbasis (i j : V) : L (Matrix.single i j (1 : ℂ)) = 0 := by
    let e (i : V) : V → ℂ := (Pi.single i (1 : ℂ) : V → ℂ)
    let P (x : V → ℂ) := Matrix.vecMulVec x (star x)
    have hp : P (e i + e j) - P (e i - e j) +
        Complex.I • (P (e i + Complex.I • e j) - P (e i - Complex.I • e j)) =
        (4 : ℂ) • Matrix.single i j (1 : ℂ) := by
      ext a b
      by_cases hai : a = i <;> by_cases haj : a = j <;>
        by_cases hbi : b = i <;> by_cases hbj : b = j <;>
        simp [P, e, Matrix.vecMulVec, Matrix.single, Pi.single_apply, hai, haj, hbi, hbj] <;>
        (try simp_all [Pi.single_apply]) <;> (try ring_nf) <;> norm_num [Complex.ext_iff] <;> aesop
    have hz := congrArg L hp
    simp only [map_add, map_sub, map_smul] at hz
    simp only [hrank, sub_self, smul_zero, add_zero, P] at hz
    exact (smul_eq_zero.mp hz.symm).resolve_left (by norm_num)
  intro X
  rw [Matrix.matrix_eq_sum_single X, map_sum]
  simp only [map_sum]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  have hs : Matrix.single i j (X i j) = X i j • Matrix.single i j (1 : ℂ) := by
    simp [Matrix.smul_single]
  rw [hs, map_smul, hbasis, smul_zero]

/-- The partial trace is complex linear. -/
def workPartialTraceLinear {W V : Type*} [Fintype W] :
    Matrix (W × V) (W × V) ℂ →ₗ[ℂ] Matrix V V ℂ where
  toFun := workPartialTrace
  map_add' A B := by ext i j; simp [workPartialTrace, Finset.sum_add_distrib]
  map_smul' c A := by ext i j; simp [workPartialTrace, Finset.mul_sum]

/-- Restore every state, and linearity restores every operator. -/
theorem restores_operators_of_states {W V : Type*} [Fintype W] [Fintype V] [DecidableEq V]
    (Ψ : Matrix (V) (V) ℂ →ₗ[ℂ]
      Matrix (W × V) (W × V) ℂ)
    (h : ∀ ρ, IsDensity ρ → workPartialTrace (Ψ ρ) = ρ)
    (X : Matrix (V) (V) ℂ) : workPartialTrace (Ψ X) = X := by
  let L := workPartialTraceLinear.comp Ψ - LinearMap.id
  have hz := linearMap_eq_zero_of_density L (fun ρ hρ => by
    change workPartialTrace (Ψ ρ) - ρ = 0
    exact sub_eq_zero.mpr (h ρ hρ)) X
  exact sub_eq_zero.mp hz

end Paper25

namespace Paper25

/-- Unnormalized Choi matrix, with index order `W,C,R`. -/
def restorationChoi {W V : Type*} [DecidableEq V]
    (Ψ : Matrix V V ℂ →ₗ[ℂ] Matrix (W × V) (W × V) ℂ) :
    Matrix (W × (V × V)) (W × (V × V)) ℂ :=
  fun p q => Ψ (Matrix.single p.2.2 q.2.2 1) (p.1, p.2.1) (q.1, q.2.1)

/-- The unnormalized maximally entangled vector. -/
def choiIdentityVector {V : Type*} [DecidableEq V] : V × V → ℂ :=
  fun p => if p.1 = p.2 then 1 else 0

/-- Tensoring with a fixed work operator is complex linear. -/
def productChannel {W V : Type*} (η : Matrix W W ℂ) :
    Matrix V V ℂ →ₗ[ℂ] Matrix (W × V) (W × V) ℂ where
  toFun X := Matrix.kronecker η X
  map_add' X Y := Matrix.kronecker_add η X Y
  map_smul' c X := Matrix.kronecker_smul c η X

/-- **Lemma 2, including the positivity argument.** Complete positivity is
expressed by the positive Choi matrix. Restoring every density operator forces
one work state and product form on every catalyst operator. -/
theorem lemma_2_from_marginal_restoration_generic {W V : Type*}
    [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V] (v₀ : V)
    (Ψ : Matrix V V ℂ →ₗ[ℂ] Matrix (W × V) (W × V) ℂ)
    (hcp : (restorationChoi Ψ).PosSemidef)
    (hrestore : ∀ ρ, IsDensity ρ → workPartialTrace (Ψ ρ) = ρ) :
    ∃ η : Matrix W W ℂ, IsDensity η ∧ ∀ X, Ψ X = Matrix.kronecker η X := by
  classical
  have hoperators := restores_operators_of_states Ψ hrestore
  have hm : workPartialTrace (restorationChoi Ψ) =
      Matrix.vecMulVec choiIdentityVector (star choiIdentityVector) := by
    ext p q
    have hm' := congrFun (congrFun (hoperators (Matrix.single p.2 q.2 1)) p.1) q.1
    change (∑ w, Ψ (Matrix.single p.2 q.2 1) (w,p.1) (w,q.1)) = _ at hm'
    change (∑ w, Ψ (Matrix.single p.2 q.2 1) (w,p.1) (w,q.1)) = _
    rw [hm']
    simp only [Matrix.single, Matrix.of_apply, Matrix.vecMulVec, choiIdentityVector,
      Pi.star_apply]
    by_cases hp : p.1 = p.2 <;> by_cases hq : q.1 = q.2 <;> simp [hp, hq, eq_comm]
  obtain ⟨η, hη, hentries⟩ := psd_pure_marginal_product (restorationChoi Ψ) hcp
    choiIdentityVector (v₀,v₀) (by simp [choiIdentityVector]) hm
  refine ⟨η, hη, ?_⟩
  have hbasis (i j : V) : Ψ (Matrix.single i j 1) =
      Matrix.kronecker η (Matrix.single i j 1) := by
    ext p q
    have he := hentries p.1 q.1 (p.2,i) (q.2,j)
    change Ψ (Matrix.single i j 1) p q = _ at he
    change Ψ (Matrix.single i j 1) p q = η p.1 q.1 * Matrix.single i j 1 p.2 q.2
    rw [he]
    simp only [choiIdentityVector, Matrix.single, Matrix.of_apply]
    by_cases hp : p.2 = i <;> by_cases hq : q.2 = j <;> simp [hp,hq] <;> aesop
  intro X
  have hX : (Ψ - productChannel (V := V) η) X = 0 := by
    rw [Matrix.matrix_eq_sum_single X, map_sum]
    simp only [map_sum]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    have hs : Matrix.single i j (X i j) = X i j • Matrix.single i j (1 : ℂ) := by
      simp [Matrix.smul_single]
    rw [hs, map_smul]
    have hz : (Ψ - productChannel (V := V) η) (Matrix.single i j 1) = 0 := by
      exact sub_eq_zero.mpr (hbasis i j)
    rw [hz, smul_zero]
  exact sub_eq_zero.mp hX

/-- Finite-dimension numeric-index form of Lemma 2. -/
theorem lemma_2_from_marginal_restoration {k d : ℕ} (hd : 0 < d)
    (Ψ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin k × Fin d) (Fin k × Fin d) ℂ)
    (hcp : (restorationChoi Ψ).PosSemidef)
    (hrestore : ∀ ρ, IsDensity ρ → workPartialTrace (Ψ ρ) = ρ) :
    ∃ η : Matrix (Fin k) (Fin k) ℂ, IsDensity η ∧
      ∀ X, Ψ X = Matrix.kronecker η X :=
  lemma_2_from_marginal_restoration_generic ⟨0,hd⟩ Ψ hcp hrestore

/-- Extension of a channel by the identity on an arbitrary finite reference.
Each reference matrix coefficient is transformed by the original linear map. -/
def referenceExtension {W V R : Type*}
    (Ψ : Matrix (V) (V) ℂ →ₗ[ℂ]
      Matrix (W × V) (W × V) ℂ)
    (X : Matrix (V × R) (V × R) ℂ) :
    Matrix (W × (V × R)) (W × (V × R)) ℂ :=
  fun p q => Ψ (fun i j => X (i,p.2.2) (j,q.2.2)) (p.1,p.2.1) (q.1,q.2.1)

/-- Product form preserves correlations for every joint reference operator,
including entangled input states. No product-state assumption is needed. -/
theorem lemma_2_preserves_arbitrary_reference {W V R : Type*}
    (η : Matrix (W) (W) ℂ)
    (Ψ : Matrix (V) (V) ℂ →ₗ[ℂ]
      Matrix (W × V) (W × V) ℂ)
    (hproduct : ∀ X, Ψ X = Matrix.kronecker η X)
    (X : Matrix (V × R) (V × R) ℂ) :
    referenceExtension Ψ X = Matrix.kronecker η X := by
  ext p q
  simp [referenceExtension, hproduct, Matrix.kronecker, Matrix.kroneckerMap]

end Paper25
