import Paper22.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! Concrete tensor products of cq channels, including the noiseless bit. -/

open scoped MatrixOrder ComplexOrder Kronecker
open Matrix

noncomputable section
namespace Paper22

theorem posSemidef_kronecker {a b : Type*} [Fintype a] [Fintype b]
    {A : Matrix a a ℂ} {B : Matrix b b ℂ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : (A ⊗ₖ B).PosSemidef := by
  classical
  obtain ⟨X, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  obtain ⟨Y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  rw [Matrix.mul_kronecker_mul, star_eq_conjTranspose, star_eq_conjTranspose,
    ← Matrix.conjTranspose_kronecker]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem posDef_kronecker {a b : Type*} [Fintype a] [Fintype b]
    {A : Matrix a a ℂ} {B : Matrix b b ℂ} (hA : A.PosDef)
    (hB : B.PosDef) : (A ⊗ₖ B).PosDef := by
  classical
  apply (posSemidef_kronecker hA.posSemidef hB.posSemidef).posDef_iff_isUnit.mpr
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_kronecker]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit |>.pow _).mul
    ((Matrix.isUnit_iff_isUnit_det _).mp hB.isUnit |>.pow _)

theorem trace_submatrix_equiv {a b : Type*} [Fintype a] [Fintype b]
    (A : Matrix a a ℂ) (e : b ≃ a) : (A.submatrix e e).trace = A.trace := by
  exact e.sum_comp (fun i => A i i)

theorem posDef_submatrix_equiv {a b : Type*} [Fintype a] [Fintype b]
    {A : Matrix a a ℂ} (hA : A.PosDef) (e : b ≃ a) :
    (A.submatrix e e).PosDef := by
  classical
  apply (hA.posSemidef.submatrix e).posDef_iff_isUnit.mpr
  exact (Matrix.isUnit_submatrix_equiv e e).mpr hA.isUnit

/-- Reindex a channel along exact equivalences of its two finite alphabets. -/
def CQChannel.relabel {n d n' d' : ℕ} (V : CQChannel n d)
    (en : Fin n' ≃ Fin n) (ed : Fin d' ≃ Fin d) : CQChannel n' d' where
  states x := (V.states (en x)).submatrix ed ed
  isDensity x := ⟨(V.isDensity (en x)).posSemidef.submatrix ed,
    (trace_submatrix_equiv _ ed).trans (V.isDensity (en x)).trace_one⟩

theorem CQChannel.relabel_fullRank {n d n' d' : ℕ} (V : CQChannel n d)
    (hV : V.FullRank) (en : Fin n' ≃ Fin n) (ed : Fin d' ≃ Fin d) :
    (V.relabel en ed).FullRank := by
  intro x
  exact posDef_submatrix_equiv (hV (en x)) ed

/-- Tensor product, with the ordinary mixed-radix identification of finite indices. -/
def CQChannel.tensor {n d m e : ℕ} (V : CQChannel n d) (W : CQChannel m e) :
    CQChannel (n * m) (d * e) where
  states x :=
    ((V.states (finProdFinEquiv.symm x).1) ⊗ₖ
      (W.states (finProdFinEquiv.symm x).2)).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm
  isDensity x := by
    constructor
    · exact (posSemidef_kronecker (V.isDensity _).posSemidef
        (W.isDensity _).posSemidef).submatrix _
    · rw [trace_submatrix_equiv, Matrix.trace_kronecker,
        (V.isDensity _).trace_one, (W.isDensity _).trace_one, one_mul]

theorem CQChannel.tensor_fullRank {n d m e : ℕ} (V : CQChannel n d)
    (W : CQChannel m e) (hV : V.FullRank) (hW : W.FullRank) :
    (V.tensor W).FullRank := by
  intro x
  exact posDef_submatrix_equiv (posDef_kronecker (hV _) (hW _)) _

/-- The unique one-dimensional output state. -/
def tensorUnitChannel : CQChannel 1 1 where
  states _ := 1
  isDensity _ := ⟨PosSemidef.one, by simp⟩

theorem tensorUnitChannel_fullRank : tensorUnitChannel.FullRank := by
  intro x
  exact PosDef.one

/-- The tensor powers are genuine iterated Kronecker products of the output states. -/
def tensorPowerFamily {n d : ℕ} (V : CQChannel n d) (k : ℕ) :
    CQChannel (n ^ k) (d ^ k) :=
  Nat.rec (motive := fun k => CQChannel (n ^ k) (d ^ k))
    tensorUnitChannel
    (fun k previous => (previous.tensor V).relabel
      (finCongr (Nat.pow_succ n k)) (finCongr (Nat.pow_succ d k))) k

theorem tensorPowerFamily_fullRank {n d : ℕ} (V : CQChannel n d)
    (hV : V.FullRank) (k : ℕ) : (tensorPowerFamily V k).FullRank := by
  induction k with
  | zero => exact tensorUnitChannel_fullRank
  | succ k ih =>
      exact CQChannel.relabel_fullRank _ (CQChannel.tensor_fullRank _ _ ih hV) _ _

/-- A noiseless classical bit, represented by its two orthogonal rank-one states. -/
def noiselessBit : CQChannel 2 2 where
  states x := Matrix.diagonal (fun i => if i = x then 1 else 0)
  isDensity x := by
    constructor
    · exact Matrix.PosSemidef.diagonal (fun i => by split_ifs <;> norm_num)
    · simp [Matrix.trace_diagonal]

/-- Tensor with one noiseless classical bit. -/
def activationFamily {n d : ℕ} (V : CQChannel n d) : CQChannel (n * 2) (d * 2) :=
  V.tensor noiselessBit

/-- Activated tensor power `W^{⊗k} ⊗ I₂`. -/
def activatedTensorPowerFamily {n d : ℕ} (V : CQChannel n d) (k : ℕ) :
    CQChannel (n ^ k * 2) (d ^ k * 2) := activationFamily (tensorPowerFamily V k)

end Paper22
end
