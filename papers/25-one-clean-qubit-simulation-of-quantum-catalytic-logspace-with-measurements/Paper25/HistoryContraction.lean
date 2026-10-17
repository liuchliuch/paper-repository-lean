import Paper25.History
import Mathlib.LinearAlgebra.Matrix.PosDef

noncomputable section
open scoped ComplexOrder

namespace Paper25

/-- Embed a rectangular data matrix into one clock value. -/
def clockColumn {J : ℕ} {ι κ : Type*} (u : Fin J) (X : Matrix ι κ ℂ) :
    Matrix (Fin J × ι) κ ℂ := fun i j => if i.1=u then X i.2 j else 0

lemma clockColumn_gram {J : ℕ} {ι κ : Type*} [Fintype ι]
    (u : Fin J) (X Y : Matrix ι κ ℂ) :
    (clockColumn u X).conjTranspose * clockColumn u Y = X.conjTranspose * Y := by
  classical
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
  have hterm : ∀ i : Fin J, ∀ j : ι,
      star (clockColumn u X (i,j) a) * clockColumn u Y (i,j) b =
        if i=u then star (X j a)*Y j b else 0 := by
    intro i j
    by_cases h : i=u <;> simp [clockColumn,h]
  simp only [hterm]
  simp [Finset.sum_ite_irrel]

lemma clockColumn_mul_adjoint {J : ℕ} {ι κ : Type*} [Fintype κ]
    (u v : Fin J) (X Y : Matrix ι κ ℂ) :
    clockColumn u X * (clockColumn v Y).conjTranspose =
      historySelector u v (X * Y.conjTranspose) := by
  classical
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, historySelector]
  by_cases hi : i.1=u <;> by_cases hj : j.1=v <;>
    simp [clockColumn,hi,hj]

/-- A partial isometry built from two isometric embeddings is a contraction,
expressed as a positive semidefinite Gram complement. -/
lemma isometries_gram_complement {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (W V : Matrix ι κ ℂ)
    (hW : W.conjTranspose * W = 1) (hV : V.conjTranspose * V = 1) :
    (1-(W*V.conjTranspose).conjTranspose*(W*V.conjTranspose)).PosSemidef := by
  classical
  have hQ : (W*V.conjTranspose).conjTranspose*(W*V.conjTranspose) = V*V.conjTranspose := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc V * W.conjTranspose * (W * V.conjTranspose)
        = V * (W.conjTranspose * W) * V.conjTranspose := by simp only [Matrix.mul_assoc]
      _ = V*V.conjTranspose := by rw [hW, Matrix.mul_one]
  rw [hQ]
  have hP : (V*V.conjTranspose).conjTranspose = V*V.conjTranspose := by simp
  have hPP : (V*V.conjTranspose)*(V*V.conjTranspose)=V*V.conjTranspose := by
    calc (V*V.conjTranspose)*(V*V.conjTranspose)
        = V*(V.conjTranspose*V)*V.conjTranspose := by simp only [Matrix.mul_assoc]
      _ = V*V.conjTranspose := by rw [hV, Matrix.mul_one]
  have hgram : (1-V*V.conjTranspose).conjTranspose*(1-V*V.conjTranspose)
      = 1-V*V.conjTranspose := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP,
      sub_mul, one_mul, mul_sub, mul_one, hPP, sub_self, sub_zero]
  rw [← hgram]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- Equation (8)'s explicit selector is a contraction when the two work
vectors have norm one. The clock indices can coincide. -/
theorem historySelector_contraction {J m n : ℕ} (u v : Fin J)
    (ω z : Fin m → ℂ) (hω : cinner ω ω=1) (hz : cinner z z=1) :
    (1-(historySelector u v (kronRankOneId (n:=n) ω z)).conjTranspose *
      historySelector u v (kronRankOneId (n:=n) ω z)).PosSemidef := by
  classical
  rw [kronRankOneId_eq_mul, ← clockColumn_mul_adjoint]
  apply isometries_gram_complement
  · rw [clockColumn_gram, kronColId_conjTranspose_mul, hω, one_smul]
  · rw [clockColumn_gram, kronColId_conjTranspose_mul, hz, one_smul]

end Paper25
