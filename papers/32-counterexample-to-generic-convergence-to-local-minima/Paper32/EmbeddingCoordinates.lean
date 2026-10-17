import Paper32.EmbeddingMain
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! The product coordinates used in the proofs are the actual `n + 2` real
coordinates, via a specified linear equivalence. -/

open BigOperators

noncomputable section
namespace Paper32

/-- List the first two real coordinates followed by the `n` extra coordinates. -/
def embeddedCoordinates (n : ℕ) : EmbeddedPoint (Fin n) ≃ₗ[ℝ] (Fin (n+2) → ℝ) :=
  (LinearEquiv.prodAssoc ℝ ℝ ℝ (Fin n → ℝ)).trans
    (((LinearEquiv.refl ℝ ℝ).prodCongr
      (Fin.consLinearEquiv ℝ (fun _ : Fin (n+1) => ℝ))).trans
      (Fin.consLinearEquiv ℝ (fun _ : Fin (n+2) => ℝ)))

@[simp] theorem embeddedCoordinates_apply (n : ℕ) (z : EmbeddedPoint (Fin n)) :
    embeddedCoordinates n z = Fin.cons z.1.1 (Fin.cons z.1.2 z.2) := rfl

theorem embeddedPoint_finrank (n : ℕ) :
    Module.finrank ℝ (EmbeddedPoint (Fin n)) = n+2 := by
  rw [(embeddedCoordinates n).finrank_eq,Module.finrank_fin_fun]

/-- The source objective written directly on `Fin (n+2) → ℝ`. -/
def nativeEmbeddedObjective (n : ℕ) (z : Fin (n+2) → ℝ) : ℝ :=
  F (z 0,z (0:Fin (n+1)).succ) + 2*∑ i : Fin n, |z i.succ.succ|

/-- The coordinate model evaluates to precisely the source objective. -/
@[simp] theorem nativeEmbeddedObjective_coordinates (n : ℕ)
    (z : EmbeddedPoint (Fin n)) :
    nativeEmbeddedObjective n (embeddedCoordinates n z) = embeddedObjective z := by
  simp [nativeEmbeddedObjective,embeddedObjective]

/-- The source's tilted function in the same native finite coordinates. -/
def nativeEmbeddedTilt (n : ℕ) (v z : Fin (n+2) → ℝ) : ℝ :=
  nativeEmbeddedObjective n z - ∑ i, v i*z i

@[simp] theorem nativeEmbeddedTilt_coordinates (n : ℕ)
    (v z : EmbeddedPoint (Fin n)) :
    nativeEmbeddedTilt n (embeddedCoordinates n v) (embeddedCoordinates n z) =
      embeddedTilt v z := by
  rw [nativeEmbeddedTilt,nativeEmbeddedObjective_coordinates]
  simp [embeddedTilt,lin,Fin.sum_univ_succ]
  ring

/-- The actual Euclidean noise ball is also unchanged by listing the coordinates. -/
theorem nativeEuclideanBall_coordinates (n : ℕ) (r : ℝ)
    (z : EmbeddedPoint (Fin n)) :
    (∑ i, (embeddedCoordinates n z i)^2 ≤ r^2) ↔
      z ∈ embeddedEuclideanBall (Fin n) r := by
  simp [embeddedEuclideanBall,Fin.sum_univ_succ,add_assoc]

/-- The specified coordinate equivalence intertwines the actual SGD updates. -/
theorem embeddedCoordinates_update (n : ℕ) (z w ν : EmbeddedPoint (Fin n)) (a : ℝ) :
    embeddedCoordinates n (z-a • (w+ν)) = embeddedCoordinates n z -
      a • (embeddedCoordinates n w+embeddedCoordinates n ν) := by
  simp only [map_sub,map_smul,map_add]

end Paper32
