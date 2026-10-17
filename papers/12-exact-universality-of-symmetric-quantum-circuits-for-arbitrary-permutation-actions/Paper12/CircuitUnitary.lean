import Paper12.Tensor
import Paper12.Threshold
noncomputable section
namespace Paper12
open Matrix Complex Classical
variable {J : Type*} [Fintype J]

theorem unitary_product {A B : Op J} (ha : Aᴴ * A = 1) (hb : Bᴴ * B = 1) :
    (A * B)ᴴ * (A * B) = 1 := by
  rw [Matrix.conjTranspose_mul]
  calc Bᴴ * Aᴴ * (A * B) = Bᴴ * (Aᴴ * A) * B := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [ha, Matrix.mul_one, hb]

theorem Gate.unitary_isUnitary (g : Gate J) : g.unitaryᴴ * g.unitary = 1 := by
  cases g with
  | one g => exact g.unitary_isUnitary
  | thr g => exact g.isUnitary

theorem Layer.unitary_isUnitary (L : Layer J) : L.unitaryᴴ * L.unitary = 1 := by
  unfold Layer.unitary
  rw [dif_pos (pairwiseCommute_to_set _ L.commute)]
  apply Finset.noncommProd_induction (p := fun A : Op J => Aᴴ * A = 1)
  · intro A B ha hb
    exact unitary_product ha hb
  · simp
  · intro g _
    exact g.unitary_isUnitary

theorem Circuit.unitary_isUnitary (C : Circuit J) : C.unitaryᴴ * C.unitary = 1 := by
  unfold Circuit.unitary
  have h : ∀ (ls : List (Layer J)),
      ((ls.map Layer.unitary).foldr (· * ·) 1)ᴴ *
        ((ls.map Layer.unitary).foldr (· * ·) 1) = 1 := by
    intro ls
    induction ls with
    | nil => simp
    | cons L ls ih =>
      simp only [List.map_cons, List.foldr_cons]
      exact unitary_product L.unitary_isUnitary ih
  exact h C.layers
end Paper12
