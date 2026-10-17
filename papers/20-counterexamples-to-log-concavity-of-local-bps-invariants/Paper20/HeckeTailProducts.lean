import Mathlib

namespace Paper20.HeckeNormalForm
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

/-- The actual increasing coset word T_j T_(j+1)...T_(n-1), with the
empty word equal to one beyond the final generator. -/
def tailProduct {A : Type*} [Monoid A] {n : ℕ} (g : Fin n → A) (j : ℕ) : A :=
  if hj : j < n then g ⟨j,hj⟩*tailProduct g (j+1) else 1
termination_by n-j

theorem tail_step {A : Type*} [Monoid A] {n : ℕ} (g : Fin n → A) (j : ℕ) (hj : j < n) :
    tailProduct g j=g ⟨j,hj⟩*tailProduct g (j+1) := by
  rw [tailProduct,dif_pos hj]

theorem tail_ge {A : Type*} [Monoid A] {n : ℕ} (g : Fin n → A) (j : ℕ) (hj : n≤j) :
    tailProduct g j=1 := by
  rw [tailProduct,dif_neg (by omega : ¬(j < n))]

/-- A generator at distance at least two commutes with the complete
actual tail word, proved by its finite word recursion. -/
theorem gen_tail_far {A : Type*} [Monoid A] {n : ℕ} (g : Fin n → A)
    (hf : ∀ i j, i.val+1 < j.val ∨ j.val+1 < i.val → g i*g j=g j*g i)
    (i : Fin n) (j : ℕ) (h : i.val+1 < j) :
    g i*tailProduct g j=tailProduct g j*g i := by
  have aux : ∀ d : ℕ, ∀ j : ℕ, n-j=d → i.val+1 < j →
      g i*tailProduct g j=tailProduct g j*g i := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro j hd hfar
      by_cases hj : j < n
      · have hn : n-(j+1)<d := by omega
        calc
          _ = g i*(g ⟨j,hj⟩*tailProduct g (j+1)) := by rw [tail_step g j hj]
          _ = g ⟨j,hj⟩*(g i*tailProduct g (j+1)) := by
            rw [← mul_assoc,hf i ⟨j,hj⟩ (Or.inl hfar),mul_assoc]
          _ = g ⟨j,hj⟩*(tailProduct g (j+1)*g i) := by
            rw [ih _ hn (j+1) rfl (by omega)]
          _ = _ := by rw [tail_step g j hj,mul_assoc]
      · rw [tail_ge g j (by omega),mul_one,one_mul]
  exact aux _ j rfl h

/-- The predecessor generator extends the actual coset word by one. -/
theorem gen_tail_predecessor {A : Type*} [Monoid A] {n : ℕ} (g : Fin n → A)
    (i : Fin n) (j : ℕ) (h : j=i.val+1) :
    g i*tailProduct g j=tailProduct g i.val := by
  rw [tail_step g i.val i.isLt,← h]

/-- The repeated first generator reduces by the exact quadratic relation
inside the actual tail word. -/
theorem gen_tail_same {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    {n : ℕ} (z : R) (g : Fin n → A) (hq : ∀ i, g i*g i=z • g i+1) (i : Fin n) :
    g i*tailProduct g i.val=z • tailProduct g i.val+tailProduct g (i.val+1) := by
  calc
    _ = (g i*g i)*tailProduct g (i.val+1) := by rw [tail_step g i.val i.isLt,mul_assoc]
    _ = (z • g i+1)*tailProduct g (i.val+1) := by rw [hq]
    _ = z • (g i*tailProduct g (i.val+1))+tailProduct g (i.val+1) := by
      rw [add_mul,smul_mul_assoc,one_mul]
    _ = _ := by rw [tail_step g i.val i.isLt]

end
end Paper20.HeckeNormalForm
