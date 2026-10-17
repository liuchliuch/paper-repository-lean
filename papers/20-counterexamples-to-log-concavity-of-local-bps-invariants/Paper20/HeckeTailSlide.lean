import Paper20.HeckeTailProducts

namespace Paper20.HeckeNormalForm
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

/-- Sliding a generator through the actual increasing coset word uses
only genuine far-commutation and the length-three braid relation. -/
theorem gen_tail_slide {A : Type*} [Monoid A] {n : ℕ} (g : Fin n → A)
    (hb : ∀ i j, j.val=i.val+1 → g i*g j*g i=g j*g i*g j)
    (hf : ∀ i j, i.val+1 < j.val ∨ j.val+1 < i.val → g i*g j=g j*g i)
    (i : Fin n) (j : ℕ) (h : j < i.val) :
    g i*tailProduct g j=tailProduct g j*g ⟨i.val-1,by have := i.isLt; omega⟩ := by
  have aux : ∀ d : ℕ, ∀ j : ℕ, n-j=d → j < i.val →
      g i*tailProduct g j=tailProduct g j*g ⟨i.val-1,by have := i.isLt; omega⟩ := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro j hd hji
      have hj : j < n := by have := i.isLt; omega
      by_cases hi : i.val=j+1
      · have hj1 : j+1 < n := by have := i.isLt; omega
        have he : (⟨j+1,hj1⟩:Fin n)=i := Fin.ext hi.symm
        have hp : (⟨i.val-1,by have := i.isLt; omega⟩:Fin n)=⟨j,hj⟩ := Fin.ext (by change i.val-1=j; omega)
        rw [tail_step g j hj,tail_step g (j+1) hj1,he,hp]
        have hc := gen_tail_far g hf ⟨j,hj⟩ (j+2) (by change j+1 < j+2; omega)
        calc
          g i*(g ⟨j,hj⟩*(g i*tailProduct g (j+2)))=
              (g i*g ⟨j,hj⟩*g i)*tailProduct g (j+2) := by simp only [mul_assoc]
          _ = (g ⟨j,hj⟩*g i*g ⟨j,hj⟩)*tailProduct g (j+2) := by
            rw [← hb ⟨j,hj⟩ i hi]
          _ = (g ⟨j,hj⟩*g i)*(g ⟨j,hj⟩*tailProduct g (j+2)) := by simp only [mul_assoc]
          _ = (g ⟨j,hj⟩*g i)*(tailProduct g (j+2)*g ⟨j,hj⟩) := by rw [hc]
          _ = (g ⟨j,hj⟩*(g i*tailProduct g (j+2)))*g ⟨j,hj⟩ := by simp only [mul_assoc]
      · have hn : n-(j+1)<d := by omega
        calc
          _ = g i*(g ⟨j,hj⟩*tailProduct g (j+1)) := by rw [tail_step g j hj]
          _ = g ⟨j,hj⟩*(g i*tailProduct g (j+1)) := by
            rw [← mul_assoc,hf i ⟨j,hj⟩ (Or.inr (by change j+1 < i.val; omega)),mul_assoc]
          _ = g ⟨j,hj⟩*(tailProduct g (j+1)*g ⟨i.val-1,by have := i.isLt; omega⟩) := by
            rw [ih _ hn (j+1) rfl (by omega)]
          _ = _ := by rw [tail_step g j hj,mul_assoc]
  exact aux _ j rfl h

end
end Paper20.HeckeNormalForm
