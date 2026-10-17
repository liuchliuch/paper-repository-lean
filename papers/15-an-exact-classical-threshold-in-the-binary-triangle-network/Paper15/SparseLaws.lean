import Paper15.FiniteLaws

noncomputable section
namespace Paper15
open Finset BigOperators Matrix
namespace Law
variable {α : Type*} [Fintype α]

/-- Two expectations are fixed while a third is increased, with at most
three positive probabilities at the optimum. -/
theorem exists_sparse (q : Law α) (f g h : α → ℝ) :
    ∃ r : Law α, {x | 0 < r x}.toFinset.card ≤ 3 ∧
      r.avg f = q.avg f ∧ r.avg g = q.avg g ∧ q.avg h ≤ r.avg h := by
  classical
  let e := Fintype.equivFin α
  let A : Matrix (Fin 2) (Fin (Fintype.card α)) ℝ :=
    fun u i => if u=0 then f (e.symm i) else g (e.symm i)
  let b : Fin 2 → ℝ := ![q.avg f,q.avg g]
  let x : Fin (Fintype.card α) → ℝ := fun i => q (e.symm i)
  have hx : LPFeasible A b x := by
    refine ⟨fun i => q.nonneg _,?_,?_⟩
    · ext u
      fin_cases u
      · simpa [A,b,x,mulVec,dotProduct,avg,mul_comm] using e.symm.sum_comp (fun a => f a*q a)
      · simpa [A,b,x,mulVec,dotProduct,avg,mul_comm] using e.symm.sum_comp (fun a => g a*q a)
    · simpa [x] using e.symm.sum_comp q.weight |>.trans q.sum_eq
  obtain ⟨y,hy,hs,hmax⟩ := exists_sparse_LP_optimizer A b (fun i => h (e.symm i)) hx
  let r : Law α := ⟨fun a => y (e a),fun a => hy.1 _,by simpa using e.sum_comp y |>.trans hy.2.2⟩
  have havg (k : α → ℝ) : r.avg k = ∑ i, k (e.symm i) * y i := by
    unfold avg
    rw [← e.symm.sum_comp (fun a => r a*k a)]
    simp [avg,r,mul_comm]
  have hcard : {a | 0 < r a}.toFinset.card = {i | 0 < y i}.toFinset.card := by
    apply Finset.card_bij (fun a _ => e a)
    · simp [r]
    · intro a _ a' _ he
      exact e.injective he
    · intro i hi
      exact ⟨e.symm i,by simpa [r] using hi,by simp⟩
  refine ⟨r,hcard.le.trans hs,?_,?_,?_⟩
  · have he := congrFun hy.2.1 0
    simpa [A,b,mulVec,dotProduct,havg,mul_comm] using he
  · have he := congrFun hy.2.1 1
    simpa [A,b,mulVec,dotProduct,havg,mul_comm] using he
  · rw [havg]
    have he : (∑ i, h (e.symm i) * x i) = q.avg h := by
      simpa [x,avg,mul_comm] using e.symm.sum_comp (fun a => q a*h a)
    simpa [he] using hmax x hx

end Law
end Paper15
