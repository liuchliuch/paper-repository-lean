import Paper37.BoundedLoopFlat

namespace Paper37.BoundedLoop

/-- Peak bound for the very tabulation evaluator, including the completed
finite array and the representation of each evaluated body. -/
lemma tabulate_peak_le (x : ℕ) (n body : Expr) (ρ : Env) (M P Q : ℕ)
    (hM : (n.eval ρ).natVal=M) (hn : n.peak ρ≤P)
    (hb : ∀i<M,body.peak (Function.update ρ x (.nat i))≤Q) :
    (Expr.tabulate x n body).peak ρ≤(M+1)*Q+P+2 := by
  rw [Expr.peak]
  apply max_le
  · simp only [Expr.eval,Value.representationSize,List.map_map,hM]
    have hh := list_sum_compare (List.range M)
      (fun i => (body.eval (Function.update ρ x (.nat i))).representationSize) (fun _ => Q)
      (by intro i hi;exact (representationSize_le_peak body _).trans (hb i (List.mem_range.mp hi)))
    simp only [List.map_const',List.length_range,List.sum_replicate] at hh
    simp only [Function.comp_def,nsmul_eq_mul] at hh ⊢
    nlinarith
  · apply max_le (by nlinarith [hn])
    rw [hM]
    apply list_foldl_max_le _ _ _ (by omega)
    intro p hp
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
    have hh := hb i (List.mem_range.mp hi)
    nlinarith

end Paper37.BoundedLoop
