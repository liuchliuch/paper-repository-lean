import Paper20.HookSum

namespace Paper20
set_option maxHeartbeats 1000000

theorem hook_parity_aux (xs : List ℕ) :
    (xs.sum+xs.countP (fun a => a%2=0))%2 = xs.length%2 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    by_cases ha : a%2=0
    · simp only [List.sum_cons, List.countP_cons, ha, decide_true, Bool.true_eq,
        ↓reduceIte, List.length_cons]
      omega
    · have ho : a%2=1 := by omega
      simp only [List.sum_cons, List.countP_cons, ha, decide_false, Bool.false_eq_true,
        ↓reduceIte, List.length_cons]
      omega

/-- The even-hook count and content have the same parity, exactly as
required in the quantum-integer normalization of (18)--(21). -/
theorem Part.hook_content_parity (p : Part n) :
    (partsEvenHooks p.parts:ℤ)%2 = contentOf p.parts%2 := by
  have hg := hook_parity_aux (hooksOf p.parts)
  rw [hooksOf_length_of_mem_partitionsOf p.mem_partitionsOf] at hg
  change ((hooksOf p.parts).sum+partsEvenHooks p.parts)%2=n%2 at hg
  have hs := p.hook_sum
  have hc := p.contentOf_eq_nu_difference
  have hsz := congrArg (fun t : ℕ => (t:ℤ)) hs
  push_cast at hsz
  omega

end Paper20
