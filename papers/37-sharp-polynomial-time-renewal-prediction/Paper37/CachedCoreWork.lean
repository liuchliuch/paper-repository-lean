import Paper37.CachedCoreProgram

namespace Paper37.CachedCoreProgram
open Finset Paper37.BoundedLoop

lemma list_sum_bound {α : Type*} (xs : List α) (f : α → ℕ) (B : ℕ)
    (hf : ∀x∈xs,f x≤B) : (xs.map f).sum≤xs.length*B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hh := ih (by intro y hy; exact hf y (by simp [hy]))
    have hx := hf x (by simp)
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

lemma foldl_charge_bound {α : Type*} (xs : List α) (step : Value → α → Value)
    (cost : Value → α → ℕ) (B : ℕ) (hc : ∀v,∀i∈xs,cost v i≤B)
    (a : Value) (w : ℕ) :
    (xs.foldl (fun vw i => (step vw.1 i,vw.2+cost vw.1 i+4)) (a,w)).2 ≤
      w+xs.length*(B+4) := by
  induction xs generalizing a w with
  | nil => simp
  | cons i xs ih =>
    have hh := ih (by intro v j hj; exact hc v j (by simp [hj])) (step a i) (w+cost a i+4)
    have hi := hc a i (by simp)
    simp only [List.foldl_cons,List.length_cons] at *
    nlinarith

lemma unmarkedTerm_work (ρ : Env) : unmarkedTerm.work ρ=31 := by
  simp [unmarkedTerm,coefficient,oldPair,multiplicity,gap,Expr.work]

lemma markedTerm_work (ρ : Env) : markedTerm.work ρ=54 := by
  simp [markedTerm,coefficient,oldPair,multiplicity,gap,Expr.work]

lemma loopBound_work (ρ : Env) : loopBound.work ρ=9 := by simp [loopBound,gap,Expr.work]
lemma layerLength_work (ρ : Env) : layerLength.work ρ=3 := by simp [layerLength,Expr.work]

lemma sumTerm_work_le (ρ : Env) (term : Expr) (B k u d : ℕ)
    (ht : ∀σ,term.work σ≤B) (h7 : ρ 7=.nat k) (h8 : ρ 8=.nat u) (h6 : ρ 6=.nat d) :
    (sumTerm term).work ρ ≤ 11+(k+1)*(B+6) := by
  have he : (loopBound.eval ρ).natVal=min k (u/(d+1))+1 := by
    simp [loopBound,gap,Expr.eval,h7,h8,h6,Value.natVal]
  unfold sumTerm
  rw [Expr.work,loopBound_work,he]
  have hh := foldl_charge_bound (List.range (min k (u/(d+1))+1))
    (fun vv i => (Expr.add (Expr.var 10) term).eval
      (Function.update (Function.update ρ 9 (.nat i)) 10 vv))
    (fun vv i => (Expr.add (Expr.var 10) term).work
      (Function.update (Function.update ρ 9 (.nat i)) 10 vv)) (B+2)
    (by intro vv i hi; have ht' := ht (Function.update (Function.update ρ 9 (.nat i)) 10 vv)
        simp only [Expr.work]; omega) (.nat 0) 0
  simp only [List.length_range,zero_add] at hh
  simp only [Expr.work,Expr.eval] at hh ⊢
  have hBB : B+2+4=B+6 := by omega
  rw [hBB] at hh
  have hm : min k (u/(d+1))+1≤k+1 := Nat.add_le_add_right (min_le_left _ _) 1
  have hp := Nat.mul_le_mul_right (B+6) hm
  omega

lemma cell_work_le (ρ : Env) (N k u d : ℕ)
    (hk : k≤N) (h7 : ρ 7=.nat k) (h8 : ρ 8=.nat u) (h6 : ρ 6=.nat d) :
    (Expr.array [sumTerm unmarkedTerm,sumTerm markedTerm]).work ρ ≤ 25+97*(N+1) := by
  have hg := sumTerm_work_le ρ unmarkedTerm 31 k u d (by intro σ; rw [unmarkedTerm_work]) h7 h8 h6
  have hs := sumTerm_work_le ρ markedTerm 54 k u d (by intro σ; rw [markedTerm_work]) h7 h8 h6
  simp only [Expr.work,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega

/-- Counts every arithmetic expression, safe array access, write and bounded
loop control in the actual first-order materialized recurrence term. -/
theorem stepProgram_work_le (ρ : Env) (N d : ℕ) (h0 : ρ 0=.nat N) (h6 : ρ 6=.nat d) :
    stepProgram.work ρ≤136*(N+1)^3 := by
  have hlen : (layerLength.eval ρ).natVal=N+1 := by simp [layerLength,Expr.eval,h0,Value.natVal]
  have hrow : ∀k∈List.range (N+1),
      (Expr.tabulate 8 layerLength (Expr.array [sumTerm unmarkedTerm,sumTerm markedTerm])).work
        (Function.update ρ 7 (.nat k))≤4+(N+1)*(28+97*(N+1)) := by
    intro k hk
    have hk' : k≤N := by have hh := List.mem_range.mp hk; omega
    have hlen' : (layerLength.eval (Function.update ρ 7 (.nat k))).natVal=N+1 := by
      simp [layerLength,Expr.eval,Function.update,h0,Value.natVal]
    rw [Expr.work,layerLength_work,hlen']
    have hh := list_sum_bound (List.range (N+1))
      (fun u => (Expr.array [sumTerm unmarkedTerm,sumTerm markedTerm]).work
        (Function.update (Function.update ρ 7 (.nat k)) 8 (.nat u))+3)
      (28+97*(N+1)) (by
        intro u hu
        have hc := cell_work_le (Function.update (Function.update ρ 7 (.nat k)) 8 (.nat u)) N k u d hk'
          (by simp [Function.update]) (by simp [Function.update]) (by simp [Function.update,h6])
        dsimp only
        omega)
    simp only [List.length_range] at hh
    omega
  unfold stepProgram
  rw [Expr.work,layerLength_work,hlen]
  have hh := list_sum_bound (List.range (N+1))
    (fun k => (Expr.tabulate 8 layerLength (Expr.array [sumTerm unmarkedTerm,sumTerm markedTerm])).work
      (Function.update ρ 7 (.nat k))+3) (7+(N+1)*(28+97*(N+1))) (by
    intro k hk
    have hr := hrow k hk
    dsimp only
    omega)
  simp only [List.length_range] at hh
  have h1 : 1≤N+1 := by omega
  have h2 : (N+1)≤(N+1)^3 := le_self_pow₀ h1 (by decide)
  have h3 : (N+1)^2≤(N+1)^3 := Nat.pow_le_pow_right h1 (by decide)
  nlinarith

lemma baseCell_work_le (ρ : Env) :
    (Expr.array [.ifLT (.var 7) (.lit 1)
      (.ifLT (.var 8) (.lit 1) (.lit 1) (.lit 0)) (.lit 0),.lit 0]).work ρ≤11 := by
  simp only [Expr.work,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  split_ifs <;> norm_num

lemma baseProgram_work_le (ρ : Env) (N : ℕ) (h0 : ρ 0=.nat N) :
    baseProgram.work ρ≤25*(N+1)^2 := by
  have hlen : (layerLength.eval ρ).natVal=N+1 := by simp [layerLength,Expr.eval,h0,Value.natVal]
  let cell : Expr := .array [.ifLT (.var 7) (.lit 1)
      (.ifLT (.var 8) (.lit 1) (.lit 1) (.lit 0)) (.lit 0),.lit 0]
  have hrow : ∀k∈List.range (N+1),
      (Expr.tabulate 8 layerLength cell).work (Function.update ρ 7 (.nat k))≤4+14*(N+1) := by
    intro k hk
    have hlen' : (layerLength.eval (Function.update ρ 7 (.nat k))).natVal=N+1 := by
      simp [layerLength,Expr.eval,Function.update,h0,Value.natVal]
    rw [Expr.work,layerLength_work,hlen']
    have hh := list_sum_bound (List.range (N+1))
      (fun u => cell.work (Function.update (Function.update ρ 7 (.nat k)) 8 (.nat u))+3) 14 (by
        intro u hu
        have hc := baseCell_work_le (Function.update (Function.update ρ 7 (.nat k)) 8 (.nat u))
        change cell.work (Function.update (Function.update ρ 7 (.nat k)) 8 (.nat u))≤11 at hc
        dsimp only
        omega)
    simp only [List.length_range] at hh
    omega
  change (Expr.tabulate 7 layerLength (.tabulate 8 layerLength cell)).work ρ≤_
  rw [Expr.work,layerLength_work,hlen]
  have hh := list_sum_bound (List.range (N+1))
    (fun k => (Expr.tabulate 8 layerLength cell).work (Function.update ρ 7 (.nat k))+3)
    (7+14*(N+1)) (by intro k hk; have hh := hrow k hk; dsimp only; omega)
  simp only [List.length_range] at hh
  have h1 : 1≤N+1 := by omega
  have h2 : N+1≤(N+1)^2 := le_self_pow₀ h1 (by decide)
  nlinarith

/-- The charged evaluator of one fixed finite term performs at most a fourth
degree number of RAM operations. This includes all index arithmetic and loop
overhead, independently of the numerical size of the table entries. -/
theorem coreProgram_work_le (ρ : Env) (N : ℕ) (h0 : ρ 0=.nat N) :
    coreProgram.work ρ≤200*(N+1)^4 := by
  have hb := baseProgram_work_le ρ N h0
  unfold coreProgram
  rw [Expr.work]
  have hh := foldl_charge_bound (List.range N)
    (fun vv i => stepProgram.eval (Function.update (Function.update ρ 6 (.nat i)) 5 vv))
    (fun vv i => stepProgram.work (Function.update (Function.update ρ 6 (.nat i)) 5 vv))
    (136*(N+1)^3) (by
      intro vv i hi
      apply stepProgram_work_le _ N i
      · simp [Function.update,h0]
      · simp [Function.update]) (baseProgram.eval ρ) 0
  simp only [List.length_range,zero_add] at hh
  simp only [Expr.work,Expr.eval,h0,Value.natVal]
  have h1 : 1≤N+1 := by omega
  have h2 : (N+1)^2≤(N+1)^4 := Nat.pow_le_pow_right h1 (by decide)
  have h3 : (N+1)^3≤(N+1)^4 := Nat.pow_le_pow_right h1 (by decide)
  have hlin : N+1≤(N+1)^4 := le_self_pow₀ h1 (by decide)
  nlinarith

end Paper37.CachedCoreProgram
