import Paper37.RefinedCoreProgram
import Paper37.IntegerOutputProgram
import Paper37.CacheBuilderProgram

/-! Polynomial work bound for the evaluator of the fixed refined-core AST. -/
namespace Paper37.RefinedCoreProgram
open Paper37.BoundedLoop Paper37.CachedDP
open Paper37.IntegerOutputProgram (fold_work_le)
open Paper37.CacheBuilderProgram (sum_map_bound)

lemma unmarkedTerm_work (ρ : Env) : unmarkedTerm.work ρ≤100 := by
  simp [unmarkedTerm,coefficient,oldPair,epsilon,multiplicity,gap,Expr.work]
lemma markedTerm_work (ρ : Env) : markedTerm.work ρ≤150 := by
  simp [markedTerm,coefficient,oldPair,epsilon,multiplicity,gap,Expr.work]

lemma guardTerm_work (ρ : Env) (term : Expr) (B : ℕ) (h:term.work ρ≤B) :
    (guardTerm term).work ρ≤B+20 := by
  simp only [guardTerm,Expr.work]
  simp only [gap,epsilon,multiplicity,Expr.work]
  split_ifs <;> omega

lemma sumTerm_work (ρ : Env) (term : Expr) (B : ℕ)
    (ht : ∀σ,(guardTerm term).work σ≤B) :
    (sumTerm term).work ρ≤5+((ρ 7).natVal+1)*(B+6) := by
  have hh := fold_work_le ρ 9 10 loopBound (Expr.lit 0)
    (Expr.add (Expr.var 10) (guardTerm term)) (B+2) (by
      intro j hj a
      have h := ht (Function.update (Function.update ρ 9 (.nat j)) 10 a)
      simp only [Expr.work]
      omega)
  simpa only [sumTerm,loopBound,Expr.work,Expr.eval,Value.natVal,Nat.reduceAdd,Nat.add_assoc] using hh

lemma pairBody_work (ρ : Env) (N k : ℕ) (hk:ρ 7=.nat k) (hkN:k≤N) :
    (Expr.array [sumTerm unmarkedTerm,sumTerm markedTerm]).work ρ≤13+302*(N+1) := by
  have hg := sumTerm_work ρ unmarkedTerm 120 (fun σ=>guardTerm_work σ _ _ (unmarkedTerm_work σ))
  have hs := sumTerm_work ρ markedTerm 170 (fun σ=>guardTerm_work σ _ _ (markedTerm_work σ))
  rw [hk] at hg hs
  simp only [Value.natVal] at hg hs
  simp only [Expr.work,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  nlinarith

lemma tabulate_work_le (ρ : Env) (i : ℕ) (bound body : Expr) (M C : ℕ)
    (hM:(bound.eval ρ).natVal=M)
    (hc:∀j<M,body.work (Function.update ρ i (.nat j))≤C) :
    (Expr.tabulate i bound body).work ρ≤bound.work ρ+1+M*(C+3) := by
  rw [Expr.work,hM]
  have hh:=sum_map_bound (List.range M)
    (fun j=>body.work (Function.update ρ i (.nat j))+3) (C+3) (by
      intro j hj
      have h:=hc j (List.mem_range.mp hj)
      dsimp only
      omega)
  simp only [List.length_range] at hh
  exact Nat.add_le_add_left hh _

lemma layerLength_eval (ρ : Env) (N : ℕ) (h0:ρ 0=.nat N) :
    (layerLength.eval ρ).natVal=N+1 := by simp [layerLength,Expr.eval,h0,Value.natVal]

lemma layerLength_work (ρ : Env) : layerLength.work ρ=3 := by simp [layerLength,Expr.work]

lemma jLayer_work (ρ : Env) (N k : ℕ) (h0:ρ 0=.nat N) (hk:ρ 7=.nat k) (hkN:k≤N) :
    (Expr.tabulate 27 layerLength (.array [sumTerm unmarkedTerm,sumTerm markedTerm])).work ρ≤330*(N+1)^2 := by
  have hh:=tabulate_work_le ρ 27 layerLength (.array [sumTerm unmarkedTerm,sumTerm markedTerm])
    (N+1) (13+302*(N+1)) (layerLength_eval ρ N h0) (by
      intro j hj
      exact pairBody_work _ N k (by simpa using hk) hkN)
  rw [layerLength_work] at hh
  change _≤4+(N+1)*(13+302*(N+1)+3) at hh
  nlinarith

lemma uLayer_work (ρ : Env) (N k : ℕ) (h0:ρ 0=.nat N) (hk:ρ 7=.nat k) (hkN:k≤N) :
    (Expr.tabulate 8 layerLength (.tabulate 27 layerLength
      (.array [sumTerm unmarkedTerm,sumTerm markedTerm]))).work ρ≤340*(N+1)^3 := by
  have hh:=tabulate_work_le ρ 8 layerLength (.tabulate 27 layerLength
    (.array [sumTerm unmarkedTerm,sumTerm markedTerm])) (N+1) (330*(N+1)^2)
    (layerLength_eval ρ N h0) (by
      intro u hu
      exact jLayer_work _ N k (by simpa using h0) (by simpa using hk) hkN)
  rw [layerLength_work] at hh
  change _≤4+(N+1)*(330*(N+1)^2+3) at hh
  nlinarith

theorem stepProgram_work (ρ : Env) (N : ℕ) (h0:ρ 0=.nat N) :
    stepProgram.work ρ≤350*(N+1)^4 := by
  have hh:=tabulate_work_le ρ 7 layerLength (.tabulate 8 layerLength (.tabulate 27 layerLength
    (.array [sumTerm unmarkedTerm,sumTerm markedTerm]))) (N+1) (340*(N+1)^3)
    (layerLength_eval ρ N h0) (by
      intro k hk
      exact uLayer_work _ N k (by simpa using h0) (by simp) (by omega))
  rw [layerLength_work] at hh
  change stepProgram.work ρ≤4+(N+1)*(340*(N+1)^3+3) at hh
  have heq : (N+1)*(340*(N+1)^3+3)=340*(N+1)^4+3*(N+1) := by ring
  have hlin : N+1≤(N+1)^4 := le_self_pow₀ (by omega) (by decide)
  have hone : 1≤(N+1)^4 := one_le_pow₀ (by omega)
  nlinarith

private def baseBody : Expr := Expr.array [Expr.ifLT (.var 7) (.lit 1)
  (.ifLT (.var 8) (.lit 1) (.ifLT (.var 27) (.lit 1) (.lit 1) (.lit 0)) (.lit 0)) (.lit 0),.lit 0]

lemma baseBody_work (ρ : Env) : baseBody.work ρ≤14 := by
  simp only [baseBody,Expr.work,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  split_ifs <;> omega

lemma baseJ_work (ρ : Env) (N : ℕ) (h0:ρ 0=.nat N) :
    (Expr.tabulate 27 layerLength baseBody).work ρ≤21*(N+1) := by
  have hh:=tabulate_work_le ρ 27 layerLength baseBody (N+1) 14 (layerLength_eval ρ N h0)
    (by intro j hj;exact baseBody_work _)
  rw [layerLength_work] at hh
  change _≤4+(N+1)*17 at hh
  omega

lemma baseU_work (ρ : Env) (N : ℕ) (h0:ρ 0=.nat N) :
    (Expr.tabulate 8 layerLength (.tabulate 27 layerLength baseBody)).work ρ≤30*(N+1)^2 := by
  have hh:=tabulate_work_le ρ 8 layerLength (.tabulate 27 layerLength baseBody)
    (N+1) (21*(N+1)) (layerLength_eval ρ N h0) (by
      intro u hu;exact baseJ_work _ N (by simpa using h0))
  rw [layerLength_work] at hh
  change _≤4+(N+1)*(21*(N+1)+3) at hh
  nlinarith

lemma baseProgram_work (ρ : Env) (N : ℕ) (h0:ρ 0=.nat N) :
    baseProgram.work ρ≤40*(N+1)^3 := by
  have hh:=tabulate_work_le ρ 7 layerLength (.tabulate 8 layerLength (.tabulate 27 layerLength baseBody))
    (N+1) (30*(N+1)^2) (layerLength_eval ρ N h0) (by
      intro k hk;exact baseU_work _ N (by simpa using h0))
  rw [layerLength_work] at hh
  change baseProgram.work ρ≤4+(N+1)*(30*(N+1)^2+3) at hh
  nlinarith

/-- The charge belongs to the very fixed syntax whose exactness was proved;
there is no separate caller-supplied operation count in this bound. -/
theorem coreProgram_work_quintic (ρ : Env) (N : ℕ) (h0:ρ 0=.nat N) :
    coreProgram.work ρ≤400*(N+1)^5 := by
  have hh := fold_work_le ρ 6 5 (Expr.var 0) baseProgram stepProgram (350*(N+1)^4) (by
    intro d hd old
    exact stepProgram_work _ N (by simpa using h0))
  rw [show (Expr.var 0).work ρ=1 by rw [Expr.work],
    show ((Expr.var 0).eval ρ).natVal=N by simp [Expr.eval,h0,Value.natVal]] at hh
  change coreProgram.work ρ≤1+baseProgram.work ρ+1+N*(350*(N+1)^4+4) at hh
  have hb:=baseProgram_work ρ N h0
  have hpow : (N+1)^3≤(N+1)^5 := Nat.pow_le_pow_right (by omega) (by decide)
  have hmul := Nat.mul_le_mul_right (350*(N+1)^4+4) (show N≤N+1 by omega)
  have heq : (N+1)*(350*(N+1)^4+4)=350*(N+1)^5+4*(N+1) := by ring
  have hlin : N+1≤(N+1)^5 := le_self_pow₀ (by omega) (by decide)
  have hone : 1≤(N+1)^5 := one_le_pow₀ (by omega)
  nlinarith

end Paper37.RefinedCoreProgram
