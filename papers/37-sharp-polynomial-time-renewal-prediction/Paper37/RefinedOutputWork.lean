import Paper37.RefinedOutputProgram
import Paper37.RefinedCoreWork

/-! The fixed all-restrictions output AST has a fourth-degree evaluator
charge; its table is computed only once before this extraction. -/
namespace Paper37.RefinedOutputProgram
open Paper37.BoundedLoop
open Paper37.IntegerOutputProgram (fold_work_le denominatorProgram_work initialProgram_work)
open Paper37.RefinedCoreProgram (tabulate_work_le)

lemma prefixSum_work (ρ : Env) : prefixSum.work ρ≤5+17*((ρ 28).natVal+1) := by
  have hh:=fold_work_le ρ 29 30 (Expr.add (.var 28) (.lit 1)) (.lit 0)
    (.add (.var 30) tableMarked) 13 (by
      intro j hj a
      simp [Expr.work,tableMarked,kIndex])
  simpa only [prefixSum,Expr.work,Expr.eval,Value.natVal,Nat.reduceAdd,Nat.add_assoc,Nat.mul_comm] using hh

lemma finalTerm_work (ρ : Env) : finalTerm.work ρ≤19+17*((ρ 28).natVal+1) := by
  have hh:=prefixSum_work ρ
  have hk:kIndex.work ρ=3 := by simp [kIndex,Expr.work]
  have hc:(Expr.div (.var 13) (.get (.var 3) (.add (.var 11) kIndex))).work ρ=9 := by
    simp [Expr.work,kIndex]
  rw [finalTerm,Expr.work,Expr.work,hk,hc]
  omega

lemma guardedTerm_work (ρ : Env) : guardedTerm.work ρ≤24+17*((ρ 28).natVal+1) := by
  have hh:=finalTerm_work ρ
  rw [guardedTerm,Expr.work]
  have hk:kIndex.work ρ=3 := by simp [kIndex,Expr.work]
  rw [hk]
  simp only [Expr.work]
  split_ifs <;> omega

lemma totalFuture_update (ρ : Env) (x : ℕ) (a : Value) (hx1:x≠1) (hx12:x≠12) :
    (totalFuture.eval (Function.update ρ x a)).natVal=(totalFuture.eval ρ).natVal := by
  simp [totalFuture,Expr.eval,Function.update_apply,Ne.symm hx1,Ne.symm hx12]

lemma innerSum_work (ρ : Env) :
    innerSum.work ρ≤7+((totalFuture.eval ρ).natVal+1)*(30+17*((ρ 28).natVal+1)) := by
  have hh:=fold_work_le ρ 17 18 (Expr.add totalFuture (.lit 1)) (.lit 0)
    (.add (.var 18) guardedTerm) (26+17*((ρ 28).natVal+1)) (by
      intro u hu a
      have hg:=guardedTerm_work (Function.update (Function.update ρ 17 (.nat u)) 18 a)
      simp only [Function.update_of_ne (by decide : (28:ℕ)≠18),
        Function.update_of_ne (by decide : (28:ℕ)≠17)] at hg
      rw [Expr.work,Expr.work]
      omega)
  have hb:(Expr.add totalFuture (.lit 1)).work ρ=5 := by simp [Expr.work,totalFuture]
  have hv:((Expr.add totalFuture (.lit 1)).eval ρ).natVal=(totalFuture.eval ρ).natVal+1 := by
    simp only [Expr.eval,Value.natVal]
  rw [hb,hv,show (Expr.lit 0).work ρ=1 by rw [Expr.work]] at hh
  change innerSum.work ρ≤5+1+1+((totalFuture.eval ρ).natVal+1)*(26+17*((ρ 28).natVal+1)+4) at hh
  nlinarith

lemma outerSum_work (ρ : Env) :
    outerSum.work ρ≤5+(totalFuture.eval ρ).natVal*
      (13+((totalFuture.eval ρ).natVal+1)*(30+17*((ρ 28).natVal+1))) := by
  have hh:=fold_work_le ρ 15 16 totalFuture (.lit 0) (.add (.var 16) innerSum)
    (9+((totalFuture.eval ρ).natVal+1)*(30+17*((ρ 28).natVal+1))) (by
      intro k hk a
      have hi:=innerSum_work (Function.update (Function.update ρ 15 (.nat k)) 16 a)
      rw [totalFuture_update _ 16 _ (by decide) (by decide),
        totalFuture_update _ 15 _ (by decide) (by decide)] at hi
      simp only [Function.update_of_ne (by decide : (28:ℕ)≠16),
        Function.update_of_ne (by decide : (28:ℕ)≠15)] at hi
      rw [Expr.work,Expr.work]
      omega)
  have hb:totalFuture.work ρ=3 := by simp [Expr.work,totalFuture]
  rw [hb,show (Expr.lit 0).work ρ=1 by rw [Expr.work]] at hh
  change outerSum.work ρ≤3+1+1+(totalFuture.eval ρ).natVal*
    (9+((totalFuture.eval ρ).natVal+1)*(30+17*((ρ 28).natVal+1))+4) at hh
  nlinarith

lemma numeratorProgram_work (ρ : Env) (H : ℕ) (hT:(totalFuture.eval ρ).natVal≤H)
    (ht:(ρ 28).natVal≤H) : numeratorProgram.work ρ≤80*(H+1)^3 := by
  have ho:=outerSum_work ρ
  have hi:(Expr.ifLT (.var 28) (.var 31) (.lit 0)
    (.mul (.var 14) (.div (.var 13) (.get (.var 3) (.var 11))))).work ρ≤10 := by
    simp only [Expr.work]
    split_ifs <;> omega
  rw [numeratorProgram,Expr.work]
  have hbig : (totalFuture.eval ρ).natVal*
      (13+((totalFuture.eval ρ).natVal+1)*(30+17*((ρ 28).natVal+1)))≤
      H*(13+(H+1)*(30+17*(H+1))) := by
    apply Nat.mul_le_mul hT
    exact Nat.add_le_add_left (Nat.mul_le_mul (by omega) (by omega)) _
  nlinarith

lemma observedTypesProgram_work (ρ : Env) : observedTypesProgram.work ρ≤3+14*(ρ 0).natVal := by
  have hh:=fold_work_le ρ 19 20 (.var 0) (.lit 0)
    (.add (.var 20) (.ifLT (.lit 0) (.get (.var 4) (.add (.var 19) (.lit 1))) (.lit 1) (.lit 0))) 10 (by
      intro d hd a
      simp [Expr.work])
  simpa only [observedTypesProgram,Expr.work,Expr.eval,Nat.reduceAdd, Nat.mul_comm] using hh

/-- This bound is derived from the evaluator's own recursive work function for
one fixed all-restrictions syntax term, uniformly over every table content. -/
theorem outputProgram_work_quartic (ρ : Env) (H : ℕ) (hH:ρ 0=.nat H)
    (hT:(totalFuture.eval ρ).natVal≤H) : outputProgram.work ρ≤140*(H+1)^4 := by
  let ρD:=Function.update ρ 13 (Paper37.IntegerOutputProgram.denominatorProgram.eval ρ)
  let ρI:=Function.update ρD 14 (Paper37.IntegerOutputProgram.initialProgram.eval ρD)
  let ρO:=Function.update ρI 31 (observedTypesProgram.eval ρI)
  have hD:=denominatorProgram_work ρ
  have hI:=initialProgram_work ρD
  have hO:=observedTypesProgram_work ρI
  have htO:(totalFuture.eval ρO).natVal≤H := by
    dsimp [ρO,ρI,ρD]
    rw [totalFuture_update _ 31 _ (by decide) (by decide),
      totalFuture_update _ 14 _ (by decide) (by decide),totalFuture_update _ 13 _ (by decide) (by decide)]
    exact hT
  have htab:=tabulate_work_le ρO 28 (Expr.add (.var 0) (.lit 1)) numeratorProgram
    (H+1) (80*(H+1)^3) (by simp [Expr.eval,ρO,ρI,ρD,hH,Value.natVal]) (by
      intro t ht
      apply numeratorProgram_work _ H
      · rw [totalFuture_update _ 28 _ (by decide) (by decide)];exact htO
      · simp only [Function.update_self,Value.natVal];omega)
  have h0D:ρD 0=ρ 0 := by simp [ρD]
  have h0I:ρI 0=ρ 0 := by simp [ρI,ρD]
  rw [h0D,hH] at hI
  rw [h0I,hH] at hO
  rw [hH] at hD
  simp only [Value.natVal] at hD hI hO
  have hb:(Expr.add (.var 0) (.lit 1)).work ρO=3 := by simp [Expr.work]
  rw [hb] at htab
  have heq:(H+1)*(80*(H+1)^3+3)=80*(H+1)^4+3*(H+1) := by ring
  change outputProgram.work ρ≤_
  rw [outputProgram,Expr.work,Expr.work,Expr.work]
  change _+1+(_+1+(_+1+(Expr.tabulate 28 (Expr.add (.var 0) (.lit 1)) numeratorProgram).work ρO))≤_
  have hlin:H+1≤(H+1)^4 := le_self_pow₀ (by omega) (by decide)
  have hone:1≤(H+1)^4 := one_le_pow₀ (by omega)
  nlinarith

end Paper37.RefinedOutputProgram
