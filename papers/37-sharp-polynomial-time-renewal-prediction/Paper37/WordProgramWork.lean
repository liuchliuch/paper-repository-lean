import Paper37.WordProgram
import Paper37.CachedCoreWork

namespace Paper37.WordProgram
open Paper37.BoundedLoop Paper37.CachedCoreProgram
set_option linter.unusedSimpArgs false
private abbrev v := Expr.var
private abbrev n := Expr.lit

lemma histogramIncrement_work (ρ : Env) (H : ℕ) (hH : ρ 0=.nat H) :
    histogramIncrement.work ρ≤100*(H+1) := by
  let cell : Expr := .ifLT (v 43) (.add (.get (v 42) (n 0)) (n 1))
    (.get (.get (v 42) (n 2)) (v 43))
    (.ifLT (.add (.get (v 42) (n 0)) (n 1)) (v 43)
      (.get (.get (v 42) (n 2)) (v 43))
      (.add (.get (.get (v 42) (n 2)) (v 43)) (n 1)))
  have hc (σ : Env) : cell.work σ≤50 := by
    simp only [cell,Expr.work]
    split_ifs <;> omega
  have hs:=list_sum_bound (List.range (H+1))
    (fun i => cell.work (Function.update ρ 43 (.nat i))+3) 53
    (by intro i hi;dsimp only;have hh:=hc (Function.update ρ 43 (.nat i));omega)
  simp only [List.length_range] at hs
  simp only [histogramIncrement,Expr.work,Expr.eval,hH,Value.natVal]
  simp only [cell,Expr.work,Expr.eval,Value.natVal] at hs
  omega


lemma parserStep_work (ρ : Env) (H : ℕ) (hH : ρ 0=.nat H) :
    parserStep.work ρ≤120*(H+1) := by
  have hh:=histogramIncrement_work ρ H hH
  simp only [parserStep,Expr.work,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  split_ifs <;> omega

lemma parserBase_work (ρ : Env) (H : ℕ) (hH : ρ 0=.nat H) :
    parserBase.work ρ≤20*(H+1) := by
  simp [parserBase,Expr.work,Expr.eval,hH,Value.natVal]
  omega

/-- Actual evaluator work of constructing the three parsed statistics,
including every histogram array write. -/
theorem parserProgram_work (ρ : Env) (H : ℕ) (x : List Bool)
    (hH : ρ 0=.nat H) (hx : ρ 40=wordValue x) :
    parserProgram.work ρ≤150*(H+1)*(x.length+1) := by
  have hb:=parserBase_work ρ H hH
  have hf:=foldl_charge_bound (x.map bitValue)
    (fun val bit => parserStep.eval (Function.update (Function.update ρ 41 bit) 42 val))
    (fun val bit => parserStep.work (Function.update (Function.update ρ 41 bit) 42 val))
    (120*(H+1)) (by
      intro val bit hi
      exact parserStep_work _ H (by simpa using hH)) (parserBase.eval ρ) 0
  simp only [List.length_map,zero_add] at hf
  simp only [parserProgram,Expr.work,Expr.eval,hx,wordValue,Value.arrayVal]
  nlinarith

lemma dropProgram_work (ρ : Env) (x : List Bool) (d : ℕ)
    (hx : ρ 40=wordValue x) (hd : ρ 44=.nat d) :
    dropProgram.work ρ≤20*(x.length+1) := by
  simp [dropProgram,Expr.work,Expr.eval,hx,hd,wordValue,Value.arrayVal,Value.natVal]
  omega

lemma appendProgram_work (ρ : Env) (x : List Bool) (hx : ρ 40=wordValue x) :
    appendProgram.work ρ≤20*(x.length+1) := by
  have hs:=list_sum_bound (List.range (x.length+1))
    (fun i => (Expr.ifLT (.var 45) (.length (.var 40)) (.get (.var 40) (.var 45)) (.var 46)).work
      (Function.update ρ 45 (.nat i))+3) 12 (by
      intro i hi
      simp only [Expr.work]
      split_ifs <;> omega)
  simp only [List.length_range,Expr.work,Expr.eval,Value.natVal] at hs
  simp only [appendProgram,Expr.work,Expr.eval,hx,wordValue_length,Value.natVal]
  omega

lemma reverseProgram_work (ρ : Env) (x : List Bool) (hx : ρ 40=wordValue x) :
    reverseProgram.work ρ≤20*(x.length+1) := by
  simp [reverseProgram,Expr.work,Expr.eval,hx,wordValue,Value.arrayVal,Value.natVal]
  omega

lemma firstIndexProgram_work (ρ : Env) (x : List Bool) (hx : ρ 40=wordValue x) :
    firstIndexProgram.work ρ≤40*(x.length+1) := by
  have hr:=reverseProgram_work ρ x hx
  have he:=reverseProgram_eval ρ x hx
  have hf:=foldl_charge_bound (x.reverse.map bitValue)
    (fun val bit => (Expr.ifLT (.lit 0) (.var 41) (.lit 0) (.add (.var 44) (.lit 1))).eval
      (Function.update (Function.update ρ 41 bit) 44 val))
    (fun val bit => (Expr.ifLT (.lit 0) (.var 41) (.lit 0) (.add (.var 44) (.lit 1))).work
      (Function.update (Function.update ρ 41 bit) 44 val)) 6 (by
      intro val bit hi
      simp only [Expr.work]
      split_ifs <;> omega) (.nat 0) 0
  simp only [List.length_map,List.length_reverse,zero_add,Expr.work,Expr.eval] at hf
  simp only [firstIndexProgram,Expr.work,he,wordValue,Value.arrayVal,Expr.work,Expr.eval]
  omega

end Paper37.WordProgram
