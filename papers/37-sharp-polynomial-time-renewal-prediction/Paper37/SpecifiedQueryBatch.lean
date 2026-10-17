import Paper37.IntegerPredictorProgramWork
import Paper37.IntegerQueryProgramPeak
import Paper37.AdaptiveQueryWork

/-! A specified finite query list is an actual input array. One fixed syntax
term traverses precisely that list; no enumeration of the prefix tree occurs.
The generic lemmas below are instantiated with the already proved complete
ordinary and adaptive conditional programs. -/
namespace Paper37.SpecifiedQueryBatch
open Paper37.BoundedLoop Paper37.WordProgram Paper37.CachedCoreProgram
set_option linter.unusedSimpArgs false

def wordsValue (qs : List (List Bool)) : Value := .array (qs.map wordValue)

/-- Horizon in slot0, the supplied query list in slot60, and a local index61.
Each query receives its selected word in slot40. -/
def program (query : Expr) : Expr := .tabulate 61 (.length (.var 60))
  (.bind 40 (.get (.var 60) (.var 61)) query)

lemma selected_word (ρ : Env) (qs : List (List Bool)) (i : ℕ) (hi : i<qs.length)
    (hqs : ρ 60=wordsValue qs) :
    (Expr.get (.var 60) (.var 61)).eval (Function.update ρ 61 (.nat i))=
      wordValue qs[i] := by
  simp [Expr.eval,Function.update_of_ne (by decide : (60:ℕ)≠61),hqs,wordsValue,
    Value.arrayVal,Value.natVal,List.getElem?_map,List.getElem?_eq_getElem hi]

lemma program_eval (query : Expr) (answer : List Bool → Value) (ρ : Env)
    (H : ℕ) (qs : List (List Bool)) (hH : ρ 0=.nat H) (hqs : ρ 60=wordsValue qs)
    (hvalid : ∀y∈qs,y.length<H)
    (hq : ∀σ y,σ 0=.nat H → σ 40=wordValue y → y.length<H → query.eval σ=answer y) :
    (program query).eval ρ=.array (qs.map answer) := by
  simp only [program,Expr.eval,hqs,wordsValue,Value.arrayVal,List.length_map,Value.natVal]
  congr 1
  apply List.ext_getElem (by simp)
  intro i hi₁ hi₂
  have hi : i<qs.length := by simpa using hi₂
  simp only [List.getElem_map,List.getElem_range]
  simp only [Function.update_of_ne (by decide : (60:ℕ)≠61),Function.update_self,hqs,wordsValue]
  simp only [List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some,Option.getD_some]
  apply hq
  · simpa using hH
  · simp
  · exact hvalid _ (List.getElem_mem hi)

lemma program_work (query : Expr) (ρ : Env) (H B : ℕ) (qs : List (List Bool))
    (hH : ρ 0=.nat H) (hqs : ρ 60=wordsValue qs) (hvalid : ∀y∈qs,y.length<H)
    (hq : ∀σ y,σ 0=.nat H → σ 40=wordValue y → y.length<H → query.work σ≤B) :
    (program query).work ρ≤3+qs.length*(B+7) := by
  have hs:=list_sum_bound (List.range qs.length)
    (fun i => (Expr.bind 40 (.get (.var 60) (.var 61)) query).work
      (Function.update ρ 61 (.nat i))+3) (B+7) (by
        intro i hi
        have hi' : i<qs.length := List.mem_range.mp hi
        have hw:=hq (Function.update (Function.update ρ 61 (.nat i)) 40 (wordValue qs[i]))
          qs[i] (by simpa using hH) (by simp) (hvalid _ (List.getElem_mem hi'))
        simp only [Expr.work]
        rw [selected_word ρ qs i hi' hqs]
        omega)
  simpa only [program,Expr.work,Expr.eval,hqs,wordsValue,Value.arrayVal,List.length_map,
    Value.natVal,List.length_range] using Nat.add_le_add_left hs 3

/-- Every supplied ordinary query is evaluated exactly by the same finite AST. -/
theorem standard_eval (ρ : Env) (H : ℕ) (qs : List (List Bool))
    (hH : ρ 0=.nat H) (hqs : ρ 60=wordsValue qs) (hvalid : ∀y∈qs,y.length<H) :
    (program Paper37.IntegerPredictorProgram.conditionalProgram).eval ρ=
      .array (qs.map (fun y => pairValue (Paper37.IntegerPredictor.conditionalPair H y))) :=
  program_eval _ _ ρ H qs hH hqs hvalid
    (fun σ y => Paper37.IntegerPredictorProgram.conditionalProgram_eval σ H y)

/-- Any specified C(H+1)-query batch uses O((H+1)^5) actual evaluator work,
including selection, loop control and all per-query preprocessing. -/
theorem standard_work (ρ : Env) (H C : ℕ) (qs : List (List Bool))
    (hH : ρ 0=.nat H) (hqs : ρ 60=wordsValue qs) (hvalid : ∀y∈qs,y.length<H)
    (hcount : qs.length≤C*(H+1)) :
    (program Paper37.IntegerPredictorProgram.conditionalProgram).work ρ≤
      3+2507*C*(H+1)^5 := by
  have hw:=program_work _ ρ H (2500*(H+1)^4) qs hH hqs hvalid
    (fun σ y => Paper37.IntegerPredictorProgram.conditionalProgram_work σ H y)
  have hp : 1≤(H+1)^4 := one_le_pow₀ (by omega)
  calc _ ≤3+qs.length*(2500*(H+1)^4+7) := hw
       _ ≤3+(C*(H+1))*(2507*(H+1)^4) := by gcongr <;> omega
       _ =_ := by ring

/-- The same batch traversal computes the adaptive mixture conditional,
using its actual mix-before-ratio program for each selected word. -/
theorem adaptive_eval (ρ : Env) (H : ℕ) (qs : List (List Bool))
    (hH : ρ 0=.nat H) (hqs : ρ 60=wordsValue qs) (hvalid : ∀y∈qs,y.length<H) :
    (program Paper37.AdaptiveQueryProgram.conditionalProgram).eval ρ=
      .array (qs.map (fun y => pairValue (Paper37.AdaptiveIntegerOutput.conditionalPair H y))) :=
  program_eval _ _ ρ H qs hH hqs hvalid
    (fun σ y => Paper37.AdaptiveQueryProgram.conditionalProgram_eval σ H y)

theorem adaptive_work (ρ : Env) (H C : ℕ) (qs : List (List Bool))
    (hH : ρ 0=.nat H) (hqs : ρ 60=wordsValue qs) (hvalid : ∀y∈qs,y.length<H)
    (hcount : qs.length≤C*(H+1)) :
    (program Paper37.AdaptiveQueryProgram.conditionalProgram).work ρ≤
      3+5107*C*(H+1)^6 := by
  have hw:=program_work _ ρ H (5100*(H+1)^5) qs hH hqs hvalid
    (fun σ y => Paper37.AdaptiveQueryProgram.conditionalProgram_work σ H y)
  have hp : 1≤(H+1)^5 := one_le_pow₀ (by omega)
  calc _ ≤3+qs.length*(5100*(H+1)^5+7) := hw
       _ ≤3+(C*(H+1))*(5107*(H+1)^5) := by gcongr <;> omega
       _ =_ := by ring

end Paper37.SpecifiedQueryBatch
