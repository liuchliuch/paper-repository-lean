import Paper37.AnytimeProgram
import Paper37.UniformPredictionMachine

namespace Paper37.AnytimeProgram
open Finset Paper37.BoundedLoop Paper37.WordProgram Paper37.AnytimePrediction
open Paper37.IntegerPredictorProgram Paper37.CachedCoreProgram

lemma epochStep_work (ρ : Env) : epochStep.work ρ≤8 := by
  simp only [epochStep,Expr.work]
  split_ifs <;> omega

lemma epochProgram_work (ρ : Env) (T : ℕ) (hT : ρ 70=.nat T) :
    epochProgram.work ρ≤3+12*T := by
  unfold epochProgram
  rw [Expr.work]
  have hh := foldl_charge_bound (List.range T)
    (fun vv j => epochStep.eval (Function.update (Function.update ρ 71 (.nat j)) 72 vv))
    (fun vv j => epochStep.work (Function.update (Function.update ρ 71 (.nat j)) 72 vv))
    8 (by intro vv j hj;exact epochStep_work _) (.nat 1) 0
  simp only [List.length_range,zero_add] at hh
  simp only [Expr.work,Expr.eval,hT,Value.natVal]
  omega

/-- One actual horizon-free query is fourth-degree arithmetic time in the
observed history length, including epoch discovery and suffix extraction. -/
theorem program_work (ρ : Env) (x : List Bool) (hx : ρ 40=wordValue x) :
    program.work ρ≤3000*(x.length+2)^4 := by
  let H := epochLength (epochIndex x.length)
  let σ := Function.update ρ 70 (.nat (x.length+1))
  let τ := Function.update σ 0 (.nat H)
  let υ := Function.update τ 44 (.nat (H-1))
  let ω := Function.update υ 40 (wordValue (x.drop (H-1)))
  have he := epochProgram_eval σ x.length (by simp [σ])
  have hew := epochProgram_work σ (x.length+1) (by simp [σ])
  have hd := dropProgram_eval υ x (H-1) (by simpa [υ,τ,σ] using hx) (by simp [υ])
  have hdw := dropProgram_work υ x (H-1) (by simpa [υ,τ,σ] using hx) (by simp [υ])
  have hlt : (x.drop (H-1)).length<H := by
    simpa [H,epochStart,epochLength] using within_epoch_prefix_lt x
  have hcw := conditionalProgram_work ω H (x.drop (H-1)) (by simp [ω,υ,τ]) (by simp [ω]) hlt
  have hH : H≤x.length+1 := (epochIndex_bounds x.length).1
  have hpow : (H+1)^4≤(x.length+2)^4 := Nat.pow_le_pow_left (by omega) _
  have hlin : x.length+1≤(x.length+2)^4 := by
    have hh : x.length+2≤(x.length+2)^4 := le_self_pow₀ (by omega) (by decide)
    omega
  have hone : 1≤(x.length+2)^4 := by
    have hh : 0<(x.length+2)^4 := by positivity
    omega
  rw [program,Expr.work]
  rw [show (Expr.add (.length (.var 40)) (.lit 1)).eval ρ=.nat (x.length+1) by
    simp [Expr.eval,hx,wordValue_length,Value.natVal]]
  rw [show (Expr.add (.length (.var 40)) (.lit 1)).work ρ=4 by simp [Expr.work]]
  change 4+1+(Expr.bind 0 epochProgram _).work σ≤_
  rw [Expr.work,he]
  change 4+1+(epochProgram.work σ+1+(Expr.bind 44 (.sub (.var 0) (.lit 1)) _).work τ)≤_
  rw [Expr.work,show (Expr.sub (.var 0) (.lit 1)).eval τ=.nat (H-1) by
    simp [Expr.eval,τ,Value.natVal]]
  rw [show (Expr.sub (.var 0) (.lit 1)).work τ=3 by simp [Expr.work]]
  change 4+1+(epochProgram.work σ+1+(3+1+(Expr.bind 40 dropProgram conditionalProgram).work υ))≤_
  rw [Expr.work,hd]
  change 4+1+(epochProgram.work σ+1+(3+1+(dropProgram.work υ+1+conditionalProgram.work ω)))≤_
  nlinarith

def cumulativeWork (x : List Bool) (N : ℕ) : ℕ :=
  ∑t∈range N,program.work (Paper37.BoundedLoopEncoding.inputEnv
    (Paper37.UniformPredictionMachine.sourceInputs (x.take t)))

/-- Through time N the single restart algorithm performs at most a fifth
degree number of arithmetic operations on the actual successive histories. -/
theorem cumulativeWork_le (x : List Bool) (N : ℕ) :
    cumulativeWork x N≤3000*(N+1)^5 := by
  have hh : cumulativeWork x N≤∑_t∈range N,3000*(N+1)^4 := by
    apply sum_le_sum
    intro t ht
    have hw := program_work _ (x.take t) (Paper37.UniformPredictionMachine.sourceInputs_word _)
    have hlen : (x.take t).length≤t := List.length_take_le _ _
    have htp : (x.take t).length+2≤N+1 := by have hh := mem_range.mp ht;omega
    exact hw.trans (Nat.mul_le_mul_left 3000 (Nat.pow_le_pow_left htp 4))
  simp only [sum_const,card_range,smul_eq_mul] at hh
  calc
    _ ≤ N*(3000*(N+1)^4) := hh
    _ ≤ (N+1)*(3000*(N+1)^4) := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring

end Paper37.AnytimeProgram
