import Paper37.AnytimePrediction
import Paper37.IntegerPredictorProgramWork
import Paper37.IntegerQueryProgramPeak

/-! A single finite first-order program for the horizon-free dyadic restart
predictor. The largest power of two is computed by a bounded doubling loop. -/
namespace Paper37.AnytimeProgram
open Finset Paper37.BoundedLoop Paper37.WordProgram Paper37.AnytimePrediction
open Paper37.IntegerPredictorProgram Paper37.IntegerQueryProgramPeak
open Paper37.CachedCoreProgram
set_option maxRecDepth 3000

def epochStep : Expr := .ifLT (.var 70) (.mul (.lit 2) (.var 72))
  (.var 72) (.mul (.lit 2) (.var 72))

def epochProgram : Expr := .fold 71 72 (.var 70) (.lit 1) epochStep

def program : Expr := .bind 70 (.add (.length (.var 40)) (.lit 1))
  (.bind 0 epochProgram (.bind 44 (.sub (.var 0) (.lit 1))
    (.bind 40 dropProgram conditionalProgram)))

lemma epochProgram_eval (ρ : Env) (t : ℕ) (hT : ρ 70=.nat (t+1)) :
    epochProgram.eval ρ=.nat (epochLength (epochIndex t)) := by
  let J := epochIndex t
  have hb := epochIndex_bounds t
  have hstep : ∀j,
      epochStep.eval (Function.update (Function.update ρ 71 (.nat j)) 72 (.nat (2^min j J)))=
        .nat (2^min (j+1) J) := by
    intro j
    simp only [epochStep,Expr.eval,Function.update_of_ne (by decide : (70:ℕ)≠72),
      Function.update_of_ne (by decide : (70:ℕ)≠71),hT,Function.update_self,Value.natVal]
    by_cases hj : j<J
    · have hj' : j+1≤J := by omega
      have hp : 2^(j+1)≤t+1 :=
        (Nat.pow_le_pow_right (by decide : 1≤2) hj').trans hb.1
      rw [min_eq_left (by omega : j≤J),min_eq_left hj',if_neg (by
        rw [pow_succ] at hp
        omega)]
      congr 1
      rw [pow_succ]
      omega
    · rw [min_eq_right (by omega : J≤j),min_eq_right (by omega : J≤j+1)]
      rw [if_pos (by simpa [J,epochLength] using hb.2)]
  have hf : ∀m,(List.range m).foldl (fun vv j => epochStep.eval
      (Function.update (Function.update ρ 71 (.nat j)) 72 vv)) (.nat 1)=.nat (2^min m J) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ,List.foldl_append,ih]
      simpa only [List.foldl_cons,List.foldl_nil] using hstep m
  have hJ : J≤t+1 := by
    dsimp [J,epochIndex]
    rw [Nat.log2_eq_log_two]
    exact Nat.log_le_self 2 (t+1)
  simp only [epochProgram,Expr.eval,hT,Value.natVal]
  rw [hf,min_eq_right hJ]
  rfl

theorem program_eval (ρ : Env) (x : List Bool) (hx : ρ 40=wordValue x) :
    program.eval ρ=pairValue (Paper37.IntegerPredictor.conditionalPair
      (epochLength (epochIndex x.length)) (x.drop (epochStart (epochIndex x.length)))) := by
  let H := epochLength (epochIndex x.length)
  let σ := Function.update ρ 70 (.nat (x.length+1))
  have he := epochProgram_eval σ x.length (by simp [σ])
  let τ := Function.update σ 0 (.nat H)
  let υ := Function.update τ 44 (.nat (H-1))
  have hd := dropProgram_eval υ x (H-1) (by simpa [υ,τ,σ] using hx) (by simp [υ])
  have hc := conditionalProgram_eval (Function.update υ 40 (wordValue (x.drop (H-1)))) H
    (x.drop (H-1)) (by simp [υ,τ]) (by simp)
    (by simpa [H,epochStart,epochLength] using within_epoch_prefix_lt x)
  rw [program,Expr.eval]
  rw [show (Expr.add (.length (.var 40)) (.lit 1)).eval ρ=.nat (x.length+1) by
    simp [Expr.eval,hx,wordValue_length,Value.natVal]]
  change (Expr.bind 0 epochProgram _).eval σ=_
  rw [Expr.eval,he]
  change (Expr.bind 44 (.sub (.var 0) (.lit 1)) _).eval τ=_
  rw [Expr.eval]
  simp only [Expr.eval,τ,Function.update_self,Value.natVal]
  change conditionalProgram.eval (Function.update υ 40 (dropProgram.eval υ))=_
  rw [hd]
  exact hc

/-- The returned unreduced natural pair denotes the exact actual G.1 kernel. -/
theorem program_source (ρ : Env) (x : List Bool) (hx : ρ 40=wordValue x) :
    (((program.eval ρ).arrayVal[0]?.getD (Value.nat 0)).natVal:ℚ)/
      ((program.eval ρ).arrayVal[1]?.getD (Value.nat 0)).natVal =
      Paper37.Prediction.blockConditional (epochLength (epochIndex x.length))
        (x.drop (epochStart (epochIndex x.length))) := by
  rw [program_eval ρ x hx]
  change ((Paper37.IntegerPredictor.conditionalPair _ _).1:ℚ)/
    (Paper37.IntegerPredictor.conditionalPair _ _).2=_
  exact Paper37.IntegerPredictor.conditionalPair_exact _ _ (within_epoch_prefix_lt x)

theorem program_source_real (ρ : Env) (x : List Bool) (hx : ρ 40=wordValue x) :
    (((((program.eval ρ).arrayVal[0]?.getD (Value.nat 0)).natVal:ℚ)/
      ((program.eval ρ).arrayVal[1]?.getD (Value.nat 0)).natVal):ℝ)=onlineKernel x true := by
  have hq := congrArg (fun q : ℚ => (q : ℝ)) (program_source ρ x hx)
  rw [onlineKernel_true]
  simpa only [Rat.cast_div,Rat.cast_natCast] using hq

end Paper37.AnytimeProgram
