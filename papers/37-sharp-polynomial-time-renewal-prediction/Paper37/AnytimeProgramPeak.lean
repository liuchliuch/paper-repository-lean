import Paper37.AnytimeProgramWork
import Paper37.PredictorBatchPeak

namespace Paper37.AnytimeProgram
open Finset Paper37.BoundedLoop Paper37.WordProgram Paper37.AnytimePrediction
open Paper37.IntegerPredictorProgram Paper37.IntegerQueryProgramPeak
open Paper37.PredictorBatchPeak (bind_peak_le)
set_option maxRecDepth 3000

lemma epochStep_flat : Flat epochStep := by
  unfold epochStep
  apply Flat.ifLT
  · exact Flat.var _
  · exact Flat.binary .mul _ _ (Flat.lit _) (Flat.var _)
  · exact Flat.var _
  · exact Flat.binary .mul _ _ (Flat.lit _) (Flat.var _)

lemma epochStep_peak (ρ : Env) (T p : ℕ) (hT : ρ 70=.nat T) (hp : ρ 72=.nat p) (hpT : p≤T) :
    epochStep.peak ρ≤4096*(T+2) := by
  have h0 : (Value.nat T).representationSize≤T+1 := by
    simpa [Value.representationSize] using Nat.add_le_add_right (Paper37.DP.binarySize_le_self T) 1
  have h1 : (Value.nat p).representationSize≤T+1 := by
    have hh := Paper37.DP.binarySize_le_self p
    simp only [Value.representationSize]
    omega
  have hv : epochStep.varsBound ρ (T+1) := by simp [epochStep,Expr.varsBound,hT,hp,h0,h1]
  apply (flat_peak_le epochStep_flat ρ (T+1) hv).trans
  simp [epochStep,Expr.flatBudget]
  have hs := Paper37.DP.binarySize_le_self 2
  omega

lemma epochProgram_peak (ρ : Env) (t : ℕ) (hT : ρ 70=.nat (t+1)) :
    epochProgram.peak ρ≤4096*(t+3) := by
  let T := t+1
  have hfold := Paper37.IntegerOutputPeak.range_foldl_peak_le T
    (fun vv j => epochStep.eval (Function.update (Function.update ρ 71 (.nat j)) 72 vv))
    (fun vv j => epochStep.peak (Function.update (Function.update ρ 71 (.nat j)) 72 vv))
    (fun _ vv => ∃p:ℕ,vv=.nat p ∧ 1≤p ∧ p≤T) (4096*(t+3)) (by
      intro j hj vv hv
      obtain ⟨p,rfl,hp,hpT⟩ := hv
      dsimp only
      by_cases hd : T<2*p
      · refine ⟨p,?_,hp,hpT⟩
        simp [epochStep,Expr.eval,Function.update,hT,Value.natVal,hd,T]
      · refine ⟨2*p,?_,by omega,by omega⟩
        simp [epochStep,Expr.eval,Function.update,hT,Value.natVal,hd,T]) (by
      intro j hj vv hv
      obtain ⟨p,rfl,hp,hpT⟩ := hv
      exact epochStep_peak _ T p (by simpa [T] using hT) (by simp) hpT)
    (.nat 1) (by refine ⟨1,rfl,by omega,by dsimp [T];omega⟩) 0 (by omega)
  unfold epochProgram
  rw [Expr.peak]
  apply max_le
  · rw [← epochProgram,epochProgram_eval ρ t hT]
    have hb := (epochIndex_bounds t).1
    have hh := (Nat.size_le_size hb).trans (Paper37.DP.binarySize_le_self (t+1))
    simp only [Value.representationSize]
    omega
  · change max ((Expr.var 70).peak ρ) (max ((Expr.lit 1).peak ρ) _)≤_
    apply max_le
    · have hh := Paper37.DP.binarySize_le_self (t+1)
      simp [Expr.peak,Expr.eval,hT,Value.representationSize]
      omega
    · apply max_le
      · norm_num [Expr.peak,Expr.eval,Value.representationSize]
        omega
      · simpa only [Expr.eval,hT,Value.natVal] using hfold.2

def peakBound (t : ℕ) : ℕ := 10000000000000*(t+3)^12

/-- Full actual dynamic peak of the fixed dyadic restart AST, including its
epoch-discovery arithmetic, input suffix and exact conditional query. -/
theorem program_peak (ρ : Env) (x : List Bool) (hx : ρ 40=wordValue x) :
    program.peak ρ≤peakBound x.length := by
  let H := epochLength (epochIndex x.length)
  let σ := Function.update ρ 70 (.nat (x.length+1))
  let τ := Function.update σ 0 (.nat H)
  let υ := Function.update τ 44 (.nat (H-1))
  let ω := Function.update υ 40 (wordValue (x.drop (H-1)))
  let Q := peakBound x.length
  have hH : H≤x.length+1 := (epochIndex_bounds x.length).1
  have he := epochProgram_eval σ x.length (by simp [σ])
  have hd := dropProgram_eval υ x (H-1) (by simpa [υ,τ,σ] using hx) (by simp [υ])
  have hpow1 : x.length+3≤(x.length+3)^12 := le_self_pow₀ (by omega) (by decide)
  have hpow3 : (x.length+3)^3≤(x.length+3)^12 := Nat.pow_le_pow_right (by omega) (by decide)
  have hsmall : 4096*(x.length+3)≤Q := by dsimp [Q,peakBound];omega
  have hdropSmall : 100000*(x.length+2)^3≤Q := by
    have hh := Nat.pow_le_pow_left (by omega : x.length+2≤x.length+3) 3
    dsimp [Q,peakBound]
    omega
  have hvar : (Expr.var 40).peak ρ≤2*x.length+2 := by
    simpa [Expr.peak,Expr.eval,hx] using wordValue_size x
  have hlen := length_peak_le (.var 40) ρ _ hvar
  have hlit : (Expr.lit 1).peak ρ≤2 := by norm_num [Expr.peak,Expr.eval,Value.representationSize]
  have hstart : (Expr.add (.length (.var 40)) (.lit 1)).peak ρ≤Q := by
    have hh := binary_peak_le .add (.length (.var 40)) (.lit 1) ρ _ 2 hlen hlit
    exact hh.trans (by omega)
  have hsub : (Expr.sub (.var 0) (.lit 1)).peak τ≤Q := by
    have hv : (Expr.var 0).peak τ≤x.length+2 := by
      have hh := Paper37.DP.binarySize_le_self H
      simp only [Expr.peak,Expr.eval,τ,Function.update_self,Value.representationSize]
      omega
    have hl : (Expr.lit 1).peak τ≤2 := by norm_num [Expr.peak,Expr.eval,Value.representationSize]
    have hh := binary_peak_le .sub (.var 0) (.lit 1) τ _ 2 hv hl
    exact hh.trans (by omega)
  have hc := conditionalProgram_peak ω H (x.drop (H-1)) (by simp [ω,υ,τ]) (by simp [ω])
    (by simpa [H,epochStart,epochLength] using within_epoch_prefix_lt x)
  have hc' : conditionalProgram.peak ω≤Q := by
    have hp := Nat.pow_le_pow_left (by omega : H+2≤x.length+3) 12
    unfold queryPeakBound at hc
    dsimp [Q,peakBound]
    nlinarith
  unfold program
  apply (bind_peak_le ρ 70 (.add (.length (.var 40)) (.lit 1)) _).trans
  rw [show (Expr.add (.length (.var 40)) (.lit 1)).eval ρ=.nat (x.length+1) by
    simp [Expr.eval,hx,wordValue_length,Value.natVal]]
  apply max_le hstart
  change (Expr.bind 0 epochProgram _).peak σ≤Q
  apply (bind_peak_le σ 0 epochProgram _).trans
  rw [he]
  apply max_le ((epochProgram_peak σ x.length (by simp [σ])).trans hsmall)
  change (Expr.bind 44 (.sub (.var 0) (.lit 1)) _).peak τ≤Q
  apply (bind_peak_le τ 44 (.sub (.var 0) (.lit 1)) _).trans
  rw [show (Expr.sub (.var 0) (.lit 1)).eval τ=.nat (H-1) by simp [Expr.eval,τ,Value.natVal]]
  apply max_le hsub
  change (Expr.bind 40 dropProgram conditionalProgram).peak υ≤Q
  apply (bind_peak_le υ 40 dropProgram conditionalProgram).trans
  rw [hd]
  exact max_le ((dropProgram_peak υ x.length x (H-1) (by simpa [υ,τ,σ] using hx) (by simp [υ]) le_rfl (by omega)).trans hdropSmall) hc'

end Paper37.AnytimeProgram
