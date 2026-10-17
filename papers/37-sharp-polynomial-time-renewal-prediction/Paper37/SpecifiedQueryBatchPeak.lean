import Paper37.SpecifiedQueryBatch
import Paper37.AdaptiveQueryPeak

namespace Paper37.SpecifiedQueryBatch
open Paper37.BoundedLoop Paper37.WordProgram Paper37.CachedCoreProgram
open Paper37.IntegerOutputPeak
set_option linter.unusedSimpArgs false

lemma wordsValue_size (H : ℕ) (qs : List (List Bool)) (hvalid : ∀y∈qs,y.length≤H) :
    (wordsValue qs).representationSize≤qs.length*(2*H+2)+2 := by
  have hs:=list_sum_bound qs (fun y => (wordValue y).representationSize) (2*H+2) (by
    intro y hy
    exact (Paper37.WordProgram.wordValue_size y).trans (by have h:=hvalid y hy;omega))
  simpa only [wordsValue,Value.representationSize,List.map_map,Function.comp_def] using
    Nat.add_le_add_right hs 2

/-- The true tabulation peak charges both the supplied input array and the
entire accumulated output array. No bounded trace is supplied by the caller. -/
lemma program_peak (query : Expr) (ρ : Env) (H P : ℕ) (qs : List (List Bool))
    (hH : ρ 0=.nat H) (hqs : ρ 60=wordsValue qs) (hvalid : ∀y∈qs,y.length<H)
    (hq : ∀σ y,σ 0=.nat H → σ 40=wordValue y → y.length<H → query.peak σ≤P) :
    (program query).peak ρ≤
      (qs.length+1)*(P+(wordsValue qs).representationSize+qs.length+10) := by
  let Q:=(wordsValue qs).representationSize
  let B:=P+Q+qs.length+10
  have hb : ∀i∈List.range qs.length,
      (Expr.bind 40 (.get (.var 60) (.var 61)) query).peak
        (Function.update ρ 61 (.nat i))≤B := by
    intro i hi
    have hi' : i<qs.length := List.mem_range.mp hi
    let σ:=Function.update ρ 61 (.nat i)
    have hsel:=selected_word ρ qs i hi' hqs
    have hw:=hq (Function.update σ 40 (wordValue qs[i])) qs[i]
      (by simpa [σ] using hH) (by simp) (hvalid _ (List.getElem_mem hi'))
    have ha : (Expr.var 60).peak σ≤Q := by simp [Expr.peak,Expr.eval,σ,hqs,Q]
    have hiPeak : (Expr.var 61).peak σ≤qs.length+1 := by
      have hs:=Paper37.DP.binarySize_le_self i
      simp only [Expr.peak,Expr.eval,σ,Function.update_self,Value.representationSize,max_eq_left (Nat.zero_le _)]
      omega
    have hg:=get_peak_le (.var 60) (.var 61) σ Q (qs.length+1) ha hiPeak
    apply bind_peak_bound
    · exact hg.trans (by dsimp [B];omega)
    · rw [hsel]
      exact hw.trans (by dsimp [B];omega)
  have hlenEval : (Expr.length (.var 60)).eval ρ=.nat qs.length := by
    simp [Expr.eval,hqs,wordsValue,Value.arrayVal]
  have hlenPeak : (Expr.length (.var 60)).peak ρ≤Q+1 := by
    apply length_peak_le
    simp [Expr.peak,Expr.eval,hqs,Q]
  have hloop : ((List.range qs.length).map (fun i =>
      (Expr.bind 40 (.get (.var 60) (.var 61)) query).peak
        (Function.update ρ 61 (.nat i)))).foldl max 0≤B :=
    list_foldl_max_le _ _ _ (by omega) (by
      intro p hp
      obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hp
      exact hb i hi)
  have hsum:=list_sum_bound (List.range qs.length) (fun i =>
    ((Expr.bind 40 (.get (.var 60) (.var 61)) query).eval
      (Function.update ρ 61 (.nat i))).representationSize) B (by
    intro i hi
    exact (representationSize_le_peak _ _).trans (hb i hi))
  simp only [List.length_range] at hsum
  rw [program,Expr.peak,hlenEval]
  apply max_le
  · rw [Expr.eval,hlenEval]
    change (Value.array ((List.range qs.length).map (fun i =>
      (Expr.bind 40 (.get (.var 60) (.var 61)) query).eval
        (Function.update ρ 61 (.nat i))))).representationSize≤_
    simp only [Value.representationSize,List.map_map,Function.comp_def]
    dsimp [B,Q] at *
    nlinarith
  · apply max_le
    · exact hlenPeak.trans (by dsimp [B,Q];nlinarith)
    · exact hloop.trans (by dsimp [B,Q];nlinarith)

theorem standard_peak (ρ : Env) (H C : ℕ) (qs : List (List Bool))
    (hH : ρ 0=.nat H) (hqs : ρ 60=wordsValue qs) (hvalid : ∀y∈qs,y.length<H)
    (hcount : qs.length≤C*(H+1)) :
    (program Paper37.IntegerPredictorProgram.conditionalProgram).peak ρ≤
      (C*(H+1)+1)*(Paper37.IntegerQueryProgramPeak.queryPeakBound H+
        C*(H+1)*(2*H+2)+C*(H+1)+12) := by
  have hp:=program_peak _ ρ H (Paper37.IntegerQueryProgramPeak.queryPeakBound H) qs hH hqs hvalid
    (fun σ y => Paper37.IntegerQueryProgramPeak.conditionalProgram_peak σ H y)
  have hs:=wordsValue_size H qs (by intro y hy;exact (hvalid y hy).le)
  have hs' : (wordsValue qs).representationSize≤C*(H+1)*(2*H+2)+2 :=
    hs.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hcount) 2)
  apply hp.trans
  apply Nat.mul_le_mul
  · omega
  · omega

theorem adaptive_peak (ρ : Env) (H C : ℕ) (qs : List (List Bool))
    (hH : ρ 0=.nat H) (hqs : ρ 60=wordsValue qs) (hvalid : ∀y∈qs,y.length<H)
    (hcount : qs.length≤C*(H+1)) :
    (program Paper37.AdaptiveQueryProgram.conditionalProgram).peak ρ≤
      (C*(H+1)+1)*(Paper37.AdaptiveQueryPeak.queryPeakBound H+
        C*(H+1)*(2*H+2)+C*(H+1)+12) := by
  have hp:=program_peak _ ρ H (Paper37.AdaptiveQueryPeak.queryPeakBound H) qs hH hqs hvalid
    (fun σ y => Paper37.AdaptiveQueryPeak.conditionalProgram_peak σ H y)
  have hs:=wordsValue_size H qs (by intro y hy;exact (hvalid y hy).le)
  have hs' : (wordsValue qs).representationSize≤C*(H+1)*(2*H+2)+2 :=
    hs.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hcount) 2)
  apply hp.trans
  apply Nat.mul_le_mul
  · omega
  · omega

end Paper37.SpecifiedQueryBatch
