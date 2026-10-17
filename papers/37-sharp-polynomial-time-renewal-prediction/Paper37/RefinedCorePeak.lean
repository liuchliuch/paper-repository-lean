import Paper37.RefinedValueSize
import Paper37.IntegerOutputPeak
import Paper37.BoundedLoopTabulate

namespace Paper37.RefinedCoreProgram
open Finset Paper37.BoundedLoop Paper37.CachedDP Paper37.DP Paper37.ContinuationDP
open Paper37.CachedRefinedDP Paper37.RefinedContinuation Paper37.AdaptiveDP
open Paper37.CachedCoreProgram (chooseValue powerValue observedValue sourceWidth source_choose_size
  source_power_size source_observed_size get_range_map)
set_option maxRecDepth 10000

lemma unmarkedTerm_flat : Flat unmarkedTerm := by
  unfold unmarkedTerm coefficient oldPair epsilon multiplicity gap
  repeat first | exact Flat.lit _ | exact Flat.var _ | apply Flat.get | apply Flat.ifLT |
    apply Flat.binary .add | apply Flat.binary .sub | apply Flat.binary .mul
lemma markedTerm_flat : Flat markedTerm := by
  unfold markedTerm coefficient oldPair epsilon multiplicity gap
  repeat first | exact Flat.lit _ | exact Flat.var _ | apply Flat.get | apply Flat.ifLT |
    apply Flat.binary .add | apply Flat.binary .sub | apply Flat.binary .mul
lemma guardTerm_flat (term : Expr) (ht:Flat term) : Flat (guardTerm term) := by
  unfold guardTerm epsilon multiplicity gap
  repeat first | exact ht | exact Flat.lit _ | exact Flat.var _ | apply Flat.get | apply Flat.ifLT |
    apply Flat.binary .add | apply Flat.binary .sub | apply Flat.binary .mul

lemma unmarked_guard_peak (ρ:Env) (B:ℕ) (hv:(guardTerm unmarkedTerm).varsBound ρ B) :
    (guardTerm unmarkedTerm).peak ρ≤65536*(B+1) := by
  apply (flat_peak_le (guardTerm_flat _ unmarkedTerm_flat) ρ B hv).trans
  simp [guardTerm,unmarkedTerm,coefficient,oldPair,epsilon,multiplicity,gap,Expr.flatBudget]
  omega
lemma marked_guard_peak (ρ:Env) (B:ℕ) (hv:(guardTerm markedTerm).varsBound ρ B) :
    (guardTerm markedTerm).peak ρ≤65536*(B+1) := by
  apply (flat_peak_le (guardTerm_flat _ markedTerm_flat) ρ B hv).trans
  simp [guardTerm,markedTerm,coefficient,oldPair,epsilon,multiplicity,gap,Expr.flatBudget]
  omega

lemma unmarked_guard_vars (ρ:Env) (B:ℕ)
    (h:∀x,x≤10 ∨ x=27→(ρ x).representationSize≤B) : (guardTerm unmarkedTerm).varsBound ρ B := by
  simp only [guardTerm,unmarkedTerm,coefficient,oldPair,epsilon,multiplicity,gap,Expr.varsBound]
  repeat' apply And.intro
  all_goals first | trivial | exact h _ (by omega)
lemma marked_guard_vars (ρ:Env) (B:ℕ)
    (h:∀x,x≤10 ∨ x=27→(ρ x).representationSize≤B) : (guardTerm markedTerm).varsBound ρ B := by
  simp only [guardTerm,markedTerm,coefficient,oldPair,epsilon,multiplicity,gap,Expr.varsBound]
  repeat' apply And.intro
  all_goals first | trivial | exact h _ (by omega)

lemma source_state_bounds (N:ℕ) (z:List Bool) (A d:ℕ) (ρ:Env)
    (hN:0<N) (hz:z.length≤N) (hA:A≤N) (hd:d≤N)
    (h:State (makeObservedCache N z) A (cachedRefinedRun N (makeObservedCache N z) A d) d ρ)
    (k u j b:ℕ) (hk:k≤N) (hu:u≤N) (hj:j≤N) (hb:b≤N)
    (h7:ρ 7=.nat k) (h8:ρ 8=.nat u) (h27:ρ 27=.nat j) (h9:ρ 9=.nat b)
    (h10:(ρ 10).representationSize≤sourceFrameBound N) :
    ∀x,x≤10 ∨ x=27→(ρ x).representationSize≤sourceFrameBound N := by
  have hf:=sourceFrame_contains N
  intro x hx
  rcases hx with hx|rfl
  · interval_cases x
    · rw [h.horizon];exact nat_sourceFrame_le N N le_rfl
    · rw [h.age];exact nat_sourceFrame_le N A hA
    · rw [h.choose];exact (source_choose_size N z).trans hf.2.1
    · rw [h.power];exact (source_power_size N z).trans hf.2.2.1
    · rw [h.observed];exact (source_observed_size N z hz).trans hf.2.2.2.1
    · rw [h.table];exact (source_layer_size N z A d hN hz hd).trans hf.1
    · rw [h.depth];exact nat_sourceFrame_le N d hd
    · rw [h7];exact nat_sourceFrame_le N k hk
    · rw [h8];exact nat_sourceFrame_le N u hu
    · rw [h9];exact nat_sourceFrame_le N b hb
    · exact h10
  · rw [h27];exact nat_sourceFrame_le N j hj

lemma state_scalar_eval {N:ℕ} (c:Cache N) (A:ℕ) (old:RefinedLayer N) (d:ℕ) (ρ:Env)
    (h:State c A old d ρ) (hd:d<N) (k u j:Fin (N+1)) :
    let σ:=Function.update (Function.update (Function.update ρ 7 (.nat k.val)) 8 (.nat u.val)) 27 (.nat j.val)
    (sumTerm unmarkedTerm).eval σ=.nat (refinedAt (cachedRefinedStep N c A ⟨d,hd⟩ old) k u j).1 ∧
    (sumTerm markedTerm).eval σ=.nat (refinedAt (cachedRefinedStep N c A ⟨d,hd⟩ old) k u j).2 := by
  have he:=congrArg (fun q=>(((q.arrayVal[k.val]?.getD (.nat 0)).arrayVal[u.val]?.getD (.nat 0)).arrayVal[j.val]?.getD (.nat 0)))
    (stepProgram_eval c A old d ρ h hd)
  dsimp only at he
  rw [layerValue_get _ _ _ _ k.isLt u.isLt j.isLt] at he
  simp only [stepProgram,Expr.eval,layerLength,h.horizon,Value.natVal,Value.arrayVal] at he
  rw [get_range_map _ _ _ k.isLt] at he
  simp only [Expr.eval,layerLength,Function.update_of_ne (by decide:(0:ℕ)≠7),h.horizon,Value.natVal,Value.arrayVal] at he
  rw [get_range_map _ _ _ u.isLt] at he
  simp only [Expr.eval,layerLength,Function.update_of_ne (by decide:(0:ℕ)≠8),
    Function.update_of_ne (by decide:(0:ℕ)≠7),h.horizon,Value.natVal,Value.arrayVal] at he
  rw [get_range_map _ _ _ j.isLt] at he
  simp only [Expr.eval,List.map_cons,List.map_nil] at he
  have he' : Value.array [
      (sumTerm unmarkedTerm).eval (Function.update (Function.update (Function.update ρ 7 (.nat k.val)) 8 (.nat u.val)) 27 (.nat j.val)),
      (sumTerm markedTerm).eval (Function.update (Function.update (Function.update ρ 7 (.nat k.val)) 8 (.nat u.val)) 27 (.nat j.val))]=
      .array [.nat (refinedAt (cachedRefinedStep N c A ⟨d,hd⟩ old) k u j).1,
        .nat (refinedAt (cachedRefinedStep N c A ⟨d,hd⟩ old) k u j).2] := by
    simpa [refinedLayerAt,k.isLt,u.isLt,j.isLt] using he
  have hfirst:=congrArg (fun q=>q.arrayVal[0]?.getD (.nat 0)) he'
  have hsecond:=congrArg (fun q=>q.arrayVal[1]?.getD (.nat 0)) he'
  exact ⟨by simpa [Value.arrayVal] using hfirst,by simpa [Value.arrayVal] using hsecond⟩

/-- The true scalar loop accumulator is a partial sum of nonnegative terms.
It is therefore bounded by the certified final refined DP entry. -/
lemma sumTerm_source_peak_le (N:ℕ) (z:List Bool) (A d:ℕ) (ρ:Env)
    (hN:0<N) (hz:z.length≤N) (hA:A≤N) (hd:d<N)
    (h:State (makeObservedCache N z) A (cachedRefinedRun N (makeObservedCache N z) A d) d ρ)
    (k u j:Fin (N+1)) (term:Expr) (f:ℕ→ℕ)
    (hvars:∀σ,(∀x,x≤10 ∨ x=27→(σ x).representationSize≤sourceFrameBound N)→
      (guardTerm term).varsBound σ (sourceFrameBound N))
    (hpeak:∀σ,(guardTerm term).varsBound σ (sourceFrameBound N)→
      (guardTerm term).peak σ≤65536*(sourceFrameBound N+1))
    (ht:∀b<k.val+1,∀a,(guardTerm term).eval
      (Function.update (Function.update
        (Function.update (Function.update (Function.update ρ 7 (.nat k.val)) 8 (.nat u.val)) 27 (.nat j.val))
          9 (.nat b)) 10 (.nat a))=.nat (f b))
    (hfinal:((sumTerm term).eval (Function.update (Function.update (Function.update ρ 7 (.nat k.val))
      8 (.nat u.val)) 27 (.nat j.val))).representationSize≤sourceFrameBound N) :
    (sumTerm term).peak (Function.update (Function.update (Function.update ρ 7 (.nat k.val))
      8 (.nat u.val)) 27 (.nat j.val))≤300000*(sourceFrameBound N+1) := by
  let σ:=Function.update (Function.update (Function.update ρ 7 (.nat k.val)) 8 (.nat u.val)) 27 (.nat j.val)
  let M:=k.val+1
  let B:=sourceFrameBound N
  let P:=300000*(B+1)
  have hs:State (makeObservedCache N z) A (cachedRefinedRun N (makeObservedCache N z) A d) d σ:=
    ((h.update_high 7 (by omega) _).update_high 8 (by omega) _).update_high 27 (by omega) _
  have h7:σ 7=.nat k.val := by simp [σ]
  have h8:σ 8=.nat u.val := by simp [σ]
  have h27:σ 27=.nat j.val := by simp [σ]
  have hM:(loopBound.eval σ).natVal=M := by simp [loopBound,Expr.eval,h7,Value.natVal,M]
  have heval:=sumTerm_eval σ term M f hM ht
  have hsum:(Value.nat (∑i∈range M,f i)).representationSize≤B := by rw [←heval];exact hfinal
  have hpart:∀i≤M,(Value.nat (∑b∈range i,f b)).representationSize≤B := by
    intro i hi
    have hh:∑b∈range i,f b≤∑b∈range M,f b:=sum_le_sum_of_subset (range_mono hi)
    simpa only [Value.representationSize] using (Nat.add_le_add_right (Nat.size_le_size hh) 1).trans
      (by simpa only [Value.representationSize] using hsum)
  have hloop:loopBound.peak σ≤65536*(B+1) := by
    have hf:Flat loopBound := by unfold loopBound;apply Flat.binary .add <;> first|exact Flat.var _|exact Flat.lit _
    have hv:loopBound.varsBound σ B := by
      simp only [loopBound,Expr.varsBound]
      exact ⟨by simpa only [h7] using nat_sourceFrame_le N k.val (by omega),trivial⟩
    exact (flat_peak_le hf σ B hv).trans (by simp [loopBound,Expr.flatBudget];omega)
  have hfold:=Paper37.IntegerOutputPeak.range_foldl_peak_le M
    (fun vv b=>(Expr.add (.var 10) (guardTerm term)).eval (Function.update (Function.update σ 9 (.nat b)) 10 vv))
    (fun vv b=>(Expr.add (.var 10) (guardTerm term)).peak (Function.update (Function.update σ 9 (.nat b)) 10 vv))
    (fun i vv=>vv=.nat (∑b∈range i,f b)) P (by
      intro i hi vv hv
      subst vv
      dsimp only
      rw [Expr.eval,ht i hi]
      simp only [Expr.eval,Function.update_self,Value.natVal]
      rw [sum_range_succ]) (by
      intro i hi vv hv
      subst vv
      let τ:=Function.update (Function.update σ 9 (.nat i)) 10 (.nat (∑b∈range i,f b))
      have ha:(τ 10).representationSize≤B := by simp only [τ,Function.update_self];exact hpart i (by omega)
      have hall:=source_state_bounds N z A d τ hN hz hA (by omega)
        ((hs.update_high 9 (by omega) _).update_high 10 (by omega) _)
        k.val u.val j.val i (by omega) (by omega) (by omega) (by dsimp [M] at hi;omega)
        (by simp [τ,h7]) (by simp [τ,h8]) (by simp [τ,h27]) (by simp [τ]) ha
      have hp:=hpeak τ (hvars τ hall)
      have hav:(Expr.var 10).peak τ≤B := by simpa [Expr.peak,Expr.eval] using ha
      have hh:=binary_peak_le .add (.var 10) (guardTerm term) τ B (65536*(B+1)) hav hp
      change (Expr.add (.var 10) (guardTerm term)).peak τ≤P
      exact hh.trans (by dsimp [P];omega)) (.nat 0) (by simp) 0 (by dsimp [P];omega)
  change (sumTerm term).peak σ≤P
  unfold sumTerm
  rw [Expr.peak]
  apply max_le (hfinal.trans (by dsimp [P,B];omega))
  change max (loopBound.peak σ) (max ((Expr.lit 0).peak σ) _)≤P
  rw [hM]
  apply max_le (hloop.trans (by dsimp [P];omega))
  apply max_le
  · simp [Expr.peak,Expr.eval,Value.representationSize,P];omega
  · simpa only [Expr.eval] using hfold.2


def cellPeakBound (N:ℕ) : ℕ := 600000*(sourceFrameBound N+1)+2

def gSummand {N:ℕ} (c:Cache N) (old:RefinedLayer N) (d:ℕ) (k u j:Fin (N+1)) (b:ℕ) : ℕ :=
  if (d+1)*b≤u.val ∧ (if 0<Paper37.CachedOutput.observedAt c (d+1)+b then 1 else 0)≤j.val then
    chooseAt c k b*powerAt c (Paper37.CachedOutput.observedAt c (d+1)+b)*
      (refinedLayerAt old (k.val-b) (u.val-(d+1)*b) (j.val-(if 0<Paper37.CachedOutput.observedAt c (d+1)+b then 1 else 0))).1 else 0

def sSummand {N:ℕ} (c:Cache N) (old:RefinedLayer N) (A d:ℕ) (k u j:Fin (N+1)) (b:ℕ) : ℕ :=
  if (d+1)*b≤u.val ∧ (if 0<Paper37.CachedOutput.observedAt c (d+1)+b then 1 else 0)≤j.val then
    chooseAt c k b*powerAt c (Paper37.CachedOutput.observedAt c (d+1)+b)*
      ((refinedLayerAt old (k.val-b) (u.val-(d+1)*b) (j.val-(if 0<Paper37.CachedOutput.observedAt c (d+1)+b then 1 else 0))).2+
        (if A<d+1 then b else 0)*(refinedLayerAt old (k.val-b) (u.val-(d+1)*b) (j.val-(if 0<Paper37.CachedOutput.observedAt c (d+1)+b then 1 else 0))).1) else 0

lemma g_guard_eval {N:ℕ} (c:Cache N) (A:ℕ) (old:RefinedLayer N) (d:ℕ) (ρ:Env)
    (h:State c A old d ρ) (k u j:Fin (N+1)) (b:ℕ) (hb:b≤N) (hd:d<N)
    (h7:ρ 7=.nat k.val) (h8:ρ 8=.nat u.val) (h27:ρ 27=.nat j.val) (h9:ρ 9=.nat b) :
    (guardTerm unmarkedTerm).eval ρ=.nat (gSummand c old d k u j b) := by
  unfold gSummand
  simp only [Paper37.CachedOutput.observedAt,dif_pos (by omega:d+1<N+1)]
  apply guardTerm_eval c A old d ρ h unmarkedTerm _ k.val u.val j.val b hd h8 h27 h9
  exact unmarked_eval c A old d ρ h k.val u.val j.val b k.isLt u.isLt j.isLt (by omega) hd h7 h8 h27 h9

lemma source_unmarked_sum_peak (N:ℕ) (z:List Bool) (A d:ℕ) (ρ:Env)
    (hN:0<N) (hz:z.length≤N) (hA:A≤N) (hd:d<N)
    (h:State (makeObservedCache N z) A (cachedRefinedRun N (makeObservedCache N z) A d) d ρ)
    (k u j:Fin (N+1)) :
    (sumTerm unmarkedTerm).peak (Function.update (Function.update (Function.update ρ 7 (.nat k.val))
      8 (.nat u.val)) 27 (.nat j.val))≤300000*(sourceFrameBound N+1) := by
  let c:=makeObservedCache N z
  let old:=cachedRefinedRun N c A d
  let σ:=Function.update (Function.update (Function.update ρ 7 (.nat k.val)) 8 (.nat u.val)) 27 (.nat j.val)
  have hs:State c A old d σ:=((h.update_high 7 (by omega) _).update_high 8 (by omega) _).update_high 27 (by omega) _
  have hc:=state_scalar_eval c A old d ρ h hd k u j
  have he:cachedRefinedStep N c A ⟨d,hd⟩ old=cachedRefinedRun N c A (d+1) := by simp [cachedRefinedRun,hd,old]
  have hh:=Paper37.CachedQueries.cachedRefined_binarySize N z A (d+1) k u j hN (by omega) hz
  have hgfinal:((sumTerm unmarkedTerm).eval σ).representationSize≤sourceFrameBound N := by
    rw [hc.1,he]
    have hg:(refinedAt (cachedRefinedRun N c A (d+1)) k u j).1.size≤sourceWidth N := by
      unfold Paper37.CachedCoreProgram.sourceWidth;nlinarith [hh.1]
    simpa only [Value.representationSize] using (Nat.add_le_add_right hg 1).trans
      (sourceFrame_contains N).2.2.2.2.2.1
  apply sumTerm_source_peak_le N z A d ρ hN hz hA hd h k u j unmarkedTerm (gSummand c old d k u j)
    (fun τ ht=>unmarked_guard_vars τ _ ht) (fun τ ht=>unmarked_guard_peak τ _ ht) _ hgfinal
  intro b hb a
  apply g_guard_eval c A old d _ ((hs.update_high 9 (by omega) _).update_high 10 (by omega) _)
    k u j b (by omega) hd <;> simp [σ,Function.update]

lemma s_guard_eval {N:ℕ} (c:Cache N) (A:ℕ) (old:RefinedLayer N) (d:ℕ) (ρ:Env)
    (h:State c A old d ρ) (k u j:Fin (N+1)) (b:ℕ) (hb:b≤N) (hd:d<N)
    (h7:ρ 7=.nat k.val) (h8:ρ 8=.nat u.val) (h27:ρ 27=.nat j.val) (h9:ρ 9=.nat b) :
    (guardTerm markedTerm).eval ρ=.nat (sSummand c old A d k u j b) := by
  unfold sSummand
  simp only [Paper37.CachedOutput.observedAt,dif_pos (by omega:d+1<N+1)]
  apply guardTerm_eval c A old d ρ h markedTerm _ k.val u.val j.val b hd h8 h27 h9
  exact marked_eval c A old d ρ h k.val u.val j.val b k.isLt u.isLt j.isLt (by omega) hd h7 h8 h27 h9

lemma source_marked_sum_peak (N:ℕ) (z:List Bool) (A d:ℕ) (ρ:Env)
    (hN:0<N) (hz:z.length≤N) (hA:A≤N) (hd:d<N)
    (h:State (makeObservedCache N z) A (cachedRefinedRun N (makeObservedCache N z) A d) d ρ)
    (k u j:Fin (N+1)) :
    (sumTerm markedTerm).peak (Function.update (Function.update (Function.update ρ 7 (.nat k.val))
      8 (.nat u.val)) 27 (.nat j.val))≤300000*(sourceFrameBound N+1) := by
  let c:=makeObservedCache N z
  let old:=cachedRefinedRun N c A d
  let σ:=Function.update (Function.update (Function.update ρ 7 (.nat k.val)) 8 (.nat u.val)) 27 (.nat j.val)
  have hs:State c A old d σ:=((h.update_high 7 (by omega) _).update_high 8 (by omega) _).update_high 27 (by omega) _
  have hc:=state_scalar_eval c A old d ρ h hd k u j
  have he:cachedRefinedStep N c A ⟨d,hd⟩ old=cachedRefinedRun N c A (d+1) := by simp [cachedRefinedRun,hd,old]
  have hh:=Paper37.CachedQueries.cachedRefined_binarySize N z A (d+1) k u j hN (by omega) hz
  have hgfinal:((sumTerm markedTerm).eval σ).representationSize≤sourceFrameBound N := by
    rw [hc.2,he]
    have hg:(refinedAt (cachedRefinedRun N c A (d+1)) k u j ).2.size≤sourceWidth N := by
      unfold Paper37.CachedCoreProgram.sourceWidth;nlinarith [hh.2]
    simpa only [Value.representationSize] using (Nat.add_le_add_right hg 1).trans
      (sourceFrame_contains N).2.2.2.2.2.1
  apply sumTerm_source_peak_le N z A d ρ hN hz hA hd h k u j markedTerm (sSummand c old A d k u j)
    (fun τ ht=>marked_guard_vars τ _ ht) (fun τ ht=>marked_guard_peak τ _ ht) _ hgfinal
  intro b hb a
  apply s_guard_eval c A old d _ ((hs.update_high 9 (by omega) _).update_high 10 (by omega) _)
    k u j b (by omega) hd <;> simp [σ,Function.update]

lemma pair_array_peak_le (a b:Expr) (ρ:Env) (B:ℕ) (ha:a.peak ρ≤B) (hb:b.peak ρ≤B) :
    (Expr.array [a,b]).peak ρ≤B+B+2 := by
  have hp:=array_peak_le [a,b] ρ (fun _=>B) (by
    intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl
    · exact ha
    · exact hb)
  simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using hp

lemma source_cell_peak_le (N:ℕ) (z:List Bool) (A d:ℕ) (ρ:Env)
    (hN:0<N) (hz:z.length≤N) (hA:A≤N) (hd:d<N)
    (h:State (makeObservedCache N z) A (cachedRefinedRun N (makeObservedCache N z) A d) d ρ)
    (k u j:Fin (N+1)) :
    (Expr.array [sumTerm unmarkedTerm,sumTerm markedTerm]).peak
      (Function.update (Function.update (Function.update ρ 7 (.nat k.val)) 8 (.nat u.val)) 27 (.nat j.val))≤cellPeakBound N := by
  have hg:=source_unmarked_sum_peak N z A d ρ hN hz hA hd h k u j
  have hs:=source_marked_sum_peak N z A d ρ hN hz hA hd h k u j
  have hp:=pair_array_peak_le _ _ _ _ hg hs
  have heq:300000*(sourceFrameBound N+1)+300000*(sourceFrameBound N+1)+2=cellPeakBound N := by
    unfold cellPeakBound
    omega
  exact hp.trans_eq heq

lemma layerLength_peak_le (ρ:Env) (N:ℕ) (h0:ρ 0=.nat N) :
    layerLength.peak ρ≤5*(sourceFrameBound N+1) := by
  have hv:(Expr.var 0).peak ρ≤sourceFrameBound N := by
    simpa [Expr.peak,Expr.eval,h0] using nat_sourceFrame_le N N le_rfl
  have hl:(Expr.lit 1).peak ρ≤2 := by norm_num [Expr.peak,Expr.eval,Value.representationSize]
  have hh:=binary_peak_le .add (.var 0) (.lit 1) ρ _ _ hv hl
  change (Expr.add (.var 0) (.lit 1)).peak ρ≤_
  exact hh.trans (by have hB:=(sourceFrame_contains N).2.2.2.2.2.2;omega)

def jPeakBound (N:ℕ) : ℕ := (N+2)*cellPeakBound N+5*(sourceFrameBound N+1)+2
def uPeakBound (N:ℕ) : ℕ := (N+2)*jPeakBound N+5*(sourceFrameBound N+1)+2
def stepPeakBound (N:ℕ) : ℕ := (N+2)*uPeakBound N+5*(sourceFrameBound N+1)+2

lemma source_step_peak_le (N:ℕ) (z:List Bool) (A d:ℕ) (ρ:Env)
    (hN:0<N) (hz:z.length≤N) (hA:A≤N) (hd:d<N)
    (h:State (makeObservedCache N z) A (cachedRefinedRun N (makeObservedCache N z) A d) d ρ) :
    stepProgram.peak ρ≤stepPeakBound N := by
  unfold stepProgram stepPeakBound
  apply tabulate_peak_le 7 layerLength _ ρ (N+1) (5*(sourceFrameBound N+1)) (uPeakBound N)
  · simp [layerLength,Expr.eval,h.horizon,Value.natVal]
  · exact layerLength_peak_le ρ N h.horizon
  · intro k hk
    unfold uPeakBound
    apply tabulate_peak_le 8 layerLength _ (Function.update ρ 7 (.nat k)) (N+1)
      (5*(sourceFrameBound N+1)) (jPeakBound N)
    · simp [layerLength,Expr.eval,Function.update,h.horizon,Value.natVal]
    · apply layerLength_peak_le _ N;simp [Function.update,h.horizon]
    · intro u hu
      unfold jPeakBound
      apply tabulate_peak_le 27 layerLength _ (Function.update (Function.update ρ 7 (.nat k)) 8 (.nat u)) (N+1)
        (5*(sourceFrameBound N+1)) (cellPeakBound N)
      · simp [layerLength,Expr.eval,Function.update,h.horizon,Value.natVal]
      · apply layerLength_peak_le _ N;simp [Function.update,h.horizon]
      · intro j hj
        exact source_cell_peak_le N z A d ρ hN hz hA hd h ⟨k,hk⟩ ⟨u,hu⟩ ⟨j,hj⟩

lemma baseProgram_peak_le (ρ:Env) (N:ℕ) (h0:ρ 0=.nat N) :
    baseProgram.peak ρ≤stepPeakBound N := by
  let cell:Expr:=.array [.ifLT (.var 7) (.lit 1)
    (.ifLT (.var 8) (.lit 1) (.ifLT (.var 27) (.lit 1) (.lit 1) (.lit 0)) (.lit 0)) (.lit 0),.lit 0]
  have hflat:Flat cell := by
    apply Flat.array
    intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl
    · repeat first|apply Flat.ifLT|exact Flat.var _|exact Flat.lit _
    · exact Flat.lit _
  have hcell:∀k<N+1,∀u<N+1,∀j<N+1,cell.peak
      (Function.update (Function.update (Function.update ρ 7 (.nat k)) 8 (.nat u)) 27 (.nat j))≤cellPeakBound N := by
    intro k hk u hu j hj
    have hkv:=nat_sourceFrame_le N k (by omega)
    have huv:=nat_sourceFrame_le N u (by omega)
    have hjv:=nat_sourceFrame_le N j (by omega)
    have hv:cell.varsBound (Function.update (Function.update (Function.update ρ 7 (.nat k)) 8 (.nat u)) 27 (.nat j))
        (sourceFrameBound N) := by
      simp only [cell,Expr.varsBound,List.mem_cons,List.not_mem_nil,or_false]
      intro e he
      rcases he with rfl|rfl
      · simp only [Expr.varsBound]
        repeat' apply And.intro
        all_goals first|trivial|simpa [Function.update] using hkv|simpa [Function.update] using huv|
          simpa [Function.update] using hjv
      · simp only [Expr.varsBound]
    apply (flat_peak_le hflat _ _ hv).trans
    simp [cell,Expr.flatBudget,cellPeakBound];omega
  change (Expr.tabulate 7 layerLength (.tabulate 8 layerLength (.tabulate 27 layerLength cell))).peak ρ≤_
  unfold stepPeakBound
  apply tabulate_peak_le 7 layerLength _ ρ (N+1) (5*(sourceFrameBound N+1)) (uPeakBound N)
  · simp [layerLength,Expr.eval,h0,Value.natVal]
  · exact layerLength_peak_le ρ N h0
  · intro k hk
    unfold uPeakBound
    apply tabulate_peak_le 8 layerLength _ (Function.update ρ 7 (.nat k)) (N+1)
      (5*(sourceFrameBound N+1)) (jPeakBound N)
    · simp [layerLength,Expr.eval,Function.update,h0,Value.natVal]
    · apply layerLength_peak_le _ N;simp [Function.update,h0]
    · intro u hu
      unfold jPeakBound
      apply tabulate_peak_le 27 layerLength cell (Function.update (Function.update ρ 7 (.nat k)) 8 (.nat u)) (N+1)
        (5*(sourceFrameBound N+1)) (cellPeakBound N)
      · simp [layerLength,Expr.eval,Function.update,h0,Value.natVal]
      · apply layerLength_peak_le _ N;simp [Function.update,h0]
      · intro j hj;exact hcell k hk u hu j hj

/-- Dynamic intermediate representations of the actual fixed refined core,
including all partial sums, complete arrays, and every old rolling layer. -/
theorem coreProgram_source_peak_le (N:ℕ) (z:List Bool) (A:ℕ) (ρ:Env)
    (hN:0<N) (hz:z.length≤N) (hA:A≤N)
    (h0:ρ 0=.nat N) (h1:ρ 1=.nat A) (h2:ρ 2=chooseValue (makeObservedCache N z))
    (h3:ρ 3=powerValue (makeObservedCache N z)) (h4:ρ 4=observedValue (makeObservedCache N z)) :
    coreProgram.peak ρ≤stepPeakBound N := by
  let c:=makeObservedCache N z
  have hB:sourceFrameBound N≤stepPeakBound N := by unfold stepPeakBound;omega
  have hp:=Paper37.IntegerOutputPeak.range_foldl_peak_le N
    (fun old d=>stepProgram.eval (Function.update (Function.update ρ 6 (.nat d)) 5 old))
    (fun old d=>stepProgram.peak (Function.update (Function.update ρ 6 (.nat d)) 5 old))
    (fun d old=>old=layerValue (cachedRefinedRun N c A d)) (stepPeakBound N) (by
      intro d hd old ho
      subst old
      have hs:State c A (cachedRefinedRun N c A d) d
          (Function.update (Function.update ρ 6 (.nat d)) 5 (layerValue (cachedRefinedRun N c A d))) := by
        constructor <;> simp [Function.update,h0,h1,h2,h3,h4,c]
      dsimp only
      rw [stepProgram_eval c A _ d _ hs hd]
      simp [cachedRefinedRun,hd]) (by
      intro d hd old ho
      subst old
      apply source_step_peak_le N z A d _ hN hz hA hd
      constructor <;> simp [Function.update,h0,h1,h2,h3,h4,c]) (baseProgram.eval ρ)
      (baseProgram_eval N ρ h0 c A) 0 (by omega)
  unfold coreProgram
  rw [Expr.peak]
  apply max_le
  · rw [←coreProgram,coreProgram_eval c A ρ h0 h1 h2 h3 h4]
    exact ((source_layer_size N z A N hN hz le_rfl).trans (sourceFrame_contains N).1).trans hB
  · change max ((Expr.var 0).peak ρ) (max (baseProgram.peak ρ) _)≤stepPeakBound N
    apply max_le
    · simpa [Expr.peak,Expr.eval,h0] using (nat_sourceFrame_le N N le_rfl).trans hB
    · apply max_le (baseProgram_peak_le ρ N h0)
      simpa only [Expr.eval,h0,Value.natVal] using hp.2

end Paper37.RefinedCoreProgram
