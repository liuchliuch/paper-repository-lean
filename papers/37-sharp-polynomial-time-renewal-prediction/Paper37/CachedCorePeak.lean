import Paper37.CachedCoreCorrect
import Paper37.CachedValueSize
import Paper37.IntegerOutputPeak
import Paper37.BoundedLoopTabulate

namespace Paper37.CachedCoreProgram
set_option maxRecDepth 3000
open Finset Paper37.BoundedLoop Paper37.CachedDP Paper37.DP Paper37.ContinuationDP

lemma unmarkedTerm_flat : Flat unmarkedTerm := by
  unfold unmarkedTerm coefficient oldPair multiplicity gap
  repeat first | exact Flat.lit _ | exact Flat.var _ | apply Flat.get |
    apply Flat.binary .add | apply Flat.binary .sub | apply Flat.binary .mul

lemma markedTerm_flat : Flat markedTerm := by
  unfold markedTerm coefficient oldPair multiplicity gap
  repeat first | exact Flat.lit _ | exact Flat.var _ | apply Flat.get | apply Flat.ifLT |
    apply Flat.binary .add | apply Flat.binary .sub | apply Flat.binary .mul

lemma loopBound_flat : Flat loopBound := by
  unfold loopBound gap
  repeat first | exact Flat.lit _ | exact Flat.var _ |
    apply Flat.binary .add | apply Flat.binary .div | apply Flat.binary .min

lemma unmarkedTerm_peak_le (ρ : Env) (B : ℕ) (hv : unmarkedTerm.varsBound ρ B) :
    unmarkedTerm.peak ρ≤4096*(B+1) := by
  apply (flat_peak_le unmarkedTerm_flat ρ B hv).trans
  simp [unmarkedTerm,coefficient,oldPair,multiplicity,gap,Expr.flatBudget]
  omega

lemma markedTerm_peak_le (ρ : Env) (B : ℕ) (hv : markedTerm.varsBound ρ B) :
    markedTerm.peak ρ≤4096*(B+1) := by
  apply (flat_peak_le markedTerm_flat ρ B hv).trans
  simp [markedTerm,coefficient,oldPair,multiplicity,gap,Expr.flatBudget]
  omega

lemma loopBound_peak_le (ρ : Env) (B : ℕ) (hv : loopBound.varsBound ρ B) :
    loopBound.peak ρ≤4096*(B+1) := by
  apply (flat_peak_le loopBound_flat ρ B hv).trans
  simp [loopBound,gap,Expr.flatBudget]
  omega

lemma state_scalar_eval {N : ℕ} (c : Cache N) (A : ℕ) (old : Layer N) (d : ℕ)
    (ρ : Env) (h : State c A old d ρ) (hd : d<N) (k u : Fin (N+1)) :
    let σ := Function.update (Function.update ρ 7 (.nat k.val)) 8 (.nat u.val)
    (sumTerm unmarkedTerm).eval σ=.nat ((cachedStep N c A ⟨d,hd⟩ old)[k.val][u.val]).1 ∧
    (sumTerm markedTerm).eval σ=.nat ((cachedStep N c A ⟨d,hd⟩ old)[k.val][u.val]).2 := by
  have he := congrArg (fun q => ((q.arrayVal[k.val]?.getD (.nat 0)).arrayVal[u.val]?.getD (.nat 0)))
    (stepProgram_eval c A old d ρ h hd)
  dsimp only at he
  rw [layerValue_get _ _ _ k.isLt u.isLt] at he
  simp only [stepProgram,Expr.eval,layerLength,h.horizon,Value.natVal,Value.arrayVal] at he
  rw [get_range_map _ _ _ k.isLt] at he
  simp only [Expr.eval,layerLength,Function.update_of_ne (by decide : (0:ℕ)≠7),h.horizon,Value.natVal,Value.arrayVal] at he
  rw [get_range_map _ _ _ u.isLt] at he
  simp only [Expr.eval,List.map_cons,List.map_nil] at he
  have he' : Value.array [(sumTerm unmarkedTerm).eval (Function.update (Function.update ρ 7 (.nat k.val)) 8 (.nat u.val)),
      (sumTerm markedTerm).eval (Function.update (Function.update ρ 7 (.nat k.val)) 8 (.nat u.val))]=
      .array [.nat ((cachedStep N c A ⟨d,hd⟩ old)[k.val][u.val]).1,
        .nat ((cachedStep N c A ⟨d,hd⟩ old)[k.val][u.val]).2] := by
    simpa [layerAt,k.isLt,u.isLt] using he
  have hfirst := congrArg (fun q => q.arrayVal[0]?.getD (.nat 0)) he'
  have hsecond := congrArg (fun q => q.arrayVal[1]?.getD (.nat 0)) he'
  exact ⟨by simpa [Value.arrayVal] using hfirst,by simpa [Value.arrayVal] using hsecond⟩

lemma unmarkedTerm_varsBound (ρ : Env) (B : ℕ)
    (h : ∀x≤10,(ρ x).representationSize≤B) : unmarkedTerm.varsBound ρ B := by
  simp only [unmarkedTerm,coefficient,oldPair,multiplicity,gap,Expr.varsBound]
  repeat' apply And.intro
  all_goals first | trivial | exact h _ (by omega)

lemma markedTerm_varsBound (ρ : Env) (B : ℕ)
    (h : ∀x≤10,(ρ x).representationSize≤B) : markedTerm.varsBound ρ B := by
  simp only [markedTerm,coefficient,oldPair,multiplicity,gap,Expr.varsBound]
  repeat' apply And.intro
  all_goals first | trivial | exact h _ (by omega)

lemma loopBound_varsBound (ρ : Env) (B : ℕ)
    (h : ∀x≤10,(ρ x).representationSize≤B) : loopBound.varsBound ρ B := by
  simp only [loopBound,gap,Expr.varsBound]
  repeat' apply And.intro
  all_goals first | trivial | exact h _ (by omega)

lemma source_state_bounds (N : ℕ) (z : List Bool) (A d : ℕ) (ρ : Env)
    (hN : 0<N) (hz : z.length≤N) (hA : A≤N) (hd : d≤N)
    (h : State (makeObservedCache N z) A (cachedRun N (makeObservedCache N z) A d) d ρ)
    (k u b : ℕ) (hk : k≤N) (hu : u≤N) (hb : b≤N)
    (h7 : ρ 7=.nat k) (h8 : ρ 8=.nat u) (h9 : ρ 9=.nat b)
    (h10 : (ρ 10).representationSize≤sourceFrameBound N) :
    ∀x≤10,(ρ x).representationSize≤sourceFrameBound N := by
  have hf := sourceFrame_contains N
  intro x hx
  interval_cases x
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

lemma sumTerm_source_peak_le (N : ℕ) (z : List Bool) (A d : ℕ) (ρ : Env)
    (hN : 0<N) (hz : z.length≤N) (hA : A≤N) (hd : d<N)
    (h : State (makeObservedCache N z) A (cachedRun N (makeObservedCache N z) A d) d ρ)
    (k u : Fin (N+1)) (term : Expr) (f : ℕ → ℕ)
    (hvars : ∀σ,(∀x≤10,(σ x).representationSize≤sourceFrameBound N) → term.varsBound σ (sourceFrameBound N))
    (hpeak : ∀σ,term.varsBound σ (sourceFrameBound N) → term.peak σ≤4096*(sourceFrameBound N+1))
    (ht : ∀b<min k.val (u.val/(d+1))+1,∀a,
      term.eval (Function.update (Function.update
        (Function.update (Function.update ρ 7 (.nat k.val)) 8 (.nat u.val)) 9 (.nat b)) 10 (.nat a))=.nat (f b))
    (hfinal : ((sumTerm term).eval (Function.update (Function.update ρ 7 (.nat k.val)) 8 (.nat u.val))).representationSize≤sourceFrameBound N) :
    (sumTerm term).peak (Function.update (Function.update ρ 7 (.nat k.val)) 8 (.nat u.val))≤
      20000*(sourceFrameBound N+1) := by
  let σ := Function.update (Function.update ρ 7 (.nat k.val)) 8 (.nat u.val)
  let M := min k.val (u.val/(d+1))+1
  let B := sourceFrameBound N
  let H := 20000*(B+1)
  have hs : State (makeObservedCache N z) A (cachedRun N (makeObservedCache N z) A d) d σ :=
    (h.update_high 7 (by omega) _).update_high 8 (by omega) _
  have h7 : σ 7=.nat k.val := by simp [σ,Function.update]
  have h8 : σ 8=.nat u.val := by simp [σ,Function.update]
  have hM : (loopBound.eval σ).natVal=M := by
    simp [loopBound,gap,Expr.eval,hs.depth,h7,h8,Value.natVal,M]
  have heval := sumTerm_eval σ term M f hM ht
  have hsum : (Value.nat (∑i∈range M,f i)).representationSize≤B := by rw [← heval];exact hfinal
  have hpart : ∀j≤M,(Value.nat (∑i∈range j,f i)).representationSize≤B := by
    intro j hj
    have hh : ∑i∈range j,f i≤∑i∈range M,f i := sum_le_sum_of_subset (range_mono hj)
    have hb := Nat.add_le_add_right (Nat.size_le_size hh) 1
    simpa only [Value.representationSize] using hb.trans (by simpa only [Value.representationSize] using hsum)
  have hloop : loopBound.peak σ≤4096*(B+1) := by
    apply loopBound_peak_le
    simp only [loopBound,gap,Expr.varsBound]
    repeat' apply And.intro
    all_goals first | trivial |
      simpa only [h7] using nat_sourceFrame_le N k.val (by omega) |
      simpa only [h8] using nat_sourceFrame_le N u.val (by omega) |
      simpa only [hs.depth] using nat_sourceFrame_le N d (by omega)
  have hfold := Paper37.IntegerOutputPeak.range_foldl_peak_le M
    (fun vv b => (Expr.add (.var 10) term).eval (Function.update (Function.update σ 9 (.nat b)) 10 vv))
    (fun vv b => (Expr.add (.var 10) term).peak (Function.update (Function.update σ 9 (.nat b)) 10 vv))
    (fun j vv => vv=.nat (∑i∈range j,f i)) H (by
      intro j hj vv hv
      subst vv
      dsimp only
      rw [Expr.eval,ht j hj]
      simp only [Expr.eval,Function.update_self,Value.natVal]
      rw [sum_range_succ]) (by
      intro j hj vv hv
      subst vv
      let τ := Function.update (Function.update σ 9 (.nat j)) 10 (.nat (∑i∈range j,f i))
      have ha : (τ 10).representationSize≤B := by simp only [τ,Function.update_self];exact hpart j (by omega)
      have hall := source_state_bounds N z A d τ hN hz hA (by omega)
        ((hs.update_high 9 (by omega) _).update_high 10 (by omega) _)
        k.val u.val j (by omega) (by omega) (by have hh := min_le_left k.val (u.val/(d+1));dsimp [M] at hj;omega)
        (by simp [τ,Function.update,h7]) (by simp [τ,Function.update,h8]) (by simp [τ,Function.update]) ha
      have hp := hpeak τ (hvars τ hall)
      have hav : (Expr.var 10).peak τ≤B := by simpa [Expr.peak,Expr.eval] using ha
      have hh := binary_peak_le .add (.var 10) term τ B (4096*(B+1)) hav hp
      change (Expr.add (.var 10) term).peak τ≤H
      exact hh.trans (by dsimp [H];omega)) (.nat 0) (by simp) 0 (by dsimp [H];omega)
  have hf :
      ((List.range M).foldl (fun vp b =>
        ((Expr.add (.var 10) term).eval (Function.update (Function.update σ 9 (.nat b)) 10 vp.1),
          max vp.2 ((Expr.add (.var 10) term).peak (Function.update (Function.update σ 9 (.nat b)) 10 vp.1))))
        (.nat 0,0)).2≤H := hfold.2
  change (sumTerm term).peak σ≤H
  unfold sumTerm
  rw [Expr.peak]
  apply max_le (hfinal.trans (by dsimp [H,B];omega))
  change max (loopBound.peak σ) (max ((Expr.lit 0).peak σ) _)≤H
  rw [hM]
  apply max_le (hloop.trans (by dsimp [H];omega))
  apply max_le
  · simp [Expr.peak,Expr.eval,Value.representationSize,H]
    omega
  · simpa only [Expr.eval] using hf

def cellPeakBound (N : ℕ) : ℕ := 40000*(sourceFrameBound N+1)+2

lemma source_cell_peak_le (N : ℕ) (z : List Bool) (A d : ℕ) (ρ : Env)
    (hN : 0<N) (hz : z.length≤N) (hA : A≤N) (hd : d<N)
    (h : State (makeObservedCache N z) A (cachedRun N (makeObservedCache N z) A d) d ρ)
    (k u : Fin (N+1)) :
    (Expr.array [sumTerm unmarkedTerm,sumTerm markedTerm]).peak
      (Function.update (Function.update ρ 7 (.nat k.val)) 8 (.nat u.val))≤cellPeakBound N := by
  let c := makeObservedCache N z
  let old := cachedRun N c A d
  let σ := Function.update (Function.update ρ 7 (.nat k.val)) 8 (.nat u.val)
  have hs : State c A old d σ := (h.update_high 7 (by omega) _).update_high 8 (by omega) _
  have h7 : σ 7=.nat k.val := by simp [σ,Function.update]
  have h8 : σ 8=.nat u.val := by simp [σ,Function.update]
  have hc := state_scalar_eval c A old d ρ h hd k u
  have he : cachedStep N c A ⟨d,hd⟩ old=cachedRun N c A (d+1) := by simp [cachedRun,hd,old]
  have hh := Paper37.CachedBitBounds.cachedRun_binarySize_source N z A (d+1) k u hN (by omega) hz
  have hgfinal : ((sumTerm unmarkedTerm).eval σ).representationSize≤sourceFrameBound N := by
    rw [hc.1,he]
    have hg : ((cachedRun N c A (d+1))[k.val][u.val]).1.size≤sourceWidth N := by
      unfold sourceWidth
      nlinarith [hh.1]
    simpa only [Value.representationSize] using (Nat.add_le_add_right hg 1).trans (sourceFrame_contains N).2.2.2.2.2.1
  have hsfinal : ((sumTerm markedTerm).eval σ).representationSize≤sourceFrameBound N := by
    rw [hc.2,he]
    simpa only [Value.representationSize] using (Nat.add_le_add_right hh.2 1).trans (sourceFrame_contains N).2.2.2.2.2.1
  have hg := sumTerm_source_peak_le N z A d ρ hN hz hA hd h k u unmarkedTerm
    (fun b => chooseAt c k b*powerAt c (c.observed[d+1]+b)*(layerAt old (k.val-b) (u.val-(d+1)*b)).1)
    (fun τ ht => unmarkedTerm_varsBound τ _ ht) (fun τ ht => unmarkedTerm_peak_le τ _ ht) (by
      intro b hb a
      apply unmarked_eval c A old d _ ((hs.update_high 9 (by omega) _).update_high 10 (by omega) _)
        k.val u.val b k.isLt u.isLt (by have hh := min_le_left k.val (u.val/(d+1));omega) hd
      · simp [Function.update,h7]
      · simp [Function.update,h8]
      · simp [Function.update]) hgfinal
  have hm := sumTerm_source_peak_le N z A d ρ hN hz hA hd h k u markedTerm
    (fun b => chooseAt c k b*powerAt c (c.observed[d+1]+b)*
      ((layerAt old (k.val-b) (u.val-(d+1)*b)).2+
        (if A<d+1 then b else 0)*(layerAt old (k.val-b) (u.val-(d+1)*b)).1))
    (fun τ ht => markedTerm_varsBound τ _ ht) (fun τ ht => markedTerm_peak_le τ _ ht) (by
      intro b hb a
      apply marked_eval c A old d _ ((hs.update_high 9 (by omega) _).update_high 10 (by omega) _)
        k.val u.val b k.isLt u.isLt (by have hh := min_le_left k.val (u.val/(d+1));omega) hd
      · simp [Function.update,h7]
      · simp [Function.update,h8]
      · simp [Function.update]) hsfinal
  have hp := array_peak_le [sumTerm unmarkedTerm,sumTerm markedTerm] σ
    (fun _ => 20000*(sourceFrameBound N+1)) (by
      intro e he
      simp only [List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with rfl|rfl
      · exact hg
      · exact hm)
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hp
  change (Expr.array [sumTerm unmarkedTerm,sumTerm markedTerm]).peak σ≤_
  unfold cellPeakBound
  omega

lemma layerLength_peak_le (ρ : Env) (N : ℕ) (h0 : ρ 0=.nat N) :
    layerLength.peak ρ≤5*(sourceFrameBound N+1) := by
  have hv : (Expr.var 0).peak ρ≤sourceFrameBound N := by
    simpa [Expr.peak,Expr.eval,h0] using nat_sourceFrame_le N N le_rfl
  have hl : (Expr.lit 1).peak ρ≤2 := by norm_num [Expr.peak,Expr.eval,Value.representationSize]
  have hh := binary_peak_le .add (.var 0) (.lit 1) ρ _ _ hv hl
  change (Expr.add (.var 0) (.lit 1)).peak ρ≤_
  exact hh.trans (by have hB := (sourceFrame_contains N).2.2.2.2.2.2;omega)

def rowPeakBound (N : ℕ) : ℕ := (N+2)*cellPeakBound N+5*(sourceFrameBound N+1)+2
def stepPeakBound (N : ℕ) : ℕ := (N+2)*rowPeakBound N+5*(sourceFrameBound N+1)+2

lemma source_step_peak_le (N : ℕ) (z : List Bool) (A d : ℕ) (ρ : Env)
    (hN : 0<N) (hz : z.length≤N) (hA : A≤N) (hd : d<N)
    (h : State (makeObservedCache N z) A (cachedRun N (makeObservedCache N z) A d) d ρ) :
    stepProgram.peak ρ≤stepPeakBound N := by
  unfold stepProgram stepPeakBound
  apply tabulate_peak_le 7 layerLength _ ρ (N+1) (5*(sourceFrameBound N+1)) (rowPeakBound N)
  · simp [layerLength,Expr.eval,h.horizon,Value.natVal]
  · exact layerLength_peak_le ρ N h.horizon
  · intro k hk
    unfold rowPeakBound
    apply tabulate_peak_le 8 layerLength _ (Function.update ρ 7 (.nat k)) (N+1)
      (5*(sourceFrameBound N+1)) (cellPeakBound N)
    · simp [layerLength,Expr.eval,Function.update,h.horizon,Value.natVal]
    · apply layerLength_peak_le _ N
      simp [Function.update,h.horizon]
    · intro u hu
      exact source_cell_peak_le N z A d ρ hN hz hA hd h ⟨k,hk⟩ ⟨u,hu⟩

lemma baseProgram_peak_le (ρ : Env) (N : ℕ) (h0 : ρ 0=.nat N) :
    baseProgram.peak ρ≤stepPeakBound N := by
  let cell : Expr := .array [.ifLT (.var 7) (.lit 1)
    (.ifLT (.var 8) (.lit 1) (.lit 1) (.lit 0)) (.lit 0),.lit 0]
  have hflat : Flat cell := by
    dsimp [cell]
    apply Flat.array
    intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl
    · apply Flat.ifLT
      · exact Flat.var _
      · exact Flat.lit _
      · apply Flat.ifLT
        · exact Flat.var _
        · exact Flat.lit _
        · exact Flat.lit _
        · exact Flat.lit _
      · exact Flat.lit _
    · exact Flat.lit _
  have hcell : ∀k<N+1,∀u<N+1,cell.peak
      (Function.update (Function.update ρ 7 (.nat k)) 8 (.nat u))≤cellPeakBound N := by
    intro k hk u hu
    have hkv := nat_sourceFrame_le N k (by omega)
    have huv := nat_sourceFrame_le N u (by omega)
    have hv : cell.varsBound (Function.update (Function.update ρ 7 (.nat k)) 8 (.nat u)) (sourceFrameBound N) := by
      simp only [cell,Expr.varsBound,List.mem_cons,List.not_mem_nil,or_false]
      intro e he
      rcases he with rfl|rfl
      · simp only [Expr.varsBound]
        repeat' apply And.intro
        all_goals
          first
          | trivial
          | simpa [Function.update] using hkv
          | simpa [Function.update] using huv
      · simp [Expr.varsBound]
    apply (flat_peak_le hflat _ _ hv).trans
    dsimp [cell]
    simp [Expr.flatBudget,cellPeakBound]
    omega
  change (Expr.tabulate 7 layerLength (.tabulate 8 layerLength cell)).peak ρ≤_
  unfold stepPeakBound
  apply tabulate_peak_le 7 layerLength _ ρ (N+1) (5*(sourceFrameBound N+1)) (rowPeakBound N)
  · simp [layerLength,Expr.eval,h0,Value.natVal]
  · exact layerLength_peak_le ρ N h0
  · intro k hk
    unfold rowPeakBound
    apply tabulate_peak_le 8 layerLength cell (Function.update ρ 7 (.nat k)) (N+1)
      (5*(sourceFrameBound N+1)) (cellPeakBound N)
    · simp [layerLength,Expr.eval,Function.update,h0,Value.natVal]
    · apply layerLength_peak_le _ N
      simp [Function.update,h0]
    · intro u hu
      exact hcell k hk u hu

/-- Peak representation length along the complete, fixed first-order cached
DP program, including all partial scalar sums and all tabulated arrays. -/
theorem coreProgram_source_peak_le (N : ℕ) (z : List Bool) (A : ℕ) (ρ : Env)
    (hN : 0<N) (hz : z.length≤N) (hA : A≤N)
    (h0 : ρ 0=.nat N) (h1 : ρ 1=.nat A) (h2 : ρ 2=chooseValue (makeObservedCache N z))
    (h3 : ρ 3=powerValue (makeObservedCache N z)) (h4 : ρ 4=observedValue (makeObservedCache N z)) :
    coreProgram.peak ρ≤stepPeakBound N := by
  let c := makeObservedCache N z
  have hB : sourceFrameBound N≤stepPeakBound N := by
    unfold stepPeakBound
    omega
  have hp := Paper37.IntegerOutputPeak.range_foldl_peak_le N
    (fun old d => stepProgram.eval (Function.update (Function.update ρ 6 (.nat d)) 5 old))
    (fun old d => stepProgram.peak (Function.update (Function.update ρ 6 (.nat d)) 5 old))
    (fun d old => old=layerValue (cachedRun N c A d)) (stepPeakBound N) (by
      intro d hd old ho
      subst old
      have hs : State c A (cachedRun N c A d) d
          (Function.update (Function.update ρ 6 (.nat d)) 5 (layerValue (cachedRun N c A d))) := by
        constructor <;> simp [Function.update,h0,h1,h2,h3,h4,c]
      dsimp only
      rw [stepProgram_eval c A _ d _ hs hd]
      simp [cachedRun,hd]) (by
      intro d hd old ho
      subst old
      apply source_step_peak_le N z A d _ hN hz hA hd
      constructor <;> simp [Function.update,h0,h1,h2,h3,h4,c]) (baseProgram.eval ρ)
      (baseProgram_eval N ρ h0 c A) 0 (by omega)
  unfold coreProgram
  rw [Expr.peak]
  apply max_le
  · rw [← coreProgram,coreProgram_eval c A ρ h0 h1 h2 h3 h4]
    exact ((source_layer_size N z A N hN hz le_rfl).trans (sourceFrame_contains N).1).trans hB
  · change max ((Expr.var 0).peak ρ) (max (baseProgram.peak ρ) _)≤stepPeakBound N
    apply max_le
    · simpa [Expr.peak,Expr.eval,h0] using (nat_sourceFrame_le N N le_rfl).trans hB
    · apply max_le (baseProgram_peak_le ρ N h0)
      simpa only [Expr.eval,h0,Value.natVal] using hp.2

lemma stepPeakBound_le (N : ℕ) :
    stepPeakBound N≤1000000*(N+1)^2*(sourceFrameBound N+1) := by
  let S := sourceFrameBound N+1
  have hS : 1≤S := by dsimp [S];omega
  have hm1 : S≤(N+1)*S := by
    simpa using Nat.mul_le_mul_right S (show 1≤N+1 by omega)
  have hm2 : S≤(N+1)^2*S := by
    have hp : 0<(N+1)^2 := by positivity
    simpa using Nat.mul_le_mul_right S (show 1≤(N+1)^2 by omega)
  have hc : cellPeakBound N≤40002*S := by unfold cellPeakBound;dsimp [S];omega
  have hrm := Nat.mul_le_mul (show N+2≤2*(N+1) by omega) hc
  have hr : rowPeakBound N≤100000*(N+1)*S := by
    unfold rowPeakBound
    change (N+2)*cellPeakBound N+5*S+2≤_
    nlinarith [hrm]
  have hsm := Nat.mul_le_mul (show N+2≤2*(N+1) by omega) hr
  unfold stepPeakBound
  change (N+2)*rowPeakBound N+5*S+2≤1000000*(N+1)^2*S
  nlinarith [hsm]

end Paper37.CachedCoreProgram
