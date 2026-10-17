import Paper37.CachedCoreProgram
import Paper37.CachedRefinedOperations

/-! One fixed first-order bounded-loop syntax term computes the actual cached
occupied-type refinement for every horizon. -/
namespace Paper37.RefinedCoreProgram
open Finset Paper37.DP Paper37.CachedDP Paper37.BoundedLoop Paper37.ContinuationDP
open Paper37.AdaptiveDP Paper37.RefinedContinuation Paper37.CachedRefinedDP
open Paper37.CachedCoreProgram (natArray chooseValue powerValue observedValue get_range_map
  natArray_get chooseValue_get powerValue_get_total fold_add_of)
private abbrev v := Expr.var
private abbrev n := Expr.lit
private abbrev add := Expr.add
private abbrev mul := Expr.mul
private abbrev sub := Expr.sub
private abbrev get := Expr.get

def layerValue {N : ℕ} (a : RefinedLayer N) : Value :=
  .array ((List.range (N+1)).map fun k =>
    .array ((List.range (N+1)).map fun u =>
      .array ((List.range (N+1)).map fun j =>
        .array [.nat (refinedLayerAt a k u j).1,.nat (refinedLayerAt a k u j).2])))

def layerLength : Expr := add (v 0) (n 1)
def gap : Expr := add (v 6) (n 1)
def multiplicity : Expr := get (v 4) gap
def epsilon : Expr := .ifLT (n 0) (add multiplicity (v 9)) (n 1) (n 0)
def loopBound : Expr := add (v 7) (n 1)
def coefficient : Expr := mul (get (get (v 2) (v 7)) (v 9))
  (get (v 3) (add multiplicity (v 9)))
def oldPair : Expr := get (get (get (v 5) (sub (v 7) (v 9)))
  (sub (v 8) (mul gap (v 9)))) (sub (v 27) epsilon)
def unmarkedTerm : Expr := mul coefficient (get oldPair (n 0))
def markedTerm : Expr := mul coefficient (add (get oldPair (n 1))
  (mul (.ifLT (v 1) gap (v 9) (n 0)) (get oldPair (n 0))))
def guardTerm (term : Expr) : Expr := .ifLT (v 8) (mul gap (v 9)) (n 0)
  (.ifLT (v 27) epsilon (n 0) term)
def sumTerm (term : Expr) : Expr := .fold 9 10 loopBound (n 0) (add (v 10) (guardTerm term))
def stepProgram : Expr := .tabulate 7 layerLength (.tabulate 8 layerLength
  (.tabulate 27 layerLength (.array [sumTerm unmarkedTerm,sumTerm markedTerm])))
def baseProgram : Expr := .tabulate 7 layerLength (.tabulate 8 layerLength
  (.tabulate 27 layerLength (.array [.ifLT (v 7) (n 1)
    (.ifLT (v 8) (n 1) (.ifLT (v 27) (n 1) (n 1) (n 0)) (n 0)) (n 0),n 0])))
def coreProgram : Expr := .fold 6 5 (v 0) baseProgram stepProgram

lemma layerValue_get {N : ℕ} (a : RefinedLayer N) (k u j : ℕ)
    (hk : k<N+1) (hu : u<N+1) (hj : j<N+1) :
    (((layerValue a).arrayVal[k]?.getD (.nat 0)).arrayVal[u]?.getD (.nat 0)).arrayVal[j]?.getD (.nat 0)=
      .array [.nat (refinedLayerAt a k u j).1,.nat (refinedLayerAt a k u j).2] := by
  simp only [layerValue,Value.arrayVal,get_range_map _ _ _ hk,get_range_map _ _ _ hu,
    get_range_map _ _ _ hj]

structure State {N : ℕ} (c : Cache N) (A : ℕ) (old : RefinedLayer N) (d : ℕ) (ρ : Env) : Prop where
  horizon : ρ 0=.nat N
  age : ρ 1=.nat A
  choose : ρ 2=chooseValue c
  power : ρ 3=powerValue c
  observed : ρ 4=observedValue c
  table : ρ 5=layerValue old
  depth : ρ 6=.nat d

lemma State.update_high {N : ℕ} {c : Cache N} {A : ℕ} {old : RefinedLayer N} {d : ℕ} {ρ : Env}
    (h : State c A old d ρ) (i : ℕ) (hi : 6 < i) (x : Value) :
    State c A old d (Function.update ρ i x) := by
  cases h
  constructor <;> rw [Function.update_of_ne (by omega)] <;> assumption

lemma unmarked_eval {N : ℕ} (c : Cache N) (A : ℕ) (old : RefinedLayer N) (d : ℕ) (ρ : Env)
    (h : State c A old d ρ) (k u j b : ℕ) (hk : k<N+1) (hu : u<N+1) (hj : j<N+1)
    (hb : b<N+1) (hd : d<N) (h7 : ρ 7=.nat k) (h8 : ρ 8=.nat u)
    (h27 : ρ 27=.nat j) (h9 : ρ 9=.nat b) :
    unmarkedTerm.eval ρ=.nat (chooseAt c ⟨k,hk⟩ b*powerAt c (c.observed[d+1]+b)*
      (refinedLayerAt old (k-b) (u-(d+1)*b) (j-(if 0<c.observed[d+1]+b then 1 else 0))).1) := by
  simp only [unmarkedTerm,coefficient,oldPair,epsilon,multiplicity,gap,Expr.eval,
    h.choose,h.power,h.observed,h.table,h.depth,h7,h8,h27,h9,Value.natVal,observedValue]
  rw [chooseValue_get c k b hk hb,natArray_get c.observed (d+1) (by omega)]
  simp only [Value.natVal]
  rw [powerValue_get_total]
  split_ifs <;> rw [layerValue_get old (k-b) (u-(d+1)*b) _ (by omega) (by omega) (by omega)] <;> rfl

lemma marked_eval {N : ℕ} (c : Cache N) (A : ℕ) (old : RefinedLayer N) (d : ℕ) (ρ : Env)
    (h : State c A old d ρ) (k u j b : ℕ) (hk : k<N+1) (hu : u<N+1) (hj : j<N+1)
    (hb : b<N+1) (hd : d<N) (h7 : ρ 7=.nat k) (h8 : ρ 8=.nat u)
    (h27 : ρ 27=.nat j) (h9 : ρ 9=.nat b) :
    markedTerm.eval ρ=.nat (chooseAt c ⟨k,hk⟩ b*powerAt c (c.observed[d+1]+b)*
      ((refinedLayerAt old (k-b) (u-(d+1)*b) (j-(if 0<c.observed[d+1]+b then 1 else 0))).2+
        (if A<d+1 then b else 0)*
          (refinedLayerAt old (k-b) (u-(d+1)*b) (j-(if 0<c.observed[d+1]+b then 1 else 0))).1)) := by
  simp only [markedTerm,coefficient,oldPair,epsilon,multiplicity,gap,Expr.eval,
    h.age,h.choose,h.power,h.observed,h.table,h.depth,h7,h8,h27,h9,Value.natVal,observedValue]
  rw [chooseValue_get c k b hk hb,natArray_get c.observed (d+1) (by omega)]
  simp only [Value.natVal]
  rw [powerValue_get_total]
  split_ifs <;> rw [layerValue_get old (k-b) (u-(d+1)*b) _ (by omega) (by omega) (by omega)]
  all_goals by_cases ha:A<d+1 <;> simp [ha,Value.natVal,Value.arrayVal]

lemma guardTerm_eval {N : ℕ} (c : Cache N) (A : ℕ) (old : RefinedLayer N) (d : ℕ) (ρ : Env)
    (h : State c A old d ρ) (term : Expr) (w k u j b : ℕ) (hd : d<N)
    (h8 : ρ 8=.nat u) (h27 : ρ 27=.nat j) (h9 : ρ 9=.nat b)
    (ht : term.eval ρ=.nat w) :
    (guardTerm term).eval ρ=.nat (if (d+1)*b≤u ∧ (if 0<c.observed[d+1]+b then 1 else 0)≤j then w else 0) := by
  simp only [guardTerm,epsilon,multiplicity,gap,Expr.eval,h.observed,h.depth,h8,h27,h9,
    Value.natVal,observedValue]
  rw [natArray_get c.observed (d+1) (by omega)]
  simp only [Value.natVal]
  split_ifs <;> simp_all [Expr.eval,Value.natVal] <;> omega

lemma sumTerm_eval (ρ : Env) (term : Expr) (M : ℕ) (f : ℕ→ℕ)
    (hM : (loopBound.eval ρ).natVal=M)
    (ht : ∀b<M,∀a,(guardTerm term).eval
      (Function.update (Function.update ρ 9 (.nat b)) 10 (.nat a))=.nat (f b)) :
    (sumTerm term).eval ρ=.nat (∑b∈range M,f b) := by
  simp only [sumTerm,Expr.eval,hM]
  rw [fold_add_of _ f _ (by
    intro b hb a
    simp only [List.mem_range] at hb
    rw [ht b hb a]
    simp [Function.update,Value.natVal])]
  simp only [Value.natVal,zero_add]
  congr 1

set_option maxHeartbeats 800000 in
lemma stepProgram_eval {N : ℕ} (c : Cache N) (A : ℕ) (old : RefinedLayer N) (d : ℕ)
    (ρ : Env) (h : State c A old d ρ) (hd : d<N) :
    stepProgram.eval ρ=layerValue (cachedRefinedStep N c A ⟨d,hd⟩ old) := by
  simp only [stepProgram,Expr.eval,layerLength,h.horizon,Value.natVal,layerValue]
  congr 1
  apply List.map_congr_left
  intro k hk
  have hk' : k<N+1 := List.mem_range.mp hk
  simp only [Expr.eval,layerLength,Function.update_of_ne (by decide : (0:ℕ)≠7),h.horizon,Value.natVal]
  congr 1
  apply List.map_congr_left
  intro u hu
  have hu' : u<N+1 := List.mem_range.mp hu
  simp only [Expr.eval,layerLength,Function.update_of_ne (by decide : (0:ℕ)≠8),
    Function.update_of_ne (by decide : (0:ℕ)≠7),h.horizon,Value.natVal]
  congr 1
  apply List.map_congr_left
  intro j hj
  have hj' : j<N+1 := List.mem_range.mp hj
  let σ := Function.update (Function.update (Function.update ρ 7 (.nat k)) 8 (.nat u)) 27 (.nat j)
  have hs : State c A old d σ := ((h.update_high 7 (by omega) _).update_high 8 (by omega) _).update_high 27 (by omega) _
  have h7 : σ 7=.nat k := by simp [σ,Function.update]
  have h8 : σ 8=.nat u := by simp [σ,Function.update]
  have h27 : σ 27=.nat j := by simp [σ,Function.update]
  have hM : (loopBound.eval σ).natVal=k+1 := by simp [loopBound,Expr.eval,h7,Value.natVal]
  have hg := sumTerm_eval σ unmarkedTerm _
    (fun b => if (d+1)*b≤u ∧ (if 0<c.observed[d+1]+b then 1 else 0)≤j then
      chooseAt c ⟨k,hk'⟩ b*powerAt c (c.observed[d+1]+b)*
        (refinedLayerAt old (k-b) (u-(d+1)*b) (j-(if 0<c.observed[d+1]+b then 1 else 0))).1 else 0) hM (by
      intro b hb a
      have hs' := (hs.update_high 9 (by omega) (.nat b)).update_high 10 (by omega) (.nat a)
      apply guardTerm_eval c A old d _ hs' unmarkedTerm _ k u j b hd
        (by simp [Function.update,h8]) (by simp [Function.update,h27]) (by simp [Function.update])
      apply unmarked_eval c A old d _ hs' k u j b hk' hu' hj' (by omega) hd
        (by simp [Function.update,h7]) (by simp [Function.update,h8])
        (by simp [Function.update,h27]) (by simp [Function.update]))
  have hm := sumTerm_eval σ markedTerm _
    (fun b => if (d+1)*b≤u ∧ (if 0<c.observed[d+1]+b then 1 else 0)≤j then
      chooseAt c ⟨k,hk'⟩ b*powerAt c (c.observed[d+1]+b)*
        ((refinedLayerAt old (k-b) (u-(d+1)*b) (j-(if 0<c.observed[d+1]+b then 1 else 0))).2+
          (if A<d+1 then b else 0)*
            (refinedLayerAt old (k-b) (u-(d+1)*b) (j-(if 0<c.observed[d+1]+b then 1 else 0))).1) else 0) hM (by
      intro b hb a
      have hs' := (hs.update_high 9 (by omega) (.nat b)).update_high 10 (by omega) (.nat a)
      apply guardTerm_eval c A old d _ hs' markedTerm _ k u j b hd
        (by simp [Function.update,h8]) (by simp [Function.update,h27]) (by simp [Function.update])
      apply marked_eval c A old d _ hs' k u j b hk' hu' hj' (by omega) hd
        (by simp [Function.update,h7]) (by simp [Function.update,h8])
        (by simp [Function.update,h27]) (by simp [Function.update]))
  change Value.array [(sumTerm unmarkedTerm).eval σ,(sumTerm markedTerm).eval σ]=_
  rw [hg,hm,←Paper37.CachedRefinedOperations.interpretedStep_correct]
  unfold refinedLayerAt
  rw [dif_pos hk',dif_pos hu',dif_pos hj']
  simp only [Paper37.CachedRefinedOperations.interpretedStep,Vector.getElem_ofFn,
    Paper37.CachedRefinedOperations.gKernel_eval,Paper37.CachedRefinedOperations.sKernel_eval,List.headD_cons]
  simp only [refinedAt,Vector.getElem_ofFn]
  unfold refinedLayerAt
  simp only [refinedAt]

lemma baseProgram_eval (N : ℕ) (ρ : Env) (h0 : ρ 0=.nat N) (c : Cache N) (A : ℕ) :
    baseProgram.eval ρ=layerValue (cachedRefinedRun N c A 0) := by
  simp only [baseProgram,Expr.eval,layerLength,h0,Value.natVal,layerValue]
  congr 1
  apply List.map_congr_left
  intro k hk
  have hk' := List.mem_range.mp hk
  simp only [Function.update_of_ne (by decide : (0:ℕ)≠7),h0]
  congr 1
  apply List.map_congr_left
  intro u hu
  have hu' := List.mem_range.mp hu
  simp only [Function.update_of_ne (by decide : (0:ℕ)≠8),Function.update_of_ne (by decide : (0:ℕ)≠7),h0]
  congr 1
  apply List.map_congr_left
  intro j hj
  have hj' := List.mem_range.mp hj
  simp [Expr.eval,Function.update,Value.natVal,Nat.lt_one_iff,refinedLayerAt,hk',hu',hj',
    cachedRefinedRun,refinedAt,Vector.getElem_ofFn]
  all_goals split_ifs <;> simp_all

/-- Extra environment slots are arbitrary: this one finite program uniformly
computes every cached refined table, not a horizon-indexed program family. -/
theorem coreProgram_eval {N : ℕ} (c : Cache N) (A : ℕ) (ρ : Env)
    (h0 : ρ 0=.nat N) (h1 : ρ 1=.nat A) (h2 : ρ 2=chooseValue c)
    (h3 : ρ 3=powerValue c) (h4 : ρ 4=observedValue c) :
    coreProgram.eval ρ=layerValue (cachedRefinedRun N c A N) := by
  have hf : ∀d≤N,(List.range d).foldl (fun old i => stepProgram.eval
      (Function.update (Function.update ρ 6 (.nat i)) 5 old))
      (layerValue (cachedRefinedRun N c A 0))=layerValue (cachedRefinedRun N c A d) := by
    intro d
    induction d with
    | zero => intro hd;rfl
    | succ d ih =>
      intro hd
      rw [List.range_succ,List.foldl_append,ih (by omega)]
      simp only [List.foldl_cons,List.foldl_nil]
      have hs : State c A (cachedRefinedRun N c A d) d
          (Function.update (Function.update ρ 6 (.nat d)) 5 (layerValue (cachedRefinedRun N c A d))) := by
        constructor <;> simp [Function.update,h0,h1,h2,h3,h4]
      rw [stepProgram_eval c A _ d _ hs (by omega)]
      simp only [cachedRefinedRun,dif_pos (by omega : d<N)]
  simp only [coreProgram,Expr.eval,h0,Value.natVal]
  rw [baseProgram_eval N ρ h0 c A]
  exact hf N le_rfl

end Paper37.RefinedCoreProgram
