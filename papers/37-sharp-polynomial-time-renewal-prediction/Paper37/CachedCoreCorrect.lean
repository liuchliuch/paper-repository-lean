import Paper37.CachedCoreProgram

namespace Paper37.CachedCoreProgram
open Finset Paper37.DP Paper37.CachedDP Paper37.BoundedLoop Paper37.ContinuationDP

structure State {N : ℕ} (c : Cache N) (A : ℕ) (old : Layer N) (d : ℕ) (ρ : Env) : Prop where
  horizon : ρ 0=.nat N
  age : ρ 1=.nat A
  choose : ρ 2=chooseValue c
  power : ρ 3=powerValue c
  observed : ρ 4=observedValue c
  table : ρ 5=layerValue old
  depth : ρ 6=.nat d

lemma unmarked_eval {N : ℕ} (c : Cache N) (A : ℕ) (old : Layer N) (d : ℕ) (ρ : Env)
    (h : State c A old d ρ) (k u b : ℕ) (hk : k<N+1) (hu : u<N+1)
    (hb : b<N+1) (hd : d<N) (h7 : ρ 7=.nat k) (h8 : ρ 8=.nat u) (h9 : ρ 9=.nat b) :
    unmarkedTerm.eval ρ=.nat (chooseAt c ⟨k,hk⟩ b * powerAt c (c.observed[d+1]+b) *
      (layerAt old (k-b) (u-(d+1)*b)).1) := by
  simp only [unmarkedTerm,coefficient,oldPair,multiplicity,gap,Expr.eval,
    h.choose,h.power,h.observed,h.table,h.depth,h7,h8,h9,Value.natVal,observedValue]
  rw [chooseValue_get c k b hk hb,natArray_get c.observed (d+1) (by omega)]
  simp only [Value.natVal]
  rw [powerValue_get_total,layerValue_get old (k-b) (u-(d+1)*b) (by omega) (by omega)]
  rfl

lemma marked_eval {N : ℕ} (c : Cache N) (A : ℕ) (old : Layer N) (d : ℕ) (ρ : Env)
    (h : State c A old d ρ) (k u b : ℕ) (hk : k<N+1) (hu : u<N+1)
    (hb : b<N+1) (hd : d<N) (h7 : ρ 7=.nat k) (h8 : ρ 8=.nat u) (h9 : ρ 9=.nat b) :
    markedTerm.eval ρ=.nat (chooseAt c ⟨k,hk⟩ b * powerAt c (c.observed[d+1]+b) *
      ((layerAt old (k-b) (u-(d+1)*b)).2+
        (if A<d+1 then b else 0)*(layerAt old (k-b) (u-(d+1)*b)).1)) := by
  simp only [markedTerm,coefficient,oldPair,multiplicity,gap,Expr.eval,
    h.age,h.choose,h.power,h.observed,h.table,h.depth,h7,h8,h9,Value.natVal,observedValue]
  rw [chooseValue_get c k b hk hb,natArray_get c.observed (d+1) (by omega)]
  simp only [Value.natVal]
  rw [powerValue_get_total,layerValue_get old (k-b) (u-(d+1)*b) (by omega) (by omega)]
  by_cases ha : A<d+1 <;> simp [ha,Value.natVal,Value.arrayVal]

lemma State.update_high {N : ℕ} {c : Cache N} {A : ℕ} {old : Layer N} {d : ℕ} {ρ : Env}
    (h : State c A old d ρ) (i : ℕ) (hi : 6 < i) (x : Value) :
    State c A old d (Function.update ρ i x) := by
  cases h
  constructor <;> rw [Function.update_of_ne (by omega)] <;> assumption

lemma stepProgram_eval {N : ℕ} (c : Cache N) (A : ℕ) (old : Layer N) (d : ℕ)
    (ρ : Env) (h : State c A old d ρ) (hd : d<N) :
    stepProgram.eval ρ=layerValue (cachedStep N c A ⟨d,hd⟩ old) := by
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
  let σ := Function.update (Function.update ρ 7 (.nat k)) 8 (.nat u)
  have hs : State c A old d σ := (h.update_high 7 (by omega) _).update_high 8 (by omega) _
  have h7 : σ 7=.nat k := by simp [σ,Function.update]
  have h8 : σ 8=.nat u := by simp [σ,Function.update]
  have hM : (loopBound.eval σ).natVal=min k (u/(d+1))+1 := by
    simp [loopBound,gap,Expr.eval,hs.depth,h7,h8,Value.natVal]
  have hg := sumTerm_eval σ unmarkedTerm _
    (fun b => chooseAt c ⟨k,hk'⟩ b*powerAt c (c.observed[d+1]+b)*
      (layerAt old (k-b) (u-(d+1)*b)).1) hM (by
        intro b hb a
        apply unmarked_eval c A old d _ ((hs.update_high 9 (by omega) _).update_high 10 (by omega) _)
          k u b hk' hu' (by have hh := min_le_left k (u/(d+1)); omega) hd
        · simp [Function.update,h7]
        · simp [Function.update,h8]
        · simp [Function.update])
  have hm := sumTerm_eval σ markedTerm _
    (fun b => chooseAt c ⟨k,hk'⟩ b*powerAt c (c.observed[d+1]+b)*
      ((layerAt old (k-b) (u-(d+1)*b)).2+
        (if A<d+1 then b else 0)*(layerAt old (k-b) (u-(d+1)*b)).1)) hM (by
        intro b hb a
        apply marked_eval c A old d _ ((hs.update_high 9 (by omega) _).update_high 10 (by omega) _)
          k u b hk' hu' (by have hh := min_le_left k (u/(d+1)); omega) hd
        · simp [Function.update,h7]
        · simp [Function.update,h8]
        · simp [Function.update])
  change Value.array [(sumTerm unmarkedTerm).eval σ,(sumTerm markedTerm).eval σ] = _
  rw [hg,hm]
  have hstep := Paper37.CachedOperations.interpretedStep_correct N c A ⟨d,hd⟩ old
  rw [← hstep]
  unfold layerAt
  rw [dif_pos hk',dif_pos hu']
  simp only [Paper37.CachedOperations.interpretedStep,Vector.getElem_ofFn,
    Paper37.CachedOperations.gKernel_eval,Paper37.CachedOperations.sKernel_eval,List.headD_cons]
  rfl

lemma baseProgram_eval (N : ℕ) (ρ : Env) (h0 : ρ 0=.nat N) (c : Cache N) (A : ℕ) :
    baseProgram.eval ρ=layerValue (cachedRun N c A 0) := by
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
  simp [Expr.eval,Function.update,Value.natVal,Nat.lt_one_iff,layerAt,hk',hu',cachedRun,Vector.getElem_ofFn]
  all_goals split_ifs <;> simp_all

/-- The *single finite syntax term* evaluates to the actual cached table for
every horizon. Extra environment slots (e.g. the source word and outer query
loop accumulators) are arbitrary. -/
theorem coreProgram_eval {N : ℕ} (c : Cache N) (A : ℕ) (ρ : Env)
    (h0 : ρ 0=.nat N) (h1 : ρ 1=.nat A) (h2 : ρ 2=chooseValue c)
    (h3 : ρ 3=powerValue c) (h4 : ρ 4=observedValue c) :
    coreProgram.eval ρ=layerValue (cachedRun N c A N) := by
  have hf : ∀d≤N,
      (List.range d).foldl (fun old i => stepProgram.eval
        (Function.update (Function.update ρ 6 (.nat i)) 5 old))
        (layerValue (cachedRun N c A 0))=layerValue (cachedRun N c A d) := by
    intro d
    induction d with
    | zero => intro hd; rfl
    | succ d ih =>
      intro hd
      rw [List.range_succ,List.foldl_append,ih (by omega)]
      simp only [List.foldl_cons,List.foldl_nil]
      have hs : State c A (cachedRun N c A d) d
          (Function.update (Function.update ρ 6 (.nat d)) 5 (layerValue (cachedRun N c A d))) := by
        constructor <;> simp [Function.update,h0,h1,h2,h3,h4]
      rw [stepProgram_eval c A _ d _ hs (by omega)]
      simp only [cachedRun,dif_pos (by omega : d<N)]
  simp only [coreProgram,Expr.eval,h0,Value.natVal]
  rw [baseProgram_eval N ρ h0 c A]
  exact hf N le_rfl

theorem coreProgram_source (N : ℕ) (z : List Bool) (A : ℕ) (ρ : Env) (hz : z.length≤N)
    (h0 : ρ 0=.nat N) (h1 : ρ 1=.nat A) (h2 : ρ 2=chooseValue (makeObservedCache N z))
    (h3 : ρ 3=powerValue (makeObservedCache N z)) (h4 : ρ 4=observedValue (makeObservedCache N z)) :
    coreProgram.eval ρ=layerValue (run N (observedCounts z) A N) := by
  rw [coreProgram_eval (makeObservedCache N z) A ρ h0 h1 h2 h3 h4,makeObservedCache_eq,
    cachedRun_correct N (observedCounts z) A N le_rfl (observedCounts_le_horizon N z hz)]

end Paper37.CachedCoreProgram
