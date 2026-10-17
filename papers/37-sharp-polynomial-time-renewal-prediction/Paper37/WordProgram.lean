import Paper37.BoundedLoop
import Paper37.CachedCoreProgram
import Paper37.CachedOutput

/-! Finite first-order array parsing. The sole word input is a finite array
of zero/one integers. The histogram is materialized by the syntax itself. -/
namespace Paper37.WordProgram
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
open Paper37.BoundedLoop
open Paper37.Envelope Paper37.ContinuationDP

private abbrev v := Expr.var
private abbrev n := Expr.lit

lemma get_range_map (m i : ℕ) (f : ℕ → Value) (hi : i<m) :
    ((List.range m).map f)[i]?.getD (.nat 0) = f i := by
  simp [List.getElem?_map,List.getElem?_range,hi]

def bitValue (b : Bool) : Value := .nat (if b then 1 else 0)
def wordValue (x : List Bool) : Value := .array (x.map bitValue)
def pairValue (p : ℕ × ℕ) : Value := .array [.nat p.1,.nat p.2]

@[simp] lemma wordValue_length (x : List Bool) : (wordValue x).arrayVal.length=x.length := by
  simp [wordValue,Value.arrayVal]

@[simp] lemma pairValue_get_zero (p : ℕ × ℕ) :
    (pairValue p).arrayVal[0]?.getD (.nat 0)=.nat p.1 := rfl
@[simp] lemma pairValue_get_one (p : ℕ × ℕ) :
    (pairValue p).arrayVal[1]?.getD (.nat 0)=.nat p.2 := rfl

structure State where
  age : ℕ
  count : ℕ
  hist : ℕ → ℕ

def stateValue (H : ℕ) (s : State) : Value := .array [.nat s.age,.nat s.count,
  .array ((List.range (H+1)).map fun d => .nat (s.hist d))]

def step (s : State) (b : Bool) : State where
  age := if b then 0 else s.age+1
  count := if b then s.count+1 else s.count
  hist d := s.hist d + if b ∧ d=s.age+1 then 1 else 0

def run (s : State) (x : List Bool) : State := x.foldl step s

def initial : State := ⟨0,0,fun _ => 0⟩

/-- Slots 0=H, 40=word. Bound locals 41=bit,42=state,43=histogram index.
State arrays contain [terminal age, completed count, materialized histogram]. -/
def histogramIncrement : Expr := .tabulate 43 (.add (v 0) (n 1))
  (.ifLT (v 43) (.add (.get (v 42) (n 0)) (n 1))
    (.get (.get (v 42) (n 2)) (v 43))
    (.ifLT (.add (.get (v 42) (n 0)) (n 1)) (v 43)
      (.get (.get (v 42) (n 2)) (v 43))
      (.add (.get (.get (v 42) (n 2)) (v 43)) (n 1))))

def parserStep : Expr := .ifLT (n 0) (v 41)
  (.array [n 0,.add (.get (v 42) (n 1)) (n 1),histogramIncrement])
  (.array [.add (.get (v 42) (n 0)) (n 1),.get (v 42) (n 1),.get (v 42) (n 2)])

def parserBase : Expr := .array [n 0,n 0,.tabulate 43 (.add (v 0) (n 1)) (n 0)]
def parserProgram : Expr := .foldArray 41 42 (v 40) parserBase parserStep

lemma histogramIncrement_eval (ρ : Env) (H : ℕ) (s : State)
    (hH : ρ 0=.nat H) (hs : ρ 42=stateValue H s) :
    histogramIncrement.eval ρ =
      .array ((List.range (H+1)).map fun d => .nat (s.hist d+if d=s.age+1 then 1 else 0)) := by
  simp only [histogramIncrement,Expr.eval,hH,Value.natVal]
  congr 1
  apply List.map_congr_left
  intro d hd
  have hdH : d<H+1 := List.mem_range.mp hd
  simp [Function.update_apply,hs,stateValue,Value.arrayVal,Value.natVal,hdH]
  split_ifs <;> simp_all <;> omega

lemma parserStep_eval (ρ : Env) (H : ℕ) (s : State) (b : Bool)
    (hH : ρ 0=.nat H) (hs : ρ 42=stateValue H s) (hb : ρ 41=bitValue b) :
    parserStep.eval ρ=stateValue H (step s b) := by
  have hh := histogramIncrement_eval ρ H s hH hs
  cases b <;> simp [parserStep,Expr.eval,hb,bitValue,hs,stateValue,Value.arrayVal,
    Value.natVal,hh,step]

lemma parserBase_eval (ρ : Env) (H : ℕ) (hH : ρ 0=.nat H) :
    parserBase.eval ρ=stateValue H initial := by
  simp [parserBase,Expr.eval,hH,Value.natVal,stateValue,initial]

lemma fold_parser (ρ : Env) (H : ℕ) (s : State) (x : List Bool) (hH : ρ 0=.nat H) :
    (x.map bitValue).foldl
      (fun val bit => parserStep.eval (Function.update (Function.update ρ 41 bit) 42 val))
      (stateValue H s) = stateValue H (run s x) := by
  induction x generalizing s with
  | nil => rfl
  | cons b x ih =>
    simp only [List.map_cons,List.foldl_cons]
    rw [parserStep_eval _ H s b (by simpa using hH) (by simp) (by simp)]
    exact ih (step s b)

/-- The actual fixed parser syntax computes its materialized finite state. -/
theorem parserProgram_eval (ρ : Env) (H : ℕ) (x : List Bool)
    (hH : ρ 0=.nat H) (hx : ρ 40=wordValue x) :
    parserProgram.eval ρ=stateValue H (run initial x) := by
  simp only [parserProgram,Expr.eval,hx,wordValue,Value.arrayVal]
  rw [parserBase_eval ρ H hH]
  exact fold_parser ρ H initial x hH

lemma run_age (s : State) (x : List Bool) : (run s x).age=parseAge s.age x := by
  induction x generalizing s with
  | nil => rfl
  | cons b x ih =>
    cases b with
    | false => simpa [run,step,parseAge] using ih (step s false)
    | true => simpa [run,step,parseAge] using ih (step s true)

lemma run_count (s : State) (x : List Bool) :
    (run s x).count=s.count+(parseGaps s.age x).length := by
  induction x generalizing s with
  | nil => simp [run,parseGaps]
  | cons b x ih =>
    cases b <;> simp only [run,List.foldl_cons] at *
    · simpa [step,parseGaps] using ih (step s false)
    · simpa [step,parseGaps,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (step s true)

lemma run_hist (s : State) (x : List Bool) (d : ℕ) :
    (run s x).hist d=s.hist d+((parseGaps s.age x).map Nat.succ).count d := by
  induction x generalizing s with
  | nil => simp [run,parseGaps]
  | cons b x ih =>
    cases b <;> simp only [run,List.foldl_cons] at *
    · simpa [step,parseGaps] using ih (step s false)
    · by_cases hd : d=s.age+1
      · simpa [step,parseGaps,List.count_cons,hd,eq_comm,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (step s true)
      · simpa [step,parseGaps,List.count_cons,hd,eq_comm,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (step s true)

/-- Source identification for all three actually parsed statistics. -/
theorem parser_source (x : List Bool) :
    (run initial x).age=parseAge 0 x ∧
    (run initial x).count=(parseGaps 0 x).length ∧
    ∀ d, (run initial x).hist d=observedCounts x d := by
  refine ⟨run_age initial x,?_,?_⟩
  · simpa [initial] using run_count initial x
  · intro d
    simpa [initial,observedCounts] using run_hist initial x d

/-- Drop a run-time prefix length (slot44) from word40, with a bounded
finite array construction rather than a list-function primitive. -/
def dropProgram : Expr := .tabulate 45 (.sub (.length (v 40)) (v 44))
  (.get (v 40) (.add (v 44) (v 45)))

lemma dropProgram_eval (ρ : Env) (x : List Bool) (d : ℕ)
    (hx : ρ 40=wordValue x) (hd : ρ 44=.nat d) :
    dropProgram.eval ρ=wordValue (x.drop d) := by
  simp only [dropProgram,Expr.eval,hx,hd,wordValue,Value.arrayVal,List.length_map,
    Value.natVal]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  have hi : d+i<x.length := by simp only [List.length_map,List.length_drop] at h₂; omega
  simp [Expr.eval,Function.update_apply,hx,hd,wordValue,Value.arrayVal,Value.natVal,
    List.getElem?_eq_getElem hi,List.getElem_drop]

/-- Reversal needed by the right fold implementing first-renewal position. -/
def reverseProgram : Expr := .tabulate 45 (.length (v 40))
  (.get (v 40) (.sub (.sub (.length (v 40)) (n 1)) (v 45)))

lemma reverseProgram_eval (ρ : Env) (x : List Bool) (hx : ρ 40=wordValue x) :
    reverseProgram.eval ρ=wordValue x.reverse := by
  simp only [reverseProgram,Expr.eval,hx,wordValue,Value.arrayVal,List.length_map,
    Value.natVal]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  have hi : i<x.length := by simpa using h₂
  have hj : x.length-1-i<x.length := by omega
  simp [Expr.eval,Function.update_apply,hx,wordValue,Value.arrayVal,Value.natVal,
    List.getElem?_eq_getElem hj,List.getElem_reverse]

def firstIndex (x : List Bool) : ℕ := x.foldr (fun b j => if b then 0 else j+1) 0

def firstIndexProgram : Expr := .foldArray 41 44 reverseProgram (n 0)
  (.ifLT (n 0) (v 41) (n 0) (.add (v 44) (n 1)))

lemma fold_firstIndex (ρ : Env) (x : List Bool) (a : ℕ) :
    (x.map bitValue).foldl
      (fun val bit => (Expr.ifLT (n 0) (v 41) (n 0) (.add (v 44) (n 1))).eval
        (Function.update (Function.update ρ 41 bit) 44 val)) (.nat a) =
      .nat (x.foldl (fun j b => if b then 0 else j+1) a) := by
  induction x generalizing a with
  | nil => rfl
  | cons b x ih =>
    cases b with
    | false => simpa [Expr.eval,bitValue,Value.natVal] using ih (a+1)
    | true => simpa [Expr.eval,bitValue,Value.natVal] using ih 0

lemma firstIndexProgram_eval (ρ : Env) (x : List Bool) (hx : ρ 40=wordValue x) :
    firstIndexProgram.eval ρ=.nat (firstIndex x) := by
  simp only [firstIndexProgram,Expr.eval]
  rw [reverseProgram_eval ρ x hx]
  change (x.reverse.map bitValue).foldl _ (Value.nat 0)=Value.nat (firstIndex x)
  have h := fold_firstIndex ρ x.reverse 0
  simp only [Expr.eval] at h
  rw [h,List.foldl_reverse]
  rfl

lemma firstIndex_none (x : List Bool) (hx : Paper37.Prediction.firstSuffix x=none) :
    firstIndex x=x.length := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    cases b with
    | false => simpa [firstIndex] using ih hx
    | true => simp [Paper37.Prediction.firstSuffix] at hx

lemma firstIndex_some (x z : List Bool) (hx : Paper37.Prediction.firstSuffix x=some z) :
    firstIndex x+1+z.length=x.length ∧ x.drop (firstIndex x+1)=z := by
  induction x with
  | nil => simp [Paper37.Prediction.firstSuffix] at hx
  | cons b x ih =>
    cases b with
    | false =>
      have h := ih hx
      change (firstIndex x+1)+1+z.length=x.length+1 ∧
        (false::x).drop ((firstIndex x+1)+1)=z
      constructor
      · omega
      · simpa only [List.drop_succ_cons] using h.2
    | true =>
      have he : x=z := by simpa [Paper37.Prediction.firstSuffix] using hx
      simp [firstIndex,he,Nat.add_comm]

lemma parserProgram_eval_source (ρ : Env) (H : ℕ) (x : List Bool)
    (hH : ρ 0=.nat H) (hx : ρ 40=wordValue x) :
    parserProgram.eval ρ=.array [.nat (parseAge 0 x),.nat (parseGaps 0 x).length,
      Paper37.CachedCoreProgram.observedValue (Paper37.CachedDP.makeObservedCache H x)] := by
  rw [parserProgram_eval ρ H x hH hx]
  obtain ⟨ha,hc,hh⟩ := parser_source x
  simp only [stateValue,ha,hc]
  congr 2
  simp only [Paper37.CachedCoreProgram.observedValue,Paper37.CachedCoreProgram.natArray,
    Paper37.CachedDP.makeObservedCache_eq,Paper37.CachedDP.makeCache]
  congr 3
  apply List.map_congr_left
  intro d hd
  have hdH : d<H+1 := List.mem_range.mp hd
  simp [hdH,hh]

/-- Append the run-time bit46 to word40 by an explicitly bounded array loop. -/
def appendProgram : Expr := .tabulate 45 (.add (.length (v 40)) (n 1))
  (.ifLT (v 45) (.length (v 40)) (.get (v 40) (v 45)) (v 46))

lemma appendProgram_eval (ρ : Env) (x : List Bool) (b : Bool)
    (hx : ρ 40=wordValue x) (hb : ρ 46=bitValue b) :
    appendProgram.eval ρ=wordValue (x++[b]) := by
  simp only [appendProgram,Expr.eval,hx,wordValue,Value.arrayVal,List.length_map,
    Value.natVal]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  have hi : i<x.length+1 := by simpa using h₂
  by_cases hix : i<x.length
  · simp [hx,hb,wordValue,Value.arrayVal,Value.natVal,hix,
      List.getElem?_eq_getElem hix,List.getElem_append_left hix]
  · have he : i=x.length := by omega
    subst i
    simp [hx,hb,wordValue,Value.arrayVal,Value.natVal]

end Paper37.WordProgram
