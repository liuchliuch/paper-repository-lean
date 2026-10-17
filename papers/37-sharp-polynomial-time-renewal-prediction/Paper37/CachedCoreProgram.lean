import Paper37.BoundedLoop
import Paper37.CachedOperations

/-! The cached recurrence as a single finite bounded-loop syntax term. All
array indices, loop limits and summand arithmetic occur in the syntax. -/
namespace Paper37.CachedCoreProgram
open Finset Paper37.DP Paper37.CachedDP Paper37.BoundedLoop Paper37.ContinuationDP

private abbrev v := Expr.var
private abbrev n := Expr.lit
private abbrev add := Expr.add
private abbrev mul := Expr.mul
private abbrev sub := Expr.sub
private abbrev get := Expr.get

def natArray {m : ℕ} (a : Vector ℕ m) : Value :=
  .array ((List.range m).map fun i => .nat (if hi : i<m then a[i] else 0))

def layerValue {N : ℕ} (a : Layer N) : Value :=
  .array ((List.range (N+1)).map fun k =>
    .array ((List.range (N+1)).map fun u =>
      .array [.nat (layerAt a k u).1,.nat (layerAt a k u).2]))

def chooseValue {N : ℕ} (c : Cache N) : Value :=
  .array ((List.range (N+1)).map fun k =>
    .array ((List.range (N+1)).map fun b => .nat (if hk : k<N+1 then chooseAt c ⟨k,hk⟩ b else 0)))

def powerValue {N : ℕ} (c : Cache N) : Value := natArray c.power
def observedValue {N : ℕ} (c : Cache N) : Value := natArray c.observed

/-- Variable slots 0..5 are immutable inputs. Slots 6..10 are bound loop
variables: layer, k, u, b and a scalar accumulator. -/
def inputEnv {N : ℕ} (c : Cache N) (A : ℕ) (old : Layer N) : Env :=
  fun x => if x=0 then .nat N else if x=1 then .nat A else
    if x=2 then chooseValue c else if x=3 then powerValue c else
    if x=4 then observedValue c else if x=5 then layerValue old else .nat 0

def layerLength : Expr := add (v 0) (n 1)
def gap : Expr := add (v 6) (n 1)
def multiplicity : Expr := get (v 4) gap
def loopBound : Expr := add (.min (v 7) (.div (v 8) gap)) (n 1)
def coefficient : Expr := mul (get (get (v 2) (v 7)) (v 9))
  (get (v 3) (add multiplicity (v 9)))
def oldPair : Expr := get (get (v 5) (sub (v 7) (v 9)))
  (sub (v 8) (mul gap (v 9)))
def unmarkedTerm : Expr := mul coefficient (get oldPair (n 0))
def markedTerm : Expr := mul coefficient (add (get oldPair (n 1))
  (mul (.ifLT (v 1) gap (v 9) (n 0)) (get oldPair (n 0))))
def sumTerm (term : Expr) : Expr := .fold 9 10 loopBound (n 0) (add (v 10) term)
def stepProgram : Expr := .tabulate 7 layerLength (.tabulate 8 layerLength
  (.array [sumTerm unmarkedTerm,sumTerm markedTerm]))

def baseProgram : Expr := .tabulate 7 layerLength (.tabulate 8 layerLength
  (.array [.ifLT (v 7) (n 1) (.ifLT (v 8) (n 1) (n 1) (n 0)) (n 0),n 0]))

/-- The accumulator slot is the old materialized layer. The loop bound is
the horizon itself, so the syntax size is independent of the input horizon. -/
def coreProgram : Expr := .fold 6 5 (v 0) baseProgram stepProgram

lemma get_range_map (m i : ℕ) (f : ℕ → Value) (hi : i<m) :
    ((List.range m).map f)[i]?.getD (.nat 0) = f i := by
  simp [List.getElem?_map,List.getElem?_range,hi]

lemma natArray_get {m : ℕ} (a : Vector ℕ m) (i : ℕ) (hi : i<m) :
    (natArray a).arrayVal[i]?.getD (.nat 0) = .nat (a[i]) := by
  unfold natArray Value.arrayVal
  rw [get_range_map m i _ hi,dif_pos hi]

lemma layerValue_get {N : ℕ} (a : Layer N) (k u : ℕ) (hk : k<N+1) (hu : u<N+1) :
    ((layerValue a).arrayVal[k]?.getD (.nat 0)).arrayVal[u]?.getD (.nat 0) =
      .array [.nat (layerAt a k u).1,.nat (layerAt a k u).2] := by
  simp only [layerValue,Value.arrayVal,get_range_map _ _ _ hk,get_range_map _ _ _ hu]

lemma chooseValue_get {N : ℕ} (c : Cache N) (k b : ℕ) (hk : k<N+1) (hb : b<N+1) :
    ((chooseValue c).arrayVal[k]?.getD (.nat 0)).arrayVal[b]?.getD (.nat 0) =
      .nat (chooseAt c ⟨k,hk⟩ b) := by
  simp only [chooseValue,Value.arrayVal,get_range_map _ _ _ hk,get_range_map _ _ _ hb]
  simp only [dif_pos hk]

lemma powerValue_get {N : ℕ} (c : Cache N) (b : ℕ) (hb : b<2*N+1) :
    (powerValue c).arrayVal[b]?.getD (.nat 0) = .nat (powerAt c b) := by
  rw [powerValue,natArray_get _ b hb]
  simp only [powerAt,dif_pos hb]

lemma fold_add (is : List ℕ) (f : ℕ → ℕ) (a : ℕ) :
    is.foldl (fun v i => Value.nat (v.natVal+f i)) (.nat a) =
      .nat (a+(is.map f).sum) := by
  induction is generalizing a with
  | nil => simp
  | cons i is ih =>
    change is.foldl (fun v i => Value.nat (v.natVal+f i)) (.nat (a+f i)) =
      .nat (a+(f i+(is.map f).sum))
    rw [ih]
    congr 1
    omega

lemma powerValue_get_total {N : ℕ} (c : Cache N) (b : ℕ) :
    (powerValue c).arrayVal[b]?.getD (.nat 0) = .nat (powerAt c b) := by
  by_cases hb : b<2*N+1
  · exact powerValue_get c b hb
  · rw [List.getElem?_eq_none_iff.mpr (by simpa [powerValue,natArray,Value.arrayVal] using (Nat.le_of_not_gt hb))]
    simp [powerAt,hb]

lemma fold_add_of (is : List ℕ) (f : ℕ → ℕ) (step : Value → ℕ → Value)
    (hs : ∀i∈is,∀a,step (.nat a) i=.nat (a+f i)) (a : ℕ) :
    is.foldl step (.nat a)=.nat (a+(is.map f).sum) := by
  induction is generalizing a with
  | nil => simp
  | cons i is ih =>
    rw [List.foldl_cons,hs i (by simp) a,ih (by
      intro j hj b
      exact hs j (by simp [hj]) b)]
    simp only [List.map_cons,List.sum_cons,Nat.add_assoc]

lemma sumTerm_eval (ρ : Env) (term : Expr) (M : ℕ) (f : ℕ → ℕ)
    (hM : (loopBound.eval ρ).natVal=M)
    (ht : ∀b<M,∀a,term.eval (Function.update (Function.update ρ 9 (.nat b)) 10 (.nat a))=.nat (f b)) :
    (sumTerm term).eval ρ=.nat (∑b∈range M,f b) := by
  simp only [sumTerm,Expr.eval,hM]
  rw [fold_add_of _ f _ (by
    intro b hb a
    simp only [List.mem_range] at hb
    rw [ht b hb a]
    simp [Function.update,Value.natVal])]
  simp only [Value.natVal,zero_add]
  congr 1

end Paper37.CachedCoreProgram
