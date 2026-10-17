import SemidegreeExt.FlowAlgorithm
open Finset
namespace SemidegreeExt.FlowAlgorithm
variable {V : Type*} [Fintype V] [DecidableEq V] [Enumeration V]

def seenList (s : V) (table : List (V × V)) : List V := s :: table.map Prod.snd

lemma search_seen (cap : V → V → ℕ) (f : Matrix V) (s : V) (k : ℕ) :
    (search cap f s k).seen = (seenList s (search cap f s k).table).toFinset := by
  induction k with
  | zero => simp [search,seenList]
  | succ k ih =>
    rw [search]
    cases he : frontier cap f (search cap f s k).seen with
    | none => simpa only [searchStep,he] using ih
    | some e =>
      obtain ⟨a,b⟩ := e
      simp only [searchStep,he]
      simp only [seenList,List.map_cons,List.toFinset_cons]
      rw [ih]
      simp [seenList,insert_comm]

lemma search_table_length (cap : V → V → ℕ) (f : Matrix V) (s : V) (k : ℕ) :
    (search cap f s k).table.length ≤ k := by
  induction k with
  | zero => simp [search]
  | succ k ih =>
    rw [search]
    cases he : frontier cap f (search cap f s k).seen with
    | none => simpa only [searchStep,he] using ih.trans (Nat.le_succ _)
    | some e => obtain ⟨a,b⟩ := e; simpa only [searchStep,he,List.length_cons] using Nat.succ_le_succ ih

lemma lookupRoute_length (table : List (V × V)) (v : V) : (lookupRoute table v).length ≤ table.length := by
  induction table generalizing v with
  | nil => simp [lookupRoute]
  | cons e es ih =>
    obtain ⟨a,b⟩ := e
    by_cases hv : v=b
    · simpa [lookupRoute,hv] using Nat.succ_le_succ (ih a)
    · simpa [lookupRoute,hv] using (ih v).trans (Nat.le_succ _)

lemma applyRoute_append (f : Matrix V) (xs ys : List (V × V)) :
    applyRoute f (xs++ys) = applyRoute (applyRoute f ys) xs := by
  induction xs with
  | nil => rfl
  | cons e es ih => obtain ⟨a,b⟩ := e; simp only [List.cons_append,applyRoute,ih]

lemma improve_valid {cap : V → V → ℕ} {s t : V} {f : Matrix V}
    (hf : Valid cap s t f) : Valid cap s t (improve cap s t f) := by
  dsimp only [improve]
  split
  · rename_i ht
    obtain ⟨hsk,hbound,hdiv,_,_⟩ := (search_invariant s hf.1 hf.2.1 (Fintype.card V)).2 t ht
    refine ⟨hsk,hbound,?_⟩
    intro v hvs hvt
    rw [hdiv,if_neg hvs,if_neg hvt,hf.2.2 v hvs hvt]
    ring
  · exact hf

lemma run_valid (cap : V → V → ℕ) (s t : V) (k : ℕ) : Valid cap s t (run cap s t k) := by
  induction k with
  | zero => exact zero_valid cap s t
  | succ k ih => exact improve_valid ih

/-- Materialized algorithm output. Unlike a lazy composition of matrix functions,
this is a concrete finite list of elementary integer updates. -/
def program (cap : V → V → ℕ) (s t : V) : ℕ → List (V × V)
  | 0 => []
  | k+1 =>
    let old := program cap s t k
    let st := search cap (applyRoute (fun _ _ => 0) old) s (Fintype.card V)
    if t ∈ st.seen then st.routes t ++ old else old

lemma program_refines (cap : V → V → ℕ) (s t : V) (k : ℕ) :
    applyRoute (fun _ _ => 0) (program cap s t k) = run cap s t k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [program]
    split
    · rename_i ht
      rw [applyRoute_append,ih]
      exact (if_pos (by simpa only [ih] using ht) : improve cap s t (run cap s t k) = _).symm
    · rename_i ht
      rw [ih]
      exact (if_neg (by simpa only [ih] using ht) : improve cap s t (run cap s t k) = _).symm

lemma program_length (cap : V → V → ℕ) (s t : V) (k : ℕ) :
    (program cap s t k).length ≤ k * Fintype.card V := by
  induction k with
  | zero => simp [program]
  | succ k ih =>
    simp only [program]
    split
    · rename_i ht
      rw [List.length_append]
      have hlen := lookupRoute_length (search cap (applyRoute (fun _ _ => 0) (program cap s t k)) s (Fintype.card V)).table t
      have htab := search_table_length cap (applyRoute (fun _ _ => 0) (program cap s t k)) s (Fintype.card V)
      change (lookupRoute _ _).length + _ ≤ _
      nlinarith
    · nlinarith

/-- Costed elementary matrix evaluation: two ordered-pair indicator tests and
integer additions/subtractions per stored update, with a conservative ten-unit
charge for those primitive word operations. -/
def evalCost : List (V × V) → V → V → ℤ × ℕ
  | [], _, _ => (0,1)
  | (a,b)::es, u, v =>
    let z := evalCost es u v
    (z.1 + delta a b u v, z.2+10)

@[simp] lemma evalCost_value (es : List (V × V)) (u v : V) :
    (evalCost es u v).1 = applyRoute (fun _ _ => 0) es u v := by
  induction es with
  | nil => rfl
  | cons e es ih => obtain ⟨a,b⟩ := e; simp [evalCost,applyRoute,addEdge,ih]

@[simp] lemma evalCost_cost (es : List (V × V)) (u v : V) :
    (evalCost es u v).2 = 10*es.length+1 := by
  induction es with
  | nil => rfl
  | cons e es ih => obtain ⟨a,b⟩ := e; simp [evalCost,ih]; ring

/-- Instrumented list membership; each equality/branch is charged. -/
def memCost (v : V) : List V → Bool × ℕ
  | [] => (false,1)
  | x::xs => if v=x then (true,2) else
    let z := memCost v xs
    (z.1,z.2+2)

@[simp] lemma memCost_value (v : V) (xs : List V) : (memCost v xs).1 = decide (v ∈ xs) := by
  induction xs with
  | nil => simp [memCost]
  | cons x xs ih => by_cases h:v=x <;> simp [memCost,h,ih]

lemma memCost_bound (v : V) (xs : List V) : (memCost v xs).2 ≤ 2*xs.length+1 := by
  induction xs with
  | nil => simp [memCost]
  | cons x xs ih => by_cases h:v=x <;> simp [memCost,h] <;> omega

/-- Instrumented predecessor lookup. Each step follows one recursive branch. -/
def lookupCost : List (V × V) → V → List (V × V) × ℕ
  | [], _ => ([],1)
  | (a,b)::es, v => if v=b then
    let z := lookupCost es a
    ((a,b)::z.1,z.2+3)
    else let z := lookupCost es v; (z.1,z.2+3)

@[simp] lemma lookupCost_value (es : List (V × V)) (v : V) :
    (lookupCost es v).1 = lookupRoute es v := by
  induction es generalizing v with
  | nil => rfl
  | cons e es ih => obtain ⟨a,b⟩ := e; by_cases h:v=b <;> simp [lookupCost,lookupRoute,h,ih]

@[simp] lemma lookupCost_cost (es : List (V × V)) (v : V) :
    (lookupCost es v).2 = 3*es.length+1 := by
  induction es generalizing v with
  | nil => rfl
  | cons e es ih => obtain ⟨a,b⟩ := e; by_cases h:v=b <;> simp [lookupCost,h,ih] <;> ring

/-- Costed linear search, charging the predicate evaluation at every actually
examined pair and a branch/option step. -/
def scanCost {A : Type*} (p : A → Bool × ℕ) : List A → Option A × ℕ
  | [] => (none,1)
  | x::xs => if (p x).1 then (some x,(p x).2+1) else
    let z := scanCost p xs
    (z.1,(p x).2+z.2+1)

@[simp] lemma scanCost_value {A : Type*} (p : A → Bool × ℕ) (xs : List A) :
    (scanCost p xs).1 = xs.find? (fun x => (p x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h:(p x).1 <;> simp [scanCost,List.find?,h,ih]

lemma scanCost_bound {A : Type*} (p : A → Bool × ℕ) (xs : List A) (B : ℕ)
    (hb : ∀ x, (p x).2 ≤ B) : (scanCost p xs).2 ≤ xs.length*(B+1)+1 := by
  induction xs with
  | nil => simp [scanCost]
  | cons x xs ih =>
    cases h:(p x).1 <;> simp [scanCost,h]
    · have := hb x; nlinarith
    · have := hb x; nlinarith

/-- No residual-query oracle: this predicate computes both list memberships,
the integer matrix entry by traversing the accumulated update list, and the
capacity comparison. The charge includes constructing the seen-list. -/
def residualCost (cap : V → V → ℕ) (updates : List (V × V)) (s : V)
    (table : List (V × V)) (e : V × V) : Bool × ℕ :=
  let xs := seenList s table
  let a := memCost e.1 xs
  let b := memCost e.2 xs
  let f := evalCost updates e.1 e.2
  (a.1 && !b.1 && decide (f.1 < cap e.1 e.2),
    a.2+b.2+f.2+xs.length+8)

lemma residualCost_bound (cap : V → V → ℕ) (updates : List (V × V)) (s : V)
    (table : List (V × V)) (e : V × V) :
    (residualCost cap updates s table e).2 ≤ 10*updates.length+5*table.length+16 := by
  have ha := memCost_bound e.1 (seenList s table)
  have hb := memCost_bound e.2 (seenList s table)
  simp only [residualCost,evalCost_cost]
  simp only [seenList,List.length_cons,List.length_map] at ha hb ⊢
  omega

/-- Costed executable residual search. Allocation/traversal of the explicit
vertex-pair list is charged quadratically; predecessor tables are finite lists. -/
def searchCost (cap : V → V → ℕ) (updates : List (V × V)) (s : V) : ℕ → List (V × V) × ℕ
  | 0 => ([],1)
  | k+1 =>
    let old := searchCost cap updates s k
    let z := scanCost (residualCost cap updates s old.1) pairs
    let table := match z.1 with | none => old.1 | some e => e::old.1
    (table,old.2+z.2+6*(Fintype.card V)^2+6*(Fintype.card V)+10)

lemma searchCost_refines (cap : V → V → ℕ) (updates : List (V × V)) (s : V) (k : ℕ) :
    (searchCost cap updates s k).1 = (search cap (applyRoute (fun _ _ => 0) updates) s k).table := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hp : (fun e => (residualCost cap updates s (searchCost cap updates s k).1 e).1) =
        fun e => decide (e.1 ∈ (search cap (applyRoute (fun _ _ => 0) updates) s k).seen ∧
          e.2 ∉ (search cap (applyRoute (fun _ _ => 0) updates) s k).seen ∧
          applyRoute (fun _ _ => 0) updates e.1 e.2 < cap e.1 e.2) := by
      funext e
      simp [residualCost,memCost_value,evalCost_value,ih,search_seen,List.mem_toFinset,Bool.and_assoc]
    have hz : (scanCost (residualCost cap updates s (searchCost cap updates s k).1) pairs).1 =
        frontier cap (applyRoute (fun _ _ => 0) updates) (search cap (applyRoute (fun _ _ => 0) updates) s k).seen := by
      rw [scanCost_value,hp]
      rfl
    simp only [searchCost]
    rw [hz]
    rw [search]
    cases he : frontier cap (applyRoute (fun _ _ => 0) updates) (search cap (applyRoute (fun _ _ => 0) updates) s k).seen with
    | none => simp only [searchStep,he,ih]
    | some e => obtain ⟨a,b⟩ := e; simp only [searchStep,he,ih]

@[simp] lemma pairs_length : (pairs (V := V)).length = (Fintype.card V)^2 := by
  simp [pairs,List.length_flatMap,pow_two]

def searchBudget (N L : ℕ) := N^2*(10*L+5*N+17)+6*N^2+6*N+11

lemma searchCost_bound (cap : V → V → ℕ) (updates : List (V × V)) (s : V) :
    ∀ k ≤ Fintype.card V, (searchCost cap updates s k).2 ≤
      k * searchBudget (Fintype.card V) updates.length + 1 := by
  intro k hk
  induction k with
  | zero => simp [searchCost]
  | succ k ih =>
    have ih' := ih (by omega)
    have ht : (searchCost cap updates s k).1.length ≤ Fintype.card V := by
      rw [searchCost_refines]
      exact (search_table_length _ _ _ _).trans (by omega)
    have hb := scanCost_bound (residualCost cap updates s (searchCost cap updates s k).1) pairs
      (10*updates.length+5*Fintype.card V+16) (fun e =>
        (residualCost_bound _ _ _ _ _).trans (by omega))
    rw [pairs_length] at hb
    simp only [searchCost]
    unfold searchBudget at *
    nlinarith
/-- Fully materialized, instrumented construction. All residual tests are
computed from the accumulated update list. No feasible-flow witness occurs in
this executable definition. Costs include search, target membership, route
reconstruction, and copying the route into the update list. -/
def runCost (cap : V → V → ℕ) (s t : V) : ℕ → List (V × V) × ℕ
  | 0 => ([],1)
  | k+1 =>
    let old := runCost cap s t k
    let z := searchCost cap old.1 s (Fintype.card V)
    let target := memCost t (seenList s z.1)
    if target.1 then
      let route := lookupCost z.1 t
      (route.1 ++ old.1, old.2+z.2+target.2+route.2+route.1.length+6)
    else (old.1,old.2+z.2+target.2+6)

lemma runCost_refines (cap : V → V → ℕ) (s t : V) (k : ℕ) :
    (runCost cap s t k).1 = program cap s t k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hm : (memCost t (seenList s (searchCost cap (runCost cap s t k).1 s (Fintype.card V)).1)).1 =
        decide (t ∈ (search cap (applyRoute (fun _ _ => 0) (program cap s t k)) s (Fintype.card V)).seen) := by
      simp only [memCost_value,searchCost_refines,ih,search_seen,List.mem_toFinset]
    simp only [runCost]
    rw [hm]
    simp only [lookupCost_value,searchCost_refines,ih,program]
    by_cases ht : t ∈ (search cap (applyRoute (fun _ _ => 0) (program cap s t k)) s (Fintype.card V)).seen
    · simp [ht,SearchState.routes]
    · simp [ht]

/-- Explicit polynomial work bound, in primitive vertex comparisons, integer
word operations, list inspections and constructors of the instrumented program.
N is the number of input vertices and R is the number of augmentations. -/
def workBudget (N R : ℕ) := R*(N*searchBudget N (R*N)+6*N+11)+1

lemma searchBudget_mono {N L K : ℕ} (h : L ≤ K) : searchBudget N L ≤ searchBudget N K := by
  unfold searchBudget
  gcongr

/-- A proved upper bound on the actual returned operation count. In particular,
this is not an assumed complexity certificate attached to an arbitrary output. -/
theorem runCost_bound (cap : V → V → ℕ) (s t : V) (R : ℕ) :
    ∀ k ≤ R, (runCost cap s t k).2 ≤
      k*(Fintype.card V*searchBudget (Fintype.card V) (R*Fintype.card V)+6*Fintype.card V+11)+1 := by
  intro k hk
  induction k with
  | zero => simp [runCost]
  | succ k ih =>
    have ih' := ih (by omega)
    have hlen : (runCost cap s t k).1.length ≤ R*Fintype.card V := by
      rw [runCost_refines]
      exact (program_length cap s t k).trans (Nat.mul_le_mul_right _ (by omega))
    have hsearch := searchCost_bound cap (runCost cap s t k).1 s (Fintype.card V) (le_refl _)
    have hsearch' : (searchCost cap (runCost cap s t k).1 s (Fintype.card V)).2 ≤
        Fintype.card V*searchBudget (Fintype.card V) (R*Fintype.card V)+1 := by
      exact hsearch.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ (searchBudget_mono hlen)) _)
    have ht : (searchCost cap (runCost cap s t k).1 s (Fintype.card V)).1.length ≤ Fintype.card V := by
      rw [searchCost_refines]
      exact search_table_length _ _ _ _
    have hmem := memCost_bound t (seenList s (searchCost cap (runCost cap s t k).1 s (Fintype.card V)).1)
    rw [show (seenList s (searchCost cap (runCost cap s t k).1 s (Fintype.card V)).1).length =
      (searchCost cap (runCost cap s t k).1 s (Fintype.card V)).1.length+1 by simp [seenList]] at hmem
    have hlookup := lookupCost_cost (searchCost cap (runCost cap s t k).1 s (Fintype.card V)).1 t
    have hroute : (lookupCost (searchCost cap (runCost cap s t k).1 s (Fintype.card V)).1 t).1.length ≤ Fintype.card V := by
      rw [lookupCost_value]
      exact (lookupRoute_length _ _).trans ht
    simp only [runCost]
    split <;> simp only [hlookup] <;> nlinarith

/-- The metered program really produces the verified integral flow, and its
work count has the explicit polynomial bound. -/
theorem metered_correct {cap : V → V → ℕ} {s t : V} {g : Matrix V} (hst : s ≠ t)
    (hg : Valid cap s t g) (R : ℕ) (hR : divergence g s = R) :
    Valid cap s t (applyRoute (fun _ _ => 0) (runCost cap s t R).1) ∧
    divergence (applyRoute (fun _ _ => 0) (runCost cap s t R).1) s = R ∧
    (runCost cap s t R).2 ≤ workBudget (Fintype.card V) R := by
  rw [runCost_refines,program_refines]
  obtain ⟨hv,hval⟩ := run_correct hst hg R hR R (le_refl _)
  exact ⟨hv,hval,runCost_bound cap s t R R (le_refl _)⟩
/-- Instrumented full filtering: unlike find?, this visits every input entry
and returns the selected entries in their original order. -/
def filterCost {A : Type*} (p : A → Bool × ℕ) : List A → List A × ℕ
  | [] => ([],1)
  | x::xs =>
    let z := filterCost p xs
    if (p x).1 then (x::z.1,(p x).2+z.2+2) else (z.1,(p x).2+z.2+1)

@[simp] lemma filterCost_value {A : Type*} (p : A → Bool × ℕ) (xs : List A) :
    (filterCost p xs).1 = xs.filter (fun x => (p x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h:(p x).1 <;> simp [filterCost,h,ih]

lemma filterCost_bound {A : Type*} (p : A → Bool × ℕ) (xs : List A) (B : ℕ)
    (hb : ∀ x, (p x).2 ≤ B) : (filterCost p xs).2 ≤ xs.length*(B+2)+1 := by
  induction xs with
  | nil => simp [filterCost]
  | cons x xs ih =>
    cases h:(p x).1 <;> simp [filterCost,h]
    · have := hb x; nlinarith
    · have := hb x; nlinarith
end SemidegreeExt.FlowAlgorithm
