import CalibrationDistance.Grid
import Mathlib.Data.Nat.Log

/-!
# Complete cached search trees for the integer grid implementation

Each internal record stores the disjunction of its children's cached flags.
Queries inspect one child flag and descend one level; point reads and writes
also follow one root-to-leaf path. The explicit counters below count visited
records in these actual recursive operations.
-/

namespace CalibrationDistance

namespace GridTree

inductive Tree (α : Type*) : ℕ → Type _
  | leaf (value : α) (flag : Bool) : Tree α 0
  | node {d : ℕ} (flag : Bool) (left right : Tree α d) : Tree α (d + 1)

def flag {α d} : Tree α d → Bool
  | .leaf _ b => b
  | .node b _ _ => b

def branch {α d} (left right : Tree α d) : Tree α (d + 1) :=
  .node (flag left || flag right) left right

def Valid {α} (test : α → Bool) : {d : ℕ} → Tree α d → Prop
  | 0, .leaf a b => b = test a
  | _ + 1, .node b l r => b = (flag l || flag r) ∧ Valid test l ∧ Valid test r

def lookup {α} : {d : ℕ} → Tree α d → ℕ → α
  | 0, .leaf a _, _ => a
  | d + 1, .node _ l r, i => if i < 2 ^ d then lookup l i else lookup r (i - 2 ^ d)

def build {α} (test : α → Bool) : (d : ℕ) → (ℕ → α) → Tree α d
  | 0, f => .leaf (f 0) (test (f 0))
  | d + 1, f => branch (build test d f) (build test d (fun i => f (2 ^ d + i)))

theorem valid_build {α} (test : α → Bool) (d : ℕ) (f : ℕ → α) :
    Valid test (build test d f) := by
  induction d generalizing f with
  | zero => rfl
  | succ d ih => exact ⟨rfl, ih _, ih _⟩

theorem lookup_build {α} (test : α → Bool) (d : ℕ) (f : ℕ → α) (i : ℕ)
    (hi : i < 2 ^ d) : lookup (build test d f) i = f i := by
  induction d generalizing f i with
  | zero =>
    have : i = 0 := by simpa using hi
    subst i
    rfl
  | succ d ih =>
    simp only [build, branch, lookup]
    split_ifs with h
    · exact ih f i h
    · have hi' : i - 2 ^ d < 2 ^ d := by rw [pow_succ] at hi; omega
      rw [ih _ _ hi']
      congr 1
      omega

def update {α} (test : α → Bool) : {d : ℕ} → Tree α d → ℕ → α → Tree α d
  | 0, .leaf _ _, _, a => .leaf a (test a)
  | d + 1, .node _ l r, i, a =>
    if i < 2 ^ d then branch (update test l i a) r
    else branch l (update test r (i - 2 ^ d) a)

theorem valid_update {α} (test : α → Bool) {d : ℕ} (t : Tree α d)
    (ht : Valid test t) (i : ℕ) (a : α) : Valid test (update test t i a) := by
  induction t generalizing i with
  | leaf v b => rfl
  | @node d b l r ihl ihr =>
    rcases ht with ⟨hb, hl, hr⟩
    simp only [update]
    split_ifs
    · exact ⟨rfl, ihl hl _, hr⟩
    · exact ⟨rfl, hl, ihr hr _⟩

theorem lookup_update {α} (test : α → Bool) {d : ℕ} (t : Tree α d)
    (i j : ℕ) (a : α) (hi : i < 2 ^ d) (hj : j < 2 ^ d) :
    lookup (update test t i a) j = if j = i then a else lookup t j := by
  induction t generalizing i j with
  | leaf v b =>
    have hi0 : i = 0 := by simpa using hi
    have hj0 : j = 0 := by simpa using hj
    subst i; subst j
    rfl
  | @node d b l r ihl ihr =>
    rw [pow_succ] at hi hj
    by_cases hiL : i < 2 ^ d
    · rw [update, if_pos hiL]
      by_cases hjL : j < 2 ^ d
      · simp only [branch, lookup, if_pos hjL]
        exact ihl i j hiL hjL
      · have hne : j ≠ i := by omega
        simp only [branch, lookup, if_neg hjL, if_neg hne]
    · rw [update, if_neg hiL]
      by_cases hjL : j < 2 ^ d
      · have hne : j ≠ i := by omega
        simp only [branch, lookup, if_pos hjL, if_neg hne]
      · simp only [branch, lookup, if_neg hjL]
        rw [ihr (i - 2 ^ d) (j - 2 ^ d) (by omega) (by omega)]
        have heq : j - 2 ^ d = i - 2 ^ d ↔ j = i := by omega
        simp only [heq]

theorem flag_true_iff {α} (test : α → Bool) {d : ℕ} (t : Tree α d)
    (ht : Valid test t) :
    flag t = true ↔ ∃ i < 2 ^ d, test (lookup t i) = true := by
  induction t with
  | leaf a b =>
    dsimp [Valid] at ht
    simp [flag, lookup, ht]
  | @node d b l r ihl ihr =>
    rcases ht with ⟨hb, hl, hr⟩
    rw [show flag (.node b l r) = (flag l || flag r) from hb, Bool.or_eq_true,
      ihl hl, ihr hr]
    constructor
    · rintro (⟨i, hi, hh⟩ | ⟨i, hi, hh⟩)
      · refine ⟨i, by rw [pow_succ]; omega, ?_⟩
        simpa [lookup, hi] using hh
      · refine ⟨2 ^ d + i, by rw [pow_succ]; omega, ?_⟩
        simpa [lookup, show ¬ 2 ^ d + i < 2 ^ d by omega] using hh
    · rintro ⟨i, hi, hh⟩
      by_cases h : i < 2 ^ d
      · exact Or.inl ⟨i, h, by simpa [lookup, h] using hh⟩
      · refine Or.inr ⟨i - 2 ^ d, by rw [pow_succ] at hi; omega, ?_⟩
        simpa [lookup, h] using hh

theorem flag_false_iff {α} (test : α → Bool) {d : ℕ} (t : Tree α d)
    (ht : Valid test t) :
    flag t = false ↔ ∀ i < 2 ^ d, test (lookup t i) = false := by
  have h := flag_true_iff test t ht
  constructor
  · intro hb i hi
    cases hp : test (lookup t i)
    · rfl
    · have hh := h.mpr ⟨i, hi, hp⟩
      simp [hb] at hh
  · intro hf
    cases hb : flag t
    · rfl
    · obtain ⟨i, hi, hh⟩ := h.mp hb
      simp [hf i hi] at hh

def findFirst {α} : {d : ℕ} → Tree α d → Option ℕ
  | 0, .leaf _ b => if b then some 0 else none
  | d + 1, .node _ l r =>
    if flag l then findFirst l else (findFirst r).map (fun i => 2 ^ d + i)

def SearchSpec {α} (test : α → Bool) {d : ℕ} (t : Tree α d) : Option ℕ → Prop
  | none => ∀ i < 2 ^ d, test (lookup t i) = false
  | some i => i < 2 ^ d ∧ test (lookup t i) = true ∧
      ∀ j < i, test (lookup t j) = false

theorem findFirst_spec {α} (test : α → Bool) {d : ℕ} (t : Tree α d)
    (ht : Valid test t) : SearchSpec test t (findFirst t) := by
  induction t with
  | leaf a b =>
    dsimp [Valid] at ht
    cases hb : b <;> simp [findFirst, SearchSpec, lookup, hb, ← ht]
  | @node d b l r ihl ihr =>
    rcases ht with ⟨hb, hl, hr⟩
    specialize ihl hl
    specialize ihr hr
    by_cases hleft : flag l = true
    · obtain ⟨i, hi, hh⟩ := (flag_true_iff test l hl).mp hleft
      cases hq : findFirst l with
      | none =>
        rw [hq] at ihl
        have hf := ihl i hi
        simp [hh] at hf
      | some q =>
        rw [hq] at ihl
        rcases ihl with ⟨hqN, hqhit, hqmin⟩
        simp only [findFirst, hleft, Bool.true_eq, ↓reduceIte, hq, SearchSpec]
        refine ⟨by rw [pow_succ]; omega, ?_, ?_⟩
        · simpa [lookup, hqN] using hqhit
        · intro j hj
          have hjN : j < 2 ^ d := by omega
          simpa [lookup, hjN] using hqmin j hj
    · have hfalse : flag l = false := by cases h : flag l <;> simp_all
      have hall := (flag_false_iff test l hl).mp hfalse
      cases hq : findFirst r with
      | none =>
        rw [hq] at ihr
        simp only [findFirst, hfalse, Bool.false_eq_true, ↓reduceIte, hq,
          Option.map_none, SearchSpec]
        intro i hi
        by_cases hiL : i < 2 ^ d
        · simpa [lookup, hiL] using hall i hiL
        · have hiR : i - 2 ^ d < 2 ^ d := by rw [pow_succ] at hi; omega
          simpa [lookup, hiL] using ihr (i - 2 ^ d) hiR
      | some q =>
        rw [hq] at ihr
        rcases ihr with ⟨hqN, hqhit, hqmin⟩
        simp only [findFirst, hfalse, Bool.false_eq_true, ↓reduceIte, hq,
          Option.map_some, SearchSpec]
        refine ⟨by rw [pow_succ]; omega, ?_, ?_⟩
        · simpa [lookup, show ¬ 2 ^ d + q < 2 ^ d by omega] using hqhit
        · intro j hj
          by_cases hjL : j < 2 ^ d
          · simpa [lookup, hjL] using hall j hjL
          · have hjR : j - 2 ^ d < q := by omega
            simpa [lookup, hjL] using hqmin (j - 2 ^ d) hjR

def nodes {α} : {d : ℕ} → Tree α d → ℕ
  | 0, .leaf _ _ => 1
  | _ + 1, .node _ l r => 1 + nodes l + nodes r

def queryVisits {α} : {d : ℕ} → Tree α d → ℕ
  | 0, .leaf _ _ => 1
  | _ + 1, .node _ l r => 1 + if flag l then queryVisits l else queryVisits r

def lookupVisits {α} : {d : ℕ} → Tree α d → ℕ → ℕ
  | 0, .leaf _ _, _ => 1
  | d + 1, .node _ l r, i =>
    1 + if i < 2 ^ d then lookupVisits l i else lookupVisits r (i - 2 ^ d)

def updateVisits {α} : {d : ℕ} → Tree α d → ℕ → ℕ
  | 0, .leaf _ _, _ => 1
  | d + 1, .node _ l r, i =>
    1 + if i < 2 ^ d then updateVisits l i else updateVisits r (i - 2 ^ d)

theorem nodes_eq {α d} (t : Tree α d) : nodes t + 1 = 2 * 2 ^ d := by
  induction t with
  | leaf a b => rfl
  | @node d b l r ihl ihr =>
    change (1 + nodes l + nodes r) + 1 = 2 * 2 ^ (d + 1)
    rw [pow_succ]
    omega

theorem queryVisits_eq {α d} (t : Tree α d) : queryVisits t = d + 1 := by
  induction t with
  | leaf a b => rfl
  | node b l r ihl ihr => simp [queryVisits, ihl, ihr, Nat.add_comm]

theorem lookupVisits_eq {α d} (t : Tree α d) (i : ℕ) : lookupVisits t i = d + 1 := by
  induction t generalizing i with
  | leaf a b => rfl
  | node b l r ihl ihr => simp [lookupVisits, ihl, ihr, Nat.add_comm]

theorem updateVisits_eq {α d} (t : Tree α d) (i : ℕ) : updateVisits t i = d + 1 := by
  induction t generalizing i with
  | leaf a b => rfl
  | node b l r ihl ihr => simp [updateVisits, ihl, ihr, Nat.add_comm]

end GridTree

def gridTreeDepth (m : ℕ) : ℕ := Nat.clog 2 (m + 1)

abbrev GridSearchTree (m : ℕ) := GridTree.Tree (ℕ × ℤ) (gridTreeDepth m)

def gridTreeFlag (m : ℕ) (a : ℕ × ℤ) : Bool :=
  decide (a.1 ≤ m ∧ 0 ≤ a.2 + 2 * (a.1 : ℤ) - (m : ℤ))

def gridTreeInitial (m : ℕ) : GridSearchTree m :=
  GridTree.build (gridTreeFlag m) (gridTreeDepth m) (fun i => (i, 0))

def GridTreeRepresents (m : ℕ) (tree : GridSearchTree m) (v : ℕ → ℤ) : Prop :=
  GridTree.Valid (gridTreeFlag m) tree ∧
    ∀ i < 2 ^ gridTreeDepth m, GridTree.lookup tree i = (i, v i)

theorem gridTreeDepth_covers (m : ℕ) : m + 1 ≤ 2 ^ gridTreeDepth m :=
  Nat.le_pow_clog (by decide) _

theorem gridTreeLeafCount_lt (m : ℕ) : 2 ^ gridTreeDepth m < 2 * (m + 1) := by
  by_cases hm : m = 0
  · subst m
    simp [gridTreeDepth, Nat.clog_one_right]
  · have hd : 0 < gridTreeDepth m := Nat.clog_pos (by decide) (by omega)
    have hprev := Nat.pow_pred_clog_lt_self (by decide : 1 < (2 : ℕ)) (x := m + 1) (by omega)
    have heq : gridTreeDepth m = (gridTreeDepth m).pred + 1 :=
      (Nat.succ_pred_eq_of_pos hd).symm
    change 2 ^ (gridTreeDepth m).pred < m + 1 at hprev
    conv_lhs => rw [heq, pow_succ]
    omega

theorem gridTree_nodes_lt (m : ℕ) (tree : GridSearchTree m) :
    GridTree.nodes tree < 4 * (m + 1) := by
  have hnodes := GridTree.nodes_eq tree
  have hleaves := gridTreeLeafCount_lt m
  omega

theorem gridTreeInitial_represents (m : ℕ) :
    GridTreeRepresents m (gridTreeInitial m) (fun _ => 0) := by
  refine ⟨GridTree.valid_build _ _ _, ?_⟩
  intro i hi
  exact GridTree.lookup_build _ _ _ _ hi

theorem gridTree_update_represents (m : ℕ) (tree : GridSearchTree m) (v : ℕ → ℤ)
    (ht : GridTreeRepresents m tree v) (i : ℕ) (hi : i < 2 ^ gridTreeDepth m) (value : ℤ) :
    GridTreeRepresents m (GridTree.update (gridTreeFlag m) tree i (i, value))
      (Function.update v i value) := by
  refine ⟨GridTree.valid_update _ _ ht.1 _ _, ?_⟩
  intro j hj
  rw [GridTree.lookup_update _ _ _ _ _ hi hj]
  by_cases h : j = i
  · subst j
    simp
  · simp [h, ht.2 j hj, Function.update_of_ne h]

def gridTreeQuery (m : ℕ) (tree : GridSearchTree m) : ℕ :=
  (GridTree.findFirst tree).getD m

theorem gridTreeFlag_true_iff (m i : ℕ) (v : ℕ → ℤ) :
    gridTreeFlag m (i, v i) = true ↔ i ∈ integerEligible m v := by
  simp only [gridTreeFlag, decide_eq_true_eq, integerEligible, Finset.mem_filter,
    Finset.mem_range]
  omega

theorem gridTreeQuery_correct (m : ℕ) (tree : GridSearchTree m) (v : ℕ → ℤ)
    (ht : GridTreeRepresents m tree v) (hne : (integerEligible m v).Nonempty) :
    gridTreeQuery m tree = boundedIntegerQuery m v := by
  have hs := GridTree.findFirst_spec (gridTreeFlag m) tree ht.1
  cases hq : GridTree.findFirst tree with
  | none =>
    rw [hq] at hs
    obtain ⟨i, hi⟩ := hne
    have him : i < m + 1 := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hiN : i < 2 ^ gridTreeDepth m := lt_of_lt_of_le him (gridTreeDepth_covers m)
    have hf := hs i hiN
    rw [ht.2 i hiN] at hf
    have hh := (gridTreeFlag_true_iff m i v).mpr hi
    simp [hh] at hf
  | some q =>
    rw [hq] at hs
    rcases hs with ⟨hqN, hhit, hmin⟩
    rw [ht.2 q hqN] at hhit
    have hqmem := (gridTreeFlag_true_iff m q v).mp hhit
    unfold gridTreeQuery boundedIntegerQuery
    rw [hq, dif_pos hne]
    simp only [Option.getD_some]
    symm
    apply (Finset.min'_eq_iff _ _ _).mpr
    refine ⟨hqmem, ?_⟩
    intro i hi
    by_contra hle
    have hiq : i < q := by omega
    have him : i < m + 1 := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hiN : i < 2 ^ gridTreeDepth m := lt_of_lt_of_le him (gridTreeDepth_covers m)
    have hf := hmin i hiq
    rw [ht.2 i hiN] at hf
    have hh := (gridTreeFlag_true_iff m i v).mpr hi
    simp [hh] at hf

theorem integerEligible_run_nonempty {m : ℕ} (hm : 0 < m) (y : ℕ → Bool) (t : ℕ) :
    (integerEligible m (boundedIntegerRun m y t)).Nonempty := by
  rw [boundedIntegerRun_correct hm y t]
  let j := firstNonnegative hm (gridRun hm y t)
  have hj := firstNonnegative_spec hm (gridRun hm y t)
  refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by dsimp [j]; omega), ?_⟩⟩
  exact (integer_shift_sign hm y t j).mpr hj.2

theorem boundedIntegerQuery_le (m : ℕ) (v : ℕ → ℤ)
    (hne : (integerEligible m v).Nonempty) : boundedIntegerQuery m v ≤ m := by
  have hm := (Finset.mem_filter.mp (Finset.min'_mem (integerEligible m v) hne)).1
  have hlt := Finset.mem_range.mp hm
  simpa only [boundedIntegerQuery, dif_pos hne] using Nat.le_of_lt_succ hlt

def gridTreeWriteIndex (m : ℕ) (tree : GridSearchTree m) (y : Bool) : ℕ :=
  if y then gridTreeQuery m tree else gridTreeQuery m tree - 1

/-- One point read and one point update replace the integer array/dictionary.
The sign predicate and all ancestor caches are recomputed on that same path. -/
def gridTreeStep (m : ℕ) (tree : GridSearchTree m) (y : Bool) : GridSearchTree m :=
  let a := gridTreeWriteIndex m tree y
  let value := (GridTree.lookup tree a).2 + 2 * (a : ℤ) - if y then 2 * (m : ℤ) else 0
  GridTree.update (gridTreeFlag m) tree a (a, value)

theorem gridTreeStep_represents (m : ℕ) (tree : GridSearchTree m) (v : ℕ → ℤ)
    (ht : GridTreeRepresents m tree v) (hne : (integerEligible m v).Nonempty) (y : Bool) :
    GridTreeRepresents m (gridTreeStep m tree y) (boundedIntegerStep m v y) := by
  have hq := gridTreeQuery_correct m tree v ht hne
  have hqm := boundedIntegerQuery_le m v hne
  let a := gridTreeWriteIndex m tree y
  have ha : a ≤ m := by
    dsimp [a, gridTreeWriteIndex]
    rw [hq]
    cases y <;> simp <;> omega
  have haN : a < 2 ^ gridTreeDepth m := lt_of_lt_of_le (by omega) (gridTreeDepth_covers m)
  have hval := ht.2 a haN
  have hfun : Function.update v a (v a + 2 * (a : ℤ) - if y then 2 * (m : ℤ) else 0) =
      boundedIntegerStep m v y := by
    funext k
    by_cases hk : k = a
    · subst k
      simp only [Function.update_self, boundedIntegerStep]
      have haeq : (if y then boundedIntegerQuery m v else boundedIntegerQuery m v - 1) = a := by
        dsimp [a, gridTreeWriteIndex]
        rw [hq]
      rw [haeq, if_pos rfl]
      ring
    · simp only [Function.update_of_ne hk, boundedIntegerStep]
      have haeq : (if y then boundedIntegerQuery m v else boundedIntegerQuery m v - 1) = a := by
        dsimp [a, gridTreeWriteIndex]
        rw [hq]
      rw [haeq, if_neg hk, add_zero]
  unfold gridTreeStep
  change GridTreeRepresents m
    (GridTree.update (gridTreeFlag m) tree a
      (a, (GridTree.lookup tree a).2 + 2 * (a : ℤ) - if y then 2 * (m : ℤ) else 0)) _
  rw [hval]
  rw [← hfun]
  exact gridTree_update_represents m tree v ht a haN _

def gridTreeRun (m : ℕ) (y : ℕ → Bool) : ℕ → GridSearchTree m
  | 0 => gridTreeInitial m
  | t + 1 => gridTreeStep m (gridTreeRun m y t) (y t)

theorem gridTreeRun_represents {m : ℕ} (hm : 0 < m) (y : ℕ → Bool) (t : ℕ) :
    GridTreeRepresents m (gridTreeRun m y t) (boundedIntegerRun m y t) := by
  induction t with
  | zero => exact gridTreeInitial_represents m
  | succ t ih =>
    exact gridTreeStep_represents m _ _ ih (integerEligible_run_nonempty hm y t) (y t)

theorem gridTreeRun_query_correct {m : ℕ} (hm : 0 < m) (y : ℕ → Bool) (t : ℕ) :
    gridTreeQuery m (gridTreeRun m y t) = firstNonnegative hm (gridRun hm y t) := by
  rw [gridTreeQuery_correct m _ _ (gridTreeRun_represents hm y t)
    (integerEligible_run_nonempty hm y t), boundedIntegerRun_correct hm y t,
    boundedIntegerQuery_eq hm y t]

def gridTreeForecast (m : ℕ) (tree : GridSearchTree m) : ℚ :=
  (2 * (gridTreeQuery m tree : ℚ) - 1) / (2 * (m : ℚ))

theorem gridTreeForecast_correct {m : ℕ} (hm : 0 < m) (y : ℕ → Bool) (t : ℕ) :
    (gridTreeForecast m (gridTreeRun m y t) : ℝ) = gridForecast hm (gridRun hm y t) := by
  unfold gridTreeForecast
  push_cast
  rw [gridTreeRun_query_correct hm y t]
  exact (gridForecast_exact_rational hm _).symm

/-- Both the announced forecast and the subsequent update may query the cached
tree. Counting both queries, the point read, and the point write is still a
worst-case logarithmic bound for every individual round. -/
def gridTreeRoundVisits (m : ℕ) (tree : GridSearchTree m) (y : Bool) : ℕ :=
  2 * GridTree.queryVisits tree +
    GridTree.lookupVisits tree (gridTreeWriteIndex m tree y) +
    GridTree.updateVisits tree (gridTreeWriteIndex m tree y)

theorem gridTreeRoundVisits_eq (m : ℕ) (tree : GridSearchTree m) (y : Bool) :
    gridTreeRoundVisits m tree y = 4 * (Nat.clog 2 (m + 1) + 1) := by
  simp only [gridTreeRoundVisits, GridTree.queryVisits_eq, GridTree.lookupVisits_eq,
    GridTree.updateVisits_eq, gridTreeDepth]
  omega

theorem gridTreeRun_numerator_bounds {m : ℕ} (hm : 0 < m) (y : ℕ → Bool) (t i : ℕ)
    (hi : i < 2 ^ gridTreeDepth m) :
    -(m : ℤ) ≤ (GridTree.lookup (gridTreeRun m y t) i).2 ∧
      (GridTree.lookup (gridTreeRun m y t) i).2 ≤ (m : ℤ) := by
  rw [(gridTreeRun_represents hm y t).2 i hi, boundedIntegerRun_correct hm y t]
  by_cases him : i ≤ m
  · exact gridNumerator_bounds hm y t i him
  · rw [gridNumerator_zero_outside hm y t i (by omega)]
    constructor <;> omega

end CalibrationDistance
