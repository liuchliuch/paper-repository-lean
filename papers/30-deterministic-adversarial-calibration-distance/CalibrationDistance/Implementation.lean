import CalibrationDistance.GridTree
import CalibrationDistance.Anytime

/-! Exact implementation in the record-access word-RAM model of §6.5.

A record contains a key, a signed bias numerator, two child addresses and one
cached Boolean. The recursive cost semantics count record visits: reading or
rewriting one record and the constant number of additions/comparisons at it
have constant word cost when its fields fit a word. Forecasts are emitted as
a numerator/denominator pair, so reduction by a gcd is not required. Complete
cached binary trees replace balanced dictionaries, with a fixed number of
records. This proves the source's existence of an efficient implementation
without requiring an unformalized balanced-tree complexity theorem.
-/

open scoped BigOperators

namespace CalibrationDistance
namespace GridTree

/-- The actual bulk builder with a record-allocation counter. -/
def buildCounted {α} (test : α → Bool) : (d : ℕ) → (ℕ → α) → Tree α d × ℕ
  | 0, f => (.leaf (f 0) (test (f 0)), 1)
  | d+1, f =>
    let left := buildCounted test d f
    let right := buildCounted test d (fun i => f (2^d+i))
    (branch left.1 right.1, left.2+right.2+1)

theorem buildCounted_correct {α} (test : α → Bool) (d : ℕ) (f : ℕ → α) :
    (buildCounted test d f).1 = build test d f ∧
      (buildCounted test d f).2 = nodes (build test d f) := by
  induction d generalizing f with
  | zero => exact ⟨rfl,rfl⟩
  | succ d ih =>
    rcases ih f with ⟨hl, hcl⟩
    rcases ih (fun i => f (2^d+i)) with ⟨hr, hcr⟩
    simp only [buildCounted, build, hl, hr, hcl, hcr, branch, nodes]
    constructor
    · trivial
    · omega

/-- A costed query runs the same first-hit recursion; no scanning occurs. -/
def findFirstCounted {α} : {d : ℕ} → Tree α d → Option ℕ × ℕ
  | 0, .leaf _ b => (if b then some 0 else none,1)
  | d+1, .node _ left right =>
    if flag left then
      let q := findFirstCounted left
      (q.1,q.2+1)
    else
      let q := findFirstCounted right
      (q.1.map (fun i => 2^d+i),q.2+1)

theorem findFirstCounted_correct {α d} (tree : Tree α d) :
    (findFirstCounted tree).1 = findFirst tree ∧
      (findFirstCounted tree).2 = queryVisits tree := by
  induction tree with
  | leaf _ b => exact ⟨rfl,rfl⟩
  | node _ left right ihl ihr =>
    cases h : flag left <;>
      simp [findFirstCounted, findFirst, queryVisits, h, ihl.1, ihl.2, ihr.1, ihr.2,
        Nat.add_comm]

end GridTree

/-- Initial construction and storage require fewer than 4(m+1) records. -/
theorem grid_initialization_linear (m : ℕ) :
    (GridTree.buildCounted (gridTreeFlag m) (gridTreeDepth m) (fun i => (i,(0:ℤ)))).1 =
        gridTreeInitial m ∧
    (GridTree.buildCounted (gridTreeFlag m) (gridTreeDepth m) (fun i => (i,(0:ℤ)))).2 <
        4*(m+1) := by
  have hh := GridTree.buildCounted_correct (gridTreeFlag m) (gridTreeDepth m)
    (fun i => (i,(0:ℤ)))
  exact ⟨hh.1, hh.2.trans_lt (gridTree_nodes_lt m (gridTreeInitial m))⟩

/-- Exact rational representation with no normalization cost. -/
def gridForecastPair (m : ℕ) (tree : GridSearchTree m) : ℤ × ℕ :=
  (2*(gridTreeQuery m tree : ℤ)-1, 2*m)

theorem gridForecastPair_correct {m : ℕ} (hm : 0 < m) (y : ℕ → Bool) (t : ℕ) :
    ((gridForecastPair m (gridTreeRun m y t)).1 : ℝ) /
        ((gridForecastPair m (gridTreeRun m y t)).2 : ℝ) =
      gridForecast hm (gridRun hm y t) := by
  simpa [gridForecastPair, gridTreeForecast] using gridTreeForecast_correct hm y t

/-- Signed word width; the sign consumes only one additional bit. -/
def gridWordWidth (m : ℕ) : ℕ := gridTreeDepth m + 4

theorem gridWordCapacity (m : ℕ) : 8*(m+1) < 2^gridWordWidth m := by
  have hc := gridTreeDepth_covers m
  have hp : 0 < 2^gridTreeDepth m := by positivity
  simp only [gridWordWidth, pow_add]
  norm_num
  omega

/-- Keys, stored signed numerators and record addresses all fit logarithmic
width. This bound is uniform over the number of rounds already played. -/
theorem gridTree_stored_words {m : ℕ} (hm : 0 < m) (y : ℕ → Bool) (t i : ℕ)
    (hi : i < 2^gridTreeDepth m) :
    (GridTree.lookup (gridTreeRun m y t) i).1 < 2^gridWordWidth m ∧
    -((2^gridWordWidth m : ℕ) : ℤ) < (GridTree.lookup (gridTreeRun m y t) i).2 ∧
    (GridTree.lookup (gridTreeRun m y t) i).2 < ((2^gridWordWidth m : ℕ) : ℤ) ∧
    GridTree.nodes (gridTreeRun m y t) < 2^gridWordWidth m := by
  have hc := gridWordCapacity m
  have hn := gridTree_nodes_lt m (gridTreeRun m y t)
  have hv := gridTreeRun_numerator_bounds hm y t i hi
  have hl := gridTreeLeafCount_lt m
  have hrep := (gridTreeRun_represents hm y t).2 i hi
  have hmcap : (m : ℤ) < ((2^gridWordWidth m : ℕ) : ℤ) := by
    exact_mod_cast (show m < 2^gridWordWidth m by omega)
  rw [hrep] at hv ⊢
  constructor
  · simp only [Prod.fst]; omega
  · simp only [Prod.snd] at hv ⊢
    exact ⟨by omega, by omega, by omega⟩

/-- Proposition 6.5 with explicit constants instead of asymptotic notation.
The implementation produces the original forecast, maintains a fixed linear
record pool, and performs logarithmically many record visits each round. -/
theorem fixed_grid_exact_implementation {m : ℕ} (hm : 0 < m) (y : ℕ → Bool) (t : ℕ) :
    (gridTreeForecast m (gridTreeRun m y t) : ℝ) = gridForecast hm (gridRun hm y t) ∧
    GridTree.nodes (gridTreeRun m y t) < 4*(m+1) ∧
    gridTreeRoundVisits m (gridTreeRun m y t) (y t) = 4*(Nat.clog 2 (m+1)+1) ∧
    gridWordWidth m = Nat.clog 2 (m+1)+4 :=
  ⟨gridTreeForecast_correct hm y t, gridTree_nodes_lt m _,
    gridTreeRoundVisits_eq m _ _,rfl⟩

/-- Cost of initializing the next complete cached tree. -/
noncomputable def nextTreeBuildRecords (L : ℕ) : ℕ :=
  GridTree.nodes (gridTreeInitial (optimalGrid (2*L)))

theorem nextTreeBuildRecords_budget (L : ℕ) (hL : 1 ≤ L) :
    nextTreeBuildRecords L ≤ 8*L := by
  have hn := gridTree_nodes_lt (optimalGrid (2*L)) (gridTreeInitial (optimalGrid (2*L)))
  have hm := next_grid_node_budget L hL
  unfold nextTreeBuildRecords
  omega

/-- Eight constant-size record construction tasks per current round suffice
for the next tree. A paused recursive builder keeps its continuation stack. -/
noncomputable def preparedTreeRecords (L rounds : ℕ) : ℕ := min (nextTreeBuildRecords L) (8*rounds)

theorem preparedTreeRecords_step (L rounds : ℕ) :
    preparedTreeRecords L rounds ≤ preparedTreeRecords L (rounds+1) ∧
    preparedTreeRecords L (rounds+1) ≤ preparedTreeRecords L rounds+8 := by
  unfold preparedTreeRecords
  omega

theorem preparedTreeRecords_complete (L : ℕ) (hL : 1 ≤ L) :
    preparedTreeRecords L L = nextTreeBuildRecords L :=
  Nat.min_eq_left (nextTreeBuildRecords_budget L hL)

/-- Storage counts current, prepared and all retired trees, as in Appendix B.2. -/
theorem all_allocated_tree_records_lt (T : ℕ) (hT : 1 ≤ T) :
    (∑ k ∈ Finset.range (Nat.log 2 T+2),
      (GridTree.nodes (gridTreeInitial (optimalGrid (2^k))) : ℝ)) <
        96*Real.sqrt (T : ℝ) := by
  have hpoint : (∑ k ∈ Finset.range (Nat.log 2 T+2),
      (GridTree.nodes (gridTreeInitial (optimalGrid (2^k))) : ℝ)) ≤
        4*(∑ k ∈ Finset.range (Nat.log 2 T+2), ((optimalGrid (2^k)+1 : ℕ) : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    exact_mod_cast (gridTree_nodes_lt (optimalGrid (2^k)) _).le
  have hh := all_allocated_grid_nodes_lt T hT
  linarith

/-- The current epoch's grid cannot exceed its budget. -/
theorem optimalGrid_le_budget (L : ℕ) (hL : 1 ≤ L) : optimalGrid L ≤ L := by
  apply (optimalGrid_le_iff L L hL).2
  nlinarith

/-- Uniform prefix-time logarithmic bound for current-epoch work. -/
theorem epoch_tree_round_log_bound (L T : ℕ) (hL : 1 ≤ L) (hLT : L ≤ T)
    (tree : GridSearchTree (optimalGrid L)) (b : Bool) :
    gridTreeRoundVisits (optimalGrid L) tree b ≤ 4*(Nat.clog 2 (T+1)+1) := by
  rw [gridTreeRoundVisits_eq]
  have hm := optimalGrid_le_budget L hL
  have hd := Nat.clog_mono_right 2 (show optimalGrid L+1 ≤ T+1 by omega)
  omega

/-- Bounded integer search for the optimal grid; no square-root instruction
or noncomputable ceiling is needed by the implemented preparation routine. -/
def gridParameterSearch (T : ℕ) : ℕ → ℕ → ℕ
  | 0, n => n
  | fuel+1, n => if T ≤ n*(n+1) then n else gridParameterSearch T fuel (n+1)

def gridParameterSearchVisits (T : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel+1, n => if T ≤ n*(n+1) then 1 else 1+gridParameterSearchVisits T fuel (n+1)

theorem gridParameterSearchVisits_le (T fuel n : ℕ) :
    gridParameterSearchVisits T fuel n ≤ fuel := by
  induction fuel generalizing n with
  | zero => exact le_refl 0
  | succ fuel ih =>
    simp only [gridParameterSearchVisits]
    split_ifs
    · omega
    · have hh := ih (n+1)
      omega

theorem gridParameterSearch_correct (T : ℕ) (hT : 1 ≤ T) (fuel : ℕ) :
    ∀ n, 1 ≤ n → n ≤ optimalGrid T → optimalGrid T ≤ n+fuel →
      gridParameterSearch T fuel n = optimalGrid T := by
  induction fuel with
  | zero => intro n hn hlo hhi; simp only [gridParameterSearch]; omega
  | succ fuel ih =>
    intro n hn hlo hhi
    simp only [gridParameterSearch]
    split_ifs with hs
    · have hh : optimalGrid T ≤ n := (optimalGrid_le_iff T n hT).2 hs
      omega
    · have hnxt : n+1 ≤ optimalGrid T := by
        have hh : ¬ optimalGrid T ≤ n := by
          intro hh
          exact hs ((optimalGrid_le_iff T n hT).1 hh)
        omega
      exact ih (n+1) (by omega) hnxt (by omega)

def nextGridParameter (L : ℕ) : ℕ := gridParameterSearch (2*L) L 1

theorem nextGridParameter_correct (L : ℕ) (hL : 1 ≤ L) :
    nextGridParameter L = optimalGrid (2*L) := by
  apply gridParameterSearch_correct (2*L) (by omega) L 1 (by omega)
  · exact (optimalGrid_threshold (2*L) (by omega)).1
  · have hh : optimalGrid (2*L) ≤ L :=
      (optimalGrid_le_iff (2*L) L (by omega)).2 (by nlinarith)
    omega

/-- The next-epoch initializer is executable and has the original optimal
parameter, even though the mathematical specification uses a real ceiling. -/
def nextTreeInitializer (L : ℕ) : GridSearchTree (nextGridParameter L) :=
  gridTreeInitial (nextGridParameter L)

noncomputable def nextInitializationWork (L : ℕ) : ℕ :=
  gridParameterSearchVisits (2*L) L 1 + nextTreeBuildRecords L

theorem nextInitializationWork_budget (L : ℕ) (hL : 1 ≤ L) :
    nextInitializationWork L ≤ 9*L := by
  have hp := gridParameterSearchVisits_le (2*L) L 1
  have hb := nextTreeBuildRecords_budget L hL
  unfold nextInitializationWork
  omega

noncomputable def initializationProgress (L rounds : ℕ) : ℕ :=
  min (nextInitializationWork L) (9*rounds)

theorem initializationProgress_step (L rounds : ℕ) :
    initializationProgress L rounds ≤ initializationProgress L (rounds+1) ∧
    initializationProgress L (rounds+1) ≤ initializationProgress L rounds+9 := by
  unfold initializationProgress
  omega

theorem initializationProgress_complete (L : ℕ) (hL : 1 ≤ L) :
    initializationProgress L L = nextInitializationWork L :=
  Nat.min_eq_left (nextInitializationWork_budget L hL)

end CalibrationDistance
