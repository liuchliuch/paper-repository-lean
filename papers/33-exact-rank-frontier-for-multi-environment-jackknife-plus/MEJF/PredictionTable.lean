import MEJF.OrderStatistics
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Erase

/-!
# The additive prediction table construction (Section 5)

The learner below acts on actual finite multisets of blocks, retaining repeated
occurrences.  Its type indicator reads the complete covariate tuple and ignores
responses.  The table is arbitrary: the telescoping theorem is not restricted to
the three-valued sharpness table.
-/
namespace MEJF.PredictionTable

open Finset
noncomputable section

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

/-- A block at the designated finite covariate space, with arbitrary responses. -/
structure Block (V J : Type*) where
  x : J → V × J
  y : J → ℝ

/-- The deterministic block type in (5.1). -/
def typeBlock (v : V) : Block V J := ⟨fun j => (v, j), fun _ => 0⟩

/-- The full-tuple type recognizer used in (5.3); responses are ignored. -/
def recognizes (Z : Block V J) (v : V) : Prop := Z.x = fun j => (v, j)

instance (Z : Block V J) (v : V) : Decidable (recognizes Z v) :=
  inferInstanceAs (Decidable (Z.x = fun j => (v, j)))

lemma recognizes_typeBlock [Nonempty J] (v w : V) :
    recognizes (typeBlock (J := J) v) w ↔ v = w := by
  constructor
  · intro h
    exact congrArg Prod.fst (congrFun h (Classical.choice (inferInstance : Nonempty J)))
  · rintro rfl
    rfl

/-- The constant `c_uj` in (5.3). -/
def tableConstant (p : V → V → J → ℝ) (u : V) (j : J) : ℝ :=
  ∑ v ∈ (univ : Finset V).erase u, p u v j

/-- One training-block contribution, including every type indicator in (5.3). -/
def contribution (p : V → V → J → ℝ) (Z : Block V J) (u : V) (j : J) : ℝ :=
  ∑ v ∈ (univ : Finset V).erase u, if recognizes Z v then p u v j else 0

/-- The actual additive multiset learner (5.3), evaluated at `(u,j)`. -/
def learner (p : V → V → J → ℝ) (T : Multiset (Block V J)) (u : V) (j : J) : ℝ :=
  tableConstant p u j - (T.map fun Z => contribution p Z u j).sum

lemma contribution_typeBlock [Nonempty J] (p : V → V → J → ℝ) (u v : V) (j : J) :
    contribution p (typeBlock v) u j = if v = u then 0 else p u v j := by
  classical
  simp only [contribution, recognizes_typeBlock]
  by_cases h : v = u
  · subst v
    simp
  · simp [h]

/-- The training multiset containing each type except the omitted pair once. -/
def leavePair (u v : V) : Multiset (Block V J) :=
  (((univ : Finset V).erase u).erase v).val.map typeBlock

/-- The formula (5.3) realizes every prescribed pairwise table entry exactly. -/
theorem learner_leavePair [Nonempty J] (p : V → V → J → ℝ)
    (u v : V) (huv : u ≠ v) (j : J) :
    learner p (leavePair u v) u j = p u v j := by
  classical
  have hv : v ∈ (univ : Finset V).erase u := by simp [Ne.symm huv]
  have hsum : (∑ w ∈ ((univ : Finset V).erase u).erase v, p u w j) + p u v j =
      tableConstant p u j := by
    exact sum_erase_add _ _ hv
  unfold learner leavePair
  simp only [Multiset.map_map, Function.comp_apply, contribution_typeBlock]
  have hterm : ∀ w ∈ ((univ : Finset V).erase u).erase v,
      (if w = u then (0 : ℝ) else p u w j) = p u w j := by
    intro w hw
    have hwu : w ≠ u := (mem_erase.mp (mem_erase.mp hw).2).1
    simp [hwu]
  change tableConstant p u j - (∑ w ∈ ((univ : Finset V).erase u).erase v,
      if w = u then (0 : ℝ) else p u w j) = _
  rw [Finset.sum_congr rfl hterm]
  linarith

/-- Adding multisets counts every training occurrence, including duplicates. -/
theorem learner_add (p : V → V → J → ℝ) (T U : Multiset (Block V J))
    (u : V) (j : J) :
    learner p (T + U) u j = learner p T u j + learner p U u j - tableConstant p u j := by
  simp only [learner, Multiset.map_add, Multiset.sum_add]
  ring

/-- Repeating a recognized type subtracts its table entry once per occurrence. -/
theorem learner_replicate [Nonempty J] (p : V → V → J → ℝ)
    (T : Multiset (Block V J)) (u v : V) (huv : u ≠ v) (j : J) (k : ℕ) :
    learner p (T + Multiset.replicate k (typeBlock v)) u j =
      learner p T u j - k * p u v j := by
  simp [learner, contribution_typeBlock, Ne.symm huv, nsmul_eq_mul]
  ring

/-- List implementations are invariant under reordering the training blocks. -/
theorem learner_list_perm (p : V → V → J → ℝ) (T U : List (Block V J))
    (h : T.Perm U) (u : V) (j : J) :
    learner p (T : Multiset (Block V J)) u j = learner p (U : Multiset (Block V J)) u j := by
  exact congrArg (fun M => learner p M u j) (Quot.sound h)

/-- Responses never affect the fitted prediction in the construction. -/
theorem contribution_ignores_responses (p : V → V → J → ℝ)
    (Z W : Block V J) (h : Z.x = W.x) (u : V) (j : J) :
    contribution p Z u j = contribution p W u j := by
  simp only [contribution, recognizes, h]

end
end MEJF.PredictionTable

namespace MEJF.PredictionTable
open Finset
noncomputable section
open MEJF.OrderStatistics

variable {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}

/-- The binary incidence column sum, counting indexed coordinates. -/
def markedCount (B : V → Fin n → V → Bool) (u v : V) : ℕ :=
  (univ.filter fun j => B u j v = true).card

/-- Equation (5.2), with inactive rows/vertices encoded by zero incidence bits. -/
def incidenceTable (edge : V → V → Prop) [DecidableRel edge]
    (B : V → Fin n → V → Bool) (u v : V) (j : Fin n) : ℝ :=
  if B u j v then if edge v u then 3 else 2 else 1

lemma incidenceTable_values (edge : V → V → Prop) [DecidableRel edge]
    (B : V → Fin n → V → Bool) (u v : V) (j : Fin n) :
    incidenceTable edge B u v j = 1 ∨ incidenceTable edge B u v j = 2 ∨
      incidenceTable edge B u v j = 3 := by
  unfold incidenceTable
  split_ifs <;> norm_num

lemma incidenceTable_pos (edge : V → V → Prop) [DecidableRel edge]
    (B : V → Fin n → V → Bool) (u v : V) (j : Fin n) :
    0 < incidenceTable edge B u v j := by
  rcases incidenceTable_values edge B u v j with h | h | h <;> norm_num [h]

lemma incidenceTable_ge_one (edge : V → V → Prop) [DecidableRel edge]
    (B : V → Fin n → V → Bool) (u v : V) (j : Fin n) :
    1 ≤ incidenceTable edge B u v j := by
  rcases incidenceTable_values edge B u v j with h | h | h <;> norm_num [h]

lemma incidenceTable_gt_one_count (edge : V → V → Prop) [DecidableRel edge]
    (B : V → Fin n → V → Bool) (u v : V) :
    count (incidenceTable edge B u v) (1 < ·) = markedCount B u v := by
  classical
  unfold count markedCount
  congr 1
  ext j
  simp only [mem_filter, mem_univ, true_and]
  by_cases he : edge v u <;> cases h : B u j v <;> simp [incidenceTable, h, he]

/-- The positive finite inner rank of (5.4), with paper rank `n+1-t`. -/
def tableRadius (p : V → V → Fin n → ℝ) (u v : V) (t : ℕ)
    (ht : 0 < t) (htn : t ≤ n) : ℝ :=
  stat (p u v) ⟨n - t, by omega⟩

/-- If fewer than `t` entries exceed one, the inner statistic is exactly one. -/
lemma stat_eq_one_of_few_above (a : Fin n → ℝ) {t : ℕ}
    (ht : 0 < t) (htn : t ≤ n) (hmin : ∀ j, 1 ≤ a j)
    (hfew : count a (1 < ·) < t) :
    stat a ⟨n - t, by omega⟩ = 1 := by
  apply le_antisymm
  · apply (stat_le_iff_count _ _ _).mpr
    change n - t < count a (· ≤ 1)
    have htotal := count_le_add_count_gt a 1
    omega
  · exact hmin _

/-- A one/two column with at least `t` twos has inner statistic exactly two. -/
lemma stat_eq_two_of_many (a : Fin n → ℝ) {t : ℕ}
    (ht : 0 < t) (htn : t ≤ n) (hvalues : ∀ j, a j = 1 ∨ a j = 2)
    (hmany : t ≤ count a (1 < ·)) :
    stat a ⟨n - t, by omega⟩ = 2 := by
  have hval := hvalues (Tuple.sort a ⟨n - t, by omega⟩)
  change stat a ⟨n - t, by omega⟩ = 1 ∨ stat a ⟨n - t, by omega⟩ = 2 at hval
  rcases hval with hone | htwo
  · have hle : stat a ⟨n - t, by omega⟩ ≤ 1 := by rw [hone]
    have hlarge := (stat_le_iff_count _ _ _).mp hle
    change n - t < count a (· ≤ 1) at hlarge
    have htotal := count_le_add_count_gt a 1
    omega
  · exact htwo

/-- The exact inner radii (5.4), obtained from genuine sorted order statistics. -/
theorem tableRadius_incidence (edge : V → V → Prop) [DecidableRel edge]
    (hasym : ∀ {u v}, edge u v → ¬ edge v u)
    (B : V → Fin n → V → Bool) {t : ℕ} (ht : 0 < t) (htn : t ≤ n)
    (hmarked : ∀ u v, edge u v → t ≤ markedCount B u v)
    (hunmarked : ∀ u v, ¬ edge u v → markedCount B u v < t) (u v : V) :
    tableRadius (incidenceTable edge B) u v t ht htn = if edge u v then 2 else 1 := by
  unfold tableRadius
  by_cases huv : edge u v
  · simp only [if_pos huv]
    apply stat_eq_two_of_many _ ht htn
    · intro j
      cases h : B u j v <;> simp [incidenceTable, h, hasym huv]
    · rw [incidenceTable_gt_one_count]
      exact hmarked u v huv
  · simp only [if_neg huv]
    apply stat_eq_one_of_few_above _ ht htn
    · exact incidenceTable_ge_one edge B u v
    · rw [incidenceTable_gt_one_count]
      exact hunmarked u v huv

/-- Zero-response absolute residuals of the actual learner equal the table. -/
theorem learner_residual_leavePair (edge : V → V → Prop) [DecidableRel edge]
    (B : V → Fin n → V → Bool) (hn : 0 < n) (u v : V) (huv : u ≠ v) (j : Fin n) :
    |0 - learner (incidenceTable edge B) (leavePair u v) u j| =
      incidenceTable edge B u v j := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [learner_leavePair _ _ _ huv]
  simp only [zero_sub, abs_neg, abs_of_pos (incidenceTable_pos edge B u v j)]

/-- The radius of an actual leave-two multiset fit is the graph's one/two radius. -/
theorem learner_radius_incidence (edge : V → V → Prop) [DecidableRel edge]
    (hasym : ∀ {u v}, edge u v → ¬ edge v u)
    (B : V → Fin n → V → Bool) {t : ℕ} (ht : 0 < t) (htn : t ≤ n)
    (hmarked : ∀ u v, edge u v → t ≤ markedCount B u v)
    (hunmarked : ∀ u v, ¬ edge u v → markedCount B u v < t)
    (u v : V) (huv : u ≠ v) :
    stat (fun j => |0 - learner (incidenceTable edge B) (leavePair u v) u j|)
      ⟨n - t, by omega⟩ = if edge u v then 2 else 1 := by
  have hn : 0 < n := by omega
  simp_rw [learner_residual_leavePair edge B hn u v huv]
  exact tableRadius_incidence edge hasym B ht htn hmarked hunmarked u v

end
end MEJF.PredictionTable

namespace MEJF.PredictionTable
open Finset
noncomputable section
open MEJF.OrderStatistics

variable {V : Type*} [Fintype V] [DecidableEq V] {n m : ℕ}

/-- Candidate endpoints after substituting the exact radii (5.4). -/
def incidenceLower (edge : V → V → Prop) [DecidableRel edge]
    (B : V → Fin n → V → Bool) (u v : V) (j : Fin n) : ℝ :=
  incidenceTable edge B u v j - if edge v u then 2 else 1

def incidenceUpper (edge : V → V → Prop) [DecidableRel edge]
    (B : V → Fin n → V → Bool) (u v : V) (j : Fin n) : ℝ :=
  incidenceTable edge B u v j + if edge v u then 2 else 1

/-- The marked entries in (5.5) are exactly one. -/
lemma incidenceLower_marked (edge : V → V → Prop) [DecidableRel edge]
    (B : V → Fin n → V → Bool) (u v : V) (j : Fin n) (hB : B u j v = true) :
    incidenceLower edge B u v j = 1 := by
  unfold incidenceLower incidenceTable
  simp only [hB, Bool.true_eq, ↓reduceIte]
  split_ifs <;> norm_num

/-- Every unmarked lower candidate is nonpositive. -/
lemma incidenceLower_unmarked (edge : V → V → Prop) [DecidableRel edge]
    (B : V → Fin n → V → Bool) (u v : V) (j : Fin n) (hB : B u j v = false) :
    incidenceLower edge B u v j ≤ 0 := by
  unfold incidenceLower incidenceTable
  simp only [hB, Bool.false_eq_true, ↓reduceIte]
  split_ifs <;> norm_num

lemma incidenceLower_nonpositive_iff (edge : V → V → Prop) [DecidableRel edge]
    (B : V → Fin n → V → Bool) (u v : V) (j : Fin n) :
    incidenceLower edge B u v j ≤ 0 ↔ B u j v = false := by
  cases hB : B u j v
  · simp [incidenceLower_unmarked edge B u v j hB]
  · simp [incidenceLower_marked edge B u v j hB]

lemma incidenceUpper_pos (edge : V → V → Prop) [DecidableRel edge]
    (B : V → Fin n → V → Bool) (u v : V) (j : Fin n) :
    0 < incidenceUpper edge B u v j := by
  have hp := incidenceTable_pos edge B u v j
  unfold incidenceUpper
  split_ifs <;> linarith

/-- Exact endpoint order statistic from the number of nonpositive candidates. -/
lemma stat_eq_one_of_nonpositive_count (a : Fin m → ℝ) {ell : ℕ}
    (hell : 0 < ell) (hellm : ell ≤ m)
    (hvalues : ∀ v, a v = 1 ∨ a v ≤ 0)
    (hcount : count a (· ≤ 0) = ell - 1) :
    stat a ⟨ell - 1, by omega⟩ = 1 := by
  have hvalue := hvalues (Tuple.sort a ⟨ell - 1, by omega⟩)
  change stat a ⟨ell - 1, by omega⟩ = 1 ∨ stat a ⟨ell - 1, by omega⟩ ≤ 0 at hvalue
  rcases hvalue with hone | hzero
  · exact hone
  · have hlt := (stat_le_iff_count _ _ _).mp hzero
    simp only [hcount] at hlt
    omega

/-- The row-sum argument in (5.5), for any enumeration of calibration types. -/
theorem incidence_lower_endpoint (edge : V → V → Prop) [DecidableRel edge]
    (B : V → Fin n → V → Bool) (u : V) (j : Fin n) (e : Fin m → V)
    {ell : ℕ} (hell : 0 < ell) (hellm : ell ≤ m)
    (hrow : (univ.filter fun i => B u j (e i) = false).card = ell - 1) :
    stat (fun i => incidenceLower edge B u (e i) j) ⟨ell - 1, by omega⟩ = 1 := by
  apply stat_eq_one_of_nonpositive_count _ hell hellm
  · intro i
    cases hB : B u j (e i)
    · exact Or.inr (incidenceLower_unmarked edge B u (e i) j hB)
    · exact Or.inl (incidenceLower_marked edge B u (e i) j hB)
  · unfold count
    simpa only [incidenceLower_nonpositive_iff] using hrow

/-- Hence the zero response misses this coordinate of the actual sorted interval. -/
theorem incidence_coordinate_miss (edge : V → V → Prop) [DecidableRel edge]
    (B : V → Fin n → V → Bool) (u : V) (j : Fin n) (e : Fin m → V)
    {ell : ℕ} (hell : 0 < ell) (hellm : ell ≤ m)
    (hrow : (univ.filter fun i => B u j (e i) = false).card = ell - 1)
    (kupper : Fin m) :
    ¬ (stat (fun i => incidenceLower edge B u (e i) j) ⟨ell - 1, by omega⟩ ≤ 0 ∧
       0 ≤ stat (fun i => incidenceUpper edge B u (e i) j) kupper) := by
  rw [incidence_lower_endpoint edge B u j e hell hellm hrow]
  norm_num

/-- A zero-incidence coordinate covers zero under both actual sorted endpoints. -/
theorem incidence_zero_coordinate_covered (edge : V → V → Prop) [DecidableRel edge]
    (B : V → Fin n → V → Bool) (u : V) (j : Fin n) (e : Fin m → V)
    (hzero : ∀ i, B u j (e i) = false) (klower kupper : Fin m) :
    stat (fun i => incidenceLower edge B u (e i) j) klower ≤ 0 ∧
      0 ≤ stat (fun i => incidenceUpper edge B u (e i) j) kupper := by
  constructor
  · exact incidenceLower_unmarked edge B u (e _) j (hzero _)
  · exact le_of_lt (incidenceUpper_pos edge B u (e _) j)

end
end MEJF.PredictionTable

namespace MEJF.PredictionTable
open Finset
noncomputable section
open MEJF.OrderStatistics

variable {V : Type*} [Fintype V] [DecidableEq V] {n m : ℕ}

lemma leavePair_comm (u v : V) : leavePair (J := Fin n) u v = leavePair v u := by
  unfold leavePair
  rw [Finset.erase_right_comm]

/-- The residual radius formed from the actual multiset learner. -/
def fittedRadius (p : V → V → Fin n → ℝ) (u v : V) (t : ℕ)
    (ht : 0 < t) (htn : t ≤ n) : ℝ :=
  stat (fun j => |0 - learner p (leavePair u v) u j|) ⟨n - t, by omega⟩

/-- The actual leave-two lower endpoint candidate at a designated covariate. -/
def fittedLower (p : V → V → Fin n → ℝ) (u v : V) (j : Fin n) (t : ℕ)
    (ht : 0 < t) (htn : t ≤ n) : ℝ :=
  learner p (leavePair u v) u j - fittedRadius p v u t ht htn

/-- The corresponding actual leave-two upper endpoint candidate. -/
def fittedUpper (p : V → V → Fin n → ℝ) (u v : V) (j : Fin n) (t : ℕ)
    (ht : 0 < t) (htn : t ≤ n) : ℝ :=
  learner p (leavePair u v) u j + fittedRadius p v u t ht htn

lemma fittedLower_incidence (edge : V → V → Prop) [DecidableRel edge]
    (hasym : ∀ {u v}, edge u v → ¬ edge v u)
    (B : V → Fin n → V → Bool) {t : ℕ} (ht : 0 < t) (htn : t ≤ n)
    (hmarked : ∀ u v, edge u v → t ≤ markedCount B u v)
    (hunmarked : ∀ u v, ¬ edge u v → markedCount B u v < t)
    (u v : V) (huv : u ≠ v) (j : Fin n) :
    fittedLower (incidenceTable edge B) u v j t ht htn = incidenceLower edge B u v j := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  unfold fittedLower fittedRadius incidenceLower
  rw [learner_leavePair _ _ _ huv,
    learner_radius_incidence edge hasym B ht htn hmarked hunmarked v u (Ne.symm huv)]

lemma fittedUpper_incidence (edge : V → V → Prop) [DecidableRel edge]
    (hasym : ∀ {u v}, edge u v → ¬ edge v u)
    (B : V → Fin n → V → Bool) {t : ℕ} (ht : 0 < t) (htn : t ≤ n)
    (hmarked : ∀ u v, edge u v → t ≤ markedCount B u v)
    (hunmarked : ∀ u v, ¬ edge u v → markedCount B u v < t)
    (u v : V) (huv : u ≠ v) (j : Fin n) :
    fittedUpper (incidenceTable edge B) u v j t ht htn = incidenceUpper edge B u v j := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  unfold fittedUpper fittedRadius incidenceUpper
  rw [learner_leavePair _ _ _ huv,
    learner_radius_incidence edge hasym B ht htn hmarked hunmarked v u (Ne.symm huv)]

/-- Fully fitted version of the strict lower endpoint causing each designated miss. -/
theorem fitted_incidence_lower_endpoint (edge : V → V → Prop) [DecidableRel edge]
    (hasym : ∀ {u v}, edge u v → ¬ edge v u)
    (B : V → Fin n → V → Bool) {t : ℕ} (ht : 0 < t) (htn : t ≤ n)
    (hmarked : ∀ u v, edge u v → t ≤ markedCount B u v)
    (hunmarked : ∀ u v, ¬ edge u v → markedCount B u v < t)
    (u : V) (j : Fin n) (e : Fin m → V) (he : ∀ i, u ≠ e i)
    {ell : ℕ} (hell : 0 < ell) (hellm : ell ≤ m)
    (hrow : (univ.filter fun i => B u j (e i) = false).card = ell - 1) :
    stat (fun i => fittedLower (incidenceTable edge B) u (e i) j t ht htn)
      ⟨ell - 1, by omega⟩ = 1 := by
  have heq : (fun i => fittedLower (incidenceTable edge B) u (e i) j t ht htn) =
      fun i => incidenceLower edge B u (e i) j := by
    funext i
    exact fittedLower_incidence edge hasym B ht htn hmarked hunmarked u (e i) (he i) j
  rw [heq]
  exact incidence_lower_endpoint edge B u j e hell hellm hrow

/-- The actual sorted endpoint interval excludes zero on a designated failing row. -/
theorem fitted_incidence_coordinate_miss (edge : V → V → Prop) [DecidableRel edge]
    (hasym : ∀ {u v}, edge u v → ¬ edge v u)
    (B : V → Fin n → V → Bool) {t : ℕ} (ht : 0 < t) (htn : t ≤ n)
    (hmarked : ∀ u v, edge u v → t ≤ markedCount B u v)
    (hunmarked : ∀ u v, ¬ edge u v → markedCount B u v < t)
    (u : V) (j : Fin n) (e : Fin m → V) (he : ∀ i, u ≠ e i)
    {ell : ℕ} (hell : 0 < ell) (hellm : ell ≤ m)
    (hrow : (univ.filter fun i => B u j (e i) = false).card = ell - 1)
    (kupper : Fin m) :
    ¬ (stat (fun i => fittedLower (incidenceTable edge B) u (e i) j t ht htn)
        ⟨ell - 1, by omega⟩ ≤ 0 ∧
       0 ≤ stat (fun i => fittedUpper (incidenceTable edge B) u (e i) j t ht htn) kupper) := by
  rw [fitted_incidence_lower_endpoint edge hasym B ht htn hmarked hunmarked u j e he hell hellm hrow]
  norm_num

end
end MEJF.PredictionTable

namespace MEJF.PredictionTable
open Finset
noncomputable section
open MEJF.OrderStatistics

variable {V : Type*} [Fintype V] [DecidableEq V] {n m : ℕ}

/-- Actual endpoint coverage on the coordinates whose incidence entries vanish. -/
theorem fitted_incidence_zero_coordinate_covered (edge : V → V → Prop) [DecidableRel edge]
    (hasym : ∀ {u v}, edge u v → ¬ edge v u)
    (B : V → Fin n → V → Bool) {t : ℕ} (ht : 0 < t) (htn : t ≤ n)
    (hmarked : ∀ u v, edge u v → t ≤ markedCount B u v)
    (hunmarked : ∀ u v, ¬ edge u v → markedCount B u v < t)
    (u : V) (j : Fin n) (e : Fin m → V) (he : ∀ i, u ≠ e i)
    (hzero : ∀ i, B u j (e i) = false) (klower kupper : Fin m) :
    stat (fun i => fittedLower (incidenceTable edge B) u (e i) j t ht htn) klower ≤ 0 ∧
      0 ≤ stat (fun i => fittedUpper (incidenceTable edge B) u (e i) j t ht htn) kupper := by
  have hl : ∀ i, fittedLower (incidenceTable edge B) u (e i) j t ht htn =
      incidenceLower edge B u (e i) j := fun i =>
    fittedLower_incidence edge hasym B ht htn hmarked hunmarked u (e i) (he i) j
  have hu : ∀ i, fittedUpper (incidenceTable edge B) u (e i) j t ht htn =
      incidenceUpper edge B u (e i) j := fun i =>
    fittedUpper_incidence edge hasym B ht htn hmarked hunmarked u (e i) (he i) j
  simp_rw [hl, hu]
  exact incidence_zero_coordinate_covered edge B u j e hzero klower kupper

/-- The constructed learner misses exactly the prescribed set of coordinates. -/
theorem fitted_incidence_failure_set (edge : V → V → Prop) [DecidableRel edge]
    (hasym : ∀ {u v}, edge u v → ¬ edge v u)
    (B : V → Fin n → V → Bool) {t : ℕ} (ht : 0 < t) (htn : t ≤ n)
    (hmarked : ∀ u v, edge u v → t ≤ markedCount B u v)
    (hunmarked : ∀ u v, ¬ edge u v → markedCount B u v < t)
    (u : V) (e : Fin m → V) (he : ∀ i, u ≠ e i)
    {ell : ℕ} (hell : 0 < ell) (hellm : ell ≤ m) (s : Finset (Fin n))
    (hrows : ∀ j ∈ s, (univ.filter fun i => B u j (e i) = false).card = ell - 1)
    (hzero : ∀ j ∉ s, ∀ i, B u j (e i) = false) (kupper : Fin m) :
    (univ.filter fun j =>
      ¬ (stat (fun i => fittedLower (incidenceTable edge B) u (e i) j t ht htn)
           ⟨ell - 1, by omega⟩ ≤ 0 ∧
         0 ≤ stat (fun i => fittedUpper (incidenceTable edge B) u (e i) j t ht htn) kupper)) = s := by
  classical
  ext j
  simp only [mem_filter, mem_univ, true_and]
  by_cases hj : j ∈ s
  · simp only [hj, iff_true]
    exact fitted_incidence_coordinate_miss edge hasym B ht htn hmarked hunmarked u j e he
      hell hellm (hrows j hj) kupper
  · simp only [hj, iff_false, not_not]
    exact fitted_incidence_zero_coordinate_covered edge hasym B ht htn hmarked hunmarked u j e he
      (hzero j hj) _ kupper

end
end MEJF.PredictionTable
