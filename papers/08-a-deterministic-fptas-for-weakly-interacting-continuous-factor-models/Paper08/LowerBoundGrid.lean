import Paper08.LowerBoundSmooth
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! A finite, explicit `C¹` fooling function on a grid. Cells are marked exactly
when their interiors contain an actual queried point; all boundary queries also
vanish, because every one-dimensional bump has a vanishing first jet. -/
noncomputable section
open scoped Real BigOperators
open Set
namespace Paper08.LowerBound

abbrev GridCell (r L : ℕ) := Fin r → Fin L

/-- Interior membership, expressed without division so it also handles `L = 0`. -/
def InGridCell {r L : ℕ} (z : GridCell r L) (x : Fin r → ℝ) : Prop :=
  ∀ j, (z j : ℝ) < (L : ℝ) * x j ∧ (L : ℝ) * x j < (z j : ℝ) + 1

lemma inGridCell_unique {r L : ℕ} {z w : GridCell r L} {x : Fin r → ℝ}
    (hz : InGridCell z x) (hw : InGridCell w x) : z = w := by
  funext j
  apply Fin.ext
  have hzw : ((z j).val : ℝ) < ((w j).val : ℝ) + 1 := (hz j).1.trans (hw j).2
  have hwz : ((w j).val : ℝ) < ((z j).val : ℝ) + 1 := (hw j).1.trans (hz j).2
  have hzw' : (z j).val < (w j).val + 1 := by exact_mod_cast hzw
  have hwz' : (w j).val < (z j).val + 1 := by exact_mod_cast hwz
  omega

/-- Every queried point marks its unique interior cell, if there is one. -/
def markedGridCells {r L : ℕ} (queries : Finset (Fin r → ℝ)) : Finset (GridCell r L) := by
  classical
  exact queries.biUnion fun q => Finset.univ.filter fun z => InGridCell z q

lemma mem_markedGridCells {r L : ℕ} {queries : Finset (Fin r → ℝ)} {z : GridCell r L} :
    z ∈ markedGridCells queries ↔ ∃ q ∈ queries, InGridCell z q := by
  classical
  simp [markedGridCells]

lemma markedGridCells_card_le {r L : ℕ} (queries : Finset (Fin r → ℝ)) :
    (markedGridCells (L := L) queries).card ≤ queries.card := by
  classical
  unfold markedGridCells
  calc
    _ ≤ ∑ q ∈ queries, (Finset.univ.filter fun z : GridCell r L => InGridCell z q).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _q ∈ queries, 1 := by
      apply Finset.sum_le_sum
      intro q _
      apply Finset.card_le_one.mpr
      intro z hz w hw
      exact inGridCell_unique (Finset.mem_filter.mp hz).2 (Finset.mem_filter.mp hw).2
    _ = queries.card := by simp

/-- The unmarked grid cells. -/
def activeGridCells {r L : ℕ} (queries : Finset (Fin r → ℝ)) : Finset (GridCell r L) := by
  classical
  exact Finset.univ \ markedGridCells queries

lemma activeGridCells_card_ge {r L : ℕ} (queries : Finset (Fin r → ℝ)) :
    L ^ r - queries.card ≤ (activeGridCells (L := L) queries).card := by
  classical
  have hmark := markedGridCells_card_le (L := L) queries
  simp only [activeGridCells, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  omega

/-- The zero-extended product bump on one grid cell, with amplitude `a/L`. -/
def gridBump {r L : ℕ} (a : ℝ) (z : GridCell r L) (x : Fin r → ℝ) : ℝ :=
  (a / L) * ∏ j, compactBump ((L : ℝ) * x j - (z j : ℝ))

lemma gridBump_nonneg {r L : ℕ} {a : ℝ} (ha : 0 ≤ a) (z : GridCell r L)
    (x : Fin r → ℝ) : 0 ≤ gridBump a z x := by
  apply mul_nonneg (div_nonneg ha (Nat.cast_nonneg _))
  exact Finset.prod_nonneg fun j _ => compactBump_nonneg _

lemma gridBump_le {r L : ℕ} {a : ℝ} (ha : 0 ≤ a) (z : GridCell r L)
    (x : Fin r → ℝ) : gridBump a z x ≤ a / L := by
  apply mul_le_of_le_one_right (div_nonneg ha (Nat.cast_nonneg _))
  exact Finset.prod_le_one (fun j _ => compactBump_nonneg _) (fun j _ => compactBump_le_one _)

lemma gridBump_eq_zero_of_not_inGridCell {r L : ℕ} (a : ℝ) (z : GridCell r L)
    (x : Fin r → ℝ) (hx : ¬ InGridCell z x) : gridBump a z x = 0 := by
  classical
  simp only [InGridCell, not_forall] at hx
  obtain ⟨j, hj⟩ := hx
  have hb : compactBump ((L : ℝ) * x j - (z j : ℝ)) = 0 := by
    apply compactBump_eq_zero_of_not_mem_Ioo
    intro h
    exact hj ⟨by linarith [h.1], by linarith [h.2]⟩
  unfold gridBump
  rw [Finset.prod_eq_zero (f := fun j => compactBump ((L : ℝ) * x j - (z j : ℝ)))
    (Finset.mem_univ j) hb, mul_zero]

lemma contDiff_gridBump {r L : ℕ} (a : ℝ) (z : GridCell r L) :
    ContDiff ℝ 1 (gridBump a z) := by
  unfold gridBump
  apply contDiff_const.mul
  apply contDiff_prod
  intro j _
  exact contDiff_compactBump.comp (by fun_prop)

/-- The explicit fooling function: put a bump on every unmarked cell. -/
def foolingBump {r L : ℕ} (a : ℝ) (queries : Finset (Fin r → ℝ))
    (x : Fin r → ℝ) : ℝ := ∑ z ∈ activeGridCells (L := L) queries, gridBump a z x

theorem contDiff_foolingBump {r L : ℕ} (a : ℝ) (queries : Finset (Fin r → ℝ)) :
    ContDiff ℝ 1 (foolingBump (L := L) a queries) := by
  exact ContDiff.sum fun z _ => contDiff_gridBump a z

/-- All queries vanish, including queries lying on any grid face. -/
theorem foolingBump_at_query {r L : ℕ} (a : ℝ) (queries : Finset (Fin r → ℝ))
    {q : Fin r → ℝ} (hq : q ∈ queries) : foolingBump (L := L) a queries q = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro z hz
  apply gridBump_eq_zero_of_not_inGridCell
  intro hin
  have hmarked : z ∈ markedGridCells queries := mem_markedGridCells.mpr ⟨q, hq, hin⟩
  exact (Finset.mem_sdiff.mp hz).2 hmarked

lemma foolingBump_nonneg {r L : ℕ} {a : ℝ} (ha : 0 ≤ a)
    (queries : Finset (Fin r → ℝ)) (x : Fin r → ℝ) :
    0 ≤ foolingBump (L := L) a queries x := by
  exact Finset.sum_nonneg fun z _ => gridBump_nonneg ha z x

/-- Disjoint interiors ensure that a sum of bumps never adds their heights. -/
theorem foolingBump_le {r L : ℕ} {a : ℝ} (ha : 0 ≤ a)
    (queries : Finset (Fin r → ℝ)) (x : Fin r → ℝ) :
    foolingBump (L := L) a queries x ≤ a / L := by
  classical
  by_cases h : ∃ z ∈ activeGridCells (L := L) queries, InGridCell z x
  · obtain ⟨z, hz, hx⟩ := h
    have heq : foolingBump (L := L) a queries x = gridBump a z x := by
      apply Finset.sum_eq_single z
      · intro w hw hne
        apply gridBump_eq_zero_of_not_inGridCell
        intro hin
        exact hne (inGridCell_unique hin hx)
      · intro hnot
        exact False.elim (hnot hz)
    rw [heq]
    exact gridBump_le ha z x
  · have heq : foolingBump (L := L) a queries x = 0 := by
      apply Finset.sum_eq_zero
      intro z hz
      exact gridBump_eq_zero_of_not_inGridCell a z x (fun hx => h ⟨z, hz, hx⟩)
    rw [heq]
    positivity

/-- Adjoining the constant one gives a valid range-restricted `C¹` factor. -/
theorem foolingFactor_range {r L : ℕ} {a U : ℝ} (ha : 0 ≤ a) (haU : a ≤ U - 1)
    (hL : 1 ≤ L) (queries : Finset (Fin r → ℝ)) (x : Fin r → ℝ) :
    1 ≤ 1 + foolingBump (L := L) a queries x ∧
      1 + foolingBump (L := L) a queries x ≤ U := by
  have hlo := foolingBump_nonneg (L := L) ha queries x
  have hhi := foolingBump_le (L := L) ha queries x
  have hdiv : a / (L : ℝ) ≤ a := div_le_self ha (by exact_mod_cast hL)
  constructor <;> linarith

end Paper08.LowerBound
