/-
Copyright (c) 2026. Finite lattice separator geometry for Appendix A.2.

The separator is constructed from coordinate residue hyperplanes. Its size is
proved by finite averaging, and every path in its complement is proved to stay
inside an explicitly finite cell. No separator or geometric estimate is assumed.
-/
import Paper09.Basic
import Paper09.CanonicalPath
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Encodable.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset BigOperators

noncomputable section

namespace Paper09.LatticeGeometry

/-- Integer lattice points in dimension `d`. -/
abbrev Point (d : ℕ) := Fin d → ℤ

/-- Nearest-neighbor adjacency in the integer lattice. -/
def Adj {d : ℕ} (x y : Point d) : Prop :=
  ∃ j, (y j = x j + 1 ∨ x j = y j + 1) ∧ ∀ k, k ≠ j → x k = y k

instance {d : ℕ} (x y : Point d) : Decidable (Adj x y) := by
  unfold Adj
  infer_instance

theorem adj_symm {d : ℕ} {x y : Point d} (h : Adj x y) : Adj y x := by
  obtain ⟨j, hj, hk⟩ := h
  exact ⟨j, hj.symm, fun k hkj => (hk k hkj).symm⟩

theorem adj_irrefl {d : ℕ} (x : Point d) : ¬ Adj x x := by
  rintro ⟨j, hj, _⟩
  rcases hj with h | h <;> omega

/-- The explicit `2d` possible lattice neighbors of a point. -/
def neighbors {d : ℕ} (x : Point d) : Finset (Point d) :=
  Finset.univ.biUnion (fun j : Fin d =>
    {Function.update x j (x j + 1), Function.update x j (x j - 1)})

@[simp]
theorem mem_neighbors {d : ℕ} {x y : Point d} : y ∈ neighbors x ↔ Adj x y := by
  classical
  constructor
  · intro hy
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · refine ⟨j, Or.inl (by simp), ?_⟩
      intro k hkj
      simp [Function.update_of_ne hkj]
    · refine ⟨j, Or.inr (by simp), ?_⟩
      intro k hkj
      simp [Function.update_of_ne hkj]
  · rintro ⟨j, hj, hother⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨j, Finset.mem_univ _, ?_⟩
    rcases hj with hj | hj
    · have heq : y = Function.update x j (x j + 1) := by
        funext k
        by_cases hkj : k = j
        · subst k; simp [hj]
        · simp [Function.update_of_ne hkj, ← hother k hkj]
      simp [heq]
    · have heq : y = Function.update x j (x j - 1) := by
        funext k
        by_cases hkj : k = j
        · subst k; simp; omega
        · simp [Function.update_of_ne hkj, ← hother k hkj]
      simp [heq]

theorem card_neighbors_le {d : ℕ} (x : Point d) : (neighbors x).card ≤ 2 * d := by
  classical
  calc
    (neighbors x).card ≤ ∑ j : Fin d,
        ({Function.update x j (x j + 1), Function.update x j (x j - 1)} :
          Finset (Point d)).card := Finset.card_biUnion_le
    _ ≤ ∑ _j : Fin d, 2 := Finset.sum_le_sum (fun j _ => by
      simpa using Finset.card_insert_le
        (Function.update x j (x j + 1)) {Function.update x j (x j - 1)})
    _ = 2 * d := by simp [Nat.mul_comm]

/-- Degree bound for every induced finite lattice domain. -/
theorem degree_bound {d : ℕ} (A : Finset (Point d)) (x : Point d) :
    (A.filter (Adj x)).card ≤ 2 * d := by
  classical
  exact (Finset.card_le_card (show A.filter (Adj x) ⊆ neighbors x from
    fun _ hy => mem_neighbors.mpr (Finset.mem_filter.mp hy).2)).trans (card_neighbors_le x)

/-- A residue class containing at most the average number of points. -/
theorem exists_sparse_residue {α : Type*} [DecidableEq α]
    (A : Finset α) (f : α → ℤ) (ell : ℕ) (hell : 0 < ell) :
    ∃ r ∈ Finset.Ico (0 : ℤ) ell,
      (A.filter (fun x => f x % (ell : ℤ) = r)).card * ell ≤ A.card := by
  classical
  let T : Finset ℤ := Finset.Ico 0 ell
  have hT : T.Nonempty := ⟨0, by simp [T, hell]⟩
  have hcard : T.card = ell := by simp [T, Int.card_Ico]
  have hmap : ∀ x ∈ A, f x % (ell : ℤ) ∈ T := by
    intro x _
    have hpos : (0 : ℤ) < ell := by exact_mod_cast hell
    exact Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ (ne_of_gt hpos),
      Int.emod_lt_of_pos _ hpos⟩
  have hsum : ∑ r ∈ T, (A.filter (fun x => f x % (ell : ℤ) = r)).card = A.card := by
    exact (Finset.card_eq_sum_card_fiberwise hmap).symm
  have havg :
      (∑ r ∈ T, (A.filter (fun x => f x % (ell : ℤ) = r)).card * ell)
        ≤ ∑ _r ∈ T, A.card := by
    rw [← Finset.sum_mul, hsum]
    simp [hcard, Nat.mul_comm]
  exact Finset.exists_le_of_sum_le hT havg

/-- Vertices lying on one of the selected coordinate hyperplanes. -/
def separator {d : ℕ} (A : Finset (Point d)) (ell : ℕ) (r : Point d) :
    Finset (Point d) :=
  A.filter (fun x => ∃ j, x j % (ell : ℤ) = r j)

@[simp]
theorem mem_separator {d : ℕ} {A : Finset (Point d)} {ell : ℕ} {r x : Point d} :
    x ∈ separator A ell r ↔ x ∈ A ∧ ∃ j, x j % (ell : ℤ) = r j := by
  classical
  simp [separator]

theorem separator_subset {d : ℕ} (A : Finset (Point d)) (ell : ℕ) (r : Point d) :
    separator A ell r ⊆ A := by
  classical
  exact Finset.filter_subset _ _

/-- The elementary averaging step of Appendix A.2, with no rounding loss:
`ell * |S| ≤ d * |A|`. -/
theorem exists_small_separator {d : ℕ} (A : Finset (Point d))
    (ell : ℕ) (hell : 0 < ell) :
    ∃ r : Point d, (∀ j, 0 ≤ r j ∧ r j < ell) ∧
      (separator A ell r).card * ell ≤ d * A.card := by
  classical
  have hchoice : ∀ j : Fin d, ∃ r : ℤ, r ∈ Finset.Ico (0 : ℤ) ell ∧
      (A.filter (fun x => x j % (ell : ℤ) = r)).card * ell ≤ A.card := by
    intro j
    exact exists_sparse_residue A (fun x => x j) ell hell
  choose r hr hcount using hchoice
  refine ⟨r, fun j => Finset.mem_Ico.mp (hr j), ?_⟩
  have hsub : separator A ell r ⊆
      Finset.univ.biUnion (fun j : Fin d => A.filter (fun x => x j % (ell : ℤ) = r j)) := by
    intro x hx
    obtain ⟨hxA, j, hj⟩ := mem_separator.mp hx
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hxA, hj⟩⟩
  calc
    (separator A ell r).card * ell ≤
        (Finset.univ.biUnion (fun j : Fin d =>
          A.filter (fun x => x j % (ell : ℤ) = r j))).card * ell :=
      Nat.mul_le_mul_right ell (Finset.card_le_card hsub)
    _ ≤ (∑ j : Fin d, (A.filter (fun x => x j % (ell : ℤ) = r j)).card) * ell :=
      Nat.mul_le_mul_right ell Finset.card_biUnion_le
    _ = ∑ j : Fin d, (A.filter (fun x => x j % (ell : ℤ) = r j)).card * ell :=
      Finset.sum_mul _ _ _
    _ ≤ ∑ _j : Fin d, A.card := Finset.sum_le_sum (fun j _ => hcount j)
    _ = d * A.card := by simp

/-- The index of the open cell containing a point outside the hyperplanes. -/
def cellIndex {d : ℕ} (ell : ℕ) (r x : Point d) : Point d :=
  fun j => (x j - r j) / (ell : ℤ)

/-- The open lattice cell between successive coordinate hyperplanes. -/
def cell {d : ℕ} (ell : ℕ) (r k : Point d) : Finset (Point d) :=
  Fintype.piFinset (fun j => Finset.Icc
    (r j + k j * (ell : ℤ) + 1) (r j + k j * (ell : ℤ) + (ell : ℤ) - 1))

/-- Each open cell has exactly `(ell-1)^d` lattice points. -/
theorem card_cell {d : ℕ} (ell : ℕ) (hell : 0 < ell) (r k : Point d) :
    (cell ell r k).card = (ell - 1) ^ d := by
  classical
  unfold cell
  rw [Fintype.card_piFinset]
  have hcoord : ∀ j : Fin d,
      (Finset.Icc (r j + k j * (ell : ℤ) + 1)
        (r j + k j * (ell : ℤ) + (ell : ℤ) - 1)).card = ell - 1 := by
    intro j
    rw [Int.card_Icc]
    have heq : r j + k j * (ell : ℤ) + (ell : ℤ) - 1 + 1 -
        (r j + k j * (ell : ℤ) + 1) = (ell : ℤ) - 1 := by ring
    rw [heq]
    omega
  simp_rw [hcoord]
  simp

/-- Successive integers outside the removed residue hyperplanes have the same quotient. -/
theorem ediv_eq_of_successive {a b ell : ℤ} (hell : 0 < ell)
    (hab : b = a + 1) (hb : b % ell ≠ 0) : b / ell = a / ell := by
  have haBounds := (Int.ediv_eq_iff_of_pos hell).mp (rfl : a / ell = a / ell)
  apply (Int.ediv_eq_iff_of_pos hell).mpr
  refine ⟨by omega, ?_⟩
  have hne : b ≠ (a / ell) * ell + ell := by
    intro h
    apply hb
    rw [h, Int.add_emod]
    simp
  omega

/-- Adjacent nonseparator vertices lie in the same open cell. -/
theorem adjacent_cellIndex_eq {d : ℕ} {A : Finset (Point d)} {ell : ℕ}
    (hell : 0 < ell) {r x y : Point d}
    (hr : ∀ j, 0 ≤ r j ∧ r j < ell)
    (hx : x ∈ A \ separator A ell r) (hy : y ∈ A \ separator A ell r)
    (hxy : Adj x y) : cellIndex ell r x = cellIndex ell r y := by
  have hpos : (0 : ℤ) < ell := by exact_mod_cast hell
  have hnmod (z : Point d) (hz : z ∈ A \ separator A ell r) (j : Fin d) :
      (z j - r j) % (ell : ℤ) ≠ 0 := by
    intro hzero
    have hmod : z j % (ell : ℤ) = r j := by
      have h := Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr hzero
      rwa [Int.emod_eq_of_lt (hr j).1 (hr j).2] at h
    exact (Finset.mem_sdiff.mp hz).2 (mem_separator.mpr
      ⟨(Finset.mem_sdiff.mp hz).1, j, hmod⟩)
  obtain ⟨j, hj, hother⟩ := hxy
  funext k
  unfold cellIndex
  by_cases hkj : k = j
  · subst k
    rcases hj with h | h
    · exact (ediv_eq_of_successive hpos (by omega) (hnmod y hy j)).symm
    · exact ediv_eq_of_successive hpos (by omega) (hnmod x hx j)
  · rw [hother k hkj]

/-- A nonseparator vertex lies in the finite cell indexed by its quotient. -/
theorem mem_cell_of_mem_complement {d : ℕ} {A : Finset (Point d)} {ell : ℕ}
    (hell : 0 < ell) {r x : Point d}
    (hr : ∀ j, 0 ≤ r j ∧ r j < ell)
    (hx : x ∈ A \ separator A ell r) : x ∈ cell ell r (cellIndex ell r x) := by
  classical
  apply Fintype.mem_piFinset.mpr
  intro j
  have hpos : (0 : ℤ) < ell := by exact_mod_cast hell
  have hmod : (x j - r j) % (ell : ℤ) ≠ 0 := by
    intro hzero
    have heq : x j % (ell : ℤ) = r j := by
      have h := Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr hzero
      rwa [Int.emod_eq_of_lt (hr j).1 (hr j).2] at h
    exact (Finset.mem_sdiff.mp hx).2 (mem_separator.mpr
      ⟨(Finset.mem_sdiff.mp hx).1, j, heq⟩)
  have hnonneg := Int.emod_nonneg (x j - r j) (ne_of_gt hpos)
  have hlt := Int.emod_lt_of_pos (x j - r j) hpos
  have hdecomp := Int.ediv_mul_add_emod (x j - r j) (ell : ℤ)
  apply Finset.mem_Icc.mpr
  dsimp [cellIndex]
  omega

/-- Adjacency restricted to the complement of the selected hyperplanes. -/
def AvoidAdj {d : ℕ} (A : Finset (Point d)) (ell : ℕ) (r : Point d)
    (x y : Point d) : Prop :=
  x ∈ A \ separator A ell r ∧ y ∈ A \ separator A ell r ∧ Adj x y

/-- The finite connected component of a vertex after deleting the separator. -/
def component {d : ℕ} (A : Finset (Point d)) (ell : ℕ) (r x : Point d) :
    Finset (Point d) := by
  classical
  exact (A \ separator A ell r).filter (fun y => Relation.ReflTransGen (AvoidAdj A ell r) x y)

/-- Every path avoiding the separator stays inside a single cell. -/
theorem path_cellIndex_eq {d : ℕ} {A : Finset (Point d)} {ell : ℕ}
    (hell : 0 < ell) {r x y : Point d}
    (hr : ∀ j, 0 ≤ r j ∧ r j < ell)
    (hpath : Relation.ReflTransGen (AvoidAdj A ell r) x y) :
    cellIndex ell r x = cellIndex ell r y := by
  induction hpath with
  | refl => rfl
  | @tail b c _ hbc ih =>
    exact ih.trans (adjacent_cellIndex_eq hell hr hbc.1 hbc.2.1 hbc.2.2)

/-- Components are contained in explicit cells, regardless of the shape of `A`. -/
theorem component_subset_cell {d : ℕ} {A : Finset (Point d)} {ell : ℕ}
    (hell : 0 < ell) (r x : Point d)
    (hr : ∀ j, 0 ≤ r j ∧ r j < ell) :
    component A ell r x ⊆ cell ell r (cellIndex ell r x) := by
  classical
  intro y hy
  obtain ⟨hyA, hpath⟩ := Finset.mem_filter.mp hy
  have hcell := mem_cell_of_mem_complement hell hr hyA
  rwa [← path_cellIndex_eq hell hr hpath] at hcell

/-- The component size bound used in the recursive separator construction. -/
theorem component_card_le {d : ℕ} {A : Finset (Point d)} {ell : ℕ}
    (hell : 0 < ell) (r x : Point d)
    (hr : ∀ j, 0 ≤ r j ∧ r j < ell) :
    (component A ell r x).card ≤ (ell - 1) ^ d := by
  calc
    (component A ell r x).card ≤ (cell ell r (cellIndex ell r x)).card :=
      Finset.card_le_card (component_subset_cell hell r x hr)
    _ = (ell - 1) ^ d := card_cell ell hell r _

/-- An actual balanced separator at every admissible integer scale. -/
theorem exists_balanced_separator_at_scale {d : ℕ} (A : Finset (Point d))
    (ell : ℕ) (hell : 0 < ell) (hscale : 2 * (ell - 1) ^ d ≤ A.card) :
    ∃ r : Point d, (∀ j, 0 ≤ r j ∧ r j < ell) ∧
      (separator A ell r).card * ell ≤ d * A.card ∧
      ∀ x : Point d, 2 * (component A ell r x).card ≤ A.card := by
  obtain ⟨r, hr, hsize⟩ := exists_small_separator A ell hell
  exact ⟨r, hr, hsize, fun x => (Nat.mul_le_mul_left 2
    (component_card_le hell r x hr)).trans hscale⟩

/-- The scale chosen in Appendix A.2. -/
def separatorScale (d q : ℕ) : ℕ :=
  ⌊((q : ℝ) / 2) ^ ((d : ℝ)⁻¹)⌋₊

/-- The floor scale is positive, makes every open cell balanced, and loses
at most a factor of two compared with the real root. -/
theorem separatorScale_bounds (d q : ℕ) (hd : 0 < d) (hq : 2 ^ (d + 1) ≤ q) :
    0 < separatorScale d q ∧
    2 * (separatorScale d q - 1) ^ d ≤ q ∧
    ((q : ℝ) / 2) ^ ((d : ℝ)⁻¹) ≤ 2 * (separatorScale d q : ℝ) := by
  let t : ℝ := ((q : ℝ) / 2) ^ ((d : ℝ)⁻¹)
  have ht0 : 0 ≤ t := Real.rpow_nonneg (by positivity) _
  have htpow : t ^ d = (q : ℝ) / 2 := by
    exact Real.rpow_inv_natCast_pow (by positivity) (ne_of_gt hd)
  have hlarge : (2 : ℝ) ^ d ≤ (q : ℝ) / 2 := by
    have hq' : (2 : ℝ) ^ (d + 1) ≤ (q : ℝ) := by exact_mod_cast hq
    rw [pow_succ] at hq'
    linarith
  have ht2 : (2 : ℝ) ≤ t := by
    by_contra h
    have hpow : t ^ d < (2 : ℝ) ^ d :=
      pow_lt_pow_left₀ (lt_of_not_ge h) ht0 (ne_of_gt hd)
    linarith
  have hell1 : 1 ≤ separatorScale d q := by
    apply Nat.le_floor
    norm_num only [Nat.cast_one]
    exact (by norm_num : (1 : ℝ) ≤ 2).trans ht2
  have hell0 : 0 < separatorScale d q := by omega
  have hfloor : (separatorScale d q : ℝ) ≤ t := Nat.floor_le ht0
  have hlt : t < (separatorScale d q : ℝ) + 1 := Nat.lt_floor_add_one t
  refine ⟨hell0, ?_, ?_⟩
  · have hpow : (separatorScale d q : ℝ) ^ d ≤ t ^ d :=
      pow_le_pow_left₀ (by positivity) hfloor d
    have hsub : ((separatorScale d q - 1 : ℕ) : ℝ) ≤ (separatorScale d q : ℝ) := by
      exact_mod_cast Nat.sub_le (separatorScale d q) 1
    have hpow' : ((separatorScale d q - 1 : ℕ) : ℝ) ^ d ≤
        (separatorScale d q : ℝ) ^ d := pow_le_pow_left₀ (by positivity) hsub d
    have h : (2 : ℝ) * ((separatorScale d q - 1 : ℕ) : ℝ) ^ d ≤ (q : ℝ) := by
      rw [htpow] at hpow
      linarith
    exact_mod_cast h
  · have hell1' : (1 : ℝ) ≤ separatorScale d q := by exact_mod_cast hell1
    linarith

/-- An explicit surface-order balanced separator for every sufficiently large
finite subset of the lattice. This is the geometric separator used in Appendix A.2.
The constant depends only on dimension. -/
theorem exists_surface_order_balanced_separator {d : ℕ} (A : Finset (Point d))
    (hd : 0 < d) (hlarge : 2 ^ (d + 1) ≤ A.card) :
    ∃ r : Point d,
      (∀ j, 0 ≤ r j ∧ r j < separatorScale d A.card) ∧
      ((separator A (separatorScale d A.card) r).card : ℝ) ≤
        (2 * (d : ℝ) * (2 : ℝ) ^ ((d : ℝ)⁻¹)) *
          (A.card : ℝ) ^ Paper09.exponentA d ∧
      ∀ x : Point d,
        2 * (component A (separatorScale d A.card) r x).card ≤ A.card := by
  obtain ⟨hell, hbalance, hroot⟩ := separatorScale_bounds d A.card hd hlarge
  obtain ⟨r, hr, hsize, hcomp⟩ :=
    exists_balanced_separator_at_scale A (separatorScale d A.card) hell hbalance
  refine ⟨r, hr, ?_, hcomp⟩
  have hq0 : (0 : ℝ) < A.card := by
    have : 0 < A.card := lt_of_lt_of_le (by positivity : 0 < 2 ^ (d + 1)) hlarge
    exact_mod_cast this
  have ht : 0 < ((A.card : ℝ) / 2) ^ ((d : ℝ)⁻¹) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hsize' : ((separator A (separatorScale d A.card) r).card : ℝ) *
      (separatorScale d A.card : ℝ) ≤ (d : ℝ) * (A.card : ℝ) := by
    exact_mod_cast hsize
  have hroot' := mul_le_mul_of_nonneg_left hroot
    (show (0 : ℝ) ≤ (separator A (separatorScale d A.card) r).card by positivity)
  have hquot : ((separator A (separatorScale d A.card) r).card : ℝ) ≤
      2 * (d : ℝ) * (A.card : ℝ) /
        (((A.card : ℝ) / 2) ^ ((d : ℝ)⁻¹)) := by
    apply (le_div_iff₀ ht).mpr
    nlinarith
  have hexponent : Paper09.exponentA d = 1 - (d : ℝ)⁻¹ := by
    simpa [one_div] using Paper09.exponentA_eq hd
  have hratio :
      2 * (d : ℝ) * (A.card : ℝ) / (((A.card : ℝ) / 2) ^ ((d : ℝ)⁻¹)) =
        (2 * (d : ℝ) * (2 : ℝ) ^ ((d : ℝ)⁻¹)) *
          (A.card : ℝ) ^ Paper09.exponentA d := by
    rw [Real.div_rpow (le_of_lt hq0) (by norm_num), hexponent,
      Real.rpow_sub hq0, Real.rpow_one]
    have hqroot : (A.card : ℝ) ^ ((d : ℝ)⁻¹) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hq0 _)
    have h2root : (2 : ℝ) ^ ((d : ℝ)⁻¹) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
    field_simp
  exact hquot.trans_eq hratio

/-- The actual directed interaction edges crossing a rank cut. -/
def cutBefore {d : ℕ} (A : Finset (Point d)) (f : Point d → ℕ) (x : Point d) :
    Finset (Point d × Point d) :=
  (A ×ˢ A).filter (fun e => Adj e.1 e.2 ∧ ¬ (f e.1 < f x ↔ f e.2 < f x))

/-- All directed edges with at least one endpoint in `S`. -/
def incidentPairs {d : ℕ} (S : Finset (Point d)) : Finset (Point d × Point d) :=
  S.biUnion (fun x => (neighbors x).biUnion (fun y => {(x,y), (y,x)}))

theorem mem_incidentPairs {d : ℕ} {S : Finset (Point d)} {x y : Point d}
    (hxy : Adj x y) (hS : x ∈ S ∨ y ∈ S) : (x,y) ∈ incidentPairs S := by
  classical
  rcases hS with hx | hy
  · exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_biUnion.mpr
      ⟨y, mem_neighbors.mpr hxy, by simp⟩⟩
  · exact Finset.mem_biUnion.mpr ⟨y, hy, Finset.mem_biUnion.mpr
      ⟨x, mem_neighbors.mpr (adj_symm hxy), by simp⟩⟩

theorem card_incidentPairs_le {d : ℕ} (S : Finset (Point d)) :
    (incidentPairs S).card ≤ 4 * d * S.card := by
  classical
  calc
    (incidentPairs S).card ≤ ∑ x ∈ S,
        ((neighbors x).biUnion (fun y => ({(x,y), (y,x)} : Finset _))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ x ∈ S, ∑ y ∈ neighbors x, ({(x,y), (y,x)} : Finset _).card :=
      Finset.sum_le_sum (fun _ _ => Finset.card_biUnion_le)
    _ ≤ ∑ x ∈ S, ∑ _y ∈ neighbors x, 2 :=
      Finset.sum_le_sum (fun _ _ => Finset.sum_le_sum (fun _ _ => Finset.card_le_two))
    _ = ∑ x ∈ S, (neighbors x).card * 2 := by simp
    _ ≤ ∑ _x ∈ S, (2 * d) * 2 :=
      Finset.sum_le_sum (fun x _ => Nat.mul_le_mul_right 2 (card_neighbors_le x))
    _ = 4 * d * S.card := by simp; ring

/-- A coarse bound on every cut, used for bounded-size domains. -/
theorem card_cutBefore_le {d : ℕ} (A : Finset (Point d)) (f : Point d → ℕ)
    (x : Point d) : (cutBefore A f x).card ≤ 2 * d * A.card := by
  classical
  have hsub : cutBefore A f x ⊆ A.biUnion (fun y =>
      (neighbors y).image (fun z => (y,z))) := by
    intro e he
    obtain ⟨hprod, hA, _⟩ := Finset.mem_filter.mp he
    obtain ⟨hy, hz⟩ := Finset.mem_product.mp hprod
    exact Finset.mem_biUnion.mpr ⟨e.1, hy, Finset.mem_image.mpr
      ⟨e.2, mem_neighbors.mpr hA, rfl⟩⟩
  calc
    (cutBefore A f x).card ≤ (A.biUnion (fun y =>
      (neighbors y).image (fun z => (y,z)))).card := Finset.card_le_card hsub
    _ ≤ ∑ y ∈ A, ((neighbors y).image (fun z => (y,z))).card := Finset.card_biUnion_le
    _ ≤ ∑ y ∈ A, (neighbors y).card := Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
    _ ≤ ∑ _y ∈ A, 2 * d := Finset.sum_le_sum (fun y _ => card_neighbors_le y)
    _ = 2 * d * A.card := by simp [Nat.mul_comm]

/-- Number of ranks strictly before a vertex; this compresses an arbitrary
injective finite rank assignment into the interval `[0, |A|)`. -/
def compressRank {d : ℕ} (A : Finset (Point d)) (f : Point d → ℕ) (x : Point d) : ℕ :=
  (A.filter (fun y => f y < f x)).card

theorem compressRank_lt_card {d : ℕ} {A : Finset (Point d)} (f : Point d → ℕ)
    {x : Point d} (hx : x ∈ A) : compressRank A f x < A.card := by
  classical
  apply Finset.card_lt_card
  apply (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).mpr
  exact ⟨x, hx, by simp⟩

theorem compressRank_lt_iff {d : ℕ} {A : Finset (Point d)} {f : Point d → ℕ}
    {x y : Point d} (hx : x ∈ A) (hy : y ∈ A) :
    compressRank A f x < compressRank A f y ↔ f x < f y := by
  classical
  have hmono {x y : Point d} (hx : x ∈ A) (hxy : f x < f y) :
      compressRank A f x < compressRank A f y := by
    apply Finset.card_lt_card
    have hsub : A.filter (fun z => f z < f x) ⊆ A.filter (fun z => f z < f y) := by
      intro z hz
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,
        lt_trans (Finset.mem_filter.mp hz).2 hxy⟩
    apply (Finset.ssubset_iff_of_subset hsub).mpr
    exact ⟨x, Finset.mem_filter.mpr ⟨hx, hxy⟩, by simp⟩
  constructor
  · intro h
    by_contra hxy
    rcases eq_or_lt_of_le (le_of_not_gt hxy) with heq | hlt
    · have hc : compressRank A f x = compressRank A f y := by
        unfold compressRank
        simp [heq]
      omega
    · have := hmono hy hlt
      omega
  · exact hmono hx

/-- Compressing ranks changes none of the cuts at vertices of `A`. -/
theorem cutBefore_compressRank {d : ℕ} {A : Finset (Point d)} (f : Point d → ℕ)
    {x : Point d} (hx : x ∈ A) :
    cutBefore A (compressRank A f) x = cutBefore A f x := by
  classical
  ext e
  simp only [cutBefore, Finset.mem_filter, Finset.mem_product]
  constructor <;> rintro ⟨⟨he1, he2⟩, hadj, hcut⟩
  · refine ⟨⟨he1, he2⟩, hadj, ?_⟩
    simpa only [compressRank_lt_iff he1 hx, compressRank_lt_iff he2 hx] using hcut
  · refine ⟨⟨he1, he2⟩, hadj, ?_⟩
    simpa only [compressRank_lt_iff he1 hx, compressRank_lt_iff he2 hx] using hcut

/-- An arbitrary injective assignment of bounded ranks to a finite domain. -/
def baseRank {d : ℕ} (A : Finset (Point d)) (x : Point d) : ℕ :=
  if hx : x ∈ A then (A.equivFin ⟨x,hx⟩).val else 0

theorem baseRank_lt {d : ℕ} {A : Finset (Point d)} {x : Point d} (hx : x ∈ A) :
    baseRank A x < A.card := by
  classical
  simp only [baseRank, dif_pos hx]
  exact (A.equivFin ⟨x,hx⟩).isLt

theorem baseRank_inj {d : ℕ} {A : Finset (Point d)} {x y : Point d}
    (hx : x ∈ A) (hy : y ∈ A) (h : baseRank A x = baseRank A y) : x = y := by
  classical
  simp only [baseRank, dif_pos hx, dif_pos hy] at h
  exact congrArg Subtype.val (A.equivFin.injective (Fin.ext h))

/-- The part of the separator complement contained in a chosen open cell. -/
def cellPart {d : ℕ} (A : Finset (Point d)) (ell : ℕ) (r k : Point d) :
    Finset (Point d) :=
  (A \ separator A ell r).filter (fun x => cellIndex ell r x = k)

@[simp]
theorem mem_cellPart {d : ℕ} {A : Finset (Point d)} {ell : ℕ} {r k x : Point d} :
    x ∈ cellPart A ell r k ↔ x ∈ A \ separator A ell r ∧ cellIndex ell r x = k := by
  simp [cellPart]

theorem card_cellPart_le {d : ℕ} {A : Finset (Point d)} {ell : ℕ}
    (hell : 0 < ell) (r k : Point d) (hr : ∀ j, 0 ≤ r j ∧ r j < ell) :
    (cellPart A ell r k).card ≤ (ell - 1) ^ d := by
  calc
    (cellPart A ell r k).card ≤ (cell ell r k).card := Finset.card_le_card (by
      intro x hx
      obtain ⟨hxA, hxk⟩ := mem_cellPart.mp hx
      simpa [hxk] using mem_cell_of_mem_complement hell hr hxA)
    _ = (ell - 1) ^ d := card_cell ell hell r k

/-- Comparison of local ranks in different consecutive rank blocks. -/
theorem blockRank_lt_iff (q a b i j : ℕ) (hi : i < q + 1) (hj : j < q + 1) :
    a * (q + 1) + i < b * (q + 1) + j ↔ a < b ∨ (a = b ∧ i < j) := by
  have hlt (a b i j : ℕ) (hab : a < b) (hi : i < q + 1) :
      a * (q + 1) + i < b * (q + 1) + j := by
    have hh := Nat.mul_le_mul_right (q + 1) (show a + 1 ≤ b by omega)
    nlinarith
  rcases lt_trichotomy a b with hab | hab | hab
  · simp only [hab, true_or, iff_true]
    exact hlt a b i j hab hi
  · subst b
    simp
  · have hrev := hlt b a j i hab hj
    have hnot : ¬ a < b := by omega
    have hne : a ≠ b := by omega
    simp [hnot, hne, show ¬ a * (q + 1) + i < b * (q + 1) + j by omega]

/-- Equality of two bounded local ranks in consecutive rank blocks. -/
theorem blockRank_eq_iff (q a b i j : ℕ) (hi : i < q + 1) (hj : j < q + 1) :
    a * (q + 1) + i = b * (q + 1) + j ↔ a = b ∧ i = j := by
  constructor
  · intro h
    have hab : a = b := by
      rcases lt_trichotomy a b with hab | hab | hab
      · have := (blockRank_lt_iff q a b i j hi hj).mpr (Or.inl hab)
        omega
      · exact hab
      · have := (blockRank_lt_iff q b a j i hj hi).mpr (Or.inl hab)
        omega
    subst b
    exact ⟨rfl, by omega⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- A fixed injective natural code for open lattice cells. -/
def cellCode {d : ℕ} (k : Point d) : ℕ := Encodable.encode k

theorem cellCode_inj {d : ℕ} {k l : Point d} (h : cellCode k = cellCode l) : k = l :=
  Encodable.encode_injective h

/-- A code strictly greater than the code of every cell meeting `A`. -/
def topCode {d : ℕ} (A : Finset (Point d)) (ell : ℕ) (r : Point d) : ℕ :=
  A.sup (fun x => cellCode (cellIndex ell r x)) + 1

theorem cellCode_lt_topCode {d : ℕ} {A : Finset (Point d)} {ell : ℕ}
    {r x : Point d} (hx : x ∈ A) : cellCode (cellIndex ell r x) < topCode A ell r := by
  have h := Finset.le_sup (f := fun x => cellCode (cellIndex ell r x)) hx
  exact Nat.lt_succ_of_le h

/-- Concatenate the recursively ordered open cells and put the separator last.
Unused gaps in the natural ranks are removed afterwards by `compressRank`. -/
def mergedRank {d : ℕ} (A : Finset (Point d)) (ell : ℕ) (r : Point d)
    (f : Point d → Point d → ℕ) (x : Point d) : ℕ :=
  if x ∈ separator A ell r then
    topCode A ell r * (A.card + 1) + baseRank A x
  else cellCode (cellIndex ell r x) * (A.card + 1) + f (cellIndex ell r x) x

theorem complement_before_separator {d : ℕ} {A : Finset (Point d)} {ell : ℕ}
    {r x y : Point d} (f : Point d → Point d → ℕ)
    (hlocal : ∀ k z, z ∈ cellPart A ell r k → f k z < A.card + 1)
    (hx : x ∈ A \ separator A ell r) (hy : y ∈ separator A ell r) :
    mergedRank A ell r f x < mergedRank A ell r f y := by
  classical
  have hxA := (Finset.mem_sdiff.mp hx).1
  have hxS := (Finset.mem_sdiff.mp hx).2
  have hyA := separator_subset A ell r hy
  have hxlocal := hlocal (cellIndex ell r x) x (mem_cellPart.mpr ⟨hx, rfl⟩)
  have hylocal : baseRank A y < A.card + 1 := (baseRank_lt hyA).trans (Nat.lt_succ_self _)
  simp only [mergedRank, if_neg hxS, if_pos hy]
  exact (blockRank_lt_iff _ _ _ _ _ hxlocal hylocal).mpr
    (Or.inl (cellCode_lt_topCode hxA))

theorem mergedRank_inj {d : ℕ} {A : Finset (Point d)} {ell : ℕ}
    {r : Point d} (f : Point d → Point d → ℕ)
    (hlocal : ∀ k z, z ∈ cellPart A ell r k → f k z < A.card + 1)
    (hinj : ∀ k x y, x ∈ cellPart A ell r k → y ∈ cellPart A ell r k →
      f k x = f k y → x = y)
    {x y : Point d} (hx : x ∈ A) (hy : y ∈ A)
    (heq : mergedRank A ell r f x = mergedRank A ell r f y) : x = y := by
  classical
  by_cases hxS : x ∈ separator A ell r <;> by_cases hyS : y ∈ separator A ell r
  · simp only [mergedRank, if_pos hxS, if_pos hyS] at heq
    exact baseRank_inj hx hy (by omega)
  · have hlt := complement_before_separator f hlocal (Finset.mem_sdiff.mpr ⟨hy, hyS⟩) hxS
    omega
  · have hlt := complement_before_separator f hlocal (Finset.mem_sdiff.mpr ⟨hx, hxS⟩) hyS
    omega
  · have hxc : x ∈ cellPart A ell r (cellIndex ell r x) :=
      mem_cellPart.mpr ⟨Finset.mem_sdiff.mpr ⟨hx, hxS⟩, rfl⟩
    have hyc : y ∈ cellPart A ell r (cellIndex ell r y) :=
      mem_cellPart.mpr ⟨Finset.mem_sdiff.mpr ⟨hy, hyS⟩, rfl⟩
    simp only [mergedRank, if_neg hxS, if_neg hyS] at heq
    obtain ⟨hcode, hval⟩ := (blockRank_eq_iff _ _ _ _ _
      (hlocal _ _ hxc) (hlocal _ _ hyc)).mp heq
    have hk := cellCode_inj hcode
    have hyc' : y ∈ cellPart A ell r (cellIndex ell r x) := by simpa [hk] using hyc
    exact hinj _ x y hxc hyc' (by simpa [hk] using hval)

/-- A cut taken while ordering the separator crosses only edges incident to it. -/
theorem cutBefore_merged_separator_subset {d : ℕ} {A : Finset (Point d)} {ell : ℕ}
    {r x : Point d} (f : Point d → Point d → ℕ)
    (hlocal : ∀ k z, z ∈ cellPart A ell r k → f k z < A.card + 1)
    (hx : x ∈ separator A ell r) :
    cutBefore A (mergedRank A ell r f) x ⊆ incidentPairs (separator A ell r) := by
  classical
  intro e he
  obtain ⟨hprod, hadj, hcut⟩ := Finset.mem_filter.mp he
  obtain ⟨he1, he2⟩ := Finset.mem_product.mp hprod
  by_cases hS : e.1 ∈ separator A ell r ∨ e.2 ∈ separator A ell r
  · exact mem_incidentPairs hadj hS
  · push_neg at hS
    have h1 := complement_before_separator f hlocal (Finset.mem_sdiff.mpr ⟨he1,hS.1⟩) hx
    have h2 := complement_before_separator f hlocal (Finset.mem_sdiff.mpr ⟨he2,hS.2⟩) hx
    exact False.elim (hcut (by simp [h1,h2]))

/-- At a cut inside a cell, only the recursively ordered cell and edges incident
to the separator can cross. All other cells lie entirely on one side. -/
theorem cutBefore_merged_cell_subset {d : ℕ} {A : Finset (Point d)} {ell : ℕ}
    (hell : 0 < ell) {r x : Point d} (hr : ∀ j, 0 ≤ r j ∧ r j < ell)
    (f : Point d → Point d → ℕ)
    (hlocal : ∀ k z, z ∈ cellPart A ell r k → f k z < A.card + 1)
    (hx : x ∈ A \ separator A ell r) :
    cutBefore A (mergedRank A ell r f) x ⊆
      incidentPairs (separator A ell r) ∪
        cutBefore (cellPart A ell r (cellIndex ell r x)) (f (cellIndex ell r x)) x := by
  classical
  intro e he
  obtain ⟨hprod, hadj, hcut⟩ := Finset.mem_filter.mp he
  obtain ⟨he1, he2⟩ := Finset.mem_product.mp hprod
  by_cases hS : e.1 ∈ separator A ell r ∨ e.2 ∈ separator A ell r
  · exact Finset.mem_union_left _ (mem_incidentPairs hadj hS)
  · push_neg at hS
    have h1 : e.1 ∈ A \ separator A ell r := Finset.mem_sdiff.mpr ⟨he1,hS.1⟩
    have h2 : e.2 ∈ A \ separator A ell r := Finset.mem_sdiff.mpr ⟨he2,hS.2⟩
    have hk12 := adjacent_cellIndex_eq hell hr h1 h2 hadj
    have hc1 := hlocal (cellIndex ell r e.1) e.1 (mem_cellPart.mpr ⟨h1,rfl⟩)
    have hc2 := hlocal (cellIndex ell r e.2) e.2 (mem_cellPart.mpr ⟨h2,rfl⟩)
    have hcx := hlocal (cellIndex ell r x) x (mem_cellPart.mpr ⟨hx,rfl⟩)
    have hxe := (Finset.mem_sdiff.mp hx).2
    simp only [mergedRank, if_neg hS.1, if_neg hS.2, if_neg hxe,
      blockRank_lt_iff _ _ _ _ _ hc1 hcx,
      blockRank_lt_iff _ _ _ _ _ hc2 hcx] at hcut
    have hk1x : cellIndex ell r e.1 = cellIndex ell r x := by
      by_contra hne
      have hcode : cellCode (cellIndex ell r e.1) ≠ cellCode (cellIndex ell r x) :=
        fun h => hne (cellCode_inj h)
      apply hcut
      simp [hk12, show cellCode (cellIndex ell r e.2) ≠
        cellCode (cellIndex ell r x) by simpa [hk12] using hcode]
    have hk2x := hk12.symm.trans hk1x
    apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨mem_cellPart.mpr ⟨h1,hk1x⟩,
      mem_cellPart.mpr ⟨h2,hk2x⟩⟩, hadj, ?_⟩
    simpa [hk1x, hk2x] using hcut

/-- The explicit constant in the coordinate-hyperplane separator bound. -/
def separatorConstant (d : ℕ) : ℝ := 2 * (d : ℝ) * (2 : ℝ) ^ ((d : ℝ)⁻¹)

/-- The surface-power contraction when the volume is halved. -/
def shrinkFactor (d : ℕ) : ℝ := (1 / 2 : ℝ) ^ Paper09.exponentA d

/-- A dimension-only constant large enough for the separator recursion and
for all domains below the floor-root threshold. -/
def cutwidthConstant (d : ℕ) : ℝ :=
  4 * (d : ℝ) * separatorConstant d / (1 - shrinkFactor d) +
    2 * (d : ℝ) * (2 : ℝ) ^ (d + 1)

theorem shrinkFactor_bounds {d : ℕ} (hd : 2 ≤ d) :
    0 < shrinkFactor d ∧ shrinkFactor d < 1 := by
  exact ⟨Real.rpow_pos_of_pos (by norm_num) _,
    Real.rpow_lt_one (by norm_num) (by norm_num) (Paper09.exponentA_pos hd)⟩

theorem cutwidthConstant_bounds {d : ℕ} (hd : 2 ≤ d) :
    0 ≤ cutwidthConstant d ∧
    2 * (d : ℝ) * (2 : ℝ) ^ (d + 1) ≤ cutwidthConstant d ∧
    4 * (d : ℝ) * separatorConstant d + cutwidthConstant d * shrinkFactor d ≤
      cutwidthConstant d := by
  have hs := shrinkFactor_bounds hd
  have hden : 0 < 1 - shrinkFactor d := by linarith
  have hsep : 0 ≤ separatorConstant d := by unfold separatorConstant; positivity
  have hnum : 0 ≤ 4 * (d : ℝ) * separatorConstant d := by positivity
  have hdiv : 0 ≤ 4 * (d : ℝ) * separatorConstant d / (1 - shrinkFactor d) :=
    div_nonneg hnum hden.le
  have hbase : 0 ≤ 2 * (d : ℝ) * (2 : ℝ) ^ (d + 1) := by positivity
  refine ⟨add_nonneg hdiv hbase, by unfold cutwidthConstant; linarith, ?_⟩
  have hcancel := div_mul_cancel₀ (4 * (d : ℝ) * separatorConstant d) (ne_of_gt hden)
  have hbase' := mul_nonneg hbase hden.le
  unfold cutwidthConstant
  nlinarith

/-- Surface powers contract by `shrinkFactor d` for balanced subdomains. -/
theorem balanced_power_le {d m q : ℕ} (hd : 2 ≤ d) (h : 2 * m ≤ q) :
    (m : ℝ) ^ Paper09.exponentA d ≤
      shrinkFactor d * (q : ℝ) ^ Paper09.exponentA d := by
  have hhalf : (m : ℝ) ≤ (q : ℝ) / 2 := by
    have h' : (2 : ℝ) * (m : ℝ) ≤ (q : ℝ) := by exact_mod_cast h
    linarith
  have hp := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ m) hhalf
    (le_of_lt (Paper09.exponentA_pos hd))
  have heq : ((q : ℝ) / 2) ^ Paper09.exponentA d =
      shrinkFactor d * (q : ℝ) ^ Paper09.exponentA d := by
    rw [div_eq_mul_inv, Real.mul_rpow (by positivity) (by positivity)]
    unfold shrinkFactor
    ring_nf
  exact hp.trans_eq heq

/-- Strict rank comparison survives compression, so injectivity does too. -/
theorem compressRank_inj {d : ℕ} {A : Finset (Point d)} {f : Point d → ℕ}
    (hf : ∀ x ∈ A, ∀ y ∈ A, f x = f y → x = y)
    {x y : Point d} (hx : x ∈ A) (hy : y ∈ A)
    (h : compressRank A f x = compressRank A f y) : x = y := by
  apply hf x hx y hy
  rcases lt_trichotomy (f x) (f y) with hlt | heq | hlt
  · have := (compressRank_lt_iff hx hy).mpr hlt
    omega
  · exact heq
  · have := (compressRank_lt_iff hy hx).mpr hlt
    omega

/-- Every finite lattice domain has a true vertex ordering of surface-order
cutwidth. Both orientations of crossing edges are counted. -/
theorem exists_bounded_rank {d : ℕ} (hd : 2 ≤ d) (A : Finset (Point d)) :
    ∃ f : Point d → ℕ,
      (∀ x ∈ A, f x < A.card) ∧
      (∀ x ∈ A, ∀ y ∈ A, f x = f y → x = y) ∧
      ∀ x ∈ A, ((cutBefore A f x).card : ℝ) ≤
        cutwidthConstant d * (A.card : ℝ) ^ Paper09.exponentA d := by
  classical
  have hC := cutwidthConstant_bounds hd
  have ha := Paper09.exponentA_pos hd
  suffices hmain : ∀ n : ℕ, ∀ A : Finset (Point d), A.card = n →
      ∃ f : Point d → ℕ,
        (∀ x ∈ A, f x < A.card) ∧
        (∀ x ∈ A, ∀ y ∈ A, f x = f y → x = y) ∧
        ∀ x ∈ A, ((cutBefore A f x).card : ℝ) ≤
          cutwidthConstant d * (A.card : ℝ) ^ Paper09.exponentA d from hmain _ A rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A hcard
    by_cases hsmall : A.card < 2 ^ (d + 1)
    · refine ⟨baseRank A, fun x hx => baseRank_lt hx,
        fun x hx y hy heq => baseRank_inj hx hy heq, ?_⟩
      intro x hx
      have hq1 : (1 : ℝ) ≤ A.card := by exact_mod_cast (Finset.card_pos.mpr ⟨x,hx⟩)
      have hp1 : (1 : ℝ) ≤ (A.card : ℝ) ^ Paper09.exponentA d := Real.one_le_rpow hq1 ha.le
      have hqsmall : (A.card : ℝ) ≤ (2 : ℝ) ^ (d + 1) := by exact_mod_cast hsmall.le
      have hcut : ((cutBefore A (baseRank A) x).card : ℝ) ≤ 2 * (d : ℝ) * A.card := by
        exact_mod_cast card_cutBefore_le A (baseRank A) x
      have hbase : 2 * (d : ℝ) * (A.card : ℝ) ≤ cutwidthConstant d := by
        exact (mul_le_mul_of_nonneg_left hqsmall (by positivity)).trans hC.2.1
      exact hcut.trans (hbase.trans (le_mul_of_one_le_right hC.1 hp1))
    · have hlarge := le_of_not_gt hsmall
      have hd0 : 0 < d := by omega
      let ell := separatorScale d A.card
      obtain ⟨hell, hscale, _⟩ := separatorScale_bounds d A.card hd0 hlarge
      obtain ⟨r, hr, hsep, _hcomp⟩ := exists_surface_order_balanced_separator A hd0 hlarge
      have hpart (k : Point d) : 2 * (cellPart A ell r k).card ≤ A.card :=
        (Nat.mul_le_mul_left 2 (card_cellPart_le hell r k hr)).trans hscale
      have hq0 : 0 < A.card := lt_of_lt_of_le (by positivity : 0 < 2 ^ (d + 1)) hlarge
      have hlocal : ∀ k : Point d, ∃ f : Point d → ℕ,
          (∀ x ∈ cellPart A ell r k, f x < (cellPart A ell r k).card) ∧
          (∀ x ∈ cellPart A ell r k, ∀ y ∈ cellPart A ell r k, f x = f y → x = y) ∧
          ∀ x ∈ cellPart A ell r k, ((cutBefore (cellPart A ell r k) f x).card : ℝ) ≤
            cutwidthConstant d * ((cellPart A ell r k).card : ℝ) ^ Paper09.exponentA d := by
        intro k
        have hlt : (cellPart A ell r k).card < n := by have := hpart k; omega
        exact ih _ hlt _ rfl
      choose f hfbound hfinj hfcut using hlocal
      have hlocal' : ∀ k z, z ∈ cellPart A ell r k → f k z < A.card + 1 := by
        intro k z hz
        have hb := hfbound k z hz
        have hp := hpart k
        omega
      let g := mergedRank A ell r f
      have hginj : ∀ x ∈ A, ∀ y ∈ A, g x = g y → x = y := by
        intro x hx y hy hxy
        exact mergedRank_inj f hlocal' (fun k x y hx hy hxy => hfinj k x hx y hy hxy) hx hy hxy
      refine ⟨compressRank A g, fun x hx => compressRank_lt_card g hx,
        fun x hx y hy hxy => compressRank_inj hginj hx hy hxy, ?_⟩
      intro x hx
      rw [cutBefore_compressRank g hx]
      have hsep' : ((incidentPairs (separator A ell r)).card : ℝ) ≤
          4 * (d : ℝ) * separatorConstant d * (A.card : ℝ) ^ Paper09.exponentA d := by
        have hi : ((incidentPairs (separator A ell r)).card : ℝ) ≤
            4 * (d : ℝ) * ((separator A ell r).card : ℝ) := by
          exact_mod_cast card_incidentPairs_le (separator A ell r)
        exact hi.trans (by simpa [mul_assoc, separatorConstant] using
          mul_le_mul_of_nonneg_left hsep (by positivity : 0 ≤ 4 * (d : ℝ)))
      by_cases hxS : x ∈ separator A ell r
      · have hcut : ((cutBefore A g x).card : ℝ) ≤ ((incidentPairs (separator A ell r)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card (cutBefore_merged_separator_subset f hlocal' hxS)
        have hbudget : 4 * (d : ℝ) * separatorConstant d ≤ cutwidthConstant d := by
          have hs := shrinkFactor_bounds hd
          have hnonneg := mul_nonneg hC.1 hs.1.le
          linarith [hC.2.2]
        exact hcut.trans (hsep'.trans (mul_le_mul_of_nonneg_right hbudget (by positivity)))
      · have hxcomp : x ∈ A \ separator A ell r := Finset.mem_sdiff.mpr ⟨hx,hxS⟩
        let k := cellIndex ell r x
        have hxc : x ∈ cellPart A ell r k := mem_cellPart.mpr ⟨hxcomp,rfl⟩
        have hcut : ((cutBefore A g x).card : ℝ) ≤
            ((incidentPairs (separator A ell r)).card : ℝ) +
              ((cutBefore (cellPart A ell r k) (f k) x).card : ℝ) := by
          exact_mod_cast (Finset.card_le_card
            (cutBefore_merged_cell_subset hell hr f hlocal' hxcomp)).trans (Finset.card_union_le _ _)
        have hchild : ((cutBefore (cellPart A ell r k) (f k) x).card : ℝ) ≤
            cutwidthConstant d * (shrinkFactor d * (A.card : ℝ) ^ Paper09.exponentA d) :=
          (hfcut k x hxc).trans (mul_le_mul_of_nonneg_left (balanced_power_le hd (hpart k)) hC.1)
        calc
          ((cutBefore A g x).card : ℝ) ≤
              4 * (d : ℝ) * separatorConstant d * (A.card : ℝ) ^ Paper09.exponentA d +
                cutwidthConstant d * (shrinkFactor d * (A.card : ℝ) ^ Paper09.exponentA d) :=
            hcut.trans (add_le_add hsep' hchild)
          _ = (4 * (d : ℝ) * separatorConstant d + cutwidthConstant d * shrinkFactor d) *
              (A.card : ℝ) ^ Paper09.exponentA d := by ring
          _ ≤ cutwidthConstant d * (A.card : ℝ) ^ Paper09.exponentA d :=
            mul_le_mul_of_nonneg_right hC.2.2 (by positivity)

/-- The actual `Fin |A|` vertex ordering with the surface-order bound needed by
canonical paths. The lattice structure only specifies the induced actual
nearest-neighbor graph on `A`; no cutwidth property is assumed. -/
theorem exists_ordering_cutwidth {d : ℕ} (hd : 2 ≤ d) (A : Finset (Point d))
    (Λ : Paper09.Lattice ↥A)
    (hΛ : ∀ x y : ↥A, Λ.adj x y ↔ Adj x.val y.val) :
    ∃ order : Fin A.card ≃ ↥A, ∀ j ≤ A.card,
      ((Paper09.CanonicalPath.cutEdges Λ
        (Paper09.CanonicalPath.initialSegment order j)).card : ℝ) ≤
          cutwidthConstant d * (A.card : ℝ) ^ Paper09.exponentA d := by
  classical
  obtain ⟨f, hfbound, hfinj, hfcut⟩ := exists_bounded_rank hd A
  let rank : ↥A → Fin A.card := fun x => ⟨f x.val, hfbound x.val x.property⟩
  have hrank : Function.Injective rank := by
    intro x y heq
    apply Subtype.ext
    exact hfinj x.val x.property y.val y.property (congrArg Fin.val heq)
  have hsurj : Function.Surjective rank :=
    (Finite.injective_iff_surjective_of_equiv A.equivFin).mp hrank
  let e : ↥A ≃ Fin A.card := Equiv.ofBijective rank ⟨hrank,hsurj⟩
  refine ⟨e.symm, ?_⟩
  intro j hj
  have hnonneg : 0 ≤ cutwidthConstant d * (A.card : ℝ) ^ Paper09.exponentA d :=
    mul_nonneg (cutwidthConstant_bounds hd).1 (by positivity)
  by_cases hjq : j = A.card
  · subst j
    simpa [Paper09.CanonicalPath.initialSegment_end, Paper09.CanonicalPath.cutEdges] using hnonneg
  · have hjlt : j < A.card := by omega
    let x : ↥A := e.symm ⟨j,hjlt⟩
    have hfx : f x.val = j := by
      have hh := congrArg Fin.val (e.apply_symm_apply ⟨j,hjlt⟩)
      exact hh
    have hrankval (y : ↥A) : (e y).val = f y.val := rfl
    have hmem (y : ↥A) :
        y ∈ Paper09.CanonicalPath.initialSegment e.symm j ↔ f y.val < f x.val := by
      simp [Paper09.CanonicalPath.initialSegment, hrankval, hfx]
    let embed : (↥A × ↥A) → (Point d × Point d) := fun p => (p.1.val,p.2.val)
    have hembed : Function.Injective embed := by
      intro p q heq
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg Prod.fst heq
      · apply Subtype.ext
        exact congrArg Prod.snd heq
    have hsub : (Paper09.CanonicalPath.cutEdges Λ
        (Paper09.CanonicalPath.initialSegment e.symm j)).image embed ⊆ cutBefore A f x.val := by
      intro p hp
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
      have hq' : Λ.adj q.1 q.2 ∧ ¬ (q.1 ∈ Paper09.CanonicalPath.initialSegment e.symm j ↔
          q.2 ∈ Paper09.CanonicalPath.initialSegment e.symm j) := by
        simpa only [Paper09.CanonicalPath.cutEdges, Finset.mem_filter, Finset.mem_univ,
          true_and] using hq
      obtain ⟨hadj,hcut⟩ := hq'
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨q.1.property,q.2.property⟩, (hΛ _ _).mp hadj, ?_⟩
      simpa only [hmem] using hcut
    calc
      ((Paper09.CanonicalPath.cutEdges Λ
          (Paper09.CanonicalPath.initialSegment e.symm j)).card : ℝ) =
          (((Paper09.CanonicalPath.cutEdges Λ
            (Paper09.CanonicalPath.initialSegment e.symm j)).image embed).card : ℝ) := by
        rw [Finset.card_image_of_injective _ hembed]
      _ ≤ ((cutBefore A f x.val).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ ≤ cutwidthConstant d * (A.card : ℝ) ^ Paper09.exponentA d := hfcut x.val x.property

end Paper09.LatticeGeometry
