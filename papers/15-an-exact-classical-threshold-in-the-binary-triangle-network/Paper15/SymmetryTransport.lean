import Paper15.FiniteGap

/-! # Exact transport under every triangle symmetry

The source laws are transported together with the response table. The result
holds for every numerical bound on the constrained objective, so it applies
both to the finite gap and to the exceptional upper bound.
-/
noncomputable section
namespace Paper15
open Finset BigOperators

@[ext] theorem AggregateMoments.ext {m n : AggregateMoments}
    (h1 : m.M1 = n.M1) (h2 : m.M2 = n.M2) (h3 : m.M3 = n.M3) : m = n := by
  cases m; cases n; simp_all

def Simplex2.reindex (σ : Equiv.Perm (Fin 3)) (q : Simplex2) : Simplex2 where
  v i := q (σ.symm i)
  nonneg i := q.nonneg _
  sum_eq := (Equiv.sum_comp σ.symm q).trans q.sum_eq

lemma weightExp_reindex (w : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (σ τ υ : Equiv.Perm (Fin 3)) (qx qy qz : Fin 3 → ℝ) :
    weightExp (fun x y z => w (σ x) (τ y) (υ z)) qx qy qz =
      weightExp w (fun x => qx (σ.symm x)) (fun y => qy (τ.symm y))
        (fun z => qz (υ.symm z)) := by
  unfold weightExp
  apply Fintype.sum_equiv σ
  intro x
  apply Fintype.sum_equiv τ
  intro y
  apply Fintype.sum_equiv υ
  intro z
  simp

lemma weightExp_swapXY (w : Fin 3 → Fin 3 → Fin 3 → ℝ) (qx qy qz : Fin 3 → ℝ) :
    weightExp (fun x y z => w y x z) qx qy qz = weightExp w qy qx qz := by
  unfold weightExp
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  apply sum_congr rfl
  intro z _
  ring

lemma weightExp_swapYZ (w : Fin 3 → Fin 3 → Fin 3 → ℝ) (qx qy qz : Fin 3 → ℝ) :
    weightExp (fun x y z => w x z y) qx qy qz = weightExp w qx qz qy := by
  unfold weightExp
  apply sum_congr rfl
  intro x _
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  apply sum_congr rfl
  intro z _
  ring

lemma detMoments_valueReindex (σ τ υ : Equiv.Perm (Fin 3)) (T : DetTriangle)
    (qx qy qz : Fin 3 → ℝ) :
    detMoments (valueReindex σ τ υ T) qx qy qz =
      detMoments T (fun x => qx (σ.symm x)) (fun y => qy (τ.symm y))
        (fun z => qz (υ.symm z)) := by
  apply AggregateMoments.ext
  · rw [detMoments_M1_weightExp, detMoments_M1_weightExp]
    change weightExp (fun x y z => w1 T (σ x) (τ y) (υ z)) qx qy qz / 3 = _
    rw [weightExp_reindex]
  · rw [detMoments_M2_weightExp, detMoments_M2_weightExp]
    change weightExp (fun x y z => w3 T (σ x) (τ y) (υ z)) qx qy qz / 3 = _
    rw [weightExp_reindex]
  · rw [detMoments_M3_weightExp, detMoments_M3_weightExp]
    change weightExp (fun x y z => w2 T (σ x) (τ y) (υ z)) qx qy qz = _
    rw [weightExp_reindex]

lemma detMoments_swapXY (T : DetTriangle) (qx qy qz : Fin 3 → ℝ) :
    detMoments (swapXY T) qx qy qz = detMoments T qy qx qz := by
  have hw1 : w1 (swapXY T) = fun x y z => w1 T y x z := by
    funext x y z
    dsimp [w1, swapXY, RespTable.swap]
    ring
  have hw2 : w2 (swapXY T) = fun x y z => w2 T y x z := by
    funext x y z
    dsimp [w2, swapXY, RespTable.swap]
    ring
  have hw3 : w3 (swapXY T) = fun x y z => w3 T y x z := by
    funext x y z
    dsimp [w3, swapXY, RespTable.swap]
    ring
  apply AggregateMoments.ext
  · rw [detMoments_M1_weightExp, detMoments_M1_weightExp, hw1, weightExp_swapXY]
  · rw [detMoments_M2_weightExp, detMoments_M2_weightExp, hw3, weightExp_swapXY]
  · rw [detMoments_M3_weightExp, detMoments_M3_weightExp, hw2, weightExp_swapXY]

lemma detMoments_swapYZ (T : DetTriangle) (qx qy qz : Fin 3 → ℝ) :
    detMoments (swapYZ T) qx qy qz = detMoments T qx qz qy := by
  have hw1 : w1 (swapYZ T) = fun x y z => w1 T x z y := by
    funext x y z
    dsimp [w1, swapYZ, RespTable.swap]
    ring
  have hw2 : w2 (swapYZ T) = fun x y z => w2 T x z y := by
    funext x y z
    dsimp [w2, swapYZ, RespTable.swap]
    ring
  have hw3 : w3 (swapYZ T) = fun x y z => w3 T x z y := by
    funext x y z
    dsimp [w3, swapYZ, RespTable.swap]
    ring
  apply AggregateMoments.ext
  · rw [detMoments_M1_weightExp, detMoments_M1_weightExp, hw1, weightExp_swapYZ]
  · rw [detMoments_M2_weightExp, detMoments_M2_weightExp, hw3, weightExp_swapYZ]
  · rw [detMoments_M3_weightExp, detMoments_M3_weightExp, hw2, weightExp_swapYZ]

lemma detMoments_swapXZ (T : DetTriangle) (qx qy qz : Fin 3 → ℝ) :
    detMoments (swapXZ T) qx qy qz = detMoments T qz qy qx := by
  have h : swapXZ T = swapXY (swapYZ (swapXY T)) := rfl
  rw [h, detMoments_swapXY, detMoments_swapYZ, detMoments_swapXY]

lemma detMoments_cycleXYZ (T : DetTriangle) (qx qy qz : Fin 3 → ℝ) :
    detMoments (cycleXYZ T) qx qy qz = detMoments T qy qz qx := by
  have h : cycleXYZ T = swapXY (swapYZ T) := rfl
  rw [h, detMoments_swapXY, detMoments_swapYZ]

lemma detMoments_cycleXZY (T : DetTriangle) (qx qy qz : Fin 3 → ℝ) :
    detMoments (cycleXZY T) qx qy qz = detMoments T qz qx qy := by
  have h : cycleXZY T = swapYZ (swapXY T) := rfl
  rw [h, detMoments_swapYZ, detMoments_swapXY]

/-- The constrained objective bound, with an arbitrary numerical bound. -/
def ConstrainedBound (b : ℝ) (T : DetTriangle) : Prop :=
  ∀ qx qy qz : Simplex2, (detMoments' T qx qy qz).M1 = 0 →
    (detMoments' T qx qy qz).M3 = 0 → (detMoments' T qx qy qz).M2 ≤ b

lemma ConstrainedBound.valueReindex {b : ℝ} {T : DetTriangle}
    (h : ConstrainedBound b T) (σ τ υ : Equiv.Perm (Fin 3)) :
    ConstrainedBound b (Paper15.valueReindex σ τ υ T) := by
  intro qx qy qz h1 h3
  have he : detMoments' (Paper15.valueReindex σ τ υ T) qx qy qz =
      detMoments' T (qx.reindex σ) (qy.reindex τ) (qz.reindex υ) :=
    detMoments_valueReindex σ τ υ T qx qy qz
  rw [he] at h1 h3 ⊢
  exact h _ _ _ h1 h3

lemma ConstrainedBound.swapXY {b : ℝ} {T : DetTriangle} (h : ConstrainedBound b T) :
    ConstrainedBound b (Paper15.swapXY T) := by
  intro qx qy qz h1 h3
  have he : detMoments' (Paper15.swapXY T) qx qy qz = detMoments' T qy qx qz :=
    detMoments_swapXY T qx qy qz
  rw [he] at h1 h3 ⊢
  exact h _ _ _ h1 h3

lemma ConstrainedBound.swapYZ {b : ℝ} {T : DetTriangle} (h : ConstrainedBound b T) :
    ConstrainedBound b (Paper15.swapYZ T) := by
  intro qx qy qz h1 h3
  have he : detMoments' (Paper15.swapYZ T) qx qy qz = detMoments' T qx qz qy :=
    detMoments_swapYZ T qx qy qz
  rw [he] at h1 h3 ⊢
  exact h _ _ _ h1 h3

lemma ConstrainedBound.swapXZ {b : ℝ} {T : DetTriangle} (h : ConstrainedBound b T) :
    ConstrainedBound b (Paper15.swapXZ T) := by
  intro qx qy qz h1 h3
  have he : detMoments' (Paper15.swapXZ T) qx qy qz = detMoments' T qz qy qx :=
    detMoments_swapXZ T qx qy qz
  rw [he] at h1 h3 ⊢
  exact h _ _ _ h1 h3

lemma ConstrainedBound.cycleXYZ {b : ℝ} {T : DetTriangle} (h : ConstrainedBound b T) :
    ConstrainedBound b (Paper15.cycleXYZ T) := h.swapYZ.swapXY

lemma ConstrainedBound.cycleXZY {b : ℝ} {T : DetTriangle} (h : ConstrainedBound b T) :
    ConstrainedBound b (Paper15.cycleXZY T) := h.swapXY.swapYZ

lemma ConstrainedBound.flipAll {b : ℝ} {T : DetTriangle} (h : ConstrainedBound b T) :
    ConstrainedBound b (Paper15.flipAll T) := by
  intro qx qy qz h1 h3
  have he := detMoments_flipAll T qx qy qz
  change (detMoments (Paper15.flipAll T) qx qy qz).M1 = 0 at h1
  change (detMoments (Paper15.flipAll T) qx qy qz).M3 = 0 at h3
  change (detMoments (Paper15.flipAll T) qx qy qz).M2 ≤ b
  rw [he.1] at h1
  rw [he.2.2] at h3
  rw [he.2.1]
  exact h qx qy qz (neg_eq_zero.mp h1) (neg_eq_zero.mp h3)

lemma ConstrainedBound.applyPerm {b : ℝ} {T : DetTriangle} (h : ConstrainedBound b T)
    (σ : Equiv.Perm (Fin 3)) : ConstrainedBound b (Paper15.applyPerm σ T) := by
  unfold Paper15.applyPerm
  split_ifs
  · exact h
  · exact h.swapYZ
  · exact h.swapXY
  · exact h.cycleXYZ
  · exact h.cycleXZY
  · exact h.swapXZ

/-- Full symmetry transport, including arbitrary source-value and party
permutations and a global sign flip. -/
theorem ConstrainedBound.symmetry {b : ℝ} {T : DetTriangle} (h : ConstrainedBound b T)
    (g : Symmetry) : ConstrainedBound b (g.apply T) := by
  unfold Symmetry.apply
  have ht := (h.valueReindex g.σX g.σY g.σZ).applyPerm g.srcPerm
  split_ifs
  · exact ht.flipAll
  · exact ht

theorem gapHolds_symmetry {T : DetTriangle} (h : GapHolds T) (g : Symmetry) :
    GapHolds (g.apply T) := ConstrainedBound.symmetry h g

/-- A bound for table (6) holds on its entire exceptional orbit. -/
theorem constrainedBound_exceptionalOrbit {b : ℝ}
    (h : ConstrainedBound b DetTriangle.exceptional) {T : DetTriangle}
    (hT : inExceptionalOrbit T) : ConstrainedBound b T := by
  obtain ⟨g, rfl⟩ := hT
  exact h.symmetry g

end Paper15
