import Paper15.SymmetryTransport
import Paper15.Main

/-! # Excluding zero-probability source values on the exceptional table

Changing an unused response entry leaves all observed moments unchanged.
Its total sign sum becomes -7 or -11; every exceptional-orbit table has total
sign sum -9 or 9. The finite gap therefore excludes this boundary whenever
the constrained objective exceeds 9/25.
-/
noncomputable section
namespace Paper15
open Finset BigOperators

def signSum (T : DetTriangle) : ℝ :=
  (∑ i, ∑ j, T.A i j) + (∑ i, ∑ j, T.B i j) + (∑ i, ∑ j, T.C i j)

lemma sum2_reindex (f : Fin 3 → Fin 3 → ℝ) (σ τ : Equiv.Perm (Fin 3)) :
    (∑ i, ∑ j, f (σ i) (τ j)) = ∑ i, ∑ j, f i j := by
  calc
    _ = ∑ i, ∑ j, f (σ i) j := sum_congr rfl (fun i _ => Equiv.sum_comp τ (fun j => f (σ i) j))
    _ = _ := Equiv.sum_comp σ (fun i => ∑ j, f i j)

lemma signSum_valueReindex (T : DetTriangle) (σ τ υ : Equiv.Perm (Fin 3)) :
    signSum (valueReindex σ τ υ T) = signSum T := by
  simp only [signSum, valueReindex]
  rw [sum2_reindex, sum2_reindex, sum2_reindex]

lemma signSum_swapXY (T : DetTriangle) : signSum (swapXY T) = signSum T := by
  have hA : (∑ i, ∑ j, (swapXY T).A i j) = ∑ i, ∑ j, T.B i j := by
    change (∑ i, ∑ j, T.B j i) = _
    exact sum_comm
  have hB : (∑ i, ∑ j, (swapXY T).B i j) = ∑ i, ∑ j, T.A i j := by
    change (∑ i, ∑ j, T.A j i) = _
    exact sum_comm
  have hC : (∑ i, ∑ j, (swapXY T).C i j) = ∑ i, ∑ j, T.C i j := by
    change (∑ i, ∑ j, T.C j i) = _
    exact sum_comm
  unfold signSum
  rw [hA, hB, hC]
  ring

lemma signSum_swapYZ (T : DetTriangle) : signSum (swapYZ T) = signSum T := by
  have hA : (∑ i, ∑ j, (swapYZ T).A i j) = ∑ i, ∑ j, T.A i j := by
    change (∑ i, ∑ j, T.A j i) = _
    exact sum_comm
  have hB : (∑ i, ∑ j, (swapYZ T).B i j) = ∑ i, ∑ j, T.C i j := by
    change (∑ i, ∑ j, T.C j i) = _
    exact sum_comm
  have hC : (∑ i, ∑ j, (swapYZ T).C i j) = ∑ i, ∑ j, T.B i j := by
    change (∑ i, ∑ j, T.B j i) = _
    exact sum_comm
  unfold signSum
  rw [hA, hB, hC]
  ring

lemma signSum_swapXZ (T : DetTriangle) : signSum (swapXZ T) = signSum T := by
  have hA : (∑ i, ∑ j, (swapXZ T).A i j) = ∑ i, ∑ j, T.C i j := by
    change (∑ i, ∑ j, T.C j i) = _
    exact sum_comm
  have hB : (∑ i, ∑ j, (swapXZ T).B i j) = ∑ i, ∑ j, T.B i j := by
    change (∑ i, ∑ j, T.B j i) = _
    exact sum_comm
  have hC : (∑ i, ∑ j, (swapXZ T).C i j) = ∑ i, ∑ j, T.A i j := by
    change (∑ i, ∑ j, T.A j i) = _
    exact sum_comm
  unfold signSum
  rw [hA, hB, hC]
  ring

lemma signSum_cycleXYZ (T : DetTriangle) : signSum (cycleXYZ T) = signSum T := by
  change signSum (swapXY (swapYZ T)) = _
  rw [signSum_swapXY, signSum_swapYZ]

lemma signSum_cycleXZY (T : DetTriangle) : signSum (cycleXZY T) = signSum T := by
  change signSum (swapYZ (swapXY T)) = _
  rw [signSum_swapYZ, signSum_swapXY]

lemma signSum_applyPerm (T : DetTriangle) (σ : Equiv.Perm (Fin 3)) :
    signSum (applyPerm σ T) = signSum T := by
  unfold applyPerm
  split_ifs
  · rfl
  · exact signSum_swapYZ T
  · exact signSum_swapXY T
  · exact signSum_cycleXYZ T
  · exact signSum_cycleXZY T
  · exact signSum_swapXZ T

lemma signSum_flipAll (T : DetTriangle) : signSum (flipAll T) = -signSum T := by
  simp only [signSum, flipAll, RespTable.flip, sum_neg_distrib]
  ring

lemma signSum_symmetry (T : DetTriangle) (g : Symmetry) :
    signSum (g.apply T) = if g.flip then -signSum T else signSum T := by
  unfold Symmetry.apply
  split_ifs <;> simp only [signSum_flipAll, signSum_applyPerm, signSum_valueReindex]

lemma signSum_exceptional : signSum DetTriangle.exceptional = -9 := by
  simp only [signSum, Fin.sum_univ_three, DetTriangle.exceptional_A,
    DetTriangle.exceptional_B, DetTriangle.exceptional_C]
  norm_num

theorem signSum_exceptionalOrbit {T : DetTriangle} (h : inExceptionalOrbit T) :
    signSum T = -9 ∨ signSum T = 9 := by
  obtain ⟨g, rfl⟩ := h
  rw [signSum_symmetry, signSum_exceptional]
  cases g.flip <;> simp

/-- Flip exactly one response entry. -/
def RespTable.flipEntry (T : RespTable) (i j : Fin 3) : RespTable where
  f u v := if u = i ∧ v = j then -T u v else T u v
  legal u v := by
    split_ifs
    · exact (T.flip).legal u v
    · exact T.legal u v

def flipEntryC (T : DetTriangle) (i j : Fin 3) : DetTriangle :=
  ⟨T.A, T.B, T.C.flipEntry i j⟩

lemma signSum_flipEntryC (T : DetTriangle) (i j : Fin 3) :
    signSum (flipEntryC T i j) = signSum T - 2 * T.C i j := by
  have hf (u v : Fin 3) : (T.C.flipEntry i j) u v =
      T.C u v - (if u = i ∧ v = j then 2 * T.C i j else 0) := by
    by_cases h : u = i ∧ v = j
    · obtain ⟨rfl, rfl⟩ := h
      simp [RespTable.flipEntry]
      ring
    · simp [RespTable.flipEntry, h]
  have hsum : (∑ u : Fin 3, ∑ v : Fin 3,
      if u = i ∧ v = j then 2 * T.C i j else 0) = 2 * T.C i j := by
    calc
      _ = ∑ u : Fin 3, if u = i then 2 * T.C i j else 0 := by
        apply sum_congr rfl
        intro u _
        by_cases hu : u = i <;> simp [hu]
      _ = _ := by simp
  simp only [signSum, flipEntryC, hf, sum_sub_distrib]
  rw [hsum]
  ring

lemma weightExp_flipEntryC (T : DetTriangle) (qx qy qz : Simplex2)
    (i j : Fin 3) (hzero : qx i = 0 ∨ qy j = 0) (f : ℝ → ℝ → ℝ → ℝ) :
    weightExp (fun a b c => f ((flipEntryC T i j).A b c)
      ((flipEntryC T i j).B c a) ((flipEntryC T i j).C a b)) qx qy qz =
    weightExp (fun a b c => f (T.A b c) (T.B c a) (T.C a b)) qx qy qz := by
  unfold weightExp
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro c _
  by_cases hab : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := hab
    obtain hz | hz := hzero <;> simp [hz]
  · simp [flipEntryC, RespTable.flipEntry, hab]

/-- An unused edge cannot affect any of the three aggregate moments. -/
theorem detMoments_flipEntryC (T : DetTriangle) (qx qy qz : Simplex2)
    (i j : Fin 3) (hzero : qx i = 0 ∨ qy j = 0) :
    detMoments' (flipEntryC T i j) qx qy qz = detMoments' T qx qy qz := by
  apply AggregateMoments.ext
  · change (detMoments _ qx qy qz).M1 = (detMoments _ qx qy qz).M1
    rw [detMoments_M1_weightExp, detMoments_M1_weightExp]
    exact congrArg (fun r : ℝ => r / 3)
      (weightExp_flipEntryC T qx qy qz i j hzero (fun a b c => a+b+c))
  · change (detMoments _ qx qy qz).M2 = (detMoments _ qx qy qz).M2
    rw [detMoments_M2_weightExp, detMoments_M2_weightExp]
    exact congrArg (fun r : ℝ => r / 3)
      (weightExp_flipEntryC T qx qy qz i j hzero (fun a b c => a*b+b*c+c*a))
  · change (detMoments _ qx qy qz).M3 = (detMoments _ qx qy qz).M3
    rw [detMoments_M3_weightExp, detMoments_M3_weightExp]
    exact weightExp_flipEntryC T qx qy qz i j hzero (fun a b c => a*b*c)

lemma flipEntryC_exceptional_not_in_orbit (i j : Fin 3) :
    ¬ inExceptionalOrbit (flipEntryC DetTriangle.exceptional i j) := by
  intro h
  have hs := signSum_exceptionalOrbit h
  rw [signSum_flipEntryC, signSum_exceptional] at hs
  obtain he | he := DetTriangle.exceptional.C.legal i j <;>
    rcases hs with hs | hs <;> rw [he] at hs <;> norm_num at hs

/-- Conditional use of the paper's finite gap: a zero first-source weight
forces the exceptional table's constrained value below 9/25. -/
theorem exceptional_zero_first_gap (hgap : GapHypothesis) (qx qy qz : Simplex2)
    (i : Fin 3) (hi : qx i = 0)
    (h1 : (detMoments' DetTriangle.exceptional qx qy qz).M1 = 0)
    (h3 : (detMoments' DetTriangle.exceptional qx qy qz).M3 = 0) :
    (detMoments' DetTriangle.exceptional qx qy qz).M2 ≤ nineTwentyFifths := by
  have he := detMoments_flipEntryC DetTriangle.exceptional qx qy qz i 0 (Or.inl hi)
  have hb := hgap _ (flipEntryC_exceptional_not_in_orbit i 0) qx qy qz
  rw [he] at hb
  exact hb h1 h3

/-- At a constrained value above the finite gap, all nine source weights are
strictly positive. No assumption of interiority is supplied. -/
theorem exceptional_positive_of_high (hgap : GapHypothesis) (qx qy qz : Simplex2)
    (h1 : (detMoments' DetTriangle.exceptional qx qy qz).M1 = 0)
    (h3 : (detMoments' DetTriangle.exceptional qx qy qz).M3 = 0)
    (hhigh : nineTwentyFifths < (detMoments' DetTriangle.exceptional qx qy qz).M2) :
    (∀ i, 0 < qx i) ∧ (∀ i, 0 < qy i) ∧ (∀ i, 0 < qz i) := by
  have hcycle (qx qy qz : Simplex2) :
      detMoments' DetTriangle.exceptional qx qy qz =
        detMoments' DetTriangle.exceptional qy qz qx :=
    detMoments_cycleXYZ DetTriangle.exceptional qx qy qz
  have hfirst (qx qy qz : Simplex2)
      (h1 : (detMoments' DetTriangle.exceptional qx qy qz).M1 = 0)
      (h3 : (detMoments' DetTriangle.exceptional qx qy qz).M3 = 0)
      (hh : nineTwentyFifths < (detMoments' DetTriangle.exceptional qx qy qz).M2) :
      ∀ i, 0 < qx i := by
    intro i
    apply lt_of_le_of_ne (qx.nonneg i)
    intro hz
    have hb := exceptional_zero_first_gap hgap qx qy qz i hz.symm h1 h3
    exact hh.not_ge hb
  refine ⟨hfirst _ _ _ h1 h3 hhigh, ?_, ?_⟩
  · rw [hcycle] at h1 h3 hhigh
    exact hfirst _ _ _ h1 h3 hhigh
  · rw [hcycle, hcycle] at h1 h3 hhigh
    exact hfirst _ _ _ h1 h3 hhigh

end Paper15
