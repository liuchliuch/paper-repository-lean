import Paper09.RFIM
import Paper09.ProductCoordinates

open Finset BigOperators Real MeasureTheory Classical
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Paper09.RFIM
local instance (priority := 2000) placementPointDecEq (d : ℕ) : DecidableEq (Point d) :=
  Classical.decEq _
local instance (priority := 2000) placementSiteDecEq {d : ℕ} (A : Finset (Point d)) : DecidableEq ↥A :=
  Classical.decEq _

/-- A candidate index for disjoint boxes in the positive orthant. -/
abbrev Candidate (d n m : ℕ) := Fin d → Fin (n / (m + 2))

/-- Lower-left corner of the enlarged island cell. -/
def islandOffset {d n m : ℕ} (k : Candidate d n m) : Point d :=
  fun j => (m + 2 : ℕ) * (k j : ℕ)

/-- Translation of a finite lattice set. -/
def translate {d : ℕ} (t : Point d) (A : Finset (Point d)) : Finset (Point d) :=
  A.image (fun x => x + t)

@[simp] theorem mem_translate {d : ℕ} {t x : Point d} {A : Finset (Point d)} :
    x ∈ translate t A ↔ x - t ∈ A := by
  simp only [translate, mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨x-t,hx,sub_add_cancel _ _⟩

theorem adj_add_iff {d : ℕ} (x y t : Point d) :
    LatticeGeometry.Adj (x+t) (y+t) ↔ LatticeGeometry.Adj x y := by
  constructor <;> rintro ⟨j,hj,hrest⟩ <;> refine ⟨j,?_,?_⟩
  · rcases hj with hj | hj <;> simp only [Pi.add_apply] at hj
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · intro k hk
    have hh := hrest k hk
    simp only [Pi.add_apply] at hh
    omega
  · rcases hj with hj | hj
    · exact Or.inl (by simp only [Pi.add_apply]; omega)
    · exact Or.inr (by simp only [Pi.add_apply]; omega)
  · intro k hk
    simp only [Pi.add_apply, hrest k hk]

theorem externalBoundary_translate {d : ℕ} (t : Point d) (A : Finset (Point d)) :
    externalBoundary (translate t A) = translate t (externalBoundary A) := by
  ext y
  simp only [mem_translate, mem_externalBoundary]
  constructor
  · rintro ⟨hy,x,hx,hadj⟩
    refine ⟨hy, x-t, hx, ?_⟩
    have hh := (adj_add_iff (x-t) (y-t) t).mp
    apply hh
    simpa using hadj
  · rintro ⟨hy,x,hx,hadj⟩
    refine ⟨hy,x+t,(by simpa using hx),?_⟩
    have hh := (adj_add_iff x (y-t) t).mpr hadj
    simpa using hh

/-- Every coordinate of an island or its one-site shell lies in `[0,m+1]`. -/
theorem island_base_bounds {d m : ℕ} {x : Point d}
    (hx : x ∈ pureBox d m ∪ externalBoundary (pureBox d m)) (j : Fin d) :
    0 ≤ x j ∧ x j < (m + 2 : ℕ) := by
  rcases mem_union.mp hx with hx | hx
  · have hh := mem_pureBox.mp hx j
    constructor <;> omega
  · obtain ⟨_, y, hy, k, hstep, hother⟩ := mem_externalBoundary.mp hx
    have hyj := mem_pureBox.mp hy j
    by_cases hj : j = k
    · subst j
      rcases hstep with hs | hs <;> constructor <;> omega
    · have hh := hother j hj
      constructor <;> omega

/-- Interior or shell coordinates, with no overlap between the two types. -/
def islandBasePoint {d m : ℕ}
    (x : ↥(pureBox d m) ⊕ ↥(externalBoundary (pureBox d m))) : Point d :=
  Sum.elim Subtype.val Subtype.val x

theorem islandBasePoint_mem {d m : ℕ}
    (x : ↥(pureBox d m) ⊕ ↥(externalBoundary (pureBox d m))) :
    islandBasePoint x ∈ pureBox d m ∪ externalBoundary (pureBox d m) := by
  cases x with
  | inl x => exact mem_union_left _ x.property
  | inr x => exact mem_union_right _ x.property

theorem islandBasePoint_injective {d m : ℕ} :
    Function.Injective (@islandBasePoint d m) := by
  intro x y h
  cases x with
  | inl x =>
    cases y with
    | inl y => exact congrArg Sum.inl (Subtype.ext h)
    | inr y =>
      change (x : Point d) = (y : Point d) at h
      exact False.elim ((mem_externalBoundary.mp y.property).1 (h ▸ x.property))
  | inr x =>
    cases y with
    | inl y =>
      change (x : Point d) = (y : Point d) at h
      exact False.elim ((mem_externalBoundary.mp x.property).1 (h.symm ▸ y.property))
    | inr y => exact congrArg Sum.inr (Subtype.ext h)

/-- The actual coordinates inspected by every island event. -/
def placementCoordinate {d n m : ℕ}
    (p : Sigma (fun _ : Candidate d n m =>
      ↥(pureBox d m) ⊕ ↥(externalBoundary (pureBox d m)))) : Point d :=
  islandBasePoint p.2 + islandOffset p.1

/-- Disjointness is proved by Euclidean decoding of the containing cell. -/
theorem placementCoordinate_injective (d n m : ℕ) :
    Function.Injective (@placementCoordinate d n m) := by
  rintro ⟨k,x⟩ ⟨l,y⟩ h
  have hL : (0 : ℤ) < (m + 2 : ℕ) := by positivity
  have hdecode (z : ↥(pureBox d m) ⊕ ↥(externalBoundary (pureBox d m)))
      (i : Candidate d n m) (j : Fin d) :
      (placementCoordinate ⟨i,z⟩ j) / (m + 2 : ℕ) = (i j : ℕ) := by
    have hz := island_base_bounds (islandBasePoint_mem z) j
    change (islandBasePoint z j + (m + 2 : ℕ) * (i j : ℕ)) / (m + 2 : ℕ) = _
    rw [Int.add_mul_ediv_left _ _ hL.ne', Int.ediv_eq_zero_of_lt hz.1 hz.2, zero_add]
  have hkl : k = l := by
    funext j
    apply Fin.ext
    have hval := congrArg (fun z : Point d => z j / (m + 2 : ℕ)) h
    dsimp only at hval
    rw [hdecode, hdecode] at hval
    exact_mod_cast hval
  subst l
  have hxy : x = y := islandBasePoint_injective (add_right_cancel h)
  subst y
  rfl

/-- All coordinates of all candidates are genuinely inside `Λ_n`. -/
theorem placementCoordinate_in_volume {d n m : ℕ}
    (p : Sigma (fun _ : Candidate d n m =>
      ↥(pureBox d m) ⊕ ↥(externalBoundary (pureBox d m)))) :
    placementCoordinate p ∈ volumeBox d n := by
  apply mem_volumeBox.mpr
  intro j
  have hx := island_base_bounds (islandBasePoint_mem p.2) j
  have hk : (p.1 j : ℕ) < n / (m+2) := (p.1 j).isLt
  have hmul : (m+2) * ((p.1 j : ℕ) + 1) ≤ n := by
    have hh := Nat.mul_le_mul_left (m+2) (Nat.succ_le_of_lt hk)
    exact hh.trans (by simpa [Nat.mul_comm] using Nat.div_mul_le_self n (m+2))
  change -(n : ℤ) ≤ islandBasePoint p.2 j + (m+2 : ℕ) * (p.1 j : ℕ) ∧
    islandBasePoint p.2 j + (m+2 : ℕ) * (p.1 j : ℕ) ≤ n
  have hmul' : ((m+2 : ℕ) : ℤ) * ((p.1 j : ℕ) + 1) ≤ n := by exact_mod_cast hmul
  constructor
  · have hoff : (0 : ℤ) ≤ ((m+2 : ℕ) : ℤ) * (p.1 j : ℕ) := by positivity
    linarith [Nat.cast_nonneg (α := ℤ) n]
  · nlinarith

@[simp] theorem card_candidates (d n m : ℕ) :
    Fintype.card (Candidate d n m) = (n / (m+2)) ^ d := by
  simp [Candidate]

/-- Actual lattice packing and Gaussian coordinate identification. -/
theorem environment_placement_law (d n m : ℕ) (σ : ℝ) :
    (environmentLaw d σ).map (fun h (k : Candidate d n m) x =>
      h (placementCoordinate ⟨k,x⟩)) =
      Measure.pi (fun _ : Candidate d n m =>
        Measure.pi (fun _ : ↥(pureBox d m) ⊕ ↥(externalBoundary (pureBox d m)) =>
          Gaussian.law σ)) := by
  exact ProductCoordinates.infinitePi_map_groups (fun _ : Point d => Gaussian.law σ)
    placementCoordinate (placementCoordinate_injective d n m)

/-- The island event at an actual translate inside `Λ_n`. -/
def islandOccurs {d n m : ℕ}
    (ζ : ↥(externalBoundary (pureBox d m)) → Bool) (u H : ℝ)
    (k : Candidate d n m) : Set (Point d → ℝ) :=
  (fun h x => h (placementCoordinate ⟨k,x⟩)) ⁻¹'
    Gaussian.islandEvent ↥(pureBox d m) ↥(externalBoundary (pureBox d m)) ζ u H

/-- The absence probability in the actual infinite Gaussian environment,
with the original unrestricted exterior fields. -/
theorem no_lattice_island_bound (d : ℕ) (σ ε H : ℝ)
    (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ C > 0, ∀ (n m : ℕ) (ζ : ↥(externalBoundary (pureBox d m)) → Bool), 2 ≤ m →
      (environmentLaw d σ).real {h | ∀ k : Candidate d n m, h ∉ islandOccurs ζ (ε/m) H k} ≤
        exp (-((n / (m+2) : ℕ) : ℝ) ^ d * exp (-C * (m : ℝ) ^ d * log m)) := by
  obtain ⟨C,hC,hno⟩ := Gaussian.no_gaussian_island σ ε H hσ hε
  let C₂ := 1 + (1 + 2 * d) * C / log 2
  refine ⟨C₂, by dsimp [C₂]; positivity, ?_⟩
  intro n m ζ hm
  let B := ↥(pureBox d m)
  let S := ↥(externalBoundary (pureBox d m))
  let J := Candidate d n m
  let E := Gaussian.islandEvent B S ζ (ε/m) H
  let F : (Point d → ℝ) → J → (B ⊕ S → ℝ) :=
    fun h k x => h (placementCoordinate ⟨k,x⟩)
  have hE : MeasurableSet E := Gaussian.measurableSet_islandEvent B S ζ _ _
  have hmap := environment_placement_law d n m σ
  have heq : (environmentLaw d σ).real {h | ∀ k : J, h ∉ islandOccurs ζ (ε/m) H k} =
      (Measure.pi (fun _ : J => Measure.pi (fun _ : B ⊕ S => Gaussian.law σ))).real
        (Set.univ.pi (fun _ : J => Eᶜ)) := by
    have hs : {h | ∀ k : J, h ∉ islandOccurs ζ (ε/m) H k} =
        F ⁻¹' (Set.univ.pi (fun _ : J => Eᶜ)) := by
      ext h
      simp only [F, E, islandOccurs, Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const,
        Set.mem_compl_iff, Set.mem_setOf_eq]
      rfl
    rw [hs, measureReal_def, measureReal_def, ← hmap,
      Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi (fun _ => hE.compl))]
  rw [heq]
  have hh := hno B S J ζ m (by omega)
  have hB : Fintype.card B = m ^ d := by simp [B]
  have hS : Fintype.card S ≤ 2 * d * m ^ (d-1) := by
    simpa [S] using card_externalBoundary_pureBox_le d m
  have hcost : (Fintype.card B : ℝ) * (log m + C) + C * Fintype.card S ≤
      C₂ * (m : ℝ) ^ d * log m := by
    rw [hB]
    push_cast
    apply le_trans _ (Gaussian.geometric_cost_bound hC.le d m hm)
    have hS' : (Fintype.card S : ℝ) ≤ 2 * d * (m : ℝ) ^ (d-1) := by exact_mod_cast hS
    nlinarith
  apply hh.trans
  apply exp_le_exp.mpr
  have hp := exp_le_exp.mpr (neg_le_neg hcost)
  have hJ : (Fintype.card J : ℝ) = ((n / (m+2) : ℕ) : ℝ) ^ d := by
    simp [J]
  rw [hJ]
  have hp' : exp (-C₂ * (m : ℝ) ^ d * log m) ≤
      exp (-((Fintype.card B : ℝ) * (log m + C) + C * Fintype.card S)) := by
    convert hp using 1 <;> congr 1 <;> ring
  exact mul_le_mul_of_nonpos_left hp' (neg_nonpos.mpr (by positivity))

end Paper09.RFIM
