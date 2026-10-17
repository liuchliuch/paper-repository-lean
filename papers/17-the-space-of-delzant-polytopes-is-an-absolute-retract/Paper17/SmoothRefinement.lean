import Paper17.ExtremeNormalCones
import Paper17.RationalBasisFaces
import Paper17.DelzantDensity

/-! Common smooth projective refinements of finitely many genuine Delzant
polytopes. Rational normal data is proved from their actual basis cones. -/
noncomputable section
open scoped BigOperators
namespace Paper17

/-- Rational H-data for every listed vertex normal cone. -/
def HasRationalConePresentations {n : ℕ} (P : Polytope n) : Prop :=
  ∀ v ∈ P.verts, Nonempty (RationalConePresentation (normalConeAt P v : Set (V n)))

theorem delzant_hasRationalConePresentations {n : ℕ} (P : DelzantPolytope n) :
    HasRationalConePresentations P.val := by
  intro v hv
  obtain ⟨a, I, hd, heq⟩ := delzant_normalCone_basis_face P (subset_convexHull ℝ _ hv)
  rw [heq]
  exact ⟨basisFacePresentation a hd I⟩

theorem HasRationalConePresentations.add {n : ℕ} {P Q : Polytope n}
    (hP : HasRationalConePresentations P) (hQ : HasRationalConePresentations Q) :
    HasRationalConePresentations (P.add Q) := by
  classical
  intro v hv
  obtain ⟨⟨p, q⟩, hpq, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨hp, hq⟩ := Finset.mem_product.mp hpq
  obtain ⟨HP⟩ := hP p hp
  obtain ⟨HQ⟩ := hQ q hq
  rw [normalConeAt_add (subset_convexHull ℝ _ hp) (subset_convexHull ℝ _ hq)]
  exact ⟨HP.inter HQ⟩

theorem HasRationalConePresentations.normal_generators {n : ℕ} {P : Polytope n}
    (hP : HasRationalConePresentations P) : HasRationalNormalPresentation P := by
  intro v hv
  obtain ⟨H⟩ := hP v hv
  exact H.integer_generators

/-- The full-dimensional coordinate cube gives an actual starting Delzant
polytope via the already proved halfspace-resolution engine. -/
theorem delzant_nonempty (n : ℕ) : Nonempty (DelzantPolytope n) := by
  let v : Fin 0 → Fin n → ℤ := Fin.elim0
  let h : Fin 0 → ℝ := Fin.elim0
  let a := coordinateAugmentedNormals v
  let heights := coordinateAugmentedHeights (n := n) h 1
  have hne : (finiteHalfspaces (realRays a) heights).Nonempty := by
    refine ⟨0, ?_⟩
    intro i
    cases i with
    | inl i => exact Fin.elim0 i
    | inr i => simp [heights, coordinateAugmentedHeights, dot]
  obtain ⟨Q, _⟩ := exists_delzant_refinement_halfspaces a heights
    (Metric.closedBall (0 : V n) (1 + 1)) (isCompact_closedBall _ _)
    (fun h' hh => coordinateAugmented_uniform_bound v h 1 (by norm_num) h' hh) hne
  exact ⟨Q⟩

/-- The actual sum has rational normal cones, so resolving it gives a common
smooth projective refinement of the two summands. -/
theorem common_smooth_refinement_pair {n : ℕ} (P Q : DelzantPolytope n) :
    ∃ S : DelzantPolytope n, DelzantPolytope.le P S ∧ DelzantPolytope.le Q S := by
  have hsum := (delzant_hasRationalConePresentations P).add
    (delzant_hasRationalConePresentations Q)
  obtain ⟨S, hS⟩ := exists_delzant_refining_normalFan (P.val.add Q.val) hsum.normal_generators
  have hmeet := Fan.refines_trans hS (normalFan_add P.val Q.val).1
  exact ⟨S, Fan.refines_trans hmeet (Fan.meet_refines_left _ _),
    Fan.refines_trans hmeet (Fan.meet_refines_right _ _)⟩

/-- Finite families, including the empty family, admit a genuine common
smooth polytopal refinement. -/
theorem common_smooth_refinement {n m : ℕ} (Ps : Fin m → DelzantPolytope n) :
    ∃ Q : DelzantPolytope n, ∀ i, DelzantPolytope.le (Ps i) Q := by
  induction m with
  | zero =>
    obtain ⟨Q⟩ := delzant_nonempty n
    exact ⟨Q, fun i => Fin.elim0 i⟩
  | succ m ih =>
    obtain ⟨S, hS⟩ := ih (fun i => Ps i.succ)
    obtain ⟨Q, hP, hSQ⟩ := common_smooth_refinement_pair (Ps 0) S
    refine ⟨Q, ?_⟩
    intro i
    refine Fin.cases hP (fun j => ?_) i
    exact DelzantPolytope.le_trans (hS j) hSQ

/-- The finite-family consequence also applies to arbitrary actual rational
normal presentations: resolve each first, then refine the resulting Delzant
family. -/
theorem common_refinement_of_rational_normal {n m : ℕ} (Ps : Fin m → Polytope n)
    (hPs : ∀ i, HasRationalNormalPresentation (Ps i)) :
    ∃ Q : DelzantPolytope n, ∀ i, (NormalFan Q.val).refines (NormalFan (Ps i)) := by
  classical
  choose S hS using fun i => exists_delzant_refining_normalFan (Ps i) (hPs i)
  obtain ⟨Q, hQ⟩ := common_smooth_refinement S
  exact ⟨Q, fun i => Fan.refines_trans (hQ i) (hS i)⟩

namespace DelzantPolytope
/-- **Lemma 2.2**, the finite Delzant-family interface to the proved general
smooth projective resolution theorem. -/
theorem lemma_2_2 {n m : ℕ} (Ps : Fin m → DelzantPolytope n) :
    ∃ Q : DelzantPolytope n, ∀ i, DelzantPolytope.le (Ps i) Q :=
  common_smooth_refinement Ps
end DelzantPolytope

end Paper17
