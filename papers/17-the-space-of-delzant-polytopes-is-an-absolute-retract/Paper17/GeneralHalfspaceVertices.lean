import Paper17.HalfspaceVertices

/-! Finite vertex realization without a simplicity assumption. -/
noncomputable section
open scoped BigOperators
namespace Paper17
section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- Every extreme point admits a nonsingular square subsystem of its actual
active supporting equations, including when more than `n` faces meet there. -/
theorem extreme_exists_constraint_system (a : ι → V n) (h : ι → ℝ)
    {x : V n} (hx : x ∈ (finiteHalfspaces a h).extremePoints ℝ) :
    ∃ s : Finset ι, ∃ hs : s.card = n,
      s ⊆ activeConstraints a h x ∧ (constraintMatrix a s hs).det ≠ 0 ∧
        x = constraintVertex a h s := by
  classical
  let A := activeConstraints a h x
  obtain ⟨κ, f, hf, hspan, hli⟩ :=
    exists_linearIndependent' ℝ (fun i : A => a i.val)
  letI : Finite κ := Finite.of_injective f hf
  letI : Fintype κ := Fintype.ofFinite κ
  let L : V n →ₗ[ℝ] (κ → ℝ) :=
    { toFun := fun v i => dot (a (f i).val) v
      map_add' := by intro v w; ext i; exact dot_add_right _ _ _
      map_smul' := by intro t v; ext i; exact dot_smul_right _ _ _ }
  have hkernel : ∀ v, L v = 0 → v = 0 := by
    intro v hv
    let T : V n →ₗ[ℝ] ℝ :=
      { toFun := fun y => dot y v
        map_add' := by intro y z; exact dot_add_left _ _ _
        map_smul' := by intro t y; exact dot_smul_left _ _ _ }
    have hle : Submodule.span ℝ (Set.range ((fun i : A => a i.val) ∘ f)) ≤ LinearMap.ker T := by
      apply Submodule.span_le.mpr
      rintro y ⟨i, rfl⟩
      exact congrFun hv i
    rw [hspan] at hle
    apply extreme_active_kernel_eq_zero a h hx v
    intro i hi
    exact hle (Submodule.subset_span (Set.mem_range.mpr ⟨⟨i, hi⟩, rfl⟩))
  have hinj : Function.Injective L := by
    intro v w hvw
    apply sub_eq_zero.mp
    apply hkernel
    rw [map_sub, hvw, sub_self]
  have hcard : Fintype.card κ = n := by
    apply le_antisymm
    · simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
        hli.fintype_card_le_finrank
    · simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
        LinearMap.finrank_le_finrank_of_injective hinj
  let g : κ → ι := fun i => (f i).val
  have hg : Function.Injective g := Subtype.val_injective.comp hf
  let s : Finset ι := Finset.univ.image g
  have hs : s.card = n := by rw [Finset.card_image_of_injective _ hg]; exact hcard
  have hsub : s ⊆ A := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact (f j).property
  let e := cellEnumeration s hs
  let M := constraintMatrix a s hs
  have hMinj : Function.Injective M.mulVec := by
    intro v w hvw
    apply hinj
    funext j
    have hgj : g j ∈ s := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    obtain ⟨k, hk⟩ := e.surjective ⟨g j, hgj⟩
    have hval : (e k).val = g j := congrArg Subtype.val hk
    have hh := congrFun hvw k
    change dot (a (e k).val) v = dot (a (e k).val) w at hh
    simpa only [hval] using hh
  have hdet : M.det ≠ 0 := isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det M).mp (Matrix.mulVec_injective_iff_isUnit.mp hMinj))
  refine ⟨s, hs, hsub, hdet, ?_⟩
  apply hMinj
  funext k
  change dot (a (e k).val) x = dot (a (e k).val) (constraintVertex a h s)
  rw [(mem_activeConstraints a h x _).mp (hsub (e k).property),
    constraintVertex_solves a h s hs hdet _ (e k).property]

/-- Candidate square systems contain every extreme point of arbitrary finite
halfspace data; redundant and nonsimple supporting faces are allowed. -/
theorem extremePoints_subset_constraintVertices_general (a : ι → V n) (h : ι → ℝ) :
    (finiteHalfspaces a h).extremePoints ℝ ⊆ (constraintVertices a h : Set (V n)) := by
  classical
  intro x hx
  obtain ⟨s, hs, _, hd, heq⟩ := extreme_exists_constraint_system a h hx
  apply Finset.mem_image.mpr
  refine ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩,
    heq.symm⟩
  exact ⟨hs, hd, heq ▸ hx.1⟩

/-- Every compact finite halfspace intersection is the convex hull of its
actual finitely many feasible nonsingular candidate solutions. -/
theorem finiteHalfspaces_eq_convexHull_constraintVertices_general
    (a : ι → V n) (h : ι → ℝ) (hc : IsCompact (finiteHalfspaces a h)) :
    finiteHalfspaces a h = convexHull ℝ (constraintVertices a h : Set (V n)) := by
  have hclosed : IsClosed (convexHull ℝ (constraintVertices a h : Set (V n))) :=
    (constraintVertices a h).finite_toSet.isCompact_convexHull.isClosed
  apply Set.Subset.antisymm
  · rw [← closure_convexHull_extremePoints hc (finiteHalfspaces_convex a h)]
    exact closure_minimal
      (convexHull_mono (extremePoints_subset_constraintVertices_general a h)) hclosed
  · exact convexHull_min (constraintVertices_subset a h) (finiteHalfspaces_convex a h)

end
end Paper17
