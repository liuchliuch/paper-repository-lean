import Paper17.BoundedHalfspaceRefinement

/-!
# From genuine rational normal generators to smooth projective refinement

The source's rational-normal hypothesis supplies integer generators for each
actual vertex normal cone. They give a finite supporting-halfspace
presentation. Coordinate augmentation, generic outward perturbation and the
completed projective stellar resolution produce a genuine Delzant polytope.
-/
noncomputable section
open scoped BigOperators
namespace Paper17

/-- A finite integral H-presentation of an actual carrier. No refinement or
Delzant conclusion is assumed in this representation data. -/
structure IntegralHalfspacePresentation {n : ℕ} (K : Set (V n)) where
  index : Type
  [indexFintype : Fintype index]
  [indexDecidableEq : DecidableEq index]
  normals : index → Fin n → ℤ
  heights : index → ℝ
  carrier_eq : finiteHalfspaces (realRays normals) heights = K

attribute [instance] IntegralHalfspacePresentation.indexFintype IntegralHalfspacePresentation.indexDecidableEq

/-- Finite integer generators for each actual geometric normal cone. -/
def HasRationalNormalPresentation {n : ℕ} (P : Polytope n) : Prop :=
  ∀ v ∈ P.verts, ∃ m : ℕ, ∃ rays : Fin m → Fin n → ℤ,
    (normalConeAt P v : Set (V n)) = {u | ∃ c : Fin m → ℝ,
      (∀ i, 0 ≤ c i) ∧ u = ∑ i, c i • realRays rays i}

theorem supportFunction_eq_of_normal {n : ℕ} (P : Polytope n) {v u : V n}
    (hv : v ∈ P.carrier) (hu : u ∈ normalConeAt P v) :
    supportFunction P.carrier u = dot u v := by
  apply le_antisymm
  · obtain ⟨y, hy, heq⟩ := exists_mem_eq_supportFunction P.isCompact P.nonempty u
    rw [heq]
    exact hu y hy
  · exact supportFunction_ub P.isCompact hv

/-- The supplied integral normal rays give the actual supporting halfspace
presentation, including for redundant finite vertex presentations. -/
theorem integralHalfspacePresentation_of_normal_generators {n : ℕ} (P : Polytope n)
    (hP : HasRationalNormalPresentation P) : Nonempty (IntegralHalfspacePresentation P.carrier) := by
  classical
  have hex : ∀ v : P.verts, ∃ m : ℕ, ∃ rays : Fin m → Fin n → ℤ,
      (normalConeAt P v.val : Set (V n)) = {u | ∃ c : Fin m → ℝ,
        (∀ i, 0 ≤ c i) ∧ u = ∑ i, c i • realRays rays i} := fun v => hP v.val v.property
  choose m rays hcone using hex
  let J := (v : P.verts) × Fin (m v)
  let a : J → Fin n → ℤ := fun j => rays j.1 j.2
  let heights : J → ℝ := fun j => supportFunction P.carrier (realRays a j)
  have hcarrier : finiteHalfspaces (realRays a) heights = P.carrier := by
    apply Set.Subset.antisymm
    · apply subset_of_forall_dot_le_supportFunction P.isCompact P.nonempty P.convex
      intro u x hx
      obtain ⟨v, hv, hmax⟩ := exists_mem_verts_isMaxOn P u
      let v' : P.verts := ⟨v, hv⟩
      have hu : u ∈ (normalConeAt P v : Set (V n)) := hmax
      rw [hcone v'] at hu
      obtain ⟨c, hc, hu⟩ := hu
      have hRayNormal : ∀ i, realRays (rays v') i ∈ normalConeAt P v := by
        intro i
        change realRays (rays v') i ∈ (normalConeAt P v'.val : Set (V n))
        rw [hcone v']
        refine ⟨Pi.single i 1, ?_, ?_⟩
        · intro j
          simp only [Pi.single_apply]
          split_ifs <;> norm_num
        · simp
      have hheight : ∀ i, heights ⟨v', i⟩ = dot (realRays (rays v') i) v := by
        intro i
        exact supportFunction_eq_of_normal P (subset_convexHull ℝ _ hv) (hRayNormal i)
      calc dot u x = ∑ i, c i * dot (realRays (rays v') i) x := by rw [hu, dot_fintype_sum_smul]
        _ ≤ ∑ i, c i * heights ⟨v', i⟩ :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hx ⟨v', i⟩) (hc i))
        _ = ∑ i, c i * dot (realRays (rays v') i) v := by simp_rw [hheight]
        _ = dot u v := by rw [hu, dot_fintype_sum_smul]
        _ ≤ supportFunction P.carrier u := supportFunction_ub P.isCompact (subset_convexHull ℝ _ hv)
    · intro x hx j
      exact supportFunction_ub P.isCompact hx
  exact ⟨{ index := J, normals := a, heights := heights, carrier_eq := hcarrier }⟩

/-- Every nonempty compact carrier with an actual integral halfspace
presentation admits an actual Delzant normal-fan refinement. -/
theorem IntegralHalfspacePresentation.exists_delzant_refinement {n : ℕ} {K : Set (V n)}
    (H : IntegralHalfspacePresentation K) (hcompact : IsCompact K) (hne : K.Nonempty) :
    ∃ Q : DelzantPolytope n, ∀ C ∈ (NormalFan Q.val).cones,
      ∃ y ∈ K, (C : Set (V n)) ⊆ carrierNormalCone K y := by
  classical
  obtain ⟨R, hR, hbound⟩ := hcompact.isBounded.exists_pos_norm_le
  let a := coordinateAugmentedNormals H.normals
  let h : (H.index ⊕ (Fin n × Bool)) → ℝ := coordinateAugmentedHeights H.heights R
  have hboundOld : ∀ x ∈ finiteHalfspaces (realRays H.normals) H.heights, ‖x‖ ≤ R := by
    intro x hx
    exact hbound x (H.carrier_eq ▸ hx)
  have heq : finiteHalfspaces (realRays a) h = K :=
    (coordinateAugmented_carrier H.normals H.heights R hR.le hboundOld).trans H.carrier_eq
  have hne' : (finiteHalfspaces (realRays a) h).Nonempty := by rw [heq]; exact hne
  obtain ⟨Q, hQ⟩ := exists_delzant_refinement_halfspaces a h
    (Metric.closedBall (0 : V n) (R + 1)) (isCompact_closedBall _ _)
    (fun h' hh => coordinateAugmented_uniform_bound H.normals H.heights R hR.le h' hh) hne'
  refine ⟨Q, ?_⟩
  intro C hC
  obtain ⟨y, hy, hCy⟩ := hQ C hC
  exact ⟨y, heq ▸ hy, by simpa only [heq] using hCy⟩

/-- Smooth projective resolution for the actual rational-normal presentation.
The output is a genuine Delzant polytope and actual normal-cone containment. -/
theorem exists_delzant_refinement_of_rational_normal {n : ℕ} (P : Polytope n)
    (hP : HasRationalNormalPresentation P) :
    ∃ Q : DelzantPolytope n, ∀ C ∈ (NormalFan Q.val).cones,
      ∃ y ∈ P.carrier, (C : Set (V n)) ⊆ (normalConeAt P y : Set (V n)) := by
  obtain ⟨H⟩ := integralHalfspacePresentation_of_normal_generators P hP
  exact H.exists_delzant_refinement P.isCompact P.nonempty

end Paper17
