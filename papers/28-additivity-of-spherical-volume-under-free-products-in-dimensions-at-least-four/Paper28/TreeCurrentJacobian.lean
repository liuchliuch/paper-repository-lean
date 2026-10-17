import Paper28.TreeJacobian
import Paper28.ShadowCalculus

/-! Lemma 2.3 for the original incident-edge shadow maps and mass-a.e.
tangent planes. Both the finite-tree estimate and the shadow differential
identification are derived, with only the disclosed generic external inputs. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace Paper28
attribute [local irreducible] frameJacobian
open SimpleGraph MeasureTheory
open scoped InnerProductSpace
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type u} [Fintype V] [DecidableEq V]
  (T : SimpleGraph V) [DecidableRel T.Adj]

/-- Replacing neighbor indices by their literal incident edges preserves
the full Jacobian, by the canonical coordinate isometry. -/
theorem treeJacobian_incident_edges (hT : T.IsTree) (x : V)
    (z : EuclideanSpace ℝ T.edgeSet) (S : Submodule ℝ (EuclideanSpace ℝ T.edgeSet)) :
    treeJacobian T hT z S x = partitionJacobian (treeBranchEdge T hT x) z S := by
  apply frameJacobian_congr_inner
  intro h k
  exact shadowDifferential_reindex_inner (Equiv.refl T.edgeSet)
    (T.incidenceSetEquivNeighborSet x).symm (treeBranch T hT x) (treeBranchEdge T hT x)
    (fun _ => rfl) z h.val k.val

theorem treeJacobian_bound_on_edges (hFischer : FischerInput) (hT : T.IsTree)
    (z : EuclideanSpace ℝ T.edgeSet) (S : Submodule ℝ (EuclideanSpace ℝ T.edgeSet))
    (hn : 4 ≤ Module.finrank ℝ S) (htan : ∀ h : S, ⟪z,h.val⟫_ℝ = 0)
    (hzero : ∀ i, z i = 0 → ∀ h : S, h.val i = 0) :
    ∑ x, partitionJacobian (treeBranchEdge T hT x) z S ≤ 1 := by
  have h := treeJacobian_bound hFischer T hT z S hn htan hzero
  simp_rw [treeJacobian_incident_edges T hT] at h
  exact h

variable [MeasurableSpace (EuclideanSpace ℝ T.edgeSet)]
variable (I : RectifiableSphereCalculusInput.{u,v} (EuclideanSpace ℝ T.edgeSet))

/-- Lemma 2.3, with the actual incident-edge maps of Definition 2.2,
its original dimension threshold and its mass-almost-everywhere quantifier. -/
theorem lemma_2_3 (hFischer : FischerInput) (hT : T.IsTree)
    (n : ℕ) (hn : 4 ≤ n) (C : I.Current n) :
    ∀ᵐ z ∂I.massMeasure C,
      (∑ x, currentJacobian I (vertexShadowOnEdges T hT x) C z) ≤ 1 := by
  have hker : ∀ᵐ z ∂I.massMeasure C, ∀ i : T.edgeSet,
      z i = 0 → ∀ h : I.plane C z, h.val i = 0 := by
    apply Filter.eventually_all.mpr
    intro i
    filter_upwards [linear_kernel_tangent_ae I (fiberProjectionCLM (id : T.edgeSet → T.edgeSet) i) C]
      with z hker
    intro hi h
    have hp : fiberProjectionCLM (id : T.edgeSet → T.edgeSet) i z = 0 := by
      ext j
      change (if j = i then z j else 0) = 0
      by_cases hj : j = i
      · rw [if_pos hj, hj, hi]
      · rw [if_neg hj]
    have hh := congrArg (fun q : EuclideanSpace ℝ T.edgeSet => q i) (hker hp h)
    simpa [fiberProjectionCLM, fiberProjection_apply] using hh
  have hdiff := Filter.eventually_all.mpr (fun x : V =>
    finiteShadow_approx_differential_ae I (treeBranchEdge T hT x) C)
  filter_upwards [I.dimension_ae C, I.tangent_ae C, hker, hdiff] with z hdim htan hz hd
  have hsum : (∑ x, currentJacobian I (vertexShadowOnEdges T hT x) C z) =
      ∑ x, partitionJacobian (treeBranchEdge T hT x) z (I.plane C z) := by
    apply Finset.sum_congr rfl
    intro x _
    unfold currentJacobian partitionJacobian
    congr 1
    funext h
    exact hd x h
  rw [hsum]
  exact treeJacobian_bound_on_edges T hFischer hT z (I.plane C z) (by omega) htan hz

end Paper28
