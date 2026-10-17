import Verification.FanControl
import Paper17.ContinuousApproximation

/-! Derivation of controlled continuous Delzant approximation from the density
assertion in Lemma 4.2. The density hypothesis is discharged by that original
source lemma at the fixed Proposition 4.3 export, not added to its statement. -/
noncomputable section
open scoped Topology BigOperators Pointwise
namespace P17Contract

/-- Canonical positive carriers in the actual normed support-function space. -/
def bodySupport {n : ℕ} (K : PosBody n) : Paper17.SupportSpace n :=
  Paper17.supportMap ({
    carrier := K.carrier
    convex' := K.convex
    isCompact' := K.isCompact
    interior_nonempty' := K.interior_nonempty } : Paper17.PosBody n)

theorem isometry_bodySupport {n : ℕ} : Isometry (@bodySupport n) := by
  apply isometry_iff_dist_eq.mpr
  intro K L
  rw [bodySupport, bodySupport, Paper17.dist_supportMap]
  rfl

theorem dist_toSupport_bodySupport {n : ℕ} (P : DelzantSpace n) (K : PosBody n) :
    dist (toSupport P) (bodySupport K) = Metric.hausdorffDist P.carrier K.carrier := by
  change dist (Paper17.supportMap _) (Paper17.supportMap _) = _
  rw [Paper17.dist_supportMap]
  change Metric.hausdorffDist (toProduction P).carrier K.carrier = _
  rw [toProduction_carrier]

/-- The continuous, variable-error and locally finite-fan conclusions of
Proposition 4.3 follow from the density part of the original Lemma 4.2. -/
theorem controlled_approximation_of_density {X : Type} [MetricSpace X] {n : ℕ}
    (density : ∀ K : PosBody n, ∀ δ : ℝ, 0 < δ →
      ∃ P : DelzantSpace n, Metric.hausdorffDist P.carrier K.carrier < δ)
    (f : X → PosBody n) (hf : Continuous f)
    (ε : X → ℝ) (hε : Continuous ε) (hpos : ∀ x, 0 < ε x) :
    ∃ g : X → DelzantSpace n, Continuous g ∧
      (∀ x, Metric.hausdorffDist (g x).carrier (f x).carrier < ε x) ∧
      LocallyFiniteFansOn g Set.univ := by
  let e : DelzantSpace n ≃ₜ Set.range (@toSupport n) := isometry_toSupport.isEmbedding.toHomeomorph
  have happrox : ∀ x (δ : ℝ), 0 < δ → ∃ p ∈ Paper17.delzantSet n,
      dist p (bodySupport (f x)) < δ := by
    intro x δ hδ
    obtain ⟨P, hP⟩ := density (f x) δ hδ
    exact ⟨toSupport P, ⟨toProduction P, rfl⟩, by rw [dist_toSupport_bodySupport]; exact hP⟩
  obtain ⟨G, hGc, hGY, hGerr, hcontrol⟩ :=
    Paper17.continuous_approximation_by_chains (Paper17.delzantSet_nonempty n)
      (Paper17.delzant_extensionHypotheses n) (bodySupport ∘ f)
      (isometry_bodySupport.continuous.comp hf) ε hε hpos happrox
  have hGrange : ∀ x, G x ∈ Set.range (@toSupport n) := by
    intro x
    obtain ⟨P, hP⟩ := hGY x
    exact ⟨ofProduction P, (toSupport_ofProduction P).trans hP⟩
  let g : X → DelzantSpace n := fun x => e.symm ⟨G x, hGrange x⟩
  have hsupport : ∀ x, toSupport (g x) = G x := by
    intro x
    exact (isometry_toSupport.isEmbedding.toHomeomorph_apply_coe (g x)).symm.trans
      (congrArg Subtype.val (e.apply_symm_apply ⟨G x, hGrange x⟩))
  refine ⟨g, e.symm.continuous.comp (hGc.subtype_mk _), ?_, ?_⟩
  · intro x
    rw [← dist_toSupport_bodySupport, hsupport]
    exact hGerr x
  · intro x hx
    obtain ⟨U, hU, s, hsY, hs⟩ := hcontrol x hx
    refine ⟨U, hU, (finite_normalFans_convexHull s hsY).subset ?_⟩
    rintro C ⟨y, hy, rfl⟩
    refine ⟨g y, ?_, rfl⟩
    rw [hsupport]
    exact hs y hy

end P17Contract
