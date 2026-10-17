import Paper27.Geometry.FiniteGermNeighbourhood
import Paper27.Geometry.FiniteAnalyticGerm

/-!
# Actual isolated coordinate fibres and finite germ representatives

The source isolation below is proved for actual charts of a continuous map
with finite fibres. A separate universal classical finite mapping theorem
supplies arbitrarily small proper finite representatives of an analytic germ
with isolated centre fibre. It includes no critical-image or cyclic-normal-
form assertion. The own final argument supplies its input and then applies
the previously proved finite-branch uniqueness theorem.

The classical finite mapping theorem is the usual local finite mapping
theorem (Weierstrass preparation). Connectedness after removing the inverse
image of a graph is the general fact that deleting a proper analytic subset
from a connected complex manifold leaves it connected; see Dinh--Sibony,
*Dynamics in several complex variables*, Appendix A.1, Exercise A.1.4, p.117.
These general analytic facts remain explicit parameters.
-/
noncomputable section
open scoped Topology
namespace Paper27.Geometry.CoordinateFiniteGerms

section Topological
variable {X Y E H : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace E] [TopologicalSpace H] [CompactSpace X] [T2Space X] [T2Space Y]

/-- An isolated actual fibre stays isolated in actual source and target
coordinates. The proof also shrinks inside both chart domains. -/
theorem isolated_coordinate_fibre (q : X → Y) (hq : Continuous q)
    (hfinite : ∀ y, (q ⁻¹' {y}).Finite)
    (e : OpenPartialHomeomorph X E) (t : OpenPartialHomeomorph Y H)
    (p : X) (hp : p ∈ e.source) (hqp : q p ∈ t.source) :
    ∃ W : Set E, IsOpen W ∧ e p ∈ W ∧ W ⊆ e.target ∧
      (∀ z ∈ W, q (e.symm z) ∈ t.source) ∧
      {z | z ∈ W ∧ t (q (e.symm z)) = t (q (e.symm (e p)))} = {e p} := by
  obtain ⟨S⟩ := FiniteGermNeighbourhood.exists_fibre_isolation q hq (q p) (hfinite (q p))
  let i : q ⁻¹' {q p} := ⟨p, rfl⟩
  let O := S.source i ∩ q ⁻¹' t.source
  have hO : IsOpen O := (S.open_source i).inter (t.open_source.preimage hq)
  let W := e.target ∩ e.symm ⁻¹' O
  have hW : IsOpen W := e.isOpen_inter_preimage_symm hO
  have hpW : e p ∈ W := by
    refine ⟨e.map_source hp, ?_⟩
    change e.symm (e p) ∈ O
    rw [e.left_inv hp]
    exact ⟨S.point_mem i, hqp⟩
  refine ⟨W, hW, hpW, Set.inter_subset_left, fun z hz => hz.2.2, ?_⟩
  ext z
  constructor
  · rintro ⟨hz, heq⟩
    have hqp' : q (e.symm z) = q p := by
      apply t.injOn hz.2.2 hqp
      simpa only [e.left_inv hp] using heq
    have hsource : e.symm z = p :=
      (S.centre_fibre_source i).subset ⟨hz.2.1, hqp'⟩
    change z = e p
    calc
      z = e (e.symm z) := (e.right_inv hz.1).symm
      _ = e p := congrArg e hsource
  · intro hz
    have heq : z = e p := hz
    subst z
    exact ⟨hpW, rfl⟩

end Topological

/-- The local finite mapping theorem for arbitrary analytic maps of `ℂ²`.
The input is only an isolated actual centre fibre, and the output is raw
finite representative data. No branch image or classification is supplied. -/
def FiniteHolomorphicGermRepresentatives : Prop :=
  ∀ (F G : ℂ × ℂ → ℂ) (p : ℂ × ℂ),
    AnalyticAt ℂ F p → AnalyticAt ℂ G p →
    (∃ W : Set (ℂ × ℂ), IsOpen W ∧ p ∈ W ∧
      {z | z ∈ W ∧ (F z, G z) = (F p, G p)} = {p}) →
    ∀ (φ : ℂ → ℂ), AnalyticAt ℂ φ (F p) → φ (F p) = G p →
    ∀ (V : Set (ℂ × ℂ)), IsOpen V → p ∈ V →
    ∀ r : ℝ, 0 < r →
      ∃ A : FiniteAnalyticGerm.FiniteGermData F G p φ,
        A.radius ≤ r ∧ A.source ⊆ V

/-- The raw finite representative is now chosen, not left as an additional
per-pair hypothesis. Its critical image lies in the common graph by the own
normalization-cover and graph-uniqueness proof. -/
theorem cyclic_model_of_branch_cover
    (representatives : FiniteHolomorphicGermRepresentatives)
    (rigidity : BranchGraphs.IsometryFirstJetRigidity)
    (classification : FiniteAnalyticGerm.SmoothBranchFiniteCoverClassification)
    {F G : ℂ × ℂ → ℂ} {p : ℂ × ℂ} {ι : Type*} [Fintype ι]
    (C : FiniteAnalyticGerm.FiniteBranchCover F G p ι)
    (hF : AnalyticAt ℂ F p) (hG : AnalyticAt ℂ G p)
    (hsurj : Function.Surjective (fderiv ℂ F p)) (i₀ : ι)
    (hisolated : ∃ W : Set (ℂ × ℂ), IsOpen W ∧ p ∈ W ∧
      {z | z ∈ W ∧ (F z, G z) = (F p, G p)} = {p}) :
    ∃ B : CyclicModel.CyclicNormalForm F G p,
      B.graph = (C.branches i₀).graph.toFun := by
  obtain ⟨r, hr, hclassify⟩ := C.classify rigidity classification hF hG hsurj i₀
  let hgraph := C.branches i₀
  obtain ⟨A, hsmall, hsource⟩ := representatives F G p hF hG hisolated
    hgraph.graph.toFun (hgraph.graph.analytic _ hgraph.graph.centre_mem)
    (hgraph.value_at_centre hF hG) C.region C.open_region C.centre_mem r hr
  exact hclassify A hsmall hsource

theorem ramified_cyclic_model_of_branch_cover
    (representatives : FiniteHolomorphicGermRepresentatives)
    (rigidity : BranchGraphs.IsometryFirstJetRigidity)
    (classification : FiniteAnalyticGerm.SmoothBranchFiniteCoverClassification)
    {F G : ℂ × ℂ → ℂ} {p : ℂ × ℂ} {ι : Type*} [Fintype ι]
    (C : FiniteAnalyticGerm.FiniteBranchCover F G p ι)
    (hF : AnalyticAt ℂ F p) (hG : AnalyticAt ℂ G p)
    (hsurj : Function.Surjective (fderiv ℂ F p)) (i₀ : ι)
    (hisolated : ∃ W : Set (ℂ × ℂ), IsOpen W ∧ p ∈ W ∧
      {z | z ∈ W ∧ (F z, G z) = (F p, G p)} = {p})
    (hcrit : ¬ Function.Surjective (fderiv ℂ (fun z => (F z, G z)) p)) :
    ∃ B : CyclicModel.CyclicNormalForm F G p,
      B.graph = (C.branches i₀).graph.toFun ∧ 2 ≤ B.exponent := by
  obtain ⟨B, hB⟩ := cyclic_model_of_branch_cover representatives rigidity classification
    C hF hG hsurj i₀ hisolated
  exact ⟨B, hB, B.exponent_ge_two hcrit⟩

end Paper27.Geometry.CoordinateFiniteGerms
