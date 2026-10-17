import Paper28
import Paper28.TreeBranches
import Paper28.FoldingDifferential
set_option autoImplicit false
noncomputable section
open Paper28 WithLp SimpleGraph Filter
open scoped InnerProductSpace
namespace Verification.Certificate

section

theorem complementary_sqrt_bound (a b : ℝ) (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1)
    (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1) :
    Real.sqrt (a * b) + Real.sqrt ((1 - a) * (1 - b)) ≤ 1 := by
  sorry

theorem complementary_det_bound (D : Matrix (Fin 2) (Fin 2) ℝ)
    (hD : D.PosSemidef) (hC : (1 - D).PosSemidef) :
    Real.sqrt D.det + Real.sqrt (1 - D).det ≤ 1 := by
  sorry

theorem two_gram_det_bound (D E : Matrix (Fin 2) (Fin 2) ℝ)
    (hD : D.PosSemidef) (hE : E.PosSemidef) (hDE : D + E = 1) :
    Real.sqrt D.det + Real.sqrt E.det ≤ 1 := by
  sorry
end

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]

theorem orthogonal_slice_dim (E W : Submodule ℝ H)
    (hE : 4 ≤ Module.finrank ℝ E) (hW : Module.finrank ℝ W ≤ 2) :
    2 ≤ Module.finrank ℝ (E ⊓ Wᗮ : Submodule ℝ H) := by
  sorry
end

section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

theorem finiteShadow_sq (branch : ι → κ) (u : EuclideanSpace ℝ ι) (b : κ) :
    finiteShadow branch u b ^ 2 =
      ∑ i ∈ Finset.univ.filter (fun i => branch i = b), u i ^ 2 := by
  sorry

theorem finiteShadow_norm (branch : ι → κ) (u : EuclideanSpace ℝ ι) :
    ‖finiteShadow branch u‖ = ‖u‖ := by
  sorry

theorem finiteShadow_nonneg (branch : ι → κ) (u : EuclideanSpace ℝ ι) (b : κ) :
    0 ≤ finiteShadow branch u b := by
  sorry

theorem branch_inner_le (s : Finset ι) (u v : ι → ℝ) :
    ∑ i ∈ s, u i * v i ≤
      Real.sqrt (∑ i ∈ s, u i ^ 2) * Real.sqrt (∑ i ∈ s, v i ^ 2) := by
  sorry

theorem finiteShadow_inner (branch : ι → κ) (u v : EuclideanSpace ℝ ι) :
    ⟪u, v⟫_ℝ ≤ ⟪finiteShadow branch u, finiteShadow branch v⟫_ℝ := by
  sorry

theorem finiteShadow_angular (branch : ι → κ) (u v : EuclideanSpace ℝ ι) :
    angular (finiteShadow branch u) (finiteShadow branch v) ≤ angular u v := by
  sorry
end

section
variable {G : Type*} [Group G] [DecidableEq G]

theorem mem_overlapTranslations (F F' : Finset G) (γ : G) :
    γ ∈ overlapTranslations F F' ↔ ∃ x ∈ F, ∃ y ∈ F', x = γ * y := by
  sorry

theorem finite_overlapTranslations (F F' : Finset G) :
    {γ : G | ∃ x ∈ F, ∃ y ∈ F', x = γ * y}.Finite := by
  sorry

theorem finiteRegularCoefficient_eq_zero (u v : G →₀ ℝ) (γ : G)
    (hγ : γ ∉ overlapTranslations u.support v.support) :
    finiteRegularCoefficient u v γ = 0 := by
  sorry

theorem finiteRegularCoefficient_eventually_zero (u v : G →₀ ℝ) :
    ∀ᶠ γ in Filter.cofinite, finiteRegularCoefficient u v γ = 0 := by
  sorry
end

section
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]

theorem hasFDerivAt_hilbertNorm (u : K) (hu : u ≠ 0) :
    HasFDerivAt (fun x : K => ‖x‖) (hilbertNormDerivative u) u := by
  sorry

theorem normFoldDerivative_apply (u h : WithLp 2 (H × K)) :
    normFoldDerivative u h = toLp 2 (h.fst, ⟪u.snd, h.snd⟫_ℝ / ‖u.snd‖) := by
  sorry

theorem hasFDerivAt_normFold (u : WithLp 2 (H × K)) (hu : u.snd ≠ 0) :
    HasFDerivAt normFold (normFoldDerivative u) u := by
  sorry

theorem normFoldDerivative_orthogonal (u h : WithLp 2 (H × K))
    (hh : ⟪u.snd, h.snd⟫_ℝ = 0) :
    normFoldDerivative u h = toLp 2 (h.fst, 0) := by
  sorry

theorem normFoldDerivative_norm_le (u h : WithLp 2 (H × K)) (hu : u.snd ≠ 0) :
    ‖normFoldDerivative u h‖ ≤ ‖h‖ := by
  sorry
variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]

theorem hasFDerivAt_leftFold (u : Triple H₁ H₂) (hu : u.snd ≠ 0) :
    HasFDerivAt leftFold (normFoldDerivative u) u := by
  sorry

theorem hasFDerivAt_rightFold (u : Triple H₁ H₂) (hu : (reverseTriple u).snd ≠ 0) :
    HasFDerivAt rightFold (rightFoldDerivative u) u := by
  sorry

theorem folding_differential_inner_add (u v w : Triple H₁ H₂)
    (htv : ⟪u, v⟫_ℝ = 0) (htw : ⟪u, w⟫_ℝ = 0)
    (hxv : ⟪u.fst, v.fst⟫_ℝ = 0) (hxw : ⟪u.fst, w.fst⟫_ℝ = 0)
    (hzv : v.snd.fst = 0) (hzw : w.snd.fst = 0) :
    ⟪normFoldDerivative u v, normFoldDerivative u w⟫_ℝ +
      ⟪rightFoldDerivative u v, rightFoldDerivative u w⟫_ℝ = ⟪v, w⟫_ℝ := by
  sorry

theorem folding_differential_two_area_le_one (u : Triple H₁ H₂)
    (e : Fin 2 → Triple H₁ H₂) (he : Orthonormal ℝ e)
    (ht : ∀ i, ⟪u, e i⟫_ℝ = 0)
    (hx : ∀ i, ⟪u.fst, (e i).fst⟫_ℝ = 0) (hz : ∀ i, (e i).snd.fst = 0) :
    Real.sqrt (Matrix.gram ℝ (fun i => normFoldDerivative u (e i))).det +
      Real.sqrt (Matrix.gram ℝ (fun i => rightFoldDerivative u (e i))).det ≤ 1 := by
  sorry
end

section

theorem infimum_joint_lower_bound (A B C : Set ℝ)
    (hA : BddBelow A) (hB : BddBelow B) (hC : C.Nonempty)
    (hjoint : ∀ c ∈ C, ∀ ε : ℝ, 0 < ε →
      ∃ a ∈ A, ∃ b ∈ B, a + b ≤ c + ε) :
    sInf A + sInf B ≤ sInf C := by
  sorry

theorem infimum_additivity_of_joint_approximation (A B C : Set ℝ)
    (hA : BddBelow A) (hB : BddBelow B) (hC : BddBelow C)
    (hneA : A.Nonempty) (hneB : B.Nonempty) (hneC : C.Nonempty)
    (hglue : ∀ a ∈ A, ∀ b ∈ B, ∃ c ∈ C, c ≤ a + b)
    (hjoint : ∀ c ∈ C, ∀ ε : ℝ, 0 < ε →
      ∃ a ∈ A, ∃ b ∈ B, a + b ≤ c + ε) :
    sInf C = sInf A + sInf B := by
  sorry
end

section
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]

theorem normFold_norm (u : WithLp 2 (H × K)) : ‖normFold u‖ = ‖u‖ := by
  sorry

theorem normFold_inner (u v : WithLp 2 (H × K)) :
    ⟪u, v⟫_ℝ ≤ ⟪normFold u, normFold v⟫_ℝ := by
  sorry

theorem normFold_angular (u v : WithLp 2 (H × K)) :
    angular (normFold u) (normFold v) ≤ angular u v := by
  sorry

theorem normFold_dist (u v : WithLp 2 (H × K)) :
    dist (normFold u) (normFold v) ≤ dist u v := by
  sorry
variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]

theorem leftFold_formula (u : Triple H₁ H₂) :
    leftFold u = toLp 2 (u.fst, Real.sqrt (u.snd.fst ^ 2 + ‖u.snd.snd‖ ^ 2)) := by
  sorry

theorem rightFold_formula (u : Triple H₁ H₂) :
    rightFold u = toLp 2 (u.snd.snd, Real.sqrt (u.snd.fst ^ 2 + ‖u.fst‖ ^ 2)) := by
  sorry

theorem reverseTriple_norm (u : Triple H₁ H₂) : ‖reverseTriple u‖ = ‖u‖ := by
  sorry

theorem reverseTriple_inner (u v : Triple H₁ H₂) :
    ⟪reverseTriple u, reverseTriple v⟫_ℝ = ⟪u, v⟫_ℝ := by
  sorry

theorem leftFold_norm (u : Triple H₁ H₂) : ‖leftFold u‖ = ‖u‖ := by
  sorry

theorem rightFold_norm (u : Triple H₁ H₂) : ‖rightFold u‖ = ‖u‖ := by
  sorry

theorem leftFold_angular (u v : Triple H₁ H₂) :
    angular (leftFold u) (leftFold v) ≤ angular u v := by
  sorry

theorem rightFold_angular (u v : Triple H₁ H₂) :
    angular (rightFold u) (rightFold v) ≤ angular u v := by
  sorry
end

section
variable {V : Type*} (T : SimpleGraph V)

theorem firstNeighbor_eq_iff_avoiding (hT : T.IsTree) (v a : V) (ha : a ≠ v)
    (w : T.neighborSet v) :
    firstNeighbor T hT v a ha = w ↔
      ∃ p : T.Walk w.val a, v ∉ p.support := by
  sorry

theorem avoiding_iff_deleted_reachable (v a b : V) (ha : a ≠ v) (hb : b ≠ v) :
    (∃ p : T.Walk a b, v ∉ p.support) ↔
      (T.induce {x | x ≠ v}).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
  sorry

theorem firstNeighbor_eq_iff_deleted_reachable (hT : T.IsTree)
    (v a : V) (ha : a ≠ v) (w : T.neighborSet v) :
    firstNeighbor T hT v a ha = w ↔
      (T.induce {x | x ≠ v}).Reachable
        ⟨w.val, w.property.ne.symm⟩ ⟨a, ha⟩ := by
  sorry

theorem treeBranch_eq_iff_deleted_reachable (hT : T.IsTree) (v : V)
    (e : T.edgeSet) (w : T.neighborSet v) :
    treeBranch T hT v e = w ↔
      (T.induce {x | x ≠ v}).Reachable
        ⟨w.val, w.property.ne.symm⟩
        ⟨(edgeTarget T v e).val, (edgeTarget T v e).property.2⟩ := by
  sorry

theorem deleted_adj_reachable (v a b : V) (hab : T.Adj a b)
    (ha : a ≠ v) (hb : b ≠ v) :
    (T.induce {x | x ≠ v}).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
  sorry

theorem firstNeighbor_adj (hT : T.IsTree) (v a b : V)
    (hab : T.Adj a b) (ha : a ≠ v) (hb : b ≠ v) :
    firstNeighbor T hT v a ha = firstNeighbor T hT v b hb := by
  sorry

theorem treeBranch_eq_firstNeighbor_endpoint (hT : T.IsTree) (v : V)
    (e : T.edgeSet) (a : V) (hae : a ∈ e.val) (ha : a ≠ v) :
    treeBranch T hT v e = firstNeighbor T hT v a ha := by
  sorry

theorem treeBranch_endpoint_component (hT : T.IsTree) (v : V)
    (e : T.edgeSet) (a : V) (hae : a ∈ e.val) (ha : a ≠ v) (w : T.neighborSet v) :
    treeBranch T hT v e = w ↔
      (T.induce {x | x ≠ v}).Reachable ⟨w.val, w.property.ne.symm⟩ ⟨a, ha⟩ := by
  sorry
variable [Fintype V] [DecidableEq V] [DecidableRel T.Adj]

theorem treeBranchEdge_eq_iff (hT : T.IsTree) (v : V) (a : T.edgeSet)
    (e : T.incidenceSet v) :
    treeBranchEdge T hT v a = e ↔
      treeBranch T hT v a = T.incidenceSetEquivNeighborSet v e := by
  sorry

theorem vertexShadowOnEdges_formula (hT : T.IsTree) (v : V)
    (u : EuclideanSpace ℝ T.edgeSet) (e : T.incidenceSet v) :
    vertexShadowOnEdges T hT v u e = Real.sqrt
      (∑ a ∈ Finset.univ.filter (fun a => treeBranchEdge T hT v a = e), u a ^ 2) := by
  sorry

theorem vertexShadow_branch_component (hT : T.IsTree) (v : V)
    (a : T.edgeSet) (x : V) (hxa : x ∈ a.val) (hx : x ≠ v) (e : T.incidenceSet v) :
    treeBranchEdge T hT v a = e ↔
      (T.induce {y | y ≠ v}).Reachable
        ⟨(T.incidenceSetEquivNeighborSet v e).val,
          (T.incidenceSetEquivNeighborSet v e).property.ne.symm⟩ ⟨x, hx⟩ := by
  sorry

theorem vertexShadowOnEdges_norm (hT : T.IsTree) (v : V)
    (u : EuclideanSpace ℝ T.edgeSet) : ‖vertexShadowOnEdges T hT v u‖ = ‖u‖ := by
  sorry

theorem vertexShadowOnEdges_angular (hT : T.IsTree) (v : V)
    (u w : EuclideanSpace ℝ T.edgeSet) :
    angular (vertexShadowOnEdges T hT v u) (vertexShadowOnEdges T hT v w) ≤ angular u w := by
  sorry
end

section
variable {V : Type*} (T : SimpleGraph V)

theorem treePath_isPath (hT : T.IsTree) (v w : V) :
    (treePath T hT v w).IsPath := by
  sorry

theorem treeBranch_incident (hT : T.IsTree) (v w : V) (hvw : T.Adj v w) :
    (treeBranch T hT v ⟨s(v, w), hvw⟩).val = w := by
  sorry
variable [Fintype V] [DecidableEq V] [DecidableRel T.Adj]

theorem vertexShadow_formula (hT : T.IsTree) (v : V)
    (u : EuclideanSpace ℝ T.edgeSet) (e : T.neighborSet v) :
    vertexShadow T hT v u e = Real.sqrt
      (∑ a ∈ Finset.univ.filter (fun a => treeBranch T hT v a = e), u a ^ 2) := by
  sorry

theorem vertexShadow_norm (hT : T.IsTree) (v : V) (u : EuclideanSpace ℝ T.edgeSet) :
    ‖vertexShadow T hT v u‖ = ‖u‖ := by
  sorry

theorem vertexShadow_angular (hT : T.IsTree) (v : V) (u w : EuclideanSpace ℝ T.edgeSet) :
    angular (vertexShadow T hT v u) (vertexShadow T hT v w) ≤ angular u w := by
  sorry
end

section
open WithLp MeasureTheory
open scoped InnerProductSpace
universe u v
variable {H₁ H₂ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
  [FiniteDimensional ℝ H₁] [FiniteDimensional ℝ H₂]
  [MeasurableSpace (Triple H₁ H₂)]
variable (I : RectifiableSphereCalculusInput.{u,v} (Triple H₁ H₂))

theorem lemma_2_1 (hFischer : FischerInput) (n : ℕ) (hn : 4 ≤ n) (C : I.Current n) :
    ∀ᵐ x ∂I.massMeasure C,
      currentJacobian I leftFold C x + currentJacobian I rightFold C x ≤ 1 := by
  sorry
end

section
open SimpleGraph MeasureTheory
open scoped InnerProductSpace
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type u} [Fintype V] [DecidableEq V]
  (T : SimpleGraph V) [DecidableRel T.Adj]
  [MeasurableSpace (EuclideanSpace ℝ T.edgeSet)]
  (I : RectifiableSphereCalculusInput.{u,v} (EuclideanSpace ℝ T.edgeSet))

theorem lemma_2_3 (hFischer : FischerInput) (hT : T.IsTree)
    (n : ℕ) (hn : 4 ≤ n) (C : I.Current n) :
    ∀ᵐ z ∂I.massMeasure C,
      (∑ x, currentJacobian I (vertexShadowOnEdges T hT x) C z) ≤ 1 := by
  sorry
end

section
open Set
universe u v
variable {G : Type u} [Group G] [DecidableEq G] [Countable G]

theorem lemma_5_1 (M : SphericalQuotientMetricInput G)
    (I : CompactIntegralCurrentSupportInput.{u,v} (RegularOrbitQuotient G) M.metric)
    (S : SphericalSimplexIntegrationInput M I)
    (K : Set (RegularOrbitQuotient G)) (hK : IsCompact K)
    (k : ℕ) (C : I.Current k) (hC : C ∈ sphericalPolyhedralCurrents S k)
    (_hZK : I.support C ⊆ K) (η : ℝ) (hη : 0 < η) :
    letI := M.metric
    Nonempty (RelativeCarrierDeformation K (I.support C) ⟨1+η,by linarith⟩) := by
  sorry
end

section
open Filter
open scoped Topology

theorem lemma_5_2
    {Y : Type} [metricY : MetricSpace Y] (P : FiniteSphericalPolyhedron Y)
    (J : CompactIntegralCurrentAlgebraInput.{0,0} Y metricY)
    (Jc : ∀ j : Fin P.componentCount, CompactIntegralCurrentAlgebraInput.{0,0} (P.component j) inferInstance)
    (D : ComponentCurrentDecompositionInput P J Jc)
    (A : ∀ j, LipschitzSimplexIntegrationInput inferInstance (Jc j))
    (Foundations : ∀ j {e : ℕ} (K₁ : FiniteEuclideanComplex (EuclideanAmbient e))
      (N : SphericalNeighborhoodRealization (P.triangulation j) K₁),
      Nonempty (SphericalPolyhedronCurrentFoundations N (P.point j) (Jc j) (A j)))
    (PL : SphericalFullNeighborhoodInput) (Ref : SphericalFiniteRefinementInput)
    (RS : ∀ j, LipschitzCurrentHomologyComparisonInput (Jc j) (A j))
    (SS : SimplicialSingularHomologyComparisonInput) (k : ℕ) :
    (∀ Z : J.Current (k+1), J.boundary k Z = 0 →
      ∃ Zi : ℕ → J.Current (k+1), ∃ Wi : ℕ → J.Current (k+2),
        (∀ i, Zi i ∈ finiteSphericalPolyhedralCurrents P D A (k+1)) ∧
        (∀ i, J.boundary k (Zi i) = 0) ∧
        (∀ i, Z-Zi i = J.boundary (k+1) (Wi i)) ∧
        Tendsto (fun i => J.mass (Wi i)) atTop (𝓝 0) ∧
        Tendsto (fun i => J.mass (Zi i)) atTop (𝓝 (J.mass Z))) ∧
    (∀ Z : J.Current (k+1), Z ∈ finiteSphericalPolyhedralCurrents P D A (k+1) →
      (∃ W : J.Current (k+2), J.boundary (k+1) W = Z) →
      ∃ Q : J.Current (k+2), Q ∈ finiteSphericalPolyhedralCurrents P D A (k+2) ∧
        J.boundary (k+1) Q = Z) := by
  sorry
end

section
open Set Filter
open scoped Topology
variable {G : Type} [Group G] [DecidableEq G] [Countable G]
  (M : SphericalQuotientMetricInput G)
  (I : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient G) M.metric)
  (S : SphericalSimplexIntegrationInput M I.toCompactIntegralCurrentSupportInput)
  (Geometry : FiniteRoundQuotientRealizationInput) (AK : FiniteRoundCurrentTransportInput)
  (PL : SphericalFullNeighborhoodInput) (Ref : SphericalFiniteRefinementInput)
  (SS : SimplicialSingularHomologyComparisonInput)

include Geometry AK PL Ref SS in
theorem lemma_3_1 (Push : CanonicalLocalPushforwardInput I) (H : CompactCurrentHomotopyInput I) (k : ℕ) :
    (∀ C : I.Current (k+1), I.boundary k C = 0 → ∀ ε : ℝ, 0 < ε →
      ∃ P : I.Current (k+1), ∃ D : I.Current (k+2),
        P ∈ sphericalPolyhedralCurrents S (k+1) ∧ I.boundary k P = 0 ∧
        C-P = I.boundary (k+1) D ∧ I.mass P ≤ I.mass C+ε) ∧
    (∀ Z : I.Current (k+1), Z ∈ sphericalPolyhedralCurrents S (k+1) →
      (∃ C : I.Current (k+2), I.boundary (k+1) C = Z) →
      ∃ Q : I.Current (k+2), Q ∈ sphericalPolyhedralCurrents S (k+2) ∧ I.boundary (k+1) Q = Z) := by
  sorry
end

section
variable {G : Type} [Group G] [DecidableEq G] [Countable G]
  {M : SphericalQuotientMetricInput G}
  {I : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient G) M.metric}
  {J : CompactIntegralCurrentAlgebraInput.{0,0} (RegularSphere G) inferInstance}
  (S : SphericalSimplexIntegrationInput M I.toCompactIntegralCurrentSupportInput)
  (L : LiftedSphericalSimplexIntegrationInput (M := M) J) (F : CanonicalGlobalCurrentCalculusInput)
  {A B : Subgroup G}
  (MA : SphericalQuotientMetricInput A) (MB : SphericalQuotientMetricInput B)
  (IA : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient A) MA.metric)
  (IB : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient B) MB.metric)
  (Gluing : SphericalCurrentGluingInput S L F)
  (FaithfulA : CurrentMassFaithfulnessInput IA) (FaithfulB : CurrentMassFaithfulnessInput IB)
  (Area : FiniteCoordinateCurrentAreaInput J) (Mass : GeodesicPolyhedralMassInput)

include Area Mass in
theorem proposition_3_2 (Fischer : FischerInput) (Free : IsFreeProductOfSubgroups A B)
    (BS : BassSerreStructureInput) : ∃ T : BassSerreObject A B,
    (∀ k (σ : LiftableSphericalSimplex M (k+1)),
      bassSerreTransferA L F T MA IA S Gluing FaithfulA k (projectedSphericalGenerator S (k+1) σ) =
        (bassSerreShadowFamilyA T MA J IA F FaithfulA k (liftedSphericalGenerator L (k+1) σ)).sum (fun _ C => C) ∧
      bassSerreTransferB L F T MB IB S Gluing FaithfulB k (projectedSphericalGenerator S (k+1) σ) =
        (bassSerreShadowFamilyB T MB J IB F FaithfulB k (liftedSphericalGenerator L (k+1) σ)).sum (fun _ C => C)) ∧
    (∀ k (P : sphericalPolyhedralCurrents S (k+2)),
      IA.boundary (k+1) (bassSerreTransferA L F T MA IA S Gluing FaithfulA (k+1) P) =
        bassSerreTransferA L F T MA IA S Gluing FaithfulA k (sphericalPolyhedralBoundary S L F Gluing (k+1) P) ∧
      IB.boundary (k+1) (bassSerreTransferB L F T MB IB S Gluing FaithfulB (k+1) P) =
        bassSerreTransferB L F T MB IB S Gluing FaithfulB k (sphericalPolyhedralBoundary S L F Gluing (k+1) P)) ∧
    (∀ k, 4 ≤ k+1 → ∀ P : sphericalPolyhedralCurrents S (k+1),
      IA.mass (bassSerreTransferA L F T MA IA S Gluing FaithfulA k P)+
        IB.mass (bassSerreTransferB L F T MB IB S Gluing FaithfulB k P) ≤ I.mass P.val) := by
  sorry
end

section
variable (Std : PaperStandardInputs) {G : Type} [Group G] [DecidableEq G] [Countable G]
  {A B : Subgroup G}
  (DG : SphericalQuotientCurrentData Std.currentCalculus G)
  (DA : SphericalQuotientCurrentData Std.currentCalculus A)
  (DB : SphericalQuotientCurrentData Std.currentCalculus B)

theorem theorem_1_1 (Free : IsFreeProductOfSubgroups A B) (k : ℕ)
    (α : Std.groupHomology.group A (k+4)) (β : Std.groupHomology.group B (k+4)) :
    groupSphericalVolume Std.groupHomology Std.currentCalculus Std.song DG.M DG.algebra (k+3)
      (Std.groupHomology.map A.subtype (k+4) α+Std.groupHomology.map B.subtype (k+4) β) =
      groupSphericalVolume Std.groupHomology Std.currentCalculus Std.song DA.M DA.algebra (k+3) α+
      groupSphericalVolume Std.groupHomology Std.currentCalculus Std.song DB.M DB.algebra (k+3) β := by
  sorry
end

section
variable (Std : PaperStandardInputs) (Objects : ManifoldTopologyObjectsInput Std.groupHomology)

theorem corollary_1_2 (Topology : ConnectedSumTopologyInput Std.groupHomology Objects)
    (k : ℕ) (M N : ClosedConnectedManifold (k+4)) (oM : Objects.Orientation M) (oN : Objects.Orientation N) :
    let CS := standardConnectedSumModel Objects M N oM oN Topology (by omega : 3 ≤ k+4)
    ∀ (DG : SphericalQuotientCurrentData Std.currentCalculus CS.group)
      (DA : SphericalQuotientCurrentData Std.currentCalculus CS.leftFactor)
      (DB : SphericalQuotientCurrentData Std.currentCalculus CS.rightFactor),
    manifoldSphericalVolume Std Objects k (Objects.connectedSum M N oM oN).1 (Objects.connectedSum M N oM oN).2
      DG CS.sumFundamentalGroup =
      manifoldSphericalVolume Std Objects k M oM DA CS.leftFundamentalGroup+
        manifoldSphericalVolume Std Objects k N oN DB CS.rightFundamentalGroup := by
  sorry
end

end Verification.Certificate
