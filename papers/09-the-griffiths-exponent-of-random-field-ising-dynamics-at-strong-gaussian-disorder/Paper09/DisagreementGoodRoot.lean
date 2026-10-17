import Paper09.Disagreement
import Paper09.DisagreementTailSum
import Paper09.DisagreementUniforms

open Finset BigOperators Classical MeasureTheory ProbabilityTheory
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

namespace Paper09.DisagreementGoodRoot

/-- Injective graph maps which preserve open sites embed the actual open cluster,
including its finite cardinality events. -/
theorem clusterAtLeast_map {V W : Type*} [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V → W) (hf : Function.Injective f)
    (hadj : ∀ ⦃x y⦄, G.Adj x y → H.Adj (f x) (f y))
    (ω : V → Prop) (ω' : W → Prop) (hopen : ∀ x, ω x → ω' (f x))
    (y : V) (r : ℕ) (hr : Percolation.clusterAtLeast G ω y r) :
    Percolation.clusterAtLeast H ω' (f y) r := by
  let F : Percolation.openGraph G ω →g Percolation.openGraph H ω' := {
    toFun := f
    map_rel' := by
      intro x z hxz
      exact ⟨hadj hxz.1, hopen x hxz.2.1, hopen z hxz.2.2⟩ }
  obtain ⟨S, hS, hsub⟩ := hr
  refine ⟨S.image f, ?_, ?_⟩
  · rw [card_image_of_injective S hf, hS]
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
    have hc := hsub hx
    exact ⟨hopen y hc.1, hc.2.map F⟩

variable {V : Type*} [Fintype V]

/-- The finite exploration's ordinary cluster event is a literal subset of the
source infinite-lattice cluster event under the actual shared uniforms. -/
theorem uniformMarks_clusterAtLeast {d : ℕ} (Λ : Lattice V)
    (h : LatticeGeometry.Point d → ℝ) (K ρ : ℝ)
    (f : V → LatticeGeometry.Point d) (hf : Function.Injective f)
    (hadj : ∀ ⦃x z⦄, Λ.adj x z → LatticeGeometry.Adj (f x) (f z))
    (U : Finset V) (u : LatticeGeometry.Point d → ℝ) (y : V) (r : ℕ)
    (hr : Percolation.clusterAtLeast (Disagreement.latticeGraph Λ)
      (fun x => DisagreementUniforms.uniformMarks (fun z => h (f z)) K ρ f U u x = true) y r) :
    Percolation.clusterAtLeast (Percolation.nnGraph d) (Percolation.siteOpen K ρ h u) (f y) r := by
  apply clusterAtLeast_map (Disagreement.latticeGraph Λ) (Percolation.nnGraph d) f hf
    hadj _ _ _ y r hr
  intro x hx
  exact ((DisagreementUniforms.uniformMarks_true h K ρ f U u x).mp hx).2

/-- A true good label controls the finite ordinary-cluster tail for every
embedded finite graph, with no finite-tail certificate supplied as a premise. -/
theorem ordinary_cluster_tail {d : ℕ} (Λ : Lattice V)
    (h : LatticeGeometry.Point d → ℝ) (K ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (f : V → LatticeGeometry.Point d) (hf : Function.Injective f)
    (hadj : ∀ ⦃x z⦄, Λ.adj x z → LatticeGeometry.Adj (f x) (f z))
    (U : Finset V) (y : V) (R r₀ s : ℕ) (v : LatticeGeometry.Point d)
    (hgood : Percolation.goodLabel K ρ R r₀ s h v)
    (hy : f y ∈ Percolation.latticeCube (Percolation.coarseCenter R v) R)
    (r : ℕ) (hr₀ : r₀ ≤ r) (hrs : r ≤ s) :
    (DisagreementMarks.productMarks
      (DisagreementUniforms.openingParameter (fun z => h (f z)) K ρ)
      (DisagreementUniforms.openingParameter_nonneg _ K ρ hρ)
      (DisagreementUniforms.openingParameter_le_one _ K ρ hρ1) U).expect
      (fun ω => if Percolation.clusterAtLeast (Disagreement.latticeGraph Λ)
        (fun z => ω z = true) y r then 1 else 0) ≤ Real.exp (-(r : ℝ)) := by
  rw [← DisagreementUniforms.uniformMarks_event (fun z => h (f z)) K ρ hρ hρ1 f hf U]
  calc
    (Percolation.noiseLaw d).real {u |
      Percolation.clusterAtLeast (Disagreement.latticeGraph Λ)
        (fun z => DisagreementUniforms.uniformMarks (fun x => h (f x)) K ρ f U u z = true) y r}
      ≤ (Percolation.noiseLaw d).real {u |
        Percolation.clusterAtLeast (Percolation.nnGraph d) (Percolation.siteOpen K ρ h u) (f y) r} := by
          exact measureReal_mono
            (fun u hu => uniformMarks_clusterAtLeast Λ h K ρ f hf hadj U u y r hu) (by finiteness)
    _ ≤ Real.exp (-(r : ℝ)) := hgood (f y) hy r hr₀ hrs

/-- Forcing an exterior root open loses at most the factor `1/rho` in (3.9).
The ordinary tail is obtained from the actual source good label and uniforms. -/
theorem forced_cluster_tail {d : ℕ} (Λ : Lattice V)
    (h : LatticeGeometry.Point d → ℝ) (K ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (f : V → LatticeGeometry.Point d) (hf : Function.Injective f)
    (hadj : ∀ ⦃x z⦄, Λ.adj x z → LatticeGeometry.Adj (f x) (f z))
    (U : Finset V) (y : V) (hyU : y ∉ U) (R r₀ s : ℕ) (v : LatticeGeometry.Point d)
    (hgood : Percolation.goodLabel K ρ R r₀ s h v)
    (hy : f y ∈ Percolation.latticeCube (Percolation.coarseCenter R v) R)
    (r : ℕ) (hr : 0 < r) (hr₀ : r₀ ≤ r) (hrs : r ≤ s) :
    (DisagreementMarks.productMarks
      (DisagreementUniforms.openingParameter (fun z => h (f z)) K ρ)
      (DisagreementUniforms.openingParameter_nonneg _ K ρ hρ.le)
      (DisagreementUniforms.openingParameter_le_one _ K ρ hρ1) U).expect
      (fun ω => if r ≤ Disagreement.forcedClusterCard Λ ω y then 1 else 0)
      ≤ ρ⁻¹ * Real.exp (-(r : ℝ)) := by
  let θ := DisagreementUniforms.openingParameter (fun z => h (f z)) K ρ
  have hθy : ρ ≤ θ y := by unfold θ DisagreementUniforms.openingParameter; split_ifs <;> linarith
  rw [Disagreement.forced_cluster_probability Λ θ
    (DisagreementUniforms.openingParameter_nonneg _ K ρ hρ.le)
    (DisagreementUniforms.openingParameter_le_one _ K ρ hρ1) U y hyU (hρ.trans_le hθy) r hr]
  have ht := ordinary_cluster_tail Λ h K ρ hρ.le hρ1 f hf hadj (insert y U) y
    R r₀ s v hgood hy r hr₀ hrs
  calc
    _ ≤ Real.exp (-(r : ℝ)) / θ y := div_le_div_of_nonneg_right ht (hρ.trans_le hθy).le
    _ ≤ Real.exp (-(r : ℝ)) / ρ :=
      div_le_div_of_nonneg_left (Real.exp_nonneg _) hρ hθy
    _ = ρ⁻¹ * Real.exp (-(r : ℝ)) := by ring

/-- An explicit source-label bound on the actual expected truncated forced
cluster, valid uniformly in the finite domain and the cutoff `N`. -/
theorem expected_forced_cluster {d : ℕ} (Λ : Lattice V)
    (h : LatticeGeometry.Point d → ℝ) (K ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (f : V → LatticeGeometry.Point d) (hf : Function.Injective f)
    (hadj : ∀ ⦃x z⦄, Λ.adj x z → LatticeGeometry.Adj (f x) (f z))
    (U : Finset V) (y : V) (hyU : y ∉ U) (R r₀ s N : ℕ) (v : LatticeGeometry.Point d)
    (hr₀ : 0 < r₀) (hrs : r₀ ≤ s)
    (hgood : Percolation.goodLabel K ρ R r₀ s h v)
    (hy : f y ∈ Percolation.latticeCube (Percolation.coarseCenter R v) R) :
    (DisagreementMarks.productMarks
      (DisagreementUniforms.openingParameter (fun z => h (f z)) K ρ)
      (DisagreementUniforms.openingParameter_nonneg _ K ρ hρ.le)
      (DisagreementUniforms.openingParameter_le_one _ K ρ hρ1) U).expect
      (fun ω => (min N (Disagreement.forcedClusterCard Λ ω y) : ℝ)) ≤
        (r₀ : ℝ) + 2 / ρ + (N : ℝ) / ρ * Real.exp (-(s : ℝ)) := by
  apply Disagreement.expected_truncated_of_exponential_tail_two _ _ N r₀ s ρ hρ hr₀ hrs
  intro r hr hr₀' hrs'
  exact forced_cluster_tail Λ h K ρ hρ hρ1 f hf hadj U y hyU R r₀ s v hgood hy r hr hr₀' hrs'

/-- The actual conditionally pinned Gibbs influence bound with the explicit
source good-label constant. Only the original degree, disorder and label
hypotheses remain; no cluster-tail bound is supplied by the caller. -/
theorem gibbs_conditional_influence_good {d : ℕ} (Λ : Lattice V)
    (h : LatticeGeometry.Point d → ℝ) (β K : ℝ)
    (f : V → LatticeGeometry.Point d) (hf : Function.Injective f)
    (hadj : ∀ ⦃x z⦄, Λ.adj x z → LatticeGeometry.Adj (f x) (f z))
    (B T E : Finset V) (hBT : Disjoint B T) (hEB : E ⊆ B)
    (φ φ' τ τ' : Config V) (y : V) (hyU : y ∉ B \ E)
    (hβ : 0 ≤ β) (hdeg : (Λ.maxDegree : ℝ) ≤ 2 * (d : ℝ))
    (hsource : ∀ r ∈ E, τ r ≠ τ' r → r = y)
    (hboundary : ∀ r ∈ T, φ r ≠ φ' r → r = y)
    (R r₀ s : ℕ) (v : LatticeGeometry.Point d) (hr₀ : 0 < r₀) (hrs : r₀ ≤ s)
    (hgood : Percolation.goodLabel K (rho K (d : ℝ) β) R r₀ s h v)
    (hy : f y ∈ Percolation.latticeCube (Percolation.coarseCenter R v) R) :
    hammingWasserstein
      (Disagreement.condition (gibbs Λ (fun z => h (f z)) β B T φ)
        (Disagreement.gibbs_positive Λ _ β B T φ) E τ)
      (Disagreement.condition (gibbs Λ (fun z => h (f z)) β B T φ')
        (Disagreement.gibbs_positive Λ _ β B T φ') E τ') ≤
      (defectCount E τ' τ : ℝ) + (r₀ : ℝ) + 2 / rho K (d : ℝ) β +
        ((B \ E).card : ℝ) / rho K (d : ℝ) β * Real.exp (-(s : ℝ)) := by
  have hbase := Disagreement.gibbs_conditional_influence Λ (fun z => h (f z)) β K (d : ℝ)
    B T E hBT hEB φ φ' τ τ' y hβ hdeg hsource hboundary
  have htail := expected_forced_cluster Λ h K (rho K (d : ℝ) β)
    (rho_pos _ _ _) (rho_lt_one _ _ _).le f hf hadj (B \ E) y hyU
    R r₀ s (B \ E).card v hr₀ hrs hgood hy
  exact hbase.trans (by simpa only [add_assoc] using add_le_add_left htail (defectCount E τ' τ : ℝ))

/-- The arbitrary-block boundary influence estimate with the good-label
expectation evaluated explicitly. -/
theorem gibbs_boundary_influence_good {d : ℕ} (Λ : Lattice V)
    (h : LatticeGeometry.Point d → ℝ) (β K : ℝ)
    (f : V → LatticeGeometry.Point d) (hf : Function.Injective f)
    (hadj : ∀ ⦃x z⦄, Λ.adj x z → LatticeGeometry.Adj (f x) (f z))
    (B T : Finset V) (hBT : Disjoint B T) (φ φ' : Config V) (y : V) (hyB : y ∉ B)
    (hβ : 0 ≤ β) (hdeg : (Λ.maxDegree : ℝ) ≤ 2 * (d : ℝ))
    (hboundary : ∀ r ∈ T, φ r ≠ φ' r → r = y)
    (R r₀ s : ℕ) (v : LatticeGeometry.Point d) (hr₀ : 0 < r₀) (hrs : r₀ ≤ s)
    (hgood : Percolation.goodLabel K (rho K (d : ℝ) β) R r₀ s h v)
    (hy : f y ∈ Percolation.latticeCube (Percolation.coarseCenter R v) R) :
    hammingWasserstein
      (gibbs Λ (fun z => h (f z)) β B T φ)
      (gibbs Λ (fun z => h (f z)) β B T φ') ≤
      (r₀ : ℝ) + 2 / rho K (d : ℝ) β +
        (B.card : ℝ) / rho K (d : ℝ) β * Real.exp (-(s : ℝ)) := by
  have hbase := Disagreement.gibbs_boundary_influence Λ (fun z => h (f z)) β K (d : ℝ)
    B T hBT φ φ' y hβ hdeg hboundary
  have htail := expected_forced_cluster Λ h K (rho K (d : ℝ) β)
    (rho_pos _ _ _) (rho_lt_one _ _ _).le f hf hadj B y hyB R r₀ s B.card v hr₀ hrs hgood hy
  exact hbase.trans htail

/-- Deterministic conversion of the explicit integer-cutoff estimate to the
uniform constant and scale appearing in paper (3.6). -/
theorem source_scale_bound (ρ : ℝ) (hρ : 0 < ρ) (R N : ℕ)
    (hdiv : 8 ∣ R) (hlog : 1 ≤ (Real.log (R : ℝ)) ^ 2) :
    (Percolation.initialRadius R : ℝ) + 2 / ρ +
      (N : ℝ) / ρ * Real.exp (-((R / 8 : ℕ) : ℝ)) ≤
        (2 + 2 / ρ) * (Real.log (R : ℝ)) ^ 2 +
          (2 + 2 / ρ) * (N : ℝ) * Real.exp (-(R : ℝ) / 8) := by
  have hc : (Percolation.initialRadius R : ℝ) ≤ 2 * (Real.log (R : ℝ)) ^ 2 := by
    have hceil := Nat.ceil_lt_add_one (sq_nonneg (Real.log (R : ℝ)))
    change (Nat.ceil ((Real.log (R : ℝ)) ^ 2) : ℝ) ≤ _
    linarith
  have hcoef : 0 ≤ 2 / ρ := div_nonneg (by norm_num) hρ.le
  have hmain : (Percolation.initialRadius R : ℝ) + 2 / ρ ≤
      (2 + 2 / ρ) * (Real.log (R : ℝ)) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hlog hcoef
    nlinarith
  have hi : 0 ≤ 1 / ρ := div_nonneg zero_le_one hρ.le
  have hC : 1 / ρ ≤ 2 + 2 / ρ := by
    simp only [div_eq_mul_inv, one_mul] at hi ⊢
    linarith
  have htail := mul_le_mul_of_nonneg_right hC
    (mul_nonneg (Nat.cast_nonneg N) (Real.exp_nonneg (-(R : ℝ) / 8)))
  have he : -((R / 8 : ℕ) : ℝ) = -(R : ℝ) / 8 := by
    rw [Nat.cast_div_charZero hdiv]
    norm_num
    ring
  rw [he]
  convert add_le_add hmain htail using 1 <;> ring

/-- Paper (3.6) for arbitrary embedded finite domains. The displayed constant
`2+2/rho` depends only on the fixed physical parameters, uniformly in blocks,
boundary conditions and the ambient volume. -/
theorem gibbs_boundary_influence_paper36 {d : ℕ} (Λ : Lattice V)
    (h : LatticeGeometry.Point d → ℝ) (β K : ℝ)
    (f : V → LatticeGeometry.Point d) (hf : Function.Injective f)
    (hadj : ∀ ⦃x z⦄, Λ.adj x z → LatticeGeometry.Adj (f x) (f z))
    (B T : Finset V) (hBT : Disjoint B T) (φ φ' : Config V) (y : V) (hyB : y ∉ B)
    (hβ : 0 ≤ β) (hdeg : (Λ.maxDegree : ℝ) ≤ 2 * (d : ℝ))
    (hboundary : ∀ r ∈ T, φ r ≠ φ' r → r = y)
    (R : ℕ) (v : LatticeGeometry.Point d) (hdiv : 8 ∣ R)
    (hlog : 1 ≤ (Real.log (R : ℝ)) ^ 2) (hcut : Percolation.initialRadius R ≤ R / 8)
    (hgood : Percolation.goodLabel K (rho K (d : ℝ) β) R
      (Percolation.initialRadius R) (R / 8) h v)
    (hy : f y ∈ Percolation.latticeCube (Percolation.coarseCenter R v) R) :
    hammingWasserstein
      (gibbs Λ (fun z => h (f z)) β B T φ)
      (gibbs Λ (fun z => h (f z)) β B T φ') ≤
      (2 + 2 / rho K (d : ℝ) β) * (Real.log (R : ℝ)) ^ 2 +
        (2 + 2 / rho K (d : ℝ) β) * (B.card : ℝ) * Real.exp (-(R : ℝ) / 8) := by
  have hr₀ : 0 < Percolation.initialRadius R := by
    apply Nat.ceil_pos.mpr
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hlog
  have hbase := gibbs_boundary_influence_good Λ h β K f hf hadj B T hBT φ φ' y hyB
    hβ hdeg hboundary R (Percolation.initialRadius R) (R / 8) v hr₀ hcut hgood hy
  exact hbase.trans (source_scale_bound (rho K (d : ℝ) β) (rho_pos _ _ _) R B.card hdiv hlog)

end Paper09.DisagreementGoodRoot
