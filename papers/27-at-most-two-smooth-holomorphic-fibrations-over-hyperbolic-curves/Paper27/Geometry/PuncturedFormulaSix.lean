import Paper27.Geometry.NormalAtlasRestriction
import Paper27.Geometry.ThreeRetractionOrders

/-!
# Formula (6) for actual punctured sections and its actual regular extension

Finite sums commute with actual normal-chart evaluation. Once the actual
rotation coordinate calculation is supplied by the differential action, this
module applies the proved scalar cancellation, constructs the actual regular
splitting, and applies Bott to its actual tangent image.
-/
noncomputable section
open scoped Manifold Topology BigOperators
open Filter Finset
namespace Paper27.Geometry.RetractionCoordinateGerms.NormalAtlas
open PuncturedSplittingSections RetractionCoefficientHolomorphic MeromorphicSplittingAverage
variable {X : CompactComplexSurface} {D : EmbeddedCurve X} {U : D.Neighbourhood}
  {r₁ r₂ r₃ : D.Retraction U} {n : ℕ}
  (A : RetractionCoordinateGerms.NormalAtlas D U r₁ r₂ n)

/-- Actual normal-chart evaluation is a linear map on actual punctured sections. -/
def sliceCoefficient (i p : D.curve) :
    PuncturedSplittingSections.Section D U →ₗ[ℂ] (ℂ → ℂ × ℂ) where
  toFun σ y := chartCoefficient r₁ (A.chart i p).coordinates i ((chartAt ℂ i) p, y) σ
  map_add' σ τ := by funext y; exact (chartCoefficient r₁ _ _ _).map_add σ τ
  map_smul' a σ := by funext y; exact (chartCoefficient r₁ _ _ _).map_smul a σ

/-- Finite actual section averaging and the global affine combination have
precisely the local scalar formula (6), by linearity of actual evaluation. -/
 theorem formulaSix_coefficient_of_summands {G : Type} [Group G]
    (action : NeighbourhoodSplittings.NeighbourhoodAction G r₁)
    (hfix : ∀ g p, action.permutation g (NeighbourhoodSplittings.curvePoint U p) =
      NeighbourhoodSplittings.curvePoint U p)
    (g : G) (ζ a : ℂ) (hn : 0 < n) (ha : a ≠ 1)
    (σ₂ σ₃ : PuncturedSplittingSections.Section D U) (i p : D.curve)
    (h₂ : A.sliceCoefficient i p σ₂ =ᶠ[𝓝[≠] 0]
      fun y => (1, A.verticalSplitting r₂ i p y))
    (h₃ : ∀ j ∈ range n,
      A.sliceCoefficient i p (PuncturedSplittingSections.NeighbourhoodAction.pushforward action hfix (g ^ j) σ₃)
        =ᶠ[𝓝[≠] 0] fun y =>
          (1, ζ ^ j * A.verticalSplitting r₃ i p ((ζ ^ j)⁻¹ * y))) :
    A.sliceCoefficient i p
      (PuncturedSplittingSections.NeighbourhoodAction.formulaSix action hfix n g a σ₂ σ₃)
      =ᶠ[𝓝[≠] 0] fun y => (1, A.localFormulaSix r₃ ζ a i p y) := by
  have hall : ∀ᶠ y in 𝓝[≠] (0 : ℂ), ∀ j ∈ range n,
      A.sliceCoefficient i p (PuncturedSplittingSections.NeighbourhoodAction.pushforward action hfix (g ^ j) σ₃) y =
        (1, ζ ^ j * A.verticalSplitting r₃ i p ((ζ ^ j)⁻¹ * y)) :=
    (Filter.eventually_all_finset (range n)).mpr h₃
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  filter_upwards [h₂, hall] with y h₂y h₃y
  have hsum : (∑ j ∈ range n,
      A.sliceCoefficient i p (PuncturedSplittingSections.NeighbourhoodAction.pushforward action hfix (g ^ j) σ₃) y) =
      ((n : ℂ), ∑ j ∈ range n, ζ ^ j * A.verticalSplitting r₃ i p ((ζ ^ j)⁻¹ * y)) := by
    calc
      _ = ∑ j ∈ range n, ((1 : ℂ), ζ ^ j * A.verticalSplitting r₃ i p ((ζ ^ j)⁻¹ * y)) :=
        Finset.sum_congr rfl h₃y
      _ = _ := by ext <;> simp [Prod.fst_sum, Prod.snd_sum]
  simp only [PuncturedSplittingSections.NeighbourhoodAction.formulaSix,
    PuncturedSplittingSections.NeighbourhoodAction.powerAverage, map_smul, map_sub, map_sum,
    Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, h₂y, hsum]
  apply Prod.ext
  · change (a - 1)⁻¹ * (a * ((n : ℂ)⁻¹ * n) - 1) = 1
    rw [inv_mul_cancel₀ hnC, mul_one]
    exact inv_mul_cancel₀ (sub_ne_zero.mpr ha)
  · change (a - 1)⁻¹ * (a * ((n : ℂ)⁻¹ *
      ∑ j ∈ range n, ζ ^ j * A.verticalSplitting r₃ i p ((ζ ^ j)⁻¹ * y)) -
        A.verticalSplitting r₂ i p y) = A.localFormulaSix r₃ ζ a i p y
    simp only [localFormulaSix, scalarAffine, scalarAverage, Pi.smul_apply,
      Pi.sub_apply, Finset.sum_apply, smul_eq_mul]

/-- The actual formula-(6) coordinate germ gives an actual regular splitting
and the actual inclusion differential on D, by the universal removable theorem. -/
 theorem extend_formulaSix_coordinates (L : LaurentCalculus)
    (extension : LaurentSectionExtension L)
    (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (r₃ : D.Retraction U) (ho : A.HasThirdOrder r₃) (hn : 0 < n)
    {ζ a : ℂ} (hζ : IsPrimitiveRoot ζ n) (ha0 : a ≠ 0)
    (ha : ∀ i p, p ∈ D.curve.chartDomain i → A.leading r₃ ho i p = a)
    (σ : PuncturedSplittingSections.Section D U)
    (hhol : PuncturedSplittingSections.HolomorphicSection r₁ σ)
    (hs : PuncturedSplittingSections.IsSplitting r₁ σ)
    (hcoord : ∀ p : D.curve, A.sliceCoefficient p p σ =ᶠ[𝓝[≠] 0]
      fun y => (1, A.localFormulaSix r₃ ζ a p p y)) :
    ∃ s : NeighbourhoodSplittings.Section U,
      NeighbourhoodSplittings.HolomorphicSection r₁ s ∧
      NeighbourhoodSplittings.IsSplitting r₁ s ∧
      ∀ p : D.curve, s (NeighbourhoodSplittings.curvePoint U p) =
        mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ) D.inclusion p := by
  have hfirst (p : D.curve) :
      (fun y => (A.retractionCoordinates.coefficient σ p y).1) =ᶠ[𝓝[≠] 0]
        fun _ => (1 : ℂ) := (hcoord p).mono fun _ h => congrArg Prod.fst h
  have hsecond (p : D.curve) :
      (fun y => (A.retractionCoordinates.coefficient σ p y).2) =ᶠ[𝓝[≠] 0]
        A.localFormulaSix r₃ ζ a p p := (hcoord p).mono fun _ h => congrArg Prod.snd h
  have hconst : L.coeff (fun _ : ℂ => (1 : ℂ)) = fun k => if k = 0 then 1 else 0 := by
    funext k
    have hh := L.monomial 1 0 k
    simpa only [zpow_zero, mul_one] using hh
  have ht (p : D.curve) := A.localFormulaSix_tangent L regularity r₃ ho hn hζ ha0 ha p p
    (mem_chart_source ℂ p)
  have hmer (p : D.curve) : MeromorphicAt (A.localFormulaSix r₃ ζ a p p) 0 :=
    meromorphic_scalarAffine a
      ((A.horizontalPartial_analytic regularity r₂ p p (mem_chart_source ℂ p)).neg.meromorphicAt.div
        (A.normalPartial_analytic regularity r₂ p p (mem_chart_source ℂ p)).meromorphicAt)
      (meromorphic_scalarAverage n ζ _ (A.verticalSplitting_meromorphic regularity r₃ ho hn p p
        (mem_chart_source ℂ p)))
  apply A.extend_splitting L extension σ hhol hs
  · intro p
    exact ⟨(MeromorphicAt.const 1 0).congr (hfirst p).symm,
      (hmer p).congr (hsecond p).symm⟩
  · intro p k hk
    constructor
    · rw [L.congr (hfirst p), hconst]
      simp only [if_neg (ne_of_lt hk)]
    · rw [L.congr (hsecond p)]
      exact ht p k (le_of_lt hk)
  · intro p
    rw [L.congr (hfirst p), hconst, L.congr (hsecond p)]
    exact Prod.ext (by simp) (ht p 0 le_rfl)

/-- Retain equality with the actual formula-(6) punctured section. -/
 theorem extend_formulaSix_coordinates_with_restriction (L : LaurentCalculus)
    (extension : LaurentSectionExtension L)
    (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (r₃ : D.Retraction U) (ho : A.HasThirdOrder r₃) (hn : 0 < n)
    {ζ a : ℂ} (hζ : IsPrimitiveRoot ζ n) (ha0 : a ≠ 0)
    (ha : ∀ i p, p ∈ D.curve.chartDomain i → A.leading r₃ ho i p = a)
    (σ : PuncturedSplittingSections.Section D U)
    (hhol : PuncturedSplittingSections.HolomorphicSection r₁ σ)
    (hs : PuncturedSplittingSections.IsSplitting r₁ σ)
    (hcoord : ∀ p : D.curve, A.sliceCoefficient p p σ =ᶠ[𝓝[≠] 0]
      fun y => (1, A.localFormulaSix r₃ ζ a p p y)) :
    ∃ s : NeighbourhoodSplittings.Section U,
      NeighbourhoodSplittings.HolomorphicSection r₁ s ∧
      NeighbourhoodSplittings.IsSplitting r₁ s ∧
      PuncturedSplittingSections.restrict s = σ ∧
      ∀ p : D.curve, s (NeighbourhoodSplittings.curvePoint U p) =
        mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ) D.inclusion p := by
  have hfirst (p : D.curve) :
      (fun y => (A.retractionCoordinates.coefficient σ p y).1) =ᶠ[𝓝[≠] 0]
        fun _ => (1 : ℂ) := (hcoord p).mono fun _ h => congrArg Prod.fst h
  have hsecond (p : D.curve) :
      (fun y => (A.retractionCoordinates.coefficient σ p y).2) =ᶠ[𝓝[≠] 0]
        A.localFormulaSix r₃ ζ a p p := (hcoord p).mono fun _ h => congrArg Prod.snd h
  have hconst : L.coeff (fun _ : ℂ => (1 : ℂ)) = fun k => if k = 0 then 1 else 0 := by
    funext k
    have hh := L.monomial 1 0 k
    simpa only [zpow_zero, mul_one] using hh
  have ht (p : D.curve) := A.localFormulaSix_tangent L regularity r₃ ho hn hζ ha0 ha p p
    (mem_chart_source ℂ p)
  have hmer (p : D.curve) : MeromorphicAt (A.localFormulaSix r₃ ζ a p p) 0 :=
    meromorphic_scalarAffine a
      ((A.horizontalPartial_analytic regularity r₂ p p (mem_chart_source ℂ p)).neg.meromorphicAt.div
        (A.normalPartial_analytic regularity r₂ p p (mem_chart_source ℂ p)).meromorphicAt)
      (meromorphic_scalarAverage n ζ _ (A.verticalSplitting_meromorphic regularity r₃ ho hn p p
        (mem_chart_source ℂ p)))
  apply A.extend_splitting_with_restriction L extension σ hhol hs
  · intro p
    exact ⟨(MeromorphicAt.const 1 0).congr (hfirst p).symm,
      (hmer p).congr (hsecond p).symm⟩
  · intro p k hk
    constructor
    · rw [L.congr (hfirst p), hconst]
      simp only [if_neg (ne_of_lt hk)]
    · rw [L.congr (hsecond p)]
      exact ht p k (le_of_lt hk)
  · intro p
    rw [L.congr (hfirst p), hconst, L.congr (hsecond p)]
    exact Prod.ext (by simp) (ht p 0 le_rfl)

end Paper27.Geometry.RetractionCoordinateGerms.NormalAtlas
