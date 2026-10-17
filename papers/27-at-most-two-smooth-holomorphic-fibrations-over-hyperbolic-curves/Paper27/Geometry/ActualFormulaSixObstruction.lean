import Paper27.Geometry.PuncturedRotationCoordinates
import Paper27.Geometry.PuncturedNeighbourhoods

/-!
# The original averaging obstruction on actual neighbourhood sections

The two sections are actual inverses of the joint retraction differentials
on the actual punctured neighbourhood. Their derivative quotients, poles,
leading coefficients, and cyclic weights have been proved in the preceding
modules. The only general analytic inputs are ordinary Taylor/Laurent and
holomorphic bundle calculus, removable extension across a divisor, and Bott.
-/
noncomputable section
open scoped Manifold Topology BigOperators
open Filter Finset
namespace Paper27.Geometry.RetractionCoordinateGerms.NormalAtlas
open PuncturedSplittingSections RetractionCoefficientHolomorphic MeromorphicSplittingAverage
  NormalDegreeInvariance
variable {X : CompactComplexSurface} {D : EmbeddedCurve X} {U : D.Neighbourhood}
  {r₁ r₂ r₃ : D.Retraction U} {n : ℕ}
  (A : RetractionCoordinateGerms.NormalAtlas D U r₁ r₂ n)

/-- The actual finite differential average has exactly the scalar formula (6)
in every actual centred normal chart. All summand germs are derived from the
actual action and the actual joint inverse. -/
theorem actual_formulaSix_coordinate_germ {G : Type} [Group G]
    (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (action : NeighbourhoodSplittings.NeighbourhoodAction G r₁)
    (hfix : ∀ g p, action.permutation g (NeighbourhoodSplittings.curvePoint U p) =
      NeighbourhoodSplittings.curvePoint U p)
    (scalar : G →* ℂˣ)
    (hgerm : ∀ g p, action.map g =ᶠ[𝓝 (D.inclusion p)]
      NormalAtlasAction.localRotation (A.chart p p).coordinates (scalar g : ℂ))
    (g : G) (a : ℂ) (ha : a ≠ 1) (hn : 0 < n)
    (ho : A.HasThirdOrder r₃)
    (ht₂ : PuncturedSplittingSections.JointTransverse r₁ r₂)
    (ht₃ : PuncturedSplittingSections.JointTransverse r₁ r₃) (p : D.curve) :
    A.sliceCoefficient p p
      (PuncturedSplittingSections.NeighbourhoodAction.formulaSix action hfix n g a
        (jointInverse r₁ r₂ ht₂) (jointInverse r₁ r₃ ht₃)) =ᶠ[𝓝[≠] 0]
      fun y => (1, A.localFormulaSix r₃ (scalar g : ℂ) a p p y) := by
  apply A.formulaSix_coefficient_of_summands action hfix g (scalar g : ℂ) a hn ha
  · exact A.jointInverse_coordinate_germ regularity r₂ (A.hasThirdOrder_of_pair_atlas A)
      hn ht₂ p p (mem_chart_source ℂ p)
  · intro j hj
    have hpow : (scalar (g ^ j) : ℂ) = (scalar g : ℂ) ^ j := by simp
    have hinv : action.map ((g ^ j)⁻¹) =ᶠ[𝓝 (D.inclusion p)]
        NormalAtlasAction.localRotation (A.chart p p).coordinates (scalar (g ^ j) : ℂ)⁻¹ := by
      simpa using hgerm ((g ^ j)⁻¹) p
    have hα : (scalar (g ^ j) : ℂ) ≠ 0 := Units.ne_zero _
    have hpush := A.pushforward_sliceCoefficient_germ action hfix (g ^ j)
      (scalar (g ^ j) : ℂ) hα p (hgerm (g ^ j) p) hinv (jointInverse r₁ r₃ ht₃)
    have hsource := (A.jointInverse_coordinate_germ regularity r₃ ho hn ht₃ p p
      (mem_chart_source ℂ p)).comp_tendsto (scalar_punctured_tendsto (inv_ne_zero hα))
    filter_upwards [hpush, hsource] with y hpy hsy
    change A.sliceCoefficient p p
      (PuncturedSplittingSections.NeighbourhoodAction.pushforward action hfix (g ^ j)
        (jointInverse r₁ r₃ ht₃)) y = _ at hpy ⊢
    rw [hpy]
    change NormalAtlasAction.rotate (scalar (g ^ j) : ℂ)
      (A.sliceCoefficient p p (jointInverse r₁ r₃ ht₃) ((scalar (g ^ j) : ℂ)⁻¹ * y)) = _
    change A.sliceCoefficient p p (jointInverse r₁ r₃ ht₃) ((scalar (g ^ j) : ℂ)⁻¹ * y) = _ at hsy
    rw [hsy, hpow]
    rfl

/-- Formula (6), formed from actual punctured joint inverses, extends to an
actual holomorphic splitting whose tangent line along D is the actual TD.
The third and difference orders and the constant a are obtained from the
three actual pair atlases, rather than supplied as Laurent hypotheses. -/
theorem actual_formulaSix_extension {G : Type} [Group G]
    (J : TaylorGerms.TaylorCalculus) (P : ParametricTaylorCalculus J)
    (L : LaurentCalculus) (extension : LaurentSectionExtension L)
    (calculus : HolomorphicPuncturedCalculus)
    (B : RetractionCoordinateGerms.NormalAtlas D U r₁ r₃ n)
    (C : RetractionCoordinateGerms.NormalAtlas D U r₂ r₃ n) (hn : 2 ≤ n)
    (action : NeighbourhoodSplittings.NeighbourhoodAction G r₁)
    (hfix : ∀ g p, action.permutation g (NeighbourhoodSplittings.curvePoint U p) =
      NeighbourhoodSplittings.curvePoint U p)
    (scalar : G →* ℂˣ)
    (hgerm : ∀ g p, action.map g =ᶠ[𝓝 (D.inclusion p)]
      NormalAtlasAction.localRotation (A.chart p p).coordinates (scalar g : ℂ))
    (g : G) (hζ : IsPrimitiveRoot (scalar g : ℂ) n)
    (ht₂ : PuncturedSplittingSections.JointTransverse r₁ r₂)
    (ht₃ : PuncturedSplittingSections.JointTransverse r₁ r₃) :
    ∃ (a : ℂ) (s : NeighbourhoodSplittings.Section U), a ≠ 0 ∧ a ≠ 1 ∧
      NeighbourhoodSplittings.HolomorphicSection r₁ s ∧
      NeighbourhoodSplittings.IsSplitting r₁ s ∧
      PuncturedSplittingSections.restrict s =
        PuncturedSplittingSections.NeighbourhoodAction.formulaSix action hfix n g a
          (jointInverse r₁ r₂ ht₂) (jointInverse r₁ r₃ ht₃) ∧
      ∀ p : D.curve, s (NeighbourhoodSplittings.curvePoint U p) =
        mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ) D.inclusion p := by
  let ho := A.hasThirdOrder_of_pair_atlas B
  have hdiff := A.hasDifferenceOrder_of_pair_atlas C hn
  obtain ⟨a, ha0, ha1, ha⟩ := A.leading_constant J P r₃ ho hdiff (by omega)
  let σ₂ := jointInverse r₁ r₂ ht₂
  let σ₃ := jointInverse r₁ r₃ ht₃
  let σ := PuncturedSplittingSections.NeighbourhoodAction.formulaSix action hfix n g a σ₂ σ₃
  have hh : PuncturedSplittingSections.HolomorphicSection r₁ σ :=
    formulaSix_holomorphic calculus action hfix n g a σ₂ σ₃
      (calculus.inverse_holomorphic X D U r₁ r₂ ht₂)
      (calculus.inverse_holomorphic X D U r₁ r₃ ht₃)
  have hs : PuncturedSplittingSections.IsSplitting r₁ σ :=
    PuncturedSplittingSections.NeighbourhoodAction.formulaSix_splitting action hfix
      (by omega) g a ha1 σ₂ σ₃ (jointInverse_splitting r₁ r₂ ht₂)
      (jointInverse_splitting r₁ r₃ ht₃)
  have hc : ∀ p : D.curve, A.sliceCoefficient p p σ =ᶠ[𝓝[≠] 0]
      fun y => (1, A.localFormulaSix r₃ (scalar g : ℂ) a p p y) :=
    A.actual_formulaSix_coordinate_germ P.regularity action hfix scalar hgerm g a ha1
      (by omega) ho ht₂ ht₃
  obtain ⟨s, hshol, hssplit, hsres, hsincl⟩ := A.extend_formulaSix_coordinates_with_restriction L extension
    P.regularity r₃ ho (by omega) hζ ha0 ha σ hh hs hc
  exact ⟨a, s, ha0, ha1, hshol, hssplit, hsres, hsincl⟩

include A in
/-- The original formula-(6) proof of the common-tangency obstruction, using
actual global sections and the actual Bott degree of the actual normal line. -/
theorem actual_formulaSix_impossible {G : Type} [Group G]
    (J : TaylorGerms.TaylorCalculus) (P : ParametricTaylorCalculus J)
    (L : LaurentCalculus) (extension : LaurentSectionExtension L)
    (calculus : HolomorphicPuncturedCalculus)
    (B : RetractionCoordinateGerms.NormalAtlas D U r₁ r₃ n)
    (C : RetractionCoordinateGerms.NormalAtlas D U r₂ r₃ n) (hn : 2 ≤ n)
    (action : NeighbourhoodSplittings.NeighbourhoodAction G r₁)
    (hfix : ∀ g p, action.permutation g (NeighbourhoodSplittings.curvePoint U p) =
      NeighbourhoodSplittings.curvePoint U p)
    (scalar : G →* ℂˣ)
    (hgerm : ∀ g p, action.map g =ᶠ[𝓝 (D.inclusion p)]
      NormalAtlasAction.localRotation (A.chart p p).coordinates (scalar g : ℂ))
    (g : G) (hζ : IsPrimitiveRoot (scalar g : ℂ) n)
    (ht₂ : PuncturedSplittingSections.JointTransverse r₁ r₂)
    (ht₃ : PuncturedSplittingSections.JointTransverse r₁ r₃)
    {N : HolomorphicLineCocycle D.curve} {T : TangentLineCocycle D.curve}
    (F : EmbeddedFrames.RawEmbeddedFrames D N T.bundle)
    (theory : LineBundleDegreeTheory) (invariance : LineBundleDegreeGaugeInvariance theory)
    (bott : NeighbourhoodSplittings.BottTangentialSubbundleDegreeZero theory)
    (hD : D.curve.Hyperbolic) : False := by
  obtain ⟨a, s, _, _, hhol, hs, _, hincl⟩ := A.actual_formulaSix_extension J P L extension
    calculus B C hn action hfix scalar hgerm g hζ ht₂ ht₃
  have hzero := bott_of_extended_splitting (r₁ := r₁) theory bott F s hhol hs hincl
  have hnegative := A.normal_degree_negative P.regularity F (by omega) theory invariance hD
  omega
end Paper27.Geometry.RetractionCoordinateGerms.NormalAtlas
