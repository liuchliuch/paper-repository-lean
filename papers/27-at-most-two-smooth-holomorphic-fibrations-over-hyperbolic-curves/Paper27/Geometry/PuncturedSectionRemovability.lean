import Paper27.Geometry.PuncturedSectionAverage

/-!
# Removable actual sections, their tangent image, and the actual Bott theorem

The only extension interface is the universal hypersurface Laurent-removal
and sheaf-gluing theorem for actual punctured bundle sections in arbitrary
adapted coordinates. It contains no splitting, foliation, averaging, exponent,
or degree assertion. The splitting and tangent line after extension, and the
application of the actual tangential subbundle Bott theorem, are proved here.
-/
noncomputable section
open scoped Manifold Topology BigOperators
open Filter

namespace Paper27.Geometry.PuncturedSplittingSections
open EmbeddedFrames RetractionCoordinateGerms RetractionCoefficientHolomorphic
open MeromorphicSplittingAverage
variable {X : CompactComplexSurface} {D : EmbeddedCurve X} {U : D.Neighbourhood}

/-- Ordinary actual adapted coordinates for one retraction and an embedded
curve. There is no second retraction or ramification exponent in this type. -/
structure RetractionCoordinates (r : D.Retraction U) where
  chart : D.curve → OpenPartialHomeomorph X (ℂ × ℂ)
  source_mem : ∀ p, D.inclusion p ∈ (chart p).source
  source_subset : ∀ p, (chart p).source ⊆ U.domain
  holomorphic : ∀ p, (chart p).MDifferentiable 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ)
  axis : ∀ p q, D.inclusion q ∈ (chart p).source →
    chart p (D.inclusion q) = ((chartAt ℂ p) q, 0)
  retraction_source : ∀ p x, x ∈ (chart p).source → r.toFun x ∈ D.curve.chartDomain p
  retraction_normal : ∀ p x, x ∈ (chart p).source → (chartAt ℂ p) (r.toFun x) = (chart p x).1

 def RetractionCoordinates.coefficient {r : D.Retraction U} (C : RetractionCoordinates r)
    (σ : Section D U) (p : D.curve) (y : ℂ) : ℂ × ℂ :=
  chartCoefficient r (C.chart p) p ((chartAt ℂ p) p, y) σ

 def RetractionCoordinates.curveValue {r : D.Retraction U} (C : RetractionCoordinates r)
    (σ : NeighbourhoodSplittings.Section U) (p : D.curve) : ℂ × ℂ :=
  mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (C.chart p) (D.inclusion p)
    (σ (NeighbourhoodSplittings.curvePoint U p) ((tangentCoordinate D.curve p p).symm 1))

/-- Universal Laurent removal and sheaf gluing for actual bundle maps across
an actual smooth complex hypersurface. Constant coefficients give the value
of the extension. No paper-specific sections or pole-cancellation conclusions
appear in this standard analytic interface. -/
def LaurentSectionExtension (L : LaurentCalculus) : Prop :=
  ∀ (X : CompactComplexSurface) (D : EmbeddedCurve X) (U : D.Neighbourhood)
    (r : D.Retraction U) (C : RetractionCoordinates r) (σ : Section D U),
    HolomorphicSection r σ →
    (∀ p : D.curve, MeromorphicAt (fun y => (C.coefficient σ p y).1) 0 ∧
      MeromorphicAt (fun y => (C.coefficient σ p y).2) 0) →
    (∀ p : D.curve, ∀ k : ℤ, k < 0 →
      L.coeff (fun y => (C.coefficient σ p y).1) k = 0 ∧
        L.coeff (fun y => (C.coefficient σ p y).2) k = 0) →
    ∃ s : NeighbourhoodSplittings.Section U,
      NeighbourhoodSplittings.HolomorphicSection r s ∧ restrict s = σ ∧
        ∀ p : D.curve, C.curveValue s p =
          (L.coeff (fun y => (C.coefficient σ p y).1) 0,
            L.coeff (fun y => (C.coefficient σ p y).2) 0)

/-- Standard holomorphic inverse and pushforward bundle calculus, restricted
to the actual punctured domain. Only regularity is supplied by these facts. -/
structure HolomorphicPuncturedCalculus : Prop where
  inverse_holomorphic : ∀ (X : CompactComplexSurface) (D : EmbeddedCurve X)
    (U : D.Neighbourhood) (r s : D.Retraction U) (ht : JointTransverse r s),
      HolomorphicSection r (jointInverse r s ht)
  pushforward_holomorphic : ∀ (X : CompactComplexSurface) (D : EmbeddedCurve X)
    (U : D.Neighbourhood) (r : D.Retraction U) (G : Type) [Group G]
    (A : NeighbourhoodSplittings.NeighbourhoodAction G r)
    (hfix : ∀ g p, A.permutation g (NeighbourhoodSplittings.curvePoint U p) =
      NeighbourhoodSplittings.curvePoint U p)
    (g : G) (σ : Section D U), HolomorphicSection r σ →
      HolomorphicSection r (NeighbourhoodAction.pushforward A hfix g σ)

 def holomorphicSections (r : D.Retraction U) : Submodule ℂ (Section D U) where
  carrier := HolomorphicSection r
  zero_mem' := by
    intro p
    simpa only [map_zero] using
      (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ × ℂ => (0 : ℂ × ℂ))
        ((chartAt (ℂ × ℂ) p.val.val) p.val.val))
  add_mem' hσ hτ := by
    intro p
    simpa only [map_add] using (hσ p).add (hτ p)
  smul_mem' a σ hσ := by
    intro p
    simpa only [map_smul] using (hσ p).fun_const_smul (c := a)

 theorem formulaSix_holomorphic (calculus : HolomorphicPuncturedCalculus)
    {r : D.Retraction U} {G : Type} [Group G]
    (A : NeighbourhoodSplittings.NeighbourhoodAction G r)
    (hfix : ∀ g p, A.permutation g (NeighbourhoodSplittings.curvePoint U p) =
      NeighbourhoodSplittings.curvePoint U p)
    (n : ℕ) (g : G) (a : ℂ) (σ₂ σ₃ : Section D U)
    (h₂ : HolomorphicSection r σ₂) (h₃ : HolomorphicSection r σ₃) :
    HolomorphicSection r (NeighbourhoodAction.formulaSix A hfix n g a σ₂ σ₃) := by
  apply (holomorphicSections r).smul_mem
  apply (holomorphicSections r).sub_mem
  · apply (holomorphicSections r).smul_mem
    apply (holomorphicSections r).smul_mem
    apply (holomorphicSections r).sum_mem
    intro j hj
    exact calculus.pushforward_holomorphic X D U r G A hfix (g ^ j) σ₃ h₃
  · exact h₂

/-- Two actual complex-linear maps on a line agree if they agree on one
nonzero basis vector given by an actual coordinate equivalence. -/
 theorem clm_eq_of_coordinate_unit {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (E : ℂ ≃L[ℂ] ℂ) (L K : ℂ →L[ℂ] V) (h : L (E.symm 1) = K (E.symm 1)) : L = K := by
  apply ContinuousLinearMap.ext
  intro w
  have hw : E.symm (E w • (1 : ℂ)) = w := by simp
  rw [← hw, map_smul, map_smul, map_smul, h]

end Paper27.Geometry.PuncturedSplittingSections

namespace Paper27.Geometry.RetractionCoordinateGerms.NormalAtlas
open EmbeddedFrames PuncturedSplittingSections MeromorphicSplittingAverage
variable {X : CompactComplexSurface} {D : EmbeddedCurve X} {U : D.Neighbourhood}
  {r₁ r₂ : D.Retraction U} {n : ℕ}
  (A : RetractionCoordinateGerms.NormalAtlas D U r₁ r₂ n)

/-- The actual normal atlas supplies ordinary adapted coordinates; its second
retraction and exponent play no role in the universal removal theorem. -/
def retractionCoordinates : RetractionCoordinates r₁ where
  chart p := (A.chart p p).coordinates
  source_mem p := A.source_mem p p (mem_chart_source ℂ p)
  source_subset p := A.source_subset p p
  holomorphic p := ⟨A.holomorphic p p, A.inverse_holomorphic p p⟩
  axis p q hq := (A.centered p p (mem_chart_source ℂ p)).centre_at q hq
  retraction_source p := (A.chart p p).r_source
  retraction_normal p := (A.chart p p).r_normal

/-- Actual value (1,0) in adapted coordinates forces the extended bundle map
to equal the actual inclusion differential on the embedded curve. -/
 theorem extension_eq_inclusion (s : NeighbourhoodSplittings.Section U)
    (hvalue : ∀ p : D.curve, A.retractionCoordinates.curveValue s p = (1, 0))
    (p : D.curve) :
    s (NeighbourhoodSplittings.curvePoint U p) =
      mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ) D.inclusion p := by
  let c := A.centered p p (mem_chart_source ℂ p)
  apply clm_eq_of_coordinate_unit (tangentCoordinate D.curve p p)
  apply c.differential.injective
  have hi := c.differential_inclusion (mem_chart_source ℂ p)
    ((tangentCoordinate D.curve p p).symm 1)
  rw [ContinuousLinearEquiv.apply_symm_apply] at hi
  exact (hvalue p).trans hi.symm

/-- Construct an actual holomorphic splitting with actual tangent image from
an actual punctured splitting whose computed Laurent coefficients are regular
and have constant vector (1,0). -/
 theorem extend_splitting (L : LaurentCalculus) (extension : LaurentSectionExtension L)
    (σ : PuncturedSplittingSections.Section D U)
    (hhol : PuncturedSplittingSections.HolomorphicSection r₁ σ)
    (hs : PuncturedSplittingSections.IsSplitting r₁ σ)
    (hm : ∀ p : D.curve,
      MeromorphicAt (fun y => (A.retractionCoordinates.coefficient σ p y).1) 0 ∧
      MeromorphicAt (fun y => (A.retractionCoordinates.coefficient σ p y).2) 0)
    (hnegative : ∀ p : D.curve, ∀ k : ℤ, k < 0 →
      L.coeff (fun y => (A.retractionCoordinates.coefficient σ p y).1) k = 0 ∧
      L.coeff (fun y => (A.retractionCoordinates.coefficient σ p y).2) k = 0)
    (hconstant : ∀ p : D.curve,
      (L.coeff (fun y => (A.retractionCoordinates.coefficient σ p y).1) 0,
        L.coeff (fun y => (A.retractionCoordinates.coefficient σ p y).2) 0) = (1, 0)) :
    ∃ s : NeighbourhoodSplittings.Section U,
      NeighbourhoodSplittings.HolomorphicSection r₁ s ∧
      NeighbourhoodSplittings.IsSplitting r₁ s ∧
      ∀ p : D.curve, s (NeighbourhoodSplittings.curvePoint U p) =
        mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ) D.inclusion p := by
  obtain ⟨s, hshol, hres, hvalue⟩ := extension X D U r₁ A.retractionCoordinates σ hhol hm hnegative
  have hincl := A.extension_eq_inclusion s (fun p => (hvalue p).trans (hconstant p))
  refine ⟨s, hshol, ?_, hincl⟩
  funext x
  by_cases hd : x.val ∈ D.support
  · obtain ⟨p, hp⟩ := hd
    have heq : x = NeighbourhoodSplittings.curvePoint U p := Subtype.ext hp.symm
    subst x
    change (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) r₁.toFun (D.inclusion p)).comp
      (s (NeighbourhoodSplittings.curvePoint U p)) = _
    rw [hincl p, NeighbourhoodSplittings.retraction_inclusion_derivative]
    rfl
  · have heq := congrArg (fun t : PuncturedSplittingSections.Section D U => t ⟨x, hd⟩) hres
    change s x = σ ⟨x, hd⟩ at heq
    change (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) r₁.toFun x.val).comp (s x) = _
    rw [heq]
    exact hs ⟨x, hd⟩

/-- The same extension with its actual restriction retained explicitly. -/
 theorem extend_splitting_with_restriction (L : LaurentCalculus) (extension : LaurentSectionExtension L)
    (σ : PuncturedSplittingSections.Section D U)
    (hhol : PuncturedSplittingSections.HolomorphicSection r₁ σ)
    (hs : PuncturedSplittingSections.IsSplitting r₁ σ)
    (hm : ∀ p : D.curve,
      MeromorphicAt (fun y => (A.retractionCoordinates.coefficient σ p y).1) 0 ∧
      MeromorphicAt (fun y => (A.retractionCoordinates.coefficient σ p y).2) 0)
    (hnegative : ∀ p : D.curve, ∀ k : ℤ, k < 0 →
      L.coeff (fun y => (A.retractionCoordinates.coefficient σ p y).1) k = 0 ∧
      L.coeff (fun y => (A.retractionCoordinates.coefficient σ p y).2) k = 0)
    (hconstant : ∀ p : D.curve,
      (L.coeff (fun y => (A.retractionCoordinates.coefficient σ p y).1) 0,
        L.coeff (fun y => (A.retractionCoordinates.coefficient σ p y).2) 0) = (1, 0)) :
    ∃ s : NeighbourhoodSplittings.Section U,
      NeighbourhoodSplittings.HolomorphicSection r₁ s ∧
      NeighbourhoodSplittings.IsSplitting r₁ s ∧
      restrict s = σ ∧
      ∀ p : D.curve, s (NeighbourhoodSplittings.curvePoint U p) =
        mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ) D.inclusion p := by
  obtain ⟨s, hshol, hres, hvalue⟩ := extension X D U r₁ A.retractionCoordinates σ hhol hm hnegative
  have hincl := A.extension_eq_inclusion s (fun p => (hvalue p).trans (hconstant p))
  refine ⟨s, hshol, ?_, hres, hincl⟩
  funext x
  by_cases hd : x.val ∈ D.support
  · obtain ⟨p, hp⟩ := hd
    have heq : x = NeighbourhoodSplittings.curvePoint U p := Subtype.ext hp.symm
    subst x
    change (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) r₁.toFun (D.inclusion p)).comp
      (s (NeighbourhoodSplittings.curvePoint U p)) = _
    rw [hincl p, NeighbourhoodSplittings.retraction_inclusion_derivative]
    rfl
  · have heq := congrArg (fun t : PuncturedSplittingSections.Section D U => t ⟨x, hd⟩) hres
    change s x = σ ⟨x, hd⟩ at heq
    change (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) r₁.toFun x.val).comp (s x) = _
    rw [heq]
    exact hs ⟨x, hd⟩

/-- Apply the actual Bott tangential-subbundle theorem to the constructed
extension. No arbitrary module, leaf type, or free degree is involved. -/
 theorem bott_of_extended_splitting (theory : LineBundleDegreeTheory)
    (bott : NeighbourhoodSplittings.BottTangentialSubbundleDegreeZero theory)
    {N T : HolomorphicLineCocycle D.curve} (F : RawEmbeddedFrames D N T)
    (s : NeighbourhoodSplittings.Section U)
    (hhol : NeighbourhoodSplittings.HolomorphicSection r₁ s)
    (hs : NeighbourhoodSplittings.IsSplitting r₁ s)
    (hincl : ∀ p : D.curve, s (NeighbourhoodSplittings.curvePoint U p) =
      mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ) D.inclusion p) : theory.degree D.curve N = 0 := by
  let E : NeighbourhoodSplittings.HolomorphicLineSubbundle r₁ :=
    ⟨s, hhol, NeighbourhoodSplittings.splitting_injective r₁ s hs⟩
  apply bott X D U r₁ N T F E
  intro p
  exact congrArg (fun f : ℂ →L[ℂ] (ℂ × ℂ) => LinearMap.range f.toLinearMap) (hincl p)

end Paper27.Geometry.RetractionCoordinateGerms.NormalAtlas
