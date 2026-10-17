import Paper27.Geometry.FixedAmbientBranchGraphs
import Paper27.Geometry.NormalizationLocalization

/-!
# Assembling the actual finite family of branch graphs

Compact normalization curves give the actual finite set of normalization
points over a fixed surface point. The metric comparison constructs the
graph at each of those points in one fixed pair of ambient functions.
Compactness then shrinks the surface neighbourhood so those same actual
normalization charts cover every nearby critical point. Actual coordinate
derivative transport gives the finite branch-cover record used by the local
cyclic classification. No existence of a branch graph cover is an input.
-/

noncomputable section

open scoped Manifold Topology

namespace Paper27.Geometry.FiniteBranchAssembly

open MetricComparison NormalizedBranchConstruction FixedAmbientBranchGraphs

variable {X : CompactComplexSurface} {f g : Fibration X}
  {gB : ConformalMetric f.base} {gC : ConformalMetric g.base}

/-- The finite actual normalization fibre, used as the common branch index. -/
abbrev BranchIndex (hfinite : f.FinitePair g) (hsurj : f.PairSurjective g)
    (N : CriticalCurveNormalization (RamificationSupport.finiteSurjectivePair f g hfinite hsurj))
    (x : X) := N.toCompactCurveCover.Branch x

instance branchIndexFintype (hfinite : f.FinitePair g) (hsurj : f.PairSurjective g)
    (N : CriticalCurveNormalization (RamificationSupport.finiteSurjectivePair f g hfinite hsurj))
    (x : X) : Fintype (BranchIndex hfinite hsurj N x) := Fintype.ofFinite _

/-- The actual normalization-image cover of the nearby critical set is
transported to the fixed ambient coordinates. The open domains are pulled
back from the already constructed branch charts, so their graph identities
remain valid on every selected representative. -/
theorem finiteBranchCover_of_normalization
    (hfinite : f.FinitePair g) (hsurj : f.PairSurjective g)
    (N : CriticalCurveNormalization (RamificationSupport.finiteSurjectivePair f g hfinite hsurj))
    (x : X) (a : UniformizingDiscChart gB (f x)) (d : UniformizingDiscChart gC (g x))
    (branches : ∀ b : BranchIndex hfinite hsurj N x,
      ConstructedBranch
        (coordinateFunction a (CoordinateCalculus.fibrationMap f) x)
        (coordinateFunction d (CoordinateCalculus.fibrationMap g) x)
        ((chartAt (ℂ × ℂ) x) x)
        (CoordinateCalculus.coordinateMap (N.map b.1) b.2.val x)
        ((chartAt ℂ b.2.val) b.2.val)) :
    Nonempty (FiniteAnalyticGerm.FiniteBranchCover
      (coordinateFunction a (CoordinateCalculus.fibrationMap f) x)
      (coordinateFunction d (CoordinateCalculus.fibrationMap g) x)
      ((chartAt (ℂ × ℂ) x) x) (BranchIndex hfinite hsurj N x)) := by
  classical
  letI : Fintype (BranchIndex hfinite hsurj N x) := Fintype.ofFinite _
  let O : (b : BranchIndex hfinite hsurj N x) → Set (N.curve b.1) :=
    fun b => (chartAt ℂ b.2.val).source ∩ (chartAt ℂ b.2.val) ⁻¹' (branches b).domain
  have hO : ∀ b, IsOpen (O b) :=
    fun b => (chartAt ℂ b.2.val).isOpen_inter_preimage (branches b).open_domain
  have hpO : ∀ b, b.2.val ∈ O b :=
    fun b => ⟨mem_chart_source ℂ b.2.val, (branches b).centre_mem⟩
  obtain ⟨V, hV, hxV, hcover⟩ := N.local_critical_cover x O hO hpO
  let W : Set X := V ∩ (chartAt (ℂ × ℂ) x).source ∩
    f ⁻¹' a.coordinates.source ∩ g ⁻¹' d.coordinates.source
  have hW : IsOpen W := ((hV.inter (chartAt (ℂ × ℂ) x).open_source).inter
    (a.coordinates.open_source.preimage f.holomorphic.continuous)).inter
      (d.coordinates.open_source.preimage g.holomorphic.continuous)
  have hxW : x ∈ W := ⟨⟨⟨hxV, mem_chart_source (ℂ × ℂ) x⟩, a.centre_mem⟩, d.centre_mem⟩
  let region : Set (ℂ × ℂ) := (chartAt (ℂ × ℂ) x).target ∩
    (chartAt (ℂ × ℂ) x).symm ⁻¹' W
  have hregion : IsOpen region := (chartAt (ℂ × ℂ) x).isOpen_inter_preimage_symm hW
  have hxregion : (chartAt (ℂ × ℂ) x) x ∈ region := by
    refine ⟨(chartAt (ℂ × ℂ) x).map_source (mem_chart_source (ℂ × ℂ) x), ?_⟩
    change (chartAt (ℂ × ℂ) x).symm ((chartAt (ℂ × ℂ) x) x) ∈ W
    rwa [(chartAt (ℂ × ℂ) x).left_inv (mem_chart_source (ℂ × ℂ) x)]
  apply Nonempty.intro
  apply finiteBranchCover_of_constructed branches region hregion hxregion
  intro z hz hcritical
  have hza : Valid a (CoordinateCalculus.fibrationMap f) x z := ⟨hz.1, hz.2.1.2⟩
  have hzd : Valid d (CoordinateCalculus.fibrationMap g) x z := ⟨hz.1, hz.2.2⟩
  have hdiffF := mdifferentiableAt_iff_differentiableAt.mp
    (coordinateFunction_mdifferentiableAt a (CoordinateCalculus.fibrationMap f) x hza)
  have hdiffG := mdifferentiableAt_iff_differentiableAt.mp
    (coordinateFunction_mdifferentiableAt d (CoordinateCalculus.fibrationMap g) x hzd)
  rw [hdiffF.fderiv_prodMk hdiffG] at hcritical
  have hjoint := (pair_surjective_iff a d (CoordinateCalculus.fibrationMap f)
    (CoordinateCalculus.fibrationMap g) x hza hzd).not.mp hcritical
  have hactual := (CoordinateCalculus.pairMap_surjective_iff f g
    ((chartAt (ℂ × ℂ) x).symm z)).not.mpr hjoint
  obtain ⟨b, t, ht, hν⟩ := hcover ((chartAt (ℂ × ℂ) x).symm z) hz.2.1.1.1 hactual
  refine ⟨b, (chartAt ℂ b.2.val) t, ht.2, ?_⟩
  change (chartAt (ℂ × ℂ) x)
    (N.map b.1 ((chartAt ℂ b.2.val).symm ((chartAt ℂ b.2.val) t))) = z
  rw [(chartAt ℂ b.2.val).left_inv ht.1, hν,
    (chartAt (ℂ × ℂ) x).right_inv hz.1]

/-- Complete assembly from the actual normalization curves and the proved
global metric comparison. The actual branch-cover existence is a conclusion;
only the raw universal normalization theorem supplies the initial curves. -/
theorem finiteBranchCover_exists
    (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (maps : ClassicalCurveMapFacts)
    (constant : CovectorGauges.ClassicalZeroDifferentialConstancy)
    (pullbacks : ClassicalPullbackFacts) (unique : TroyanovUniqueness)
    (extend : DiscGraphExtension.LocalDiscIsometryExtension)
    (hf : f.Smooth) (hg : g.Smooth) (hB : f.Hyperbolic)
    (hfinite : f.FinitePair g) (hsurj : f.PairSurjective g)
    (N : CriticalCurveNormalization (RamificationSupport.finiteSurjectivePair f g hfinite hsurj))
    (hBcone : HasConeData gB 0) (hCcone : HasConeData gC 0)
    (hBcurv : HasConstantCurvature gB 0 (-1))
    (hCcurv : HasConstantCurvature gC 0 (-1))
    (x : X) (a : UniformizingDiscChart gB (f x)) (d : UniformizingDiscChart gC (g x)) :
    Nonempty (FiniteAnalyticGerm.FiniteBranchCover
      (coordinateFunction a (CoordinateCalculus.fibrationMap f) x)
      (coordinateFunction d (CoordinateCalculus.fibrationMap g) x)
      ((chartAt (ℂ × ℂ) x) x) (BranchIndex hfinite hsurj N x)) := by
  have himage : ∀ i q, N.map i q ∈ RamificationSupport.ramificationSet f g :=
    fun i q => N.image_critical i q
  have hcomparison : ∀ i,
      Nonconstant (CoordinateCalculus.restrictedMap f (N.map i)) ∧
      pullback (CoordinateCalculus.restrictedMap f (N.map i)) gB =
        pullback (CoordinateCalculus.restrictedMap g (N.map i)) gC := by
    intro i
    obtain ⟨hu, _hv, _hD, _hR, _hDiv, hmetric⟩ :=
      CoordinateCalculus.normalized_comparison_complete regularity maps constant pullbacks unique
        f g hf hg hB (N.map i) (himage i) hfinite
        (N.toCompactCurveCover.map_nonconstant i) gB gC hBcone hCcone hBcurv hCcurv
    exact ⟨hu, hmetric⟩
  obtain ⟨branches⟩ := constructedBranch_family_exists
    (ι := BranchIndex hfinite hsurj N x) regularity maps extend hf hg x
    (fun b => N.curve b.1) (fun b => N.map b.1) (fun b => b.2.val)
    (fun b => b.2.property) (fun b => himage b.1)
    (fun b => (hcomparison b.1).1) (fun b => (hcomparison b.1).2) a d
  exact finiteBranchCover_of_normalization hfinite hsurj N x a d branches

end Paper27.Geometry.FiniteBranchAssembly
