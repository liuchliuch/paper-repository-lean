import Paper27.Geometry.CoordinateCalculus
import Paper27.Geometry.DifferentialRigidity

/-!
# Metric rigidity at an intersection of two ramification curves

This is the first part of Lemma 3.1 on actual surface and curve maps. Equality
of the two metrics on one nonzero tangent of E forces equality on TX at the
intersection; its restriction to D attains Schwarz--Pick equality. The only
new classical input is the universal equality case for maps of hyperbolic
curves, together with the usual metrics and their covering invariance.
-/
noncomputable section
open scoped Manifold
namespace Paper27.Geometry.MetricTangency
open MetricComparison CoordinateCalculus

/-- The classical uniformizing metrics and the equality case of Schwarz--Pick,
quantified over arbitrary actual curve maps. No ramification component or
third-fibration conclusion occurs in this interface. McMullen's Harvard 213a
notes (2023), Theorem 2.28, p.65, state the locally isometric covering versus
strict contraction dichotomy, proved by lifting to universal discs. The
metric existence and covering invariance are the usual uniformization facts. -/
structure HyperbolicMetricTheory where
  metric : (C : Curve) → ConformalMetric C
  positive : ∀ (C : Curve), C.Hyperbolic → ∀ p : C, 0 < (metric C).weight p
  cone : ∀ (C : Curve), C.Hyperbolic → HasConeData (metric C) 0
  curvature : ∀ (C : Curve), C.Hyperbolic → HasConstantCurvature (metric C) 0 (-1)
  covering_isometry : ∀ (D B : Curve) (u : HolomorphicMap D B),
    D.Hyperbolic → B.Hyperbolic →
    (∀ p, Function.Bijective (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) u p)) →
    pullback u (metric B) = metric D
  schwarz_pick_equality : ∀ (D B : Curve) (u : HolomorphicMap D B),
    D.Hyperbolic → B.Hyperbolic →
    (∃ p : D, ∃ v : ℂ, v ≠ 0 ∧
      squaredNorm (metric D) p v =
        squaredNorm (metric B) (u p) (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) u p v)) →
    ∀ p, Function.Bijective (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) u p)

variable {X : CompactComplexSurface}

/-- Actual surface differential, with its model codomain made explicit so that
norms use the complex coordinate rather than a nonexistent intrinsic norm. -/
abbrev surfaceDifferential (f : Fibration X) (p : X) : (ℂ × ℂ) →L[ℂ] ℂ :=
  mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) f p

abbrev curveDifferential {D B : Curve} (u : HolomorphicMap D B) (p : D) : ℂ →L[ℂ] ℂ :=
  mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) u p

/-- The restriction chain rule is used to find an actual nonzero tangent in
TX, rather than assuming a convenient nonzero tangent vector. -/
theorem restriction_tangent_nonzero (f : Fibration X) {E : Curve}
    (ν : HolomorphicMap E X) (p : E)
    (hu : Function.Injective
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (restrictedMap f ν) p)) :
    mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) f (ν p)
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ) ν p (1 : ℂ)) ≠ 0 := by
  have hchain := mfderiv_comp p (f.holomorphic (ν p)) (ν.holomorphic p)
  have hu1 : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (restrictedMap f ν) p (1 : ℂ) ≠ 0 := by
    intro hz
    have heq : (1 : ℂ) = 0 := hu (hz.trans (map_zero _).symm)
    exact one_ne_zero heq
  change mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (f ∘ ν) p (1 : ℂ) ≠ 0 at hu1
  rw [hchain] at hu1
  exact hu1

/-- On E the two unramified restrictions pull back to the same metric. At a
tangency point this determines the actual ambient rank-one forms on all of TX. -/
theorem ambient_metrics_equal_at_intersection (f h : Fibration X)
    (hf : f.Smooth) (hh : h.Smooth) {E : Curve} (ν : HolomorphicMap E X) (p : E)
    (hram : ν p ∈ RamificationSupport.ramificationSet f h)
    (hu : Function.Injective
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (restrictedMap f ν) p))
    (g₁ : ConformalMetric f.base) (g₃ : ConformalMetric h.base)
    (heq : pullback (restrictedMap f ν) g₁ = pullback (restrictedMap h ν) g₃) :
    ∀ v : ℂ × ℂ,
      g₁.weight (f (ν p)) * ‖surfaceDifferential f (ν p) v‖ ^ 2 =
      g₃.weight (h (ν p)) * ‖surfaceDifferential h (ν p) v‖ ^ 2 := by
  let l₁ : (ℂ × ℂ) →L[ℂ] ℂ := mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) f (ν p)
  let l₃ : (ℂ × ℂ) →L[ℂ] ℂ := mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) h (ν p)
  have hjoint : ¬ Function.Surjective (fun v : ℂ × ℂ => (l₁ v, l₃ v)) := by
    exact fun hs => hram ((pairMap_surjective_iff f h (ν p)).mpr hs)
  obtain ⟨a, ⟨_, ha⟩, _⟩ := RamificationCovectors.existsUnique_nonzero_slope
    l₁.toLinearMap l₃.toLinearMap (hf _) (hh _) hjoint
  have haa (v : ℂ × ℂ) : l₃ v = a * l₁ v := ha v
  let e : ℂ × ℂ := mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ) ν p (1 : ℂ)
  have he : l₁ e ≠ 0 := restriction_tangent_nonzero f ν p hu
  have hmetric : g₁.weight (f (ν p)) * ‖l₁ e‖ ^ 2 =
      g₃.weight (h (ν p)) * ‖l₃ e‖ ^ 2 := by
    have hm := congrArg (fun k : ConformalMetric E => squaredNorm k p (1 : ℂ)) heq
    dsimp only at hm
    rw [pullback_squaredNorm, pullback_squaredNorm] at hm
    change g₁.weight (f (ν p)) * ‖curveDifferential (restrictedMap f ν) p (1 : ℂ)‖ ^ 2 =
      g₃.weight (h (ν p)) * ‖curveDifferential (restrictedMap h ν) p (1 : ℂ)‖ ^ 2 at hm
    have hcf : curveDifferential (restrictedMap f ν) p (1 : ℂ) = l₁ e :=
      congrArg (fun A : ℂ →L[ℂ] ℂ => A (1 : ℂ))
        (mfderiv_comp p (f.holomorphic (ν p)) (ν.holomorphic p))
    have hch : curveDifferential (restrictedMap h ν) p (1 : ℂ) = l₃ e :=
      congrArg (fun A : ℂ →L[ℂ] ℂ => A (1 : ℂ))
        (mfderiv_comp p (h.holomorphic (ν p)) (ν.holomorphic p))
    rw [hcf, hch] at hm
    exact hm
  have hmetric' : g₁.weight (f (ν p)) * ‖l₁ e‖ ^ 2 =
      g₃.weight (h (ν p)) * ‖a * l₁ e‖ ^ 2 := by
    simpa only [haa e] using hmetric
  intro v
  have hv := DifferentialRigidity.proportional_metrics_equal l₁.toLinearMap a
    (g₁.weight (f (ν p))) (g₃.weight (h (ν p))) e he hmetric' v
  change g₁.weight (f (ν p)) * ‖l₁ v‖ ^ 2 = g₃.weight (h (ν p)) * ‖l₃ v‖ ^ 2
  rw [haa v]
  exact hv

/-- Lemma 3.1, S3.p2--p3: the actual third restriction to D is unramified
once D meets a tangency curve E with unramified first/third restrictions. -/
theorem third_restriction_unramified_of_intersection (metrics : HyperbolicMetricTheory)
    (f h : Fibration X) (hf : f.Smooth) (hh : h.Smooth)
    (hB : f.Hyperbolic) (hC : h.Hyperbolic)
    {D E : Curve} (νD : HolomorphicMap D X) (νE : HolomorphicMap E X)
    (hD : D.Hyperbolic) (hE : E.Hyperbolic)
    (p : D) (q : E) (hpq : νD p = νE q)
    (hram : νE q ∈ RamificationSupport.ramificationSet f h)
    (hDf : ∀ d, Function.Bijective
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (restrictedMap f νD) d))
    (hEf : ∀ e, Function.Bijective
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (restrictedMap f νE) e))
    (hEh : ∀ e, Function.Bijective
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (restrictedMap h νE) e)) :
    ∀ d, Function.Bijective
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (restrictedMap h νD) d) := by
  have hEfmetric := metrics.covering_isometry E f.base (restrictedMap f νE) hE hB hEf
  have hEhmetric := metrics.covering_isometry E h.base (restrictedMap h νE) hE hC hEh
  have hambient := ambient_metrics_equal_at_intersection f h hf hh νE q hram (hEf q).1
    (metrics.metric f.base) (metrics.metric h.base) (hEfmetric.trans hEhmetric.symm)
  apply metrics.schwarz_pick_equality D h.base (restrictedMap h νD) hD hC
  refine ⟨p, 1, one_ne_zero, ?_⟩
  have hDmetric := metrics.covering_isometry D f.base (restrictedMap f νD) hD hB hDf
  have hDnorm := congrArg (fun k : ConformalMetric D => squaredNorm k p (1 : ℂ)) hDmetric
  dsimp only at hDnorm
  rw [pullback_squaredNorm] at hDnorm
  rw [← hDnorm]
  let t : ℂ × ℂ := mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ) νD p (1 : ℂ)
  have hcf : curveDifferential (restrictedMap f νD) p (1 : ℂ) =
      surfaceDifferential f (νD p) t :=
    congrArg (fun A : ℂ →L[ℂ] ℂ => A (1 : ℂ))
      (mfderiv_comp p (f.holomorphic (νD p)) (νD.holomorphic p))
  have hch : curveDifferential (restrictedMap h νD) p (1 : ℂ) =
      surfaceDifferential h (νD p) t :=
    congrArg (fun A : ℂ →L[ℂ] ℂ => A (1 : ℂ))
      (mfderiv_comp p (h.holomorphic (νD p)) (νD.holomorphic p))
  change (metrics.metric f.base).weight (f (νD p)) *
    ‖curveDifferential (restrictedMap f νD) p (1 : ℂ)‖ ^ 2 =
    (metrics.metric h.base).weight (h (νD p)) *
      ‖curveDifferential (restrictedMap h νD) p (1 : ℂ)‖ ^ 2
  rw [hcf, hch]
  simpa only [hpq] using hambient t

end Paper27.Geometry.MetricTangency
