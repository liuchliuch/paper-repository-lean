import Paper27.Geometry.NeighbourhoodSplittings

/-!
# Actual covering retractions and transverse neighbourhoods

The factorization `(f|D) ∘ r = f` is differentiated on the actual open
neighbourhood. Since the restricted curve map is unramified, it gives actual
kernel equality and equivalence of the two joint nonsingularity conditions.
Disjointness from the actual paired ramification set then permits shrinking
to an actual transverse neighbourhood.

Only general classical facts remain parameters: a compact unramified curve
map is a covering; a specified covering lift along a compact embedded curve
extends continuously to a neighbourhood; a continuous lift through a
holomorphic etale map is holomorphic; and the nonsingular locus of a joint
holomorphic derivative is open. No cyclic model, group action, ramification
index, or normal degree occurs in these interfaces.
-/

noncomputable section

open scoped Manifold Topology
open Filter

namespace Paper27.Geometry.RetractionFactorization

variable {X : CompactComplexSurface} {D : EmbeddedCurve X} {U : D.Neighbourhood}

def Factorization (r : D.Retraction U) (f : Fibration X) : Prop :=
  ∀ x ∈ U.domain, D.restrictedMap f (r.toFun x) = f x

theorem factorization_derivative (r : D.Retraction U) (f : Fibration X)
    (hfactor : Factorization r f) (p : U.domain) :
    (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (D.restrictedMap f) (r.toFun p.val)).comp
      (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) r.toFun p.val) =
        mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) f p.val := by
  have heq : (D.restrictedMap f) ∘ r.toFun =ᶠ[𝓝 p.val] f.map :=
    Filter.eventually_of_mem (U.open_domain.mem_nhds p.property)
      (fun x hx => hfactor x hx)
  rw [← mfderiv_comp p.val ((D.restrictedMap f).holomorphic _)
    ((r.holomorphic _ p.property).mdifferentiableAt (U.open_domain.mem_nhds p.property))]
  exact heq.mfderiv_eq

/-- Actual kernel equality follows from the actual factorization and
injectivity of the actual restricted curve differential. -/
theorem retraction_kernel_eq (r : D.Retraction U) (f : Fibration X)
    (hunramified : D.Unramified f) (hfactor : Factorization r f) (p : U.domain) :
    LinearMap.ker (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) r.toFun p.val).toLinearMap =
      LinearMap.ker (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) f p.val).toLinearMap := by
  ext v
  change mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) r.toFun p.val v = 0 ↔
    mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) f p.val v = 0
  have hderiv := congrArg (fun l : (ℂ × ℂ) →L[ℂ] ℂ => l v)
    (factorization_derivative r f hfactor p)
  change mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (D.restrictedMap f) (r.toFun p.val)
    (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) r.toFun p.val v) =
      mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) f p.val v at hderiv
  constructor
  · intro hr
    simpa only [ContinuousLinearMap.comp_apply, hr, map_zero] using hderiv.symm
  · intro hf
    apply (hunramified (r.toFun p.val)).1
    simpa only [ContinuousLinearMap.comp_apply, hf, map_zero] using hderiv

/-- Postcomposing the first scalar coordinate with a bijection preserves
bijectivity of a joint map. -/
theorem joint_bijective_iff_scalar_bijection (a : ℂ → ℂ) (ha : Function.Bijective a)
    (l k : (ℂ × ℂ) → ℂ) :
    Function.Bijective (fun v => (l v, k v)) ↔
      Function.Bijective (fun v => (a (l v), k v)) := by
  let e : ℂ ≃ ℂ := Equiv.ofBijective a ha
  let E : (ℂ × ℂ) ≃ (ℂ × ℂ) := e.prodCongr (Equiv.refl ℂ)
  change Function.Bijective (fun v => (l v, k v)) ↔
    Function.Bijective (E ∘ fun v => (l v, k v))
  constructor
  · intro h
    exact E.bijective.comp h
  · intro h
    have hinv := E.symm.bijective.comp h
    convert hinv using 1
    funext v
    exact (E.symm_apply_apply (l v, k v)).symm

/-- The actual joint differential of two maps to actual curves. -/
def jointDifferential {B C : Curve} (f : HolomorphicMap X B) (h : HolomorphicMap X C)
    (p : X) : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) f p).prod
    (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) h p)

/-- The actual joint (dr,dh) is nonsingular exactly when (df,dh) is. -/
theorem joint_bijective_iff (r : D.Retraction U) (f h : Fibration X)
    (hunramified : D.Unramified f) (hfactor : Factorization r f) (p : U.domain) :
    Function.Bijective (NeighbourhoodSplittings.jointDifferential r
      (CoordinateCalculus.fibrationMap h) p) ↔
    Function.Bijective (jointDifferential (CoordinateCalculus.fibrationMap f)
      (CoordinateCalculus.fibrationMap h) p.val) := by
  let a : ℂ →L[ℂ] ℂ := mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (D.restrictedMap f) (r.toFun p.val)
  let l : (ℂ × ℂ) →L[ℂ] ℂ := mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) r.toFun p.val
  let k : (ℂ × ℂ) →L[ℂ] ℂ := mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) h p.val
  have hderiv : a.comp l = mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) f p.val :=
    factorization_derivative r f hfactor p
  have hiff := joint_bijective_iff_scalar_bijection a
    (hunramified (r.toFun p.val)) l k
  have hcomp : (fun v => (a (l v), k v)) =
      jointDifferential (CoordinateCalculus.fibrationMap f)
        (CoordinateCalculus.fibrationMap h) p.val := by
    funext v
    exact Prod.ext (congrArg (fun L : (ℂ × ℂ) →L[ℂ] ℂ => L v) hderiv) rfl
  rw [hcomp] at hiff
  exact hiff

theorem joint_bijective_of_not_ramified (f h : Fibration X) (x : X)
    (hx : x ∉ RamificationSupport.ramificationSet f h) :
    Function.Bijective (jointDifferential (CoordinateCalculus.fibrationMap f)
      (CoordinateCalculus.fibrationMap h) x) := by
  classical
  have hpair : Function.Surjective
      (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (RamificationSupport.pairMap f h) x) :=
    not_not.mp hx
  have hs : Function.Surjective (jointDifferential (CoordinateCalculus.fibrationMap f)
      (CoordinateCalculus.fibrationMap h) x) :=
    (CoordinateCalculus.pairMap_surjective_iff f h x).mp hpair
  exact ⟨(LinearMap.injective_iff_surjective
    (f := (jointDifferential (CoordinateCalculus.fibrationMap f)
      (CoordinateCalculus.fibrationMap h) x).toLinearMap)).mpr hs, hs⟩

/-- Disjointness from the actual pair ramification gives actual transverse
retraction/third-map differentials at every point of the embedded curve. -/
theorem transverse_along_curve (r : D.Retraction U) (f h : Fibration X)
    (hunramified : D.Unramified f) (hfactor : Factorization r f)
    (hdisjoint : D.DisjointFromPair f h) (p : D.curve) :
    Function.Bijective (NeighbourhoodSplittings.jointDifferential r
      (CoordinateCalculus.fibrationMap h) (NeighbourhoodSplittings.curvePoint U p)) := by
  apply (joint_bijective_iff r f h hunramified hfactor _).mpr
  apply joint_bijective_of_not_ramified f h
  exact fun hr => Set.disjoint_left.mp hdisjoint ⟨p, rfl⟩ hr

/-- The ordinary openness of the nonsingular joint holomorphic derivative
locus, quantified over all actual maps and without ramification data. -/
def NonsingularJointLocusOpen : Prop :=
  ∀ (X : CompactComplexSurface) (B C : Curve)
    (f : HolomorphicMap X B) (h : HolomorphicMap X C),
    IsOpen {x : X | Function.Bijective (jointDifferential f h x)}

def restrictRetraction (r : D.Retraction U) (V : D.Neighbourhood)
    (hsub : V.domain ⊆ U.domain) : D.Retraction V where
  toFun := r.toFun
  holomorphic := r.holomorphic.mono hsub
  retract := r.retract

/-- Shrink by the actual open nonsingular locus. No arbitrary transverse
neighbourhood or per-pair transversality theorem is an input. -/
theorem exists_transverse_neighbourhood (openness : NonsingularJointLocusOpen)
    (r : D.Retraction U) (f h : Fibration X) (hunramified : D.Unramified f)
    (hfactor : Factorization r f) (hdisjoint : D.DisjointFromPair f h) :
    ∃ (V : D.Neighbourhood) (r' : D.Retraction V),
      V.domain ⊆ U.domain ∧ Factorization r' f ∧
      NeighbourhoodSplittings.JointTransverse r' (CoordinateCalculus.fibrationMap h) := by
  let V : D.Neighbourhood :=
    { domain := U.domain ∩ {x : X | Function.Bijective
        (jointDifferential (CoordinateCalculus.fibrationMap f)
          (CoordinateCalculus.fibrationMap h) x)}
      open_domain := U.open_domain.inter
        (openness X f.base h.base (CoordinateCalculus.fibrationMap f)
          (CoordinateCalculus.fibrationMap h))
      contains := fun p => ⟨U.contains p, joint_bijective_of_not_ramified f h _
        (fun hr => Set.disjoint_left.mp hdisjoint ⟨p, rfl⟩ hr)⟩ }
  let r' := restrictRetraction r V (fun _ hx => hx.1)
  have hfactor' : Factorization r' f := fun x hx => hfactor x hx.1
  refine ⟨V, r', (fun _ hx => hx.1), hfactor', ?_⟩
  intro p
  exact (joint_bijective_iff r' f h hunramified hfactor' p).mpr p.property.2

/-- A compact unramified actual curve map is a topological covering. -/
def CompactUnramifiedCurveCovering : Prop :=
  ∀ (C B : Curve) (a : HolomorphicMap C B),
    (∀ p : C, Function.Bijective (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) a p)) → IsCoveringMap a

/-- A continuous extension of the specified covering lift along the actual
embedded compact curve. This is topological data, with no holomorphic claim. -/
structure ContinuousCoverLift (D : EmbeddedCurve X) {B : Curve}
    (a : HolomorphicMap D.curve B) (f : HolomorphicMap X B) where
  neighbourhood : D.Neighbourhood
  lift : X → D.curve
  continuous : ContinuousOn lift neighbourhood.domain
  retract : ∀ p : D.curve, lift (D.inclusion p) = p
  factor : ∀ x ∈ neighbourhood.domain, a (lift x) = f x

/-- The general covering-neighbourhood lifting theorem: a specified lift of
a continuous map on a compact embedded submanifold extends over some open
neighbourhood. The complex objects here supply the underlying actual smooth
embedded compact submanifold; no cyclic classification is involved. -/
def TopologicalCoverNeighbourhoodLifting : Prop :=
  ∀ (X : CompactComplexSurface) (D : EmbeddedCurve X) (B : Curve)
    (a : HolomorphicMap D.curve B) (f : HolomorphicMap X B), IsCoveringMap a →
    (∀ p : D.curve, a p = f (D.inclusion p)) → Nonempty (ContinuousCoverLift D a f)

/-- A continuous lift through a holomorphic etale map is holomorphic, by its
local holomorphic inverses. This general local calculus theorem only upgrades
regularity of the given actual lift; it constructs neither r nor its factor. -/
def HolomorphicEtaleLiftRegularity : Prop :=
  ∀ (X : CompactComplexSurface) (C B : Curve) (a : HolomorphicMap C B)
    (f : HolomorphicMap X B),
    (∀ p : C, Function.Bijective (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) a p)) →
    ∀ (V : Set X), IsOpen V → ∀ (lift : X → C), ContinuousOn lift V →
    (∀ x ∈ V, a (lift x) = f x) → MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) lift V

/-- Upgrade the actual continuous lift to an actual holomorphic retraction. -/
def ContinuousCoverLift.holomorphicRetraction (regularity : HolomorphicEtaleLiftRegularity)
    {B : Curve} {a : HolomorphicMap D.curve B} {f : HolomorphicMap X B}
    (L : ContinuousCoverLift D a f)
    (ha : ∀ p : D.curve, Function.Bijective (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) a p)) :
    D.Retraction L.neighbourhood where
  toFun := L.lift
  holomorphic := regularity X D.curve B a f ha L.neighbourhood.domain
    L.neighbourhood.open_domain L.lift L.continuous L.factor
  retract := L.retract

structure FactoredRetraction (D : EmbeddedCurve X) (f : Fibration X) where
  neighbourhood : D.Neighbourhood
  retraction : D.Retraction neighbourhood
  factor : Factorization retraction f

/-- The actual unramified restriction supplies its covering lift and hence a
factored holomorphic retraction, from only general classical inputs. -/
def factoredRetraction (covering : CompactUnramifiedCurveCovering)
    (lifting : TopologicalCoverNeighbourhoodLifting) (regularity : HolomorphicEtaleLiftRegularity)
    (D : EmbeddedCurve X) (f : Fibration X) (hf : D.Unramified f) : FactoredRetraction D f := by
  let L := Classical.choice (lifting X D f.base (D.restrictedMap f)
    (CoordinateCalculus.fibrationMap f) (covering D.curve f.base (D.restrictedMap f) hf)
    (fun _ => rfl))
  exact ⟨L.neighbourhood, L.holomorphicRetraction regularity hf, L.factor⟩

structure TransverseFactoredRetraction (D : EmbeddedCurve X) (f h : Fibration X)
    extends FactoredRetraction D f where
  transverse : NeighbourhoodSplittings.JointTransverse retraction
    (CoordinateCalculus.fibrationMap h)

/-- The actual retraction/factor/transverse data required by Lemma 3.2,
constructed from an unramified actual restriction and actual disjointness.
The remaining inputs are universal covering/local-calculus theorems. -/
theorem nonempty_transverseFactoredRetraction (covering : CompactUnramifiedCurveCovering)
    (lifting : TopologicalCoverNeighbourhoodLifting) (regularity : HolomorphicEtaleLiftRegularity)
    (openness : NonsingularJointLocusOpen) (D : EmbeddedCurve X) (f h : Fibration X)
    (hf : D.Unramified f) (hdisjoint : D.DisjointFromPair f h) :
    Nonempty (TransverseFactoredRetraction D f h) := by
  let R := factoredRetraction covering lifting regularity D f hf
  obtain ⟨V, r, _, hfactor, htransverse⟩ := exists_transverse_neighbourhood openness
    R.retraction f h hf R.factor hdisjoint
  exact ⟨⟨⟨V, r, hfactor⟩, htransverse⟩⟩

end Paper27.Geometry.RetractionFactorization
