import Paper27.Geometry.Objects
import Mathlib.Topology.Separation.Connected

/-!
# Connected fibres and factorization

The topological argument below is the connected-fibre argument in P27, Lemma 2.1
and Lemma 3.4.  It is proved for actual topological spaces before specializing to
the holomorphic fibrations.  The only analytic input to the final equivalence
construction is the explicitly named classical theorem saying that a bijective
holomorphic map of compact curves has holomorphic inverse.
-/

noncomputable section

open scoped Manifold Topology

namespace Paper27.Geometry

/-- A finite preconnected subset of a T1 space is a subsingleton. -/
theorem finite_preconnected_subsingleton {B : Type*} [TopologicalSpace B] [T1Space B]
    {s : Set B} (hfinite : s.Finite) (hconnected : IsPreconnected s) : s.Subsingleton := by
  intro x hx y hy
  by_contra hxy
  exact hfinite.not_infinite
    (hconnected.infinite_of_nontrivial ⟨x, hx, y, hy, hxy⟩)

/-- The exact set-theoretic fibre identity for a surjective factorization. -/
theorem image_fibre_eq_factor_fibre {S B C : Type*} (f : S → B) (g : S → C) (α : B → C)
    (hf : Function.Surjective f) (hfactor : ∀ x, α (f x) = g x) (c : C) :
    f '' (g ⁻¹' {c}) = α ⁻¹' {c} := by
  ext b
  constructor
  · rintro ⟨x, hx, rfl⟩
    change α (f x) = c
    exact (hfactor x).trans hx
  · intro hb
    obtain ⟨x, rfl⟩ := hf b
    refine ⟨x, ?_, rfl⟩
    change g x = c
    exact (hfactor x).symm.trans hb

/-- If `g = α ∘ f`, both maps are onto, `g` has connected fibres, and `α` has
finite fibres, continuity of `f` forces `α` to be a bijection.  Neither a degree
axiom nor any smoothness or holomorphicity hypothesis is needed for this step. -/
theorem finite_fibre_factor_bijective {S B C : Type*} [TopologicalSpace S]
    [TopologicalSpace B] [T1Space B] (f : S → B) (g : S → C) (α : B → C)
    (hfcont : Continuous f) (hfsurj : Function.Surjective f)
    (hgsurj : Function.Surjective g) (hgconnected : ∀ c, IsConnected (g ⁻¹' {c}))
    (hfactor : ∀ x, α (f x) = g x) (hfinite : ∀ c, (α ⁻¹' {c}).Finite) :
    Function.Bijective α := by
  have hsub (c : C) : (α ⁻¹' {c}).Subsingleton := by
    apply finite_preconnected_subsingleton (hfinite c)
    rw [← image_fibre_eq_factor_fibre f g α hfsurj hfactor c]
    exact (hgconnected c).isPreconnected.image f hfcont.continuousOn
  constructor
  · intro b b' hbb'
    exact hsub (α b) rfl hbb'.symm
  · intro c
    obtain ⟨x, hx⟩ := hgsurj c
    exact ⟨f x, (hfactor x).trans hx⟩

/-- The named external classical theorem used to upgrade the proved bijection to
a biholomorphism.  It contains no fibration, factorization, or degree-one claim. -/
def BijectiveHolomorphicInverse : Prop :=
  ∀ (C D : Curve) (e : C ≃ D),
    MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e →
      MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e.symm

/-- Nontriviality follows from the actual open complex chart, not from an extra
field on `Curve`. -/
theorem Curve.exists_distinct (C : Curve) : ∃ x y : C, x ≠ y := by
  let e := chartAt ℂ C.basepoint
  have hinfinite : e.target.Infinite :=
    infinite_of_mem_nhds (e C.basepoint) (chart_target_mem_nhds ℂ C.basepoint)
  obtain ⟨u, hu, v, hv, huv⟩ := hinfinite.nontrivial
  refine ⟨e.symm u, e.symm v, fun h => huv ?_⟩
  calc
    u = e (e.symm u) := (e.right_inv hu).symm
    _ = e (e.symm v) := congrArg e h
    _ = v := e.right_inv hv

/-- The standard compact-curve mapping theorem.  Its hypotheses and conclusions
refer only to an actual holomorphic map between the actual compact curves. -/
def NonconstantCompactCurveMapTheorem : Prop :=
  ∀ (C D : Curve) (a : HolomorphicMap C D),
    (∃ x y : C, a x ≠ a y) →
      (∀ d : D, (a ⁻¹' {d}).Finite) ∧ Function.Surjective a

namespace Fibration

variable {X : CompactComplexSurface}

/-- Connected fibres of the actual fibration `g` make its finite-fibre factor
map bijective.  `g` is not assumed smooth. -/
theorem factor_bijective_of_finite_fibres (f g : Fibration X)
    (α : HolomorphicMap f.base g.base) (hfactor : ∀ x, α (f x) = g x)
    (hfinite : ∀ c, (α ⁻¹' {c}).Finite) : Function.Bijective α :=
  finite_fibre_factor_bijective f.map g.map α f.holomorphic.continuous
    f.surjective g.surjective g.connected_fibres hfactor hfinite

/-- The explicit analytic inverse theorem and the proved connected-fibre
argument give the biholomorphism needed in both Lemma 2.1 and Lemma 3.4. -/
def factorBiholomorphism (inverseTheorem : BijectiveHolomorphicInverse)
    (f g : Fibration X) (α : HolomorphicMap f.base g.base)
    (hfactor : ∀ x, α (f x) = g x) (hfinite : ∀ c, (α ⁻¹' {c}).Finite) :
    Biholomorphism f.base g.base where
  toEquiv := Equiv.ofBijective α (factor_bijective_of_finite_fibres f g α hfactor hfinite)
  holomorphic := α.holomorphic
  inverse_holomorphic := inverseTheorem f.base g.base _ α.holomorphic

theorem equivalent_of_factorization (inverseTheorem : BijectiveHolomorphicInverse)
    (f g : Fibration X) (α : HolomorphicMap f.base g.base)
    (hfactor : ∀ x, α (f x) = g x) (hfinite : ∀ c, (α ⁻¹' {c}).Finite) :
    Equivalent f g :=
  ⟨factorBiholomorphism inverseTheorem f g α hfactor hfinite, hfactor⟩

/-- The actual assertion that `g` is constant on the specified fibre of `f`. -/
def ConstantOnFibre (f g : Fibration X) (b : f.base) : Prop :=
  ∀ p q : X, f p = b → f q = b → g p = g q

/-- The two precise degree facts used in Lemma 2.1.  These are explicit inputs
from the classical degree theory of smooth proper families and compact curves.
They do not contain a factorization or the conclusion of Lemma 2.1. -/
structure FibreDegreeFacts (f g : Fibration X) where
  degree : f.base → ℕ
  degree_independent : ∀ b b', degree b = degree b'
  degree_zero_iff_constant : ∀ b, degree b = 0 ↔ ConstantOnFibre f g b

theorem constant_on_all_fibres_of_constant_one {f g : Fibration X}
    (degrees : FibreDegreeFacts f g) (b₀ : f.base) (h₀ : ConstantOnFibre f g b₀) :
    ∀ b, ConstantOnFibre f g b := by
  intro b
  apply (degrees.degree_zero_iff_constant b).mp
  exact (degrees.degree_independent b b₀).trans
    ((degrees.degree_zero_iff_constant b₀).mpr h₀)

/-- Explicit local holomorphic right inverses to `f`.  The section is extended
arbitrarily outside its open domain; differentiability is required only there. -/
def LocalHolomorphicSections (f : Fibration X) : Prop :=
  ∀ b : f.base, ∃ U : Set f.base, IsOpen U ∧ b ∈ U ∧
    ∃ s : f.base → X,
      MDifferentiableOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ) s U ∧
        ∀ y ∈ U, f (s y) = y

/-- The descended function is constructed by choosing an actual point of each
nonempty fibre.  Fibrewise constancy makes this choice immaterial. -/
def descendedFunction (f g : Fibration X) (b : f.base) : g.base :=
  g (Classical.choose (f.surjective b))

theorem descendedFunction_factor (f g : Fibration X)
    (hconstant : ∀ b, ConstantOnFibre f g b) (p : X) :
    descendedFunction f g (f p) = g p :=
  hconstant (f p) _ p (Classical.choose_spec (f.surjective (f p))) rfl

/-- Local sections give holomorphic descent; this construction is proved rather
than included in the external input. -/
theorem descendedFunction_holomorphic (f g : Fibration X)
    (hconstant : ∀ b, ConstantOnFibre f g b) (sections : LocalHolomorphicSections f) :
    MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (descendedFunction f g) := by
  intro b
  obtain ⟨U, hU, hb, s, hs, hright⟩ := sections b
  have hcomp := (g.holomorphic (s b)).comp b (hs.mdifferentiableAt (hU.mem_nhds hb))
  apply hcomp.congr_of_eventuallyEq
  exact Filter.eventually_of_mem (hU.mem_nhds hb) fun y hy => by
    change descendedFunction f g y = g (s y)
    calc
      descendedFunction f g y = descendedFunction f g (f (s y)) :=
        congrArg (descendedFunction f g) (hright y hy).symm
      _ = g (s y) := descendedFunction_factor f g hconstant (s y)

def descendedHolomorphicMap (f g : Fibration X)
    (hconstant : ∀ b, ConstantOnFibre f g b) (sections : LocalHolomorphicSections f) :
    HolomorphicMap f.base g.base where
  toFun := descendedFunction f g
  holomorphic := descendedFunction_holomorphic f g hconstant sections

/-- A holomorphic factor of an onto fibration is onto. -/
theorem factor_surjective (f g : Fibration X) (α : f.base → g.base)
    (hfactor : ∀ x, α (f x) = g x) : Function.Surjective α := by
  intro c
  obtain ⟨p, hp⟩ := g.surjective c
  exact ⟨f p, (hfactor p).trans hp⟩

theorem surjective_curve_map_nonconstant {C D : Curve} (a : C → D)
    (ha : Function.Surjective a) : ∃ x y, a x ≠ a y := by
  obtain ⟨d, d', hdd'⟩ := D.exists_distinct
  obtain ⟨c, hc⟩ := ha d
  obtain ⟨c', hc'⟩ := ha d'
  exact ⟨c, c', fun h => hdd' (hc.symm.trans (h.trans hc'))⟩

/-- Inequivalence rules out a constant fibre once the classical degree facts and
local sections are supplied.  This is the first argument of Lemma 2.1. -/
theorem no_constant_fibre_of_inequivalent
    (curveMaps : NonconstantCompactCurveMapTheorem)
    (inverseTheorem : BijectiveHolomorphicInverse) (f g : Fibration X)
    (degrees : FibreDegreeFacts f g) (sections : LocalHolomorphicSections f)
    (hne : ¬ Equivalent f g) : ∀ b, ¬ ConstantOnFibre f g b := by
  intro b hb
  have hall := constant_on_all_fibres_of_constant_one degrees b hb
  let α := descendedHolomorphicMap f g hall sections
  have hfactor : ∀ p, α (f p) = g p := descendedFunction_factor f g hall
  have hnonconstant := surjective_curve_map_nonconstant α (factor_surjective f g α hfactor)
  have hfinite := (curveMaps f.base g.base α hnonconstant).1
  exact hne (equivalent_of_factorization inverseTheorem f g α hfactor hfinite)

/-- Actual finite fibres of the joint map. -/
def FinitePair (f g : Fibration X) : Prop :=
  ∀ bc : f.base × g.base, {p : X | f p = bc.1 ∧ g p = bc.2}.Finite

/-- Actual surjectivity of the joint map. -/
def PairSurjective (f g : Fibration X) : Prop :=
  Function.Surjective (fun p : X => (f p, g p))

end Fibration

/-- The actual smooth fibre as a compact curve, identified with the actual fibre
subtype by a homeomorphism, with holomorphic inclusion into the surface.  The
existence of these models is the classical smooth-fibre theorem. -/
structure FibreCurveModel {X : CompactComplexSurface} (f : Fibration X) (b : f.base) where
  curve : Curve
  identify : curve ≃ₜ {p : X // f p = b}
  holomorphic_inclusion :
    MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ) (fun q : curve => (identify q).val)

namespace FibreCurveModel

variable {X : CompactComplexSurface} {f : Fibration X} {b : f.base}

def inclusion (F : FibreCurveModel f b) : HolomorphicMap F.curve X where
  toFun := fun q => (F.identify q).val
  holomorphic := F.holomorphic_inclusion

def restriction (F : FibreCurveModel f b) (g : Fibration X) : HolomorphicMap F.curve g.base where
  toFun := fun q => g (F.inclusion q)
  holomorphic := g.holomorphic.comp F.inclusion.holomorphic

@[simp] theorem map_inclusion (F : FibreCurveModel f b) (q : F.curve) :
    f (F.inclusion q) = b := (F.identify q).property

theorem inclusion_symm (F : FibreCurveModel f b) (p : X) (hp : f p = b) :
    F.inclusion (F.identify.symm ⟨p, hp⟩) = p :=
  congrArg Subtype.val (F.identify.apply_symm_apply ⟨p, hp⟩)

theorem restriction_nonconstant (F : FibreCurveModel f b) (g : Fibration X)
    (hn : ¬ Fibration.ConstantOnFibre f g b) :
    ∃ q r : F.curve, F.restriction g q ≠ F.restriction g r := by
  by_contra h
  apply hn
  intro p p' hp hp'
  let q := F.identify.symm ⟨p, hp⟩
  let r := F.identify.symm ⟨p', hp'⟩
  have heq : F.restriction g q = F.restriction g r := by
    by_contra hqr
    exact h ⟨q, r, hqr⟩
  change g (F.inclusion q) = g (F.inclusion r) at heq
  simpa only [q, r, F.inclusion_symm] using heq

theorem pair_fibre_eq_image (F : FibreCurveModel f b) (g : Fibration X) (c : g.base) :
    {p : X | f p = b ∧ g p = c} = F.inclusion '' (F.restriction g ⁻¹' {c}) := by
  ext p
  constructor
  · intro hp
    refine ⟨F.identify.symm ⟨p, hp.1⟩, ?_, F.inclusion_symm p hp.1⟩
    change g (F.inclusion (F.identify.symm ⟨p, hp.1⟩)) = c
    rw [F.inclusion_symm]
    exact hp.2
  · rintro ⟨q, hq, rfl⟩
    exact ⟨F.map_inclusion q, hq⟩

end FibreCurveModel

namespace Fibration

variable {X : CompactComplexSurface}

/-- Lemma 2.1, with every unformalized classical input displayed separately.
The propagation of constancy, holomorphic descent, connected-fibre bijection,
and passage from fibre restrictions to the joint map are all proved here. -/
theorem finitePair_pairSurjective_of_inequivalent
    (curveMaps : NonconstantCompactCurveMapTheorem)
    (inverseTheorem : BijectiveHolomorphicInverse) (f g : Fibration X)
    (hf : f.Smooth) (_hg : g.Smooth)
    (fibreModels : f.Smooth → ∀ b, FibreCurveModel f b)
    (degrees : f.Smooth → FibreDegreeFacts f g)
    (sections : f.Smooth → LocalHolomorphicSections f)
    (hne : ¬ Equivalent f g) : FinitePair f g ∧ PairSurjective f g := by
  have hnc := no_constant_fibre_of_inequivalent curveMaps inverseTheorem f g
    (degrees hf) (sections hf) hne
  have hrestr (b : f.base) := curveMaps (fibreModels hf b).curve g.base
    ((fibreModels hf b).restriction g)
    ((fibreModels hf b).restriction_nonconstant g (hnc b))
  constructor
  · intro bc
    rw [(fibreModels hf bc.1).pair_fibre_eq_image g bc.2]
    exact ((hrestr bc.1).1 bc.2).image (fibreModels hf bc.1).inclusion
  · rintro ⟨b, c⟩
    obtain ⟨q, hq⟩ := (hrestr b).2 c
    refine ⟨(fibreModels hf b).inclusion q, ?_⟩
    exact Prod.ext ((fibreModels hf b).map_inclusion q) hq

end Fibration

end Paper27.Geometry
