import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Algebra.Module.NatInt
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# The geometric objects and the statement of P27

All charts, topological conditions, holomorphicity, and submersion conditions in
this file use mathlib's actual definitions.  In particular, the genus of a curve
is half the integer rank of the abelianization of its fundamental group, rather
than an extra label on the object.  No geometric theorem is assumed in this file.

The definition of `Fibration` deliberately does not require a submersion: P27,
Lemma 3.4, also considers a third fibration that is not assumed smooth.
-/

noncomputable section

open scoped Manifold

namespace Paper27.Geometry

/-- A compact connected Hausdorff second countable complex manifold, with the
specified model vector space.  The two models used below have complex dimension
one and two respectively. -/
structure CompactComplexManifold (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] where
  Carrier : Type
  [topology : TopologicalSpace Carrier]
  [hausdorff : T2Space Carrier]
  [secondCountable : SecondCountableTopology Carrier]
  [connected : ConnectedSpace Carrier]
  [compact : CompactSpace Carrier]
  [charted : ChartedSpace E Carrier]
  [manifold : IsManifold 𝓘(ℂ, E) 1 Carrier]

namespace CompactComplexManifold

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

instance : CoeSort (CompactComplexManifold E) Type := ⟨fun M => M.Carrier⟩

instance (M : CompactComplexManifold E) : TopologicalSpace M := M.topology
instance (M : CompactComplexManifold E) : T2Space M := M.hausdorff
instance (M : CompactComplexManifold E) : SecondCountableTopology M := M.secondCountable
instance (M : CompactComplexManifold E) : ConnectedSpace M := M.connected
instance (M : CompactComplexManifold E) : CompactSpace M := M.compact
instance (M : CompactComplexManifold E) : ChartedSpace E M := M.charted
instance (M : CompactComplexManifold E) : IsManifold 𝓘(ℂ, E) 1 M := M.manifold

end CompactComplexManifold

/-- A compact complex surface, with actual charts in `ℂ × ℂ`. -/
abbrev CompactComplexSurface := CompactComplexManifold (ℂ × ℂ)

/-- A compact connected complex curve, with actual charts in `ℂ`. -/
abbrev Curve := CompactComplexManifold ℂ

namespace Curve

/-- A chosen point of the actual nonempty connected curve. -/
def basepoint (C : Curve) : C := Classical.choice (inferInstance : Nonempty C)

/-- The integral first homology group described by the abelianized fundamental group. -/
abbrev FirstHomology (C : Curve) :=
  Additive (Abelianization (FundamentalGroup C C.basepoint))

/-- The first Betti number, as the actual integer module rank of the abelianized
fundamental group.  As usual for mathlib `finrank`, infinite rank returns zero. -/
def firstBettiNumber (C : Curve) : ℕ := Module.finrank ℤ C.FirstHomology

/-- Topological genus: half the rank of the abelianized fundamental group.
The identification with the usual surface genus is a classical topological
theorem, rather than an additional datum or hypothesis in this definition. -/
def genus (C : Curve) : ℕ := C.firstBettiNumber / 2

/-- The base curves counted in P27 have genus at least two. -/
def Hyperbolic (C : Curve) : Prop := 2 ≤ C.genus

end Curve

/-- A holomorphic map between the actual complex manifolds.  Complex manifold
differentiability is holomorphicity in these finite dimensional complex models. -/
structure HolomorphicMapModel {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (M : CompactComplexManifold E) (N : CompactComplexManifold F) where
  toFun : M → N
  holomorphic : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) toFun

instance {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {M : CompactComplexManifold E} {N : CompactComplexManifold F} :
    CoeFun (HolomorphicMapModel M N) (fun _ => M → N) := ⟨fun f => f.toFun⟩

abbrev HolomorphicMap {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (M : CompactComplexManifold E) (N : CompactComplexManifold F) := HolomorphicMapModel M N

/-- A biholomorphism of curves is an actual equivalence with both directions
complex manifold differentiable. -/
structure Biholomorphism (C D : Curve) where
  toEquiv : C ≃ D
  holomorphic : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) toEquiv
  inverse_holomorphic : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) toEquiv.symm

namespace Biholomorphism

instance {C D : Curve} : CoeFun (Biholomorphism C D) (fun _ => C → D) :=
  ⟨fun e => e.toEquiv⟩

def refl (C : Curve) : Biholomorphism C C where
  toEquiv := Equiv.refl C
  holomorphic := mdifferentiable_id
  inverse_holomorphic := mdifferentiable_id

def symm {C D : Curve} (e : Biholomorphism C D) : Biholomorphism D C where
  toEquiv := e.toEquiv.symm
  holomorphic := e.inverse_holomorphic
  inverse_holomorphic := e.holomorphic

def trans {C D E : Curve} (e : Biholomorphism C D) (f : Biholomorphism D E) :
    Biholomorphism C E where
  toEquiv := e.toEquiv.trans f.toEquiv
  holomorphic := f.holomorphic.comp e.holomorphic
  inverse_holomorphic := e.inverse_holomorphic.comp f.inverse_holomorphic

/-- A biholomorphism gives an actual homeomorphism of the underlying spaces. -/
def toHomeomorph {C D : Curve} (e : Biholomorphism C D) : C ≃ₜ D where
  toEquiv := e.toEquiv
  continuous_toFun := e.holomorphic.continuous
  continuous_invFun := e.inverse_holomorphic.continuous

@[simp] theorem symm_apply_apply {C D : Curve} (e : Biholomorphism C D) (x : C) :
    e.symm (e x) = x := e.toEquiv.symm_apply_apply x

@[simp] theorem apply_symm_apply {C D : Curve} (e : Biholomorphism C D) (x : D) :
    e (e.symm x) = x := e.toEquiv.apply_symm_apply x

end Biholomorphism

/-- A holomorphic fibration is a surjective holomorphic map with connected fibres.
Smoothness is kept as a separate predicate below. -/
structure Fibration (X : CompactComplexSurface) where
  base : Curve
  map : X → base
  holomorphic : MDifferentiable 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) map
  surjective : Function.Surjective map
  connected_fibres : ∀ b : base, IsConnected (map ⁻¹' {b})

namespace Fibration

variable {X : CompactComplexSurface}

instance : CoeFun (Fibration X) (fun f => X → f.base) := ⟨fun f => f.map⟩

/-- Smoothness in the sense of P27: the actual complex manifold differential is
surjective at every point. -/
def Smooth (f : Fibration X) : Prop :=
  ∀ p : X, Function.Surjective (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) f.map p)

def Hyperbolic (f : Fibration X) : Prop := f.base.Hyperbolic

/-- Equivalence only changes the base by a biholomorphism; the surface and its
points stay fixed, exactly as in the definition of equivalence used in P27. -/
def Equivalent (f g : Fibration X) : Prop :=
  ∃ e : Biholomorphism f.base g.base, ∀ p : X, e (f p) = g p

theorem equivalent_refl (f : Fibration X) : Equivalent f f :=
  ⟨Biholomorphism.refl f.base, fun _ => rfl⟩

theorem equivalent_symm {f g : Fibration X} (h : Equivalent f g) : Equivalent g f := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, fun p => ?_⟩
  rw [← he p]
  exact e.symm_apply_apply (f p)

theorem equivalent_trans {f g h : Fibration X}
    (hfg : Equivalent f g) (hgh : Equivalent g h) : Equivalent f h := by
  obtain ⟨e, he⟩ := hfg
  obtain ⟨e', he'⟩ := hgh
  refine ⟨e.trans e', fun p => ?_⟩
  change e' (e (f p)) = h p
  rw [he p, he' p]

instance equivalenceSetoid : Setoid (Fibration X) where
  r := Equivalent
  iseqv := ⟨equivalent_refl, equivalent_symm, equivalent_trans⟩

end Fibration

/-- Smooth fibrations form a subtype, without imposing smoothness on other uses
of `Fibration`. -/
abbrev SmoothFibration (X : CompactComplexSurface) := {f : Fibration X // f.Smooth}

/-- The objects counted in the theorem. -/
abbrev HyperbolicSmoothFibration (X : CompactComplexSurface) :=
  {f : Fibration X // f.Smooth ∧ f.Hyperbolic}

instance {X : CompactComplexSurface} : Setoid (HyperbolicSmoothFibration X) :=
  Setoid.comap Subtype.val Fibration.equivalenceSetoid

/-- The theorem's conclusion, in a form that also handles zero or one fibration:
among any three smooth hyperbolic fibrations two are equivalent by a base
biholomorphism.  This definition asserts no proof of the conclusion. -/
def AtMostTwoSmoothHyperbolicFibrations (X : CompactComplexSurface) : Prop :=
  ∀ f g h : HyperbolicSmoothFibration X,
    Fibration.Equivalent f.val g.val ∨
      Fibration.Equivalent f.val h.val ∨ Fibration.Equivalent g.val h.val

/-- The equivalent cardinality-free formulation directly on equivalence classes. -/
def AtMostTwoFibrationClasses (X : CompactComplexSurface) : Prop :=
  ∀ a b c : Quotient (inferInstance : Setoid (HyperbolicSmoothFibration X)),
    a = b ∨ a = c ∨ b = c

/-- Passing to the quotient neither strengthens nor weakens the theorem's
conclusion.  This is a quotient argument, with no geometric hypotheses. -/
theorem atMostTwoSmoothHyperbolicFibrations_iff_classes (X : CompactComplexSurface) :
    AtMostTwoSmoothHyperbolicFibrations X ↔ AtMostTwoFibrationClasses X := by
  constructor
  · intro h a b c
    refine Quotient.inductionOn₃ a b c ?_
    intro f g k
    rcases h f g k with hfg | hfk | hgk
    · exact Or.inl (Quotient.sound hfg)
    · exact Or.inr (Or.inl (Quotient.sound hfk))
    · exact Or.inr (Or.inr (Quotient.sound hgk))
  · intro h f g k
    rcases h (Quotient.mk _ f) (Quotient.mk _ g) (Quotient.mk _ k) with hfg | hfk | hgk
    · exact Or.inl (Quotient.exact hfg)
    · exact Or.inr (Or.inl (Quotient.exact hfk))
    · exact Or.inr (Or.inr (Quotient.exact hgk))

end Paper27.Geometry
