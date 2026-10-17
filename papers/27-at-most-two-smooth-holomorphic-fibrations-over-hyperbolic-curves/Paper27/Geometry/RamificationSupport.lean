import Paper27.Geometry.ProductCover
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Topology.Maps.Proper.Basic

/-!
# The actual ramification set and the unramified pair

The ramification set is the failure of surjectivity of the actual complex
manifold differential of the paired map. Both model tangent spaces are `ℂ²`;
finite dimensional linear algebra, not an unramified label, supplies injectivity
from surjectivity. Compactness supplies properness of the actual paired map.

The sole additional classical interface is the general covering theorem for
proper surjective holomorphic maps with finite fibres and nonsingular actual
differential. It contains neither a fibration equivalence nor any bound on the
number of fibrations. The final theorem then applies the separately proved
unramified product-cover argument, with its previously registered classical
parameters left explicit.
-/

noncomputable section

open scoped Manifold

namespace Paper27.Geometry.RamificationSupport

variable {X : CompactComplexSurface}

/-- The actual paired holomorphic map, to the actual product complex surface. -/
def pairMap (f g : Fibration X) : HolomorphicMap X (f.base.productSurface g.base) where
  toFun := fun p => (f p, g p)
  holomorphic := by
    simpa only [← modelWithCornersSelf_prod] using f.holomorphic.prodMk g.holomorphic

/-- The actual ramification locus of the pair. -/
def ramificationSet (f g : Fibration X) : Set X :=
  {p : X | ¬ Function.Surjective
    (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (pairMap f g) p)}

theorem ramificationSet_empty_iff (f g : Fibration X) :
    ramificationSet f g = ∅ ↔ ∀ p : X, Function.Surjective
      (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (pairMap f g) p) := by
  simp only [Set.eq_empty_iff_forall_notMem, ramificationSet, Set.mem_setOf_eq, not_not]

/-- The actual tangent model of the surface has complex dimension two. -/
theorem surface_tangent_finrank (p : X) :
    Module.finrank ℂ (TangentSpace 𝓘(ℂ, ℂ × ℂ) p) = 2 := by
  change Module.finrank ℂ (ℂ × ℂ) = 2
  rw [Module.finrank_prod]
  simp

/-- Empty ramification gives actual bijectivity of the differential. The
linear map is an endomorphism of the two-dimensional model `ℂ × ℂ`. -/
theorem pair_differential_bijective_of_empty (f g : Fibration X)
    (hempty : ramificationSet f g = ∅) (p : X) :
    Function.Bijective (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (pairMap f g) p) := by
  let L : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) :=
    (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (pairMap f g) p).toLinearMap
  have hs : Function.Surjective L := (ramificationSet_empty_iff f g).mp hempty p
  have hi : Function.Injective L := (LinearMap.injective_iff_surjective (f := L)).mpr hs
  exact ⟨hi, hs⟩

/-- A finite surjective holomorphic map in its actual proper/finite-fibre sense. -/
structure FiniteSurjectiveHolomorphicMap (M N : CompactComplexSurface) where
  map : HolomorphicMap M N
  proper : IsProperMap map
  finite_fibres : ∀ y : N, (map ⁻¹' {y}).Finite
  surjective : Function.Surjective map

/-- `FinitePair` is exactly finite fibres of the actual paired map, and the
properness follows from actual compactness and Hausdorffness. -/
def finiteSurjectivePair (f g : Fibration X)
    (hfinite : f.FinitePair g) (hsurj : f.PairSurjective g) :
    FiniteSurjectiveHolomorphicMap X (f.base.productSurface g.base) where
  map := pairMap f g
  proper := (pairMap f g).holomorphic.continuous.isProperMap
  finite_fibres := by
    rintro ⟨b, c⟩
    have heq : ((pairMap f g) ⁻¹' {(b, c)}) = {p : X | f p = b ∧ g p = c} := by
      ext p
      change (f p, g p) = (b, c) ↔ f p = b ∧ g p = c
      exact ⟨fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩,
        fun h => Prod.ext h.1 h.2⟩
    rw [heq]
    exact hfinite (b, c)
  surjective := hsurj

/-- The general proper local-diffeomorphism covering theorem, including the
usual holomorphic inverse-function interpretation of a nonsingular actual
derivative. All hypotheses are actual map properties; this interface mentions
no fibration, ramification divisor, or classification conclusion. -/
def ProperHolomorphicLocalDiffeomorphismCovering : Prop :=
  ∀ (M N : CompactComplexSurface) (u : HolomorphicMap M N),
    IsProperMap u → Function.Surjective u → (∀ y : N, (u ⁻¹' {y}).Finite) →
    (∀ p : M, Function.Bijective (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) u p)) →
      IsCoveringMap u

/-- Constructing the actual finite unramified cover from the empty actual
ramification set. No unramified assertion is assumed as a separate label. -/
def unramifiedCoverOfEmptyRamification
    (coveringTheorem : ProperHolomorphicLocalDiffeomorphismCovering)
    (f g : Fibration X) (hfinite : f.FinitePair g) (hsurj : f.PairSurjective g)
    (hempty : ramificationSet f g = ∅) :
    FiniteUnramifiedCover X (f.base.productSurface g.base) where
  map := pairMap f g
  surjective := hsurj
  finite_fibres := (finiteSurjectivePair f g hfinite hsurj).finite_fibres
  covering := coveringTheorem X (f.base.productSurface g.base) (pairMap f g)
    (finiteSurjectivePair f g hfinite hsurj).proper hsurj
    (finiteSurjectivePair f g hfinite hsurj).finite_fibres
    (pair_differential_bijective_of_empty f g hempty)
  differential_bijective := pair_differential_bijective_of_empty f g hempty

/-- The first induced factor of the constructed cover is the original `f`. -/
theorem constructed_first_eq
    (coveringTheorem : ProperHolomorphicLocalDiffeomorphismCovering)
    (f g : Fibration X) (hfinite : f.FinitePair g) (hsurj : f.PairSurjective g)
    (hempty : ramificationSet f g = ∅) :
    (unramifiedCoverOfEmptyRamification coveringTheorem f g hfinite hsurj hempty).firstFibration
      f.connected_fibres = f := rfl

theorem constructed_second_eq
    (coveringTheorem : ProperHolomorphicLocalDiffeomorphismCovering)
    (f g : Fibration X) (hfinite : f.FinitePair g) (hsurj : f.PairSurjective g)
    (hempty : ramificationSet f g = ∅) :
    (unramifiedCoverOfEmptyRamification coveringTheorem f g hfinite hsurj hempty).secondFibration
      g.connected_fibres = g := rfl

/-- The exact unramified-pair conclusion, now starting from the actual
ramification set and actual finite paired map. The third fibration `h` has no
smoothness hypothesis. All general classical inputs remain explicit. -/
theorem third_equivalent_of_empty_ramification
    (coveringTheorem : ProperHolomorphicLocalDiffeomorphismCovering)
    (rigidity : ProductCurveRigidity) (productCovers : ProductCoverExistence)
    (constancy : ConnectedFibreDerivativeConstancy) (sections : HolomorphicSubmersionSections)
    (curveMaps : NonconstantCompactCurveMapTheorem) (inverseTheorem : BijectiveHolomorphicInverse)
    (f g : Fibration X) (hf : f.Hyperbolic) (hg : g.Hyperbolic)
    (hfinite : f.FinitePair g) (hsurj : f.PairSurjective g)
    (hempty : ramificationSet f g = ∅) (h : Fibration X) (hh : h.Hyperbolic) :
    Fibration.Equivalent h f ∨ Fibration.Equivalent h g := by
  let q := unramifiedCoverOfEmptyRamification coveringTheorem f g hfinite hsurj hempty
  have hclass := unramified_pair_fibration_equivalent rigidity productCovers constancy sections
    curveMaps inverseTheorem hf hg q f.connected_fibres g.connected_fibres h hh
  exact hclass

end Paper27.Geometry.RamificationSupport
