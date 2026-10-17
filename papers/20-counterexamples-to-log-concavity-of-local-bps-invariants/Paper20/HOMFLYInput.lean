import Paper20.SkeinParity
import Paper20.HilbertAtZero
import Mathlib.RingTheory.LaurentSeries

namespace Paper20.ExternalInput
open Paper20.QuantumSeriesCoordinates
noncomputable section

/-- Actual Laurent series in the HOMFLY variable a, with coefficients
in the already faithful formal z=v-v^-1 coordinate field. -/
abbrev HOMFLYField := LaurentSeries SeriesField

def homflyA : HOMFLYField := HahnSeries.single 1 1
def homflyZ : HOMFLYField := HahnSeries.C (HilbertAtZero.v-HilbertAtZero.v⁻¹)

lemma homflyA_ne_zero : homflyA≠0 := by
  intro he
  have hc := congrArg (fun f : HOMFLYField => f.coeff 1) he
  exact one_ne_zero (by
    simpa only [homflyA,HahnSeries.coeff_single_same,HahnSeries.coeff_zero] using hc)

/-- External link/skein data and the two original z conventions. The
invariant is a full Laurent series in a; lowest-a extraction below is the
ACTUAL Hahn-series coefficient map, not an opaque external functional. -/
structure HOMFLYData where
  Link : Type
  Crossing : Type
  system : SkeinParity.System Link Crossing
  familyLink : ℕ → ℕ → Link
  positive : Link → HOMFLYField
  opposite : Link → HOMFLYField

/-- The standard normalized HOMFLY skein characterization/uniqueness and
the standard branch count for the algebraic link of this pure braid.
No sign-conversion conclusion is supplied as a premise. -/
structure HOMFLYInputs (data : HOMFLYData) : Prop where
  positive_law : SkeinParity.Law data.system homflyA homflyZ data.positive
  opposite_law : SkeinParity.Law data.system homflyA (-homflyZ) data.opposite
  unique : ∀ P Q : data.Link → HOMFLYField,
    SkeinParity.Law data.system homflyA homflyZ P →
      SkeinParity.Law data.system homflyA homflyZ Q → P=Q
  family_components : ∀ r k, 2 ≤ r → 1 ≤ k →
    data.system.components (data.familyLink r k)=r

/-- The opposite-z sign conversion at ANY actual a coefficient follows
from the skein characterization. In particular the corrected sign in(7)
is derived internally rather than assumed in the Hilbert--HOMFLY input. -/
theorem homfly_coefficient_sign (data : HOMFLYData) (input : HOMFLYInputs data)
    (r k : ℕ) (hr : 2 ≤ r) (hk : 1 ≤ k) (m : ℤ) :
    (data.positive (data.familyLink r k)).coeff m=
      (-1:SeriesField)^(r-1)*(data.opposite (data.familyLink r k)).coeff m := by
  have he := congrFun (SkeinParity.convention_sign data.system homflyA homflyZ
    input.unique data.positive data.opposite input.positive_law input.opposite_law)
    (data.familyLink r k)
  rw [SkeinParity.componentSign,input.family_components r k hr hk] at he
  have hs : (-1:HOMFLYField)^(r-1)=HahnSeries.C ((-1:SeriesField)^(r-1)) := by
    rw [map_pow,map_neg,map_one]
  rw [hs] at he
  have hc := congrArg (fun f : HOMFLYField => f.coeff m) he
  dsimp only at hc
  rw [HahnSeries.C_apply,HahnSeries.coeff_single_zero_mul] at hc
  exact hc

end
end Paper20.ExternalInput
