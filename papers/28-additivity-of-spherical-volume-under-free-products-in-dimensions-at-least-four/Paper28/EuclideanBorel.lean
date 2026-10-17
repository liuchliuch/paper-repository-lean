import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! The actual Borel sigma algebra of the native finite real Hilbert spaces. -/
set_option autoImplicit false
namespace Paper28

instance realEuclideanMeasurableSpace (ι : Type*) [Fintype ι] :
    MeasurableSpace (EuclideanSpace ℝ ι) := borel _

instance realEuclideanBorelSpace (ι : Type*) [Fintype ι] :
    BorelSpace (EuclideanSpace ℝ ι) := ⟨rfl⟩

end Paper28
