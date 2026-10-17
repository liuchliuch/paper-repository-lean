import Paper18.Category.GradedQuasiCancellationPentagon
import Paper18.Category.FiniteCohomologyKilling

/-! # Finite-cover cancellation using the constructed fourth-cocycle primitive -/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category.GradedQuasiCancellation
open FiniteCohomologyKilling
variable {C : Type u} [Category.{v} C] [MonoidalCategoryStruct C]
  [Preadditive C] [Linear ℂ C] {G : Type} [Group G] [Fintype G]
  (T : TensorCoherence (C := C)) (L : TensorLinearity (C := C))
  (P : HomogeneousGrading (C := C) (KillingExtension G))
  (ω : FourCocycle G ℂˣ)

/-- The constructed finite primitive corrects an actual homogeneous
associator whose actual defect is the pullback of the given cocycle. -/
def finiteCorrectedMonoidalCategory
    (hω : HasPentagonDefect P (ω.pullback UniversalExtension.projection)) :
    MonoidalCategory C :=
  correctedMonoidalCategory T L P (ω.pullback UniversalExtension.projection)
    hω ω.finitePrimitive ω.finitePrimitive_spec

/-- The constructed finite-cover monoidal category has its actual
separately additive tensor product. -/
def finiteCorrectedMonoidalPreadditive
    (hω : HasPentagonDefect P (ω.pullback UniversalExtension.projection)) :
    letI := finiteCorrectedMonoidalCategory T L P ω hω
    MonoidalPreadditive C :=
  correctedMonoidalPreadditive T L P (ω.pullback UniversalExtension.projection)
    hω ω.finitePrimitive ω.finitePrimitive_spec

/-- The constructed finite-cover monoidal category has its actual
separately complex-linear tensor product. -/
def finiteCorrectedMonoidalLinear
    (hω : HasPentagonDefect P (ω.pullback UniversalExtension.projection)) :
    letI := finiteCorrectedMonoidalCategory T L P ω hω
    letI := finiteCorrectedMonoidalPreadditive T L P ω hω
    MonoidalLinear ℂ C :=
  correctedMonoidalLinear T L P (ω.pullback UniversalExtension.projection)
    hω ω.finitePrimitive ω.finitePrimitive_spec

end Paper18.Category.GradedQuasiCancellation
