import Paper18.Category.QuasiFusionPivotal
import Paper18.Category.PositiveMonoidalFunctor
import Paper18.Category.CrossedExtensionMonoidal

/-! # Actual positive pivotal invariance for twisted graded equivalences -/
noncomputable section
set_option maxHeartbeats 2000000
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category
namespace QuasiFusion.CocycleVec
variable {G : Type} [Group G] [Fintype G] (ψ : ThreeCocycle G)

/-- Every actual complex-linear strong monoidal autoequivalence preserves
the constructed actual positive pivotal structure, without a braiding. -/
theorem equivalence_preservesPivotal
    (F : CocycleVec ψ ⥤ CocycleVec ψ) [F.Monoidal] [F.Additive] [F.Linear ℂ]
    [F.IsEquivalence] : PreservesPivotal F (pivotalStructure ψ) (pivotalStructure ψ) :=
  preservesPivotal_of_positive_equivalence F (pivotalStructure ψ) (pivotalStructure ψ)
    (skeleton ψ) (skeleton ψ) (pivotal_positive ψ) (pivotal_positive ψ)

end QuasiFusion.CocycleVec
namespace CrossedExtension
open QuasiFusion FiniteCohomologyKilling
variable {G : Type} [Group G] [Fintype G] (ω : FourCocycle G ℂˣ)
local instance : Fintype (KillingKernel G) := Fintype.ofFinite _

/-- The actual nonbraided strong conjugation equivalences in the finite
killing extension preserve the actual canonical positive pivotal structure. -/
theorem kernelConjugation_preservesPivotal (g : KillingExtension G) :
    PreservesPivotal (kernelConjugationFunctor ω g)
      (CocycleVec.pivotalStructure (kernelCocycle ω))
      (CocycleVec.pivotalStructure (kernelCocycle ω)) :=
  CocycleVec.equivalence_preservesPivotal (kernelCocycle ω) (kernelConjugationFunctor ω g)

end CrossedExtension
end Paper18.Category
