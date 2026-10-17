import Paper18.Category.FusionSubcategoryIntegral
import Paper18.Category.FusionSubcategoryPivotal
import Paper18.Category.CentralizerSimples
import Paper18.Category.NondegenerateBasic

/-! # Actual fusion centralizers with inherited spherical structure -/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u w
namespace Paper18.Category.FiniteSemisimpleSkeleton
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)] [BraidedCategory C]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- Integrality of the actual centralizer fusion category, with its
categorical inherited structures constructed rather than assumed. -/
def CentralizerIntegral (T : Set C) : Prop :=
  S.FullSubcategoryIntegral (centralizerProperty T)

lemma centralizerIntegral_iff (T : Set C) : S.CentralizerIntegral T ↔
    ∀ i, S.simpleObject i ∈ centralizer T →
      ∃ n : ℤ, S.fpdim (S.simpleObject i) = n :=
  S.fullSubcategoryIntegral_iff (centralizerProperty T)

lemma centralizerIntegral_of_integral (T : Set C) (h : S.Integral) :
    S.CentralizerIntegral T :=
  S.fullSubcategoryIntegral_of_integral (centralizerProperty T) h

/-- The actual finite semisimple skeleton of the categorical centralizer. -/
abbrev centralizerSkeleton (T : Set C) :=
  S.fullSubcategorySkeleton (centralizerProperty T)

/-- The prescribed pivotal structure restricts to the actual centralizer. -/
abbrev centralizerPivotal (T : Set C) (J : PivotalStructure C) :=
  S.fullSubcategoryPivotal (centralizerProperty T) J

end Paper18.Category.FiniteSemisimpleSkeleton
