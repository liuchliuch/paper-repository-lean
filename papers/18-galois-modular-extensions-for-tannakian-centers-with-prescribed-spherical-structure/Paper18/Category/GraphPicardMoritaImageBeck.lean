import Paper18.Category.GraphPicardMoritaImageBasic
import Paper18.Category.DiagonalAlgebraSemisimpleAdjoint
import Paper18.Category.FixedBoundarySemisimpleExact
import Paper18.Category.SemisimpleAbelian
import Mathlib.CategoryTheory.Monad.Monadicity
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced

/-! # Genuine Beck comparison on the actual summand image

The actual constructed right adjoint restricts to the actual summand
image. Its faithfulness follows from the actual retracts defining that
image, and actual finite semisimple cokernel splittings give exactness.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u w v' u' w'
namespace Paper18.Category.GraphPicard.MoritaImage
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasFiniteBiproducts C] [HasKernels C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {D : Type u'} [Category.{v} D] [Preadditive D] [Linear ℂ D]
  [HasFiniteBiproducts D] [HasKernels D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (F : C ⥤ D) [F.Additive] [F.Linear ℂ]

/-- The actual original right adjoint restricted to actual image summands. -/
def rightAdjoint : Image F ⥤ C :=
  (property F).ι ⋙ DiagonalAlgebra.semisimpleRightAdjoint S F

instance rightAdjoint_additive : (rightAdjoint S F).Additive := by
  dsimp [rightAdjoint]
  infer_instance
instance rightAdjoint_linear : (rightAdjoint S F).Linear ℂ := by
  dsimp [rightAdjoint]
  infer_instance

/-- The actual original adjunction restricts through the actual full
inclusion, with its original Hom correspondence. -/
def adjunction : core F ⊣ rightAdjoint S F :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y => (DiagonalAlgebra.semisimpleRightAdjunction S F).homEquiv X Y.obj
      homEquiv_naturality_left_symm := fun f g =>
        (DiagonalAlgebra.semisimpleRightAdjunction S F).homEquiv_naturality_left_symm f g
      homEquiv_naturality_right := fun f g =>
        (DiagonalAlgebra.semisimpleRightAdjunction S F).homEquiv_naturality_right f g }

/-- Actual retract dominance forces actual faithfulness of the
constructed restricted right adjoint. -/
def rightAdjoint_faithful : (rightAdjoint S F).Faithful where
  map_injective {Y Z} f g h := by
    obtain ⟨X, ⟨r⟩⟩ := core_dominant F Y
    have ha : r.r ≫ f = r.r ≫ g := by
      apply ((adjunction S F).homEquiv X Z).injective
      simp only [Adjunction.homEquiv_naturality_right]
      rw [h]
    exact (cancel_epi r.r).mp ha

variable {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)

/-- The actual image comparison is monadic, derived from genuine
retraction density and genuine finite semisimple exactness. -/
def monadic : MonadicRightAdjoint (rightAdjoint S F) := by
  letI := hasKernels F T
  letI := rightAdjoint_faithful S F
  let TI := skeleton F T
  letI : Abelian (Image F) := TI.abelian
  letI : HasCoequalizers (Image F) := TI.hasCoequalizers
  letI : PreservesColimitsOfShape WalkingParallelPair (rightAdjoint S F) :=
    TI.preservesCoequalizers (rightAdjoint S F)
  letI : Monad.PreservesColimitOfIsReflexivePair (rightAdjoint S F) :=
    { out := fun {X Y} f g _ =>
      inferInstanceAs (PreservesColimit (parallelPair f g) (rightAdjoint S F)) }
  exact Monad.monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms (adjunction S F)

/-- The actual tensor image is equivalent to the actual algebras of the
actual restricted adjunction monad, without a monadicity premise. -/
def beckEquivalence : Image F ≌ Monad.Algebra (adjunction S F).toMonad := by
  letI := monadic S F T
  letI : (Monad.comparison (adjunction S F)).IsEquivalence :=
    show (Monad.comparison (monadicAdjunction (rightAdjoint S F))).IsEquivalence from inferInstance
  exact (Monad.comparison (adjunction S F)).asEquivalence

end Paper18.Category.GraphPicard.MoritaImage
