import Paper18.Category.ModuleAlphaInductionOpposite
import Paper18.Category.PivotalFunctor
import Paper18.Category.Semisimple
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-! # Actual fusion foundations for the monoidal opposite

The ordinary equivalence transports actual finite simple decompositions.
For braided categories, the actual strong monoidal mopping functor
transports exact pairings, with no pivotal structure.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open MonoidalOpposite
universe v u w
namespace Paper18.Category.MonoidalOppositeFusion
variable {D : Type u} [Category.{v} D]

instance unmopIsEquivalence : (unmopFunctor D).IsEquivalence :=
  (unmopEquiv D).isEquivalence_functor

instance mopIsEquivalence : (mopFunctor D).IsEquivalence :=
  (mopEquiv D).isEquivalence_functor

variable [Preadditive D]

instance hasFiniteBiproducts [HasFiniteBiproducts D] : HasFiniteBiproducts Dᴹᵒᵖ where
  out n := ⟨fun f => by
    change HasBiproduct (fun j => (mopFunctor D).obj (f j).unmop)
    infer_instance⟩

instance hasKernels [HasKernels D] : HasKernels Dᴹᵒᵖ where
  has_limit {X Y} f := by
    letI : HasLimit (parallelPair f 0 ⋙ unmopFunctor D) := by
      letI : HasLimit (parallelPair
          ((parallelPair f 0 ⋙ unmopFunctor D).map WalkingParallelPairHom.left)
          ((parallelPair f 0 ⋙ unmopFunctor D).map WalkingParallelPairHom.right)) := by
        simpa only [Functor.comp_map, parallelPair_map_left, parallelPair_map_right,
          Functor.map_zero] using
          (inferInstance : HasLimit (parallelPair f.unmop 0))
      exact hasLimit_of_iso (diagramIsoParallelPair (parallelPair f 0 ⋙ unmopFunctor D)).symm
    exact Adjunction.hasLimit_of_comp_equivalence _ (unmopFunctor D)

instance finiteHom [Linear ℂ D] [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
    (X Y : Dᴹᵒᵖ) : FiniteDimensional ℂ (X ⟶ Y) :=
  FiniteDimensional.of_injective ((unmopFunctor D).mapLinearMap ℂ)
    (unmopFunctor D).map_injective

/-- Actual simplicity transports through the ordinary mopping equivalence. -/
def simple (X : D) [Simple X] : Simple (mop X) where
  mono_isIso_iff_nonzero {Y} f _ := by
    letI : Mono f.unmop := (unmopFunctor D).map_mono f
    constructor
    · intro hf hz
      letI := hf
      have h := (CategoryTheory.Simple.mono_isIso_iff_nonzero f.unmop).mp
        (inferInstance : IsIso f.unmop)
      exact h (congrArg Quiver.Hom.unmop hz)
    · intro hf
      have hn : f.unmop ≠ 0 := by
        intro hz
        apply hf
        exact Quiver.Hom.unmop_inj hz
      letI : IsIso f.unmop :=
        (CategoryTheory.Simple.mono_isIso_iff_nonzero f.unmop).mpr hn
      letI : IsIso ((unmopFunctor D).map f) := inferInstanceAs (IsIso f.unmop)
      exact isIso_of_fully_faithful (unmopFunctor D) f

variable [HasFiniteBiproducts D]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)

/-- The actual finite simple skeleton of the monoidal opposite. -/
def skeleton : FiniteSemisimpleSkeleton Dᴹᵒᵖ ι where
  simpleObject i := mop (S.simpleObject i)
  simple i := simple _
  iso_injective i j h := S.iso_injective i j (h.map (unmopFunctor D).mapIso)
  length X := S.length X.unmop
  label X := S.label X.unmop
  decomposition X := (mopFunctor D).mapIso (S.decomposition X.unmop) ≪≫
    (mopFunctor D).mapBiproduct (fun a => S.simpleObject (S.label X.unmop a))

section Rigid
variable [MonoidalCategory D] [BraidedCategory D] [RightRigidCategory D]

/-- Exact pairings transported by the actual braided strong mopping
functor give actual right rigidity of the monoidal opposite. -/
def rightRigidCategory : RightRigidCategory Dᴹᵒᵖ where
  rightDual X :=
    { rightDual := mop X.unmopᘁ
      exact := mapExactPairing (mopFunctor D) X.unmop X.unmopᘁ }

def simpleUnit [Simple (𝟙_ D)] : Simple (𝟙_ Dᴹᵒᵖ) := simple (𝟙_ D)

end Rigid
end Paper18.Category.MonoidalOppositeFusion
