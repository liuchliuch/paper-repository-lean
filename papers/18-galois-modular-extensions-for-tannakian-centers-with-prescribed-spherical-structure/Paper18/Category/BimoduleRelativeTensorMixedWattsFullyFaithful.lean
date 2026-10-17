import Paper18.Category.BimoduleRelativeTensorMixedWattsBasic

/-! # Actual full faithfulness of mixed Eilenberg--Watts evaluation -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u
namespace Paper18.Category.BimoduleRelativeTensor.MixedWatts
open ModuleFunctor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  {R S : D} [MonObj R] [MonObj S]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
variable (Sep : SeparableAlgebra S)

def evaluationFaithful : (evaluation (R := R) (S := S)).Faithful where
  map_injective {F G} τ σ h := by
    apply Subtype.ext
    apply transformation_ext F.toFunctor G.toFunctor Sep τ.val σ.val
    exact congrArg Mod_.Hom.hom h

/-- A native mixed-bimodule map extends by the actual source-algebra
separable free resolution to a genuine module natural transformation. -/
def homPreimage {F G : Bundled Dᴹᵒᵖ (Mod_ D S) (Mod_ D R)}
    (h : evaluation.obj F ⟶ evaluation.obj G) : F ⟶ G :=
  ⟨transformation F.toFunctor G.toFunctor Sep h.hom,
    transformation_moduleNatural F.toFunctor G.toFunctor Sep h.hom⟩

@[simp] lemma evaluation_map_preimage
    {F G : Bundled Dᴹᵒᵖ (Mod_ D S) (Mod_ D R)}
    (h : evaluation.obj F ⟶ evaluation.obj G) : evaluation.map (homPreimage Sep h) = h := by
  apply Mod_.Hom.ext
  exact transformation_app_regular F.toFunctor G.toFunctor Sep h

def evaluationFull : (evaluation (R := R) (S := S)).Full where
  map_surjective h := ⟨homPreimage Sep h, evaluation_map_preimage Sep h⟩

def evaluationFullyFaithful : (evaluation (R := R) (S := S)).FullyFaithful := by
  letI := evaluationFaithful (R := R) Sep
  letI := evaluationFull (R := R) Sep
  exact Functor.FullyFaithful.ofFullyFaithful _

end Paper18.Category.BimoduleRelativeTensor.MixedWatts
