import Paper18.Category.FunctorImage
import Paper18.Category.SemisimpleGenerator
import Paper18.Category.SemisimpleSplitting

/-! # Finite semisimplicity reflected by an actual full faithful functor -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u v' u' w
namespace Paper18.Category.ModuleFunctor
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (T : FiniteSemisimpleSkeleton D ι)
  (F : C ⥤ D) [F.Additive] [F.Linear ℂ] [F.Full] [F.Faithful]
  [F.PreservesMonomorphisms]

/-- An actual full faithful functor reflects actual semisimple splittings. -/
def imageSplitMono {X Y : C} (f : X ⟶ Y) [Mono f] : SplitMono f := by
  let s := T.splitMono (F.map f)
  refine ⟨F.preimage s.retraction, ?_⟩
  apply F.map_injective
  rw [F.map_comp, F.map_preimage, F.map_id]
  exact s.id

/-- The actual source simple classes occupy a finite subset of the actual
target simple classes. -/
def occupiedSimple (i : ι) : Prop :=
  ∃ X : C, Simple X ∧ Nonempty (F.obj X ≅ T.simpleObject i)

/-- A chosen actual source simple for each occupied target class. -/
def imageRepresentative (i : {i : ι // occupiedSimple T F i}) : C :=
  Classical.choose i.property

instance imageRepresentative_simple (i : {i : ι // occupiedSimple T F i}) :
    Simple (imageRepresentative T F i) := (Classical.choose_spec i.property).1

def imageRepresentativeIso (i : {i : ι // occupiedSimple T F i}) :
    F.obj (imageRepresentative T F i) ≅ T.simpleObject i.val :=
  Classical.choice (Classical.choose_spec i.property).2

/-- Actual full faithfulness lifts the target simple isomorphism to an
actual isomorphism with the chosen source representative. -/
def imageGenerator : FiniteSimpleGenerator C {i : ι // occupiedSimple T F i} where
  obj := imageRepresentative T F
  covers X hX := by
    letI := hX
    letI := T.simple_map F X
    obtain ⟨i, ⟨e⟩⟩ := T.simple_isomorphic_representative (F.obj X)
    let j : {i : ι // occupiedSimple T F i} := ⟨i, X, hX, ⟨e⟩⟩
    let q := F.preimageIso (e ≪≫ (imageRepresentativeIso T F j).symm)
    exact ⟨j, ⟨⟨q.hom, q.inv, q.hom_inv_id⟩⟩⟩

def imageDecompositions : SimpleDecompositions C :=
  SimpleDecompositions.ofSplitMonos (fun f => imageSplitMono T F f)

def ImageSimpleIndex := (imageDecompositions T F).SimpleIndex (imageGenerator T F)

instance imageSimpleIndex_fintype : Fintype (ImageSimpleIndex T F) := by
  unfold ImageSimpleIndex
  infer_instance

/-- Actual source finite semisimplicity, derived from the actual full
faithful functor and its actual preservation of monomorphisms. -/
def imageSkeleton : FiniteSemisimpleSkeleton C (ImageSimpleIndex T F) :=
  (imageDecompositions T F).skeleton (imageGenerator T F)

end Paper18.Category.ModuleFunctor
