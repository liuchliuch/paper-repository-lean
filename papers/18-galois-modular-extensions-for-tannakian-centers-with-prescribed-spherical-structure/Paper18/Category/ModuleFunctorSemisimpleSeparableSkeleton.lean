import Paper18.Category.ModuleFunctorSemisimpleSeparableKernels
import Paper18.Category.ModuleFunctorSemisimpleSeparableBiproducts
import Paper18.Category.SemisimpleSplitting
import Paper18.Category.SemisimpleGenerator
import Paper18.Category.EquivariantInduction

/-! # Derived finite semisimplicity for actual external separable modules -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped MonObj MonoidalLeftAction BigOperators
universe v u v' u' w
namespace Paper18.Category.ModuleFunctor.SeparableAction
open MonoidalLeftAction
attribute [local instance] Paper18.Category.additive_preservesBiproductsOfFiniteShape
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {M : Type u'} [Category.{v'} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction C M]
  [∀ c : C, (actionLeft M c).Additive]
  [∀ c : C, (actionLeft M c).Linear ℂ]
  [HasKernels M] [HasFiniteBiproducts M]
  [∀ X Y : M, FiniteDimensional ℂ (X ⟶ Y)]
  {A : C} [MonObj A] (S : SeparableAlgebra A)
  {ι : Type w} [Fintype ι] (T : FiniteSemisimpleSkeleton M ι)

/-- Every actual module monomorphism splits by averaging its underlying
splitting in the ambient semisimple category. -/
def splitMono {X Y : Mod_ M A} (f : X ⟶ Y) [Mono f] : SplitMono f := by
  letI : Mono f.hom := (Mod_.forget (D := M) A).map_mono f
  let s := T.splitMono f.hom
  refine ⟨average S s.retraction, ?_⟩
  rw [comp_average S, s.id]
  simpa only [Mod_.id_hom'] using average_moduleHom S (𝟙 X)

include S T in
/-- Actual finite decompositions into categorical simple modules, derived
from separability and actual ambient finite semisimplicity. -/
theorem exists_simple_biproduct (X : Mod_ M A) :
    ∃ (n : ℕ) (P : Fin n → Mod_ M A),
      (∀ i, Simple (P i)) ∧ Nonempty (X ≅ ⨁ P) :=
  exists_simple_biproduct_of_splitMonos (fun f => splitMono S T f) X

/-- Free modules carry the actual ambient simple decomposition to an actual
finite biproduct of free modules on simple representatives. -/
def freeDecompositionIso (X : M) :
    free (A := A) X ≅
      ⨁ fun j : Fin (T.length X) => free (A := A) (T.simpleObject (T.label X j)) :=
  (freeFunctor (A := A)).mapIso (T.decomposition X) ≪≫
    (freeFunctor (A := A)).mapBiproduct
      (fun j : Fin (T.length X) => T.simpleObject (T.label X j))

include S in
/-- The finite family of free modules on ambient simple representatives
covers every actual simple module by an actual retract. -/
theorem simple_retract_of_free_simple (X : Mod_ M A) [Simple X] :
    ∃ i : ι, Nonempty (Retract X (free (A := A) (T.simpleObject i))) := by
  let R := freeRetract S X
  let d := freeDecompositionIso (A := A) T X.X
  let k : X ⟶ ⨁ fun j : Fin (T.length X.X) =>
      free (A := A) (T.simpleObject (T.label X.X j)) := R.i ≫ d.hom
  have hk : ∃ j : Fin (T.length X.X), k ≫ biproduct.π _ j ≠ 0 := by
    by_contra h
    push_neg at h
    have hk0 : k = 0 := by
      apply biproduct.hom_ext
      intro j
      simpa only [zero_comp] using h j
    have hi0 : R.i = 0 := by
      apply (cancel_mono d.hom).mp
      simpa only [zero_comp] using hk0
    apply CategoryTheory.id_nonzero X
    rw [← R.retract, hi0, zero_comp]
  obtain ⟨j, hj⟩ := hk
  let g := k ≫ biproduct.π _ j
  have hg : g ≠ 0 := hj
  letI : Mono g := CategoryTheory.mono_of_nonzero_from_simple hg
  let split := splitMono S T g
  exact ⟨T.label X.X j, ⟨⟨g, split.retraction, split.id⟩⟩⟩

/-- Actual simple-module decompositions, constructed from averaging. -/
def decompositions : SimpleDecompositions (Mod_ M A) :=
  SimpleDecompositions.ofSplitMonos (fun f => splitMono S T f)

/-- The finite actual family of free modules generates all categorical
simple modules by retracts. -/
def generator : FiniteSimpleGenerator (Mod_ M A) ι where
  obj i := free (A := A) (T.simpleObject i)
  covers M h := by
    letI := h
    exact simple_retract_of_free_simple S T M

/-- The derived finite set of actual simple-module isomorphism classes. -/
def SimpleIndex := (decompositions S T).SimpleIndex (generator S T)

instance simpleIndex_fintype : Fintype (SimpleIndex S T) := by
  unfold SimpleIndex
  infer_instance

/-- Actual finite semisimplicity of modules over a separable algebra,
including the finite simple skeleton, is an output of the construction. -/
def skeleton : FiniteSemisimpleSkeleton (Mod_ M A) (SimpleIndex S T) :=
  (decompositions S T).skeleton (generator S T)

end Paper18.Category.ModuleFunctor.SeparableAction
