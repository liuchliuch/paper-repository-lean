import Paper18.Category.SeparableModulesKernels
import Paper18.Category.SeparableModulesBiproducts
import Paper18.Category.SemisimpleSplitting
import Paper18.Category.SemisimpleExistence
import Paper18.Category.SemisimpleGenerator

/-!
# Semisimplicity derived from actual algebra separability

All morphism splittings are obtained by averaging actual ambient splittings.
Kernels, finite biproducts, and finite Hom spaces have been constructed
separately, so finite decompositions into categorical simple modules follow
without a semisimplicity field.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped MonObj
universe v u w
namespace Paper18.Category.SeparableAlgebra
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {A : C} [MonObj A] (S : SeparableAlgebra A)
  {ι : Type w} [Fintype ι] (T : FiniteSemisimpleSkeleton C ι)

/-- Every actual module monomorphism splits by averaging its underlying
splitting in the ambient semisimple category. -/
def splitMono {M N : Mod_ C A} (f : M ⟶ N) [Mono f] : SplitMono f := by
  letI : Mono f.hom := (Mod_.forget (D := C) A).map_mono f
  let s := T.splitMono f.hom
  refine ⟨S.average s.retraction, ?_⟩
  rw [S.comp_average, s.id]
  simpa only [Mod_.id_hom'] using S.average_moduleHom (𝟙 M)

include S T in
/-- Actual finite decompositions into categorical simple modules, derived
from separability and actual ambient finite semisimplicity. -/
theorem exists_simple_biproduct (M : Mod_ C A) :
    ∃ (n : ℕ) (P : Fin n → Mod_ C A),
      (∀ i, Simple (P i)) ∧ Nonempty (M ≅ ⨁ P) :=
  exists_simple_biproduct_of_splitMonos (fun f => S.splitMono T f) M

/-- A separable module is an actual retract of the free module on its
underlying ambient object. -/
def freeRetract (M : Mod_ C A) : Retract M (InternalModule.free A M.X) where
  i := S.moduleSectionHom M
  r := InternalModule.actionHom M
  retract := by
    apply Mod_.Hom.ext
    exact S.moduleSection_action M

omit [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] [HasKernels C]
  [HasFiniteBiproducts C] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] in
include S in
/-- The actual free-module functor is dominant by retracts. -/
theorem free_retract_dominant (M : Mod_ C A) :
    ∃ X : C, Nonempty (Retract M (InternalModule.freeFunctor.obj X)) :=
  ⟨M.X, ⟨S.freeRetract M⟩⟩

/-- Free modules carry the actual ambient simple decomposition to an actual
finite biproduct of free modules on simple representatives. -/
def freeDecompositionIso (X : C) :
    InternalModule.free A X ≅
      ⨁ fun j : Fin (T.length X) => InternalModule.free A (T.simpleObject (T.label X j)) :=
  (InternalModule.freeFunctor (A := A)).mapIso (T.decomposition X) ≪≫
    (InternalModule.freeFunctor (A := A)).mapBiproduct
      (fun j : Fin (T.length X) => T.simpleObject (T.label X j))

include S in
/-- The finite family of free modules on ambient simple representatives
covers every actual simple module by an actual retract. -/
theorem simple_retract_of_free_simple (M : Mod_ C A) [Simple M] :
    ∃ i : ι, Nonempty (Retract M (InternalModule.free A (T.simpleObject i))) := by
  let R := S.freeRetract M
  let d := freeDecompositionIso (A := A) T M.X
  let k : M ⟶ ⨁ fun j : Fin (T.length M.X) =>
      InternalModule.free A (T.simpleObject (T.label M.X j)) := R.i ≫ d.hom
  have hk : ∃ j : Fin (T.length M.X), k ≫ biproduct.π _ j ≠ 0 := by
    by_contra h
    push_neg at h
    have hk0 : k = 0 := by
      apply biproduct.hom_ext
      intro j
      simpa only [zero_comp] using h j
    have hi0 : R.i = 0 := by
      apply (cancel_mono d.hom).mp
      simpa only [zero_comp] using hk0
    apply CategoryTheory.id_nonzero M
    rw [← R.retract, hi0, zero_comp]
  obtain ⟨j, hj⟩ := hk
  let g := k ≫ biproduct.π _ j
  have hg : g ≠ 0 := hj
  letI : Mono g := CategoryTheory.mono_of_nonzero_from_simple hg
  let split := S.splitMono T g
  exact ⟨T.label M.X j, ⟨⟨g, split.retraction, split.id⟩⟩⟩

/-- Actual simple-module decompositions, constructed from averaging. -/
def decompositions : SimpleDecompositions (Mod_ C A) :=
  SimpleDecompositions.ofSplitMonos (fun f => S.splitMono T f)

/-- The finite actual family of free modules generates all categorical
simple modules by retracts. -/
def generator : FiniteSimpleGenerator (Mod_ C A) ι where
  obj i := InternalModule.free A (T.simpleObject i)
  covers M h := by
    letI := h
    exact S.simple_retract_of_free_simple T M

/-- The derived finite set of actual simple-module isomorphism classes. -/
def SimpleIndex := (S.decompositions T).SimpleIndex (S.generator T)

instance simpleIndex_fintype : Fintype (S.SimpleIndex T) := by
  unfold SimpleIndex
  infer_instance

/-- Actual finite semisimplicity of modules over a separable algebra,
including the finite simple skeleton, is an output of the construction. -/
def skeleton : FiniteSemisimpleSkeleton (Mod_ C A) (S.SimpleIndex T) :=
  (S.decompositions T).skeleton (S.generator T)

end Paper18.Category.SeparableAlgebra
