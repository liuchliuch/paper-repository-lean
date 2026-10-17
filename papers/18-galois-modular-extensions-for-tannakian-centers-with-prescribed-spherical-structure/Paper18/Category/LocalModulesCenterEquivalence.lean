import Paper18.Category.LocalModulesCenterMonoidal

/-! # Actual local modules are the centralizer of the central free image -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open CategoryTheory.BraidedCategory
open scoped MonObj
universe v u
namespace Paper18.Category.SeparableAlgebra
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [HasCoequalizers C] {A : C} [MonObj A] [IsCommMonObj A]
  (S : SeparableAlgebra A)
open RelativeTensor

/-- The actual centralizer of the whole actual central free image. -/
abbrev FreeImageCentralizer (A : C) [MonObj A] [IsCommMonObj A] :=
  CentralizerCategory (Set.range (centralFreeFunctor (A := A)).obj)

/-- The constructed local central lift with its actual centralizer codomain. -/
def localCentralizerFunctor : LocalModules A ⥤ FreeImageCentralizer A where
  obj M := ⟨S.localCenterFunctor.obj M, S.localCenter_mem_centralizer M⟩
  map f := S.localCenterFunctor.map f
  map_id M := S.localCenterFunctor.map_id M
  map_comp f g := S.localCenterFunctor.map_comp f g

instance localCentralizerFunctorFaithful : S.localCentralizerFunctor.Faithful where
  map_injective h := S.localCenterFunctor.map_injective h

instance localCentralizerFunctorFull : S.localCentralizerFunctor.Full where
  map_surjective f := ⟨S.localCenterFunctor.preimage f,
    S.localCenterFunctor.map_preimage f⟩

/-- Centralizer recognition supplies an actual local preimage and an actual
isomorphism for every object of the actual centralizer. -/
instance localCentralizerFunctorEssSurj : S.localCentralizerFunctor.EssSurj where
  mem_essImage Z := by
    let hZ : ∀ X : C, Centralizes ((centralFreeFunctor (A := A)).obj X) Z.obj :=
      fun X => (Z.property _ ⟨X, rfl⟩).symm
    let M : LocalModules A := ⟨Z.obj.1, local_of_centralizes_centralFree Z.obj hZ⟩
    refine ⟨M, ⟨?_⟩⟩
    exact (centralizerProperty (Set.range (centralFreeFunctor (A := A)).obj)).isoMk
      (S.localCenterIsoOfCentralizes Z.obj hZ).symm

instance localCentralizerFunctorIsEquivalence : S.localCentralizerFunctor.IsEquivalence where

/-- Local modules are actually equivalent to the actual centralizer of the
central free image. Neither nondegeneracy nor a dimension identity is an input. -/
def localCentralizerEquivalence : LocalModules A ≌ FreeImageCentralizer A :=
  S.localCentralizerFunctor.asEquivalence

/-- The centralizer equivalence uses the actual tensor and unit comparisons
of the actual local central lift. -/
instance localCentralizerFunctorMonoidal : S.localCentralizerFunctor.Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := (centralizerProperty (Set.range (centralFreeFunctor (A := A)).obj)).isoMk
        S.localCenterUnitIso
      μIso M N := (centralizerProperty (Set.range (centralFreeFunctor (A := A)).obj)).isoMk
        (S.localCenterTensorIso M N)
      μIso_hom_natural_left := fun f N => by
        exact Functor.LaxMonoidal.μ_natural_left S.localCenterFunctor f N
      μIso_hom_natural_right := fun M f => by
        exact Functor.LaxMonoidal.μ_natural_right S.localCenterFunctor M f
      associativity := fun M N P => by
        exact Functor.LaxMonoidal.associativity S.localCenterFunctor M N P
      left_unitality := fun M => by
        exact Functor.LaxMonoidal.left_unitality S.localCenterFunctor M
      right_unitality := fun M => by
        exact Functor.LaxMonoidal.right_unitality S.localCenterFunctor M }

/-- The centralizer equivalence preserves the reverse local braiding. -/
def localCentralizerFunctorBraidedReverse :
    letI := reverseBraiding (LocalModules A)
    S.localCentralizerFunctor.Braided := by
  letI := reverseBraiding (LocalModules A)
  letI : S.localCenterFunctor.Braided := S.localCenterFunctorBraidedReverse
  refine { toMonoidal := S.localCentralizerFunctorMonoidal, braided := ?_ }
  intro M N
  exact Functor.LaxBraided.braided (F := S.localCenterFunctor) M N

end Paper18.Category.SeparableAlgebra
