import Paper18.Category.LocalModulesCenterEssential

/-! # The actual strong monoidal central lift of local modules -/
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

@[simp]
theorem localCenterIsoOfCentralizes_hom_f (Z : Center (Mod_ C A))
    (hZ : ∀ X : C, Centralizes ((centralFreeFunctor (A := A)).obj X) Z) :
    (S.localCenterIsoOfCentralizes Z hZ).hom.f = 𝟙 Z.1 := rfl

/-- The actual unit comparison of the local central lift. -/
def localCenterUnitIso : 𝟙_ (Center (Mod_ C A)) ≅ S.localCenterFunctor.obj (𝟙_ (LocalModules A)) :=
  S.localCenterIsoOfCentralizes _ (fun _ => centralizes_unit_right _)

/-- The actual tensor comparison of the local central lift. -/
def localCenterTensorIso (M N : LocalModules A) :
    S.localCenterFunctor.obj M ⊗ S.localCenterFunctor.obj N ≅ S.localCenterFunctor.obj (M ⊗ N) :=
  S.localCenterIsoOfCentralizes _ (fun X =>
    (S.centralFree_centralizes_local X M).tensor_right (S.centralFree_centralizes_local X N))

@[simp]
theorem localCenterUnitIso_hom_f : (S.localCenterUnitIso).hom.f = 𝟙 _ := rfl

@[simp]
theorem localCenterTensorIso_hom_f (M N : LocalModules A) :
    (S.localCenterTensorIso M N).hom.f = 𝟙 (M.obj ⊗ N.obj) := rfl

/-- The actual local-module central embedding is strong monoidal; its
underlying tensor and unit comparisons are identities. -/
instance localCenterFunctorMonoidal : S.localCenterFunctor.Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := S.localCenterUnitIso
      μIso := S.localCenterTensorIso
      μIso_hom_natural_left := fun f N => by
        apply Center.ext
        simp only [Center.comp_f, Center.whiskerRight_f, localCenterTensorIso_hom_f]
        dsimp only [localCenterFunctor, localCenterMap, localCenterObj]
        simp
      μIso_hom_natural_right := fun M f => by
        apply Center.ext
        simp only [Center.comp_f, Center.whiskerLeft_f, localCenterTensorIso_hom_f]
        dsimp only [localCenterFunctor, localCenterMap, localCenterObj]
        simp
      associativity := fun M N P => by
        apply Center.ext
        simp only [Center.comp_f, Center.whiskerRight_f, Center.whiskerLeft_f,
          localCenterTensorIso_hom_f, Center.associator_hom_f]
        dsimp only [localCenterFunctor, localCenterMap, localCenterObj]
        simp
      left_unitality := fun M => by
        apply Center.ext
        simp only [Center.comp_f, Center.whiskerRight_f, localCenterTensorIso_hom_f,
          localCenterUnitIso_hom_f, Center.leftUnitor_hom_f]
        dsimp only [localCenterFunctor, localCenterMap, localCenterObj]
        simp
      right_unitality := fun M => by
        apply Center.ext
        simp only [Center.comp_f, Center.whiskerLeft_f, localCenterTensorIso_hom_f,
          localCenterUnitIso_hom_f, Center.rightUnitor_hom_f]
        dsimp only [localCenterFunctor, localCenterMap, localCenterObj]
        simp }

@[simp]
theorem localCenterFunctor_μ_f (M N : LocalModules A) :
    (Functor.LaxMonoidal.μ S.localCenterFunctor M N).f = 𝟙 (M.obj ⊗ N.obj) := rfl

@[simp]
theorem localCenterFunctor_ε_f :
    (Functor.LaxMonoidal.ε S.localCenterFunctor).f = 𝟙 (𝟙_ (Mod_ C A)) := rfl

/-- The center braiding on the local image is the inverse of the local
braiding with its inputs exchanged. -/
theorem localCenter_braiding (M N : LocalModules A) :
    (β_ (S.localCenterFunctor.obj M) (S.localCenterFunctor.obj N)).hom.f =
      (β_ N M).inv := by
  change (S.localCrossingIso M.obj N.obj M.property).inv = (β_ N M).inv
  have h : S.localCrossingIso M.obj N.obj M.property =
      localBraidingIso N.obj M.obj N.property M.property := by
    apply Iso.ext
    rfl
  rw [h]
  rfl

/-- The actual local central embedding preserves the reverse of the actual
local braiding. -/
def localCenterFunctorBraidedReverse :
    letI := reverseBraiding (LocalModules A)
    S.localCenterFunctor.Braided := by
  letI := reverseBraiding (LocalModules A)
  refine { toMonoidal := S.localCenterFunctorMonoidal, braided := ?_ }
  intro M N
  apply Center.ext
  simp only [Center.comp_f, S.localCenterFunctor_μ_f]
  erw [Category.id_comp, Category.comp_id]
  exact (S.localCenter_braiding M N).symm

end Paper18.Category.SeparableAlgebra
