import Paper18.Category.RelativeTensorFree
import Paper18.Category.CentralizerClosure

/-! # Actual free modules and locality

A free module is local exactly when its ambient generator centralizes the
algebra. Both implications concern the actual actions and braiding; the
necessary implication is detected by the actual free generators.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open CategoryTheory.BraidedCategory
open scoped MonObj
universe v u
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {A : C} [MonObj A] [IsCommMonObj A]
open RelativeTensor

omit [IsCommMonObj A] in
/-- Locality is preserved by tensoring on the right with an ambient object
that centralizes the algebra. -/
theorem IsLocalModule.ambientTensor {M : Mod_ C A} (hM : IsLocalModule M)
    (X : C) (hX : Centralizes A X) : IsLocalModule (ambientTensor M X) := by
  have hx : (β_ X A).hom = (β_ A X).inv := by
    apply (cancel_epi (β_ A X).hom).mp
    simpa only [Centralizes, doubleBraiding, Iso.trans_hom, Iso.hom_inv_id] using hX
  change (β_ (M.X ⊗ X) A).hom ≫ (α_ A M.X X).inv ≫ γ[A,M.X] ▷ X =
    (β_ A (M.X ⊗ X)).inv ≫ (α_ A M.X X).inv ≫ γ[A,M.X] ▷ X
  rw [braiding_tensor_left_hom, braiding_tensor_right_inv]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight, ← comp_whiskerRight, hx]
  exact congrArg (fun k => (α_ M.X X A).hom ≫ (M.X ◁ (β_ A X).inv) ≫
    (α_ M.X A X).inv ≫ k ▷ X) hM

/-- The actual free module on an object centralizing the algebra is local. -/
theorem localModule_free_of_centralizes (X : C) (hX : Centralizes A X) :
    IsLocalModule (InternalModule.free A X) := by
  have hA : IsLocalModule (Mod_.regular A) := by
    change (β_ A A).hom ≫ μ[A] = (β_ A A).inv ≫ μ[A]
    rw [IsCommMonObj.mul_comm, IsCommMonObj.mul_comm']
  exact hA.ambientTensor X hX

omit [IsCommMonObj A] in
/-- Locality of a free module detects actual ambient centralization of the
algebra by its generator. -/
theorem centralizes_of_localModule_free (X : C)
    (hX : IsLocalModule (InternalModule.free A X)) : Centralizes A X := by
  have hu : (A ◁ freeUnit (A := A) X) ≫ γ[A,(InternalModule.free A X).X] =
      𝟙 (InternalModule.free A X).X := by
    exact congrArg Mod_.Hom.hom (freeLift_freeUnit (A := A) X)
  have h := congrArg (fun k => (freeUnit (A := A) X ▷ A) ≫ k) hX
  change (freeUnit X ▷ A) ≫ (β_ (InternalModule.free A X).X A).hom ≫
      γ[A,(InternalModule.free A X).X] =
    (freeUnit X ▷ A) ≫ (β_ A (InternalModule.free A X).X).inv ≫
      γ[A,(InternalModule.free A X).X] at h
  rw [braiding_naturality_left_assoc, braiding_inv_naturality_left_assoc,
    hu] at h
  erw [Category.comp_id, Category.comp_id] at h
  change (β_ A X).hom ≫ (β_ X A).hom = 𝟙 _
  rw [h, Iso.hom_inv_id]

/-- The exact criterion for locality of an actual free module. -/
theorem localModule_free_iff (X : C) :
    IsLocalModule (InternalModule.free A X) ↔ Centralizes A X :=
  ⟨centralizes_of_localModule_free X, localModule_free_of_centralizes X⟩

section Functor
variable [RightRigidCategory C] [HasCoequalizers C]

/-- The actual free-module functor restricted to the ambient centralizer of
the algebra, with its image in actual local modules. -/
def localFreeFunctor : CentralizerCategory ({A} : Set C) ⥤ LocalModules A where
  obj X := ⟨InternalModule.free A X.obj, localModule_free_of_centralizes X.obj
    ((X.property A (Set.mem_singleton A)).symm)⟩
  map f := InternalModule.freeMap f
  map_id X := (InternalModule.freeFunctor (A := A)).map_id X.obj
  map_comp f g := (InternalModule.freeFunctor (A := A)).map_comp f g

/-- The restricted free functor has the same actual inverse tensorator as
the ambient free functor. -/
instance localFreeFunctorOplaxMonoidal : (localFreeFunctor (A := A)).OplaxMonoidal where
  «η» := (freeUnitIso (A := A)).inv
  δ X Y := (freeTensorIso X.obj Y.obj).inv
  δ_natural_left f Z := freeTensorIso_inv_natural_left (C := C) (A := A) f Z.obj
  δ_natural_right Z f := freeTensorIso_inv_natural_right (C := C) (A := A) Z.obj f
  oplax_associativity X Y Z := freeTensorIso_inv_associativity X.obj Y.obj Z.obj
  oplax_left_unitality X := freeFunctorOplaxMonoidal.oplax_left_unitality X.obj
  oplax_right_unitality X := freeFunctorOplaxMonoidal.oplax_right_unitality X.obj

instance localFreeFunctorOplaxUnitIsIso :
    IsIso (Functor.OplaxMonoidal.η (localFreeFunctor (A := A))) := by
  let e : (𝟙_ (LocalModules A)) ≅ (localFreeFunctor (A := A)).obj
      (𝟙_ (CentralizerCategory ({A} : Set C))) :=
    (localModuleProperty (A := A)).isoMk (freeUnitIso (A := A))
  change IsIso e.inv
  infer_instance

instance localFreeFunctorOplaxTensorIsIso (X Y : CentralizerCategory ({A} : Set C)) :
    IsIso (Functor.OplaxMonoidal.δ (localFreeFunctor (A := A)) X Y) := by
  let e : (localFreeFunctor (A := A)).obj X ⊗ (localFreeFunctor (A := A)).obj Y ≅
      (localFreeFunctor (A := A)).obj (X ⊗ Y) :=
    (localModuleProperty (A := A)).isoMk (freeTensorIso X.obj Y.obj)
  change IsIso e.inv
  infer_instance

/-- The restricted free functor is an actual strong monoidal functor. -/
instance localFreeFunctorMonoidal : (localFreeFunctor (A := A)).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    (Functor.CoreMonoidal.ofOplaxMonoidal (localFreeFunctor (A := A)))

@[reassoc]
theorem freeTensorIso_inv_localBraiding (X Y : C)
    (hY : IsLocalModule (InternalModule.free A Y)) :
    (freeTensorIso (A := A) X Y).inv ≫
        localBraidingHom (InternalModule.free A X) (InternalModule.free A Y) hY =
      InternalModule.freeMap (β_ X Y).hom ≫ (freeTensorIso Y X).inv := by
  apply free_hom_ext
  change freeUnit (X ⊗ Y) ≫ (freeTensorIso X Y).inv.hom ≫
      (localBraidingHom (InternalModule.free A X) (InternalModule.free A Y) hY).hom =
    freeUnit (X ⊗ Y) ≫ (InternalModule.freeMap (β_ X Y).hom).hom ≫
      (freeTensorIso Y X).inv.hom
  rw [freeUnit_freeTensorIso_inv_assoc, π_localBraidingHom,
    freeUnit_naturality_assoc, freeUnit_freeTensorIso_inv]
  exact BraidedCategory.braiding_naturality_assoc _ _ _

/-- The actual local free functor preserves the descended braiding. -/
instance localFreeFunctorBraided : (localFreeFunctor (A := A)).Braided where
  braided X Y := by
    apply (cancel_epi (Functor.OplaxMonoidal.δ (localFreeFunctor (A := A)) X Y)).mp
    change (freeTensorIso X.obj Y.obj).inv ≫
        Functor.LaxMonoidal.μ (localFreeFunctor (A := A)) X Y ≫
          InternalModule.freeMap (β_ X.obj Y.obj).hom =
      (freeTensorIso X.obj Y.obj).inv ≫
        localBraidingHom (InternalModule.free A X.obj) (InternalModule.free A Y.obj)
          ((localFreeFunctor (A := A)).obj Y).property ≫
          Functor.LaxMonoidal.μ (localFreeFunctor (A := A)) Y X
    rw [freeTensorIso_inv_localBraiding_assoc]
    change Functor.OplaxMonoidal.δ (localFreeFunctor (A := A)) X Y ≫
        Functor.LaxMonoidal.μ (localFreeFunctor (A := A)) X Y ≫
          InternalModule.freeMap (β_ X.obj Y.obj).hom =
      InternalModule.freeMap (β_ X.obj Y.obj).hom ≫
        Functor.OplaxMonoidal.δ (localFreeFunctor (A := A)) Y X ≫
          Functor.LaxMonoidal.μ (localFreeFunctor (A := A)) Y X
    simp only [Functor.Monoidal.δ_μ_assoc]
    erw [Functor.Monoidal.δ_μ (localFreeFunctor (A := A)) Y X]
    erw [Category.comp_id]

end Functor
end Paper18.Category
