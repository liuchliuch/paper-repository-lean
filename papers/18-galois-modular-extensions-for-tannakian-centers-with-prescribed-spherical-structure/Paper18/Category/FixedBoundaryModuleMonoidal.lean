import Paper18.Category.FixedBoundaryModuleMonoidalStrong

/-! # The actual strong monoidal functor on transported internal modules -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj Obj
universe v u v' u'
namespace Paper18.Category.InternalModule
open RelativeTensor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [HasCoequalizers C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [HasCoequalizers D]
  (F : C ⥤ D) [F.Braided] [PreservesColimitsOfShape WalkingParallelPair F]
  {A : C} [MonObj A] [IsCommMonObj A]

/-- The regular module is transported to the actual regular image algebra. -/
def mapModulesUnitHom : 𝟙_ (Mod_ D (F.obj A)) ⟶ (mapModules F).obj (𝟙_ (Mod_ C A)) :=
  Mod_.Hom.mk' (𝟙 (F.obj A)) (by
    change (Functor.LaxMonoidal.μ F A A ≫ F.map μ[A]) ≫ 𝟙 _ =
      (F.obj A ◁ 𝟙 _) ≫ (Functor.LaxMonoidal.μ F A A ≫ F.map μ[A])
    simp)

instance mapModulesUnitHom_isIso : IsIso (mapModulesUnitHom F (A := A)) := by
  letI : IsIso (mapModulesUnitHom F (A := A)).hom := inferInstanceAs (IsIso (𝟙 (F.obj A)))
  exact internalModule_isIso_of_underlying (mapModulesUnitHom F (A := A))

instance mapModulesLaxMonoidal : (mapModules F (A := A)).LaxMonoidal where
  ε := mapModulesUnitHom F
  «μ» := mapModulesTensorHom F
  μ_natural_left {M N} f P := by
    apply module_hom_ext
    change π (mapModuleObj F M) (mapModuleObj F P) ≫
        ((mapModules F).map f ▷ (mapModules F).obj P).hom ≫ (mapModulesTensorHom F N P).hom =
      π (mapModuleObj F M) (mapModuleObj F P) ≫ (mapModulesTensorHom F M P).hom ≫
        F.map (f ▷ P).hom
    erw [π_whiskerRight_assoc, π_mapModulesTensorHom, π_mapModulesTensorHom_assoc]
    change (F.map f.hom ▷ F.obj P.X) ≫ Functor.LaxMonoidal.μ F N.X P.X ≫ F.map (π N P) = _
    rw [Functor.LaxMonoidal.μ_natural_left_assoc, ← F.map_comp, ← π_whiskerRight, F.map_comp]
  μ_natural_right {M N} P f := by
    apply module_hom_ext
    change π (mapModuleObj F P) (mapModuleObj F M) ≫
        ((mapModules F).obj P ◁ (mapModules F).map f).hom ≫ (mapModulesTensorHom F P N).hom =
      π (mapModuleObj F P) (mapModuleObj F M) ≫ (mapModulesTensorHom F P M).hom ≫
        F.map (P ◁ f).hom
    erw [π_whiskerLeft_assoc, π_mapModulesTensorHom, π_mapModulesTensorHom_assoc]
    change (F.obj P.X ◁ F.map f.hom) ≫ Functor.LaxMonoidal.μ F P.X N.X ≫ F.map (π P N) = _
    rw [Functor.LaxMonoidal.μ_natural_right_assoc, ← F.map_comp, ← π_whiskerLeft, F.map_comp]
  associativity M N P := by
    apply triple_hom_ext
    change (π (mapModuleObj F M) (mapModuleObj F N) ▷ F.obj P.X) ≫
        π (mapModuleObj F M ⊗ mapModuleObj F N) (mapModuleObj F P) ≫
        (mapModulesTensorHom F M N ▷ (mapModules F).obj P).hom ≫
        (mapModulesTensorHom F (M ⊗ N) P).hom ≫ F.map (α_ M N P).hom.hom =
      (π (mapModuleObj F M) (mapModuleObj F N) ▷ F.obj P.X) ≫
        π (mapModuleObj F M ⊗ mapModuleObj F N) (mapModuleObj F P) ≫
        (α_ (mapModuleObj F M) (mapModuleObj F N) (mapModuleObj F P)).hom.hom ≫
        ((mapModules F).obj M ◁ mapModulesTensorHom F N P).hom ≫
        (mapModulesTensorHom F M (N ⊗ P)).hom
    erw [π_whiskerRight_assoc, ← comp_whiskerRight_assoc, π_mapModulesTensorHom,
      π_mapModulesTensorHom_assoc]
    erw [π_associator_assoc (mapModuleObj F M) (mapModuleObj F N) (mapModuleObj F P),
      π_whiskerLeft_assoc, ← whiskerLeft_comp_assoc, π_mapModulesTensorHom,
      π_mapModulesTensorHom]
    simp only [mapModuleObj_X, comp_whiskerRight, whiskerLeft_comp, Category.assoc]
    erw [Functor.LaxMonoidal.μ_natural_left_assoc, ← F.map_comp, ← F.map_comp, π_associator]
    simp only [F.map_comp, Category.assoc]
    rw [Functor.LaxMonoidal.associativity_assoc, ← Functor.LaxMonoidal.μ_natural_right_assoc]
    rfl
  left_unitality M := by
    apply module_hom_ext
    change π (𝟙_ (Mod_ D (F.obj A))) (mapModuleObj F M) ≫
        (λ_ (mapModuleObj F M)).hom.hom =
      π (𝟙_ (Mod_ D (F.obj A))) (mapModuleObj F M) ≫
        (mapModulesUnitHom F ▷ (mapModules F).obj M).hom ≫
        (mapModulesTensorHom F (𝟙_ (Mod_ C A)) M).hom ≫ F.map (λ_ M).hom.hom
    erw [π_leftUnitor, π_whiskerRight_assoc, π_mapModulesTensorHom_assoc]
    change Functor.LaxMonoidal.μ F A M.X ≫ F.map γ[A,M.X] =
      (𝟙 (F.obj A) ▷ F.obj M.X) ≫ Functor.LaxMonoidal.μ F A M.X ≫
        F.map (π (𝟙_ (Mod_ C A)) M) ≫ F.map (λ_ M).hom.hom
    rw [id_whiskerRight, Category.id_comp, ← F.map_comp, π_leftUnitor]
  right_unitality M := by
    apply module_hom_ext
    change π (mapModuleObj F M) (𝟙_ (Mod_ D (F.obj A))) ≫
        (ρ_ (mapModuleObj F M)).hom.hom =
      π (mapModuleObj F M) (𝟙_ (Mod_ D (F.obj A))) ≫
        ((mapModules F).obj M ◁ mapModulesUnitHom F).hom ≫
        (mapModulesTensorHom F M (𝟙_ (Mod_ C A))).hom ≫ F.map (ρ_ M).hom.hom
    erw [π_rightUnitor, π_whiskerLeft_assoc, π_mapModulesTensorHom_assoc]
    change rightAction (mapModuleObj F M) =
      (F.obj M.X ◁ 𝟙 (F.obj A)) ≫ Functor.LaxMonoidal.μ F M.X A ≫
        F.map (π M (𝟙_ (Mod_ C A))) ≫ F.map (ρ_ M).hom.hom
    rw [whiskerLeft_id, Category.id_comp, ← F.map_comp, π_rightUnitor, mapModule_rightAction]

instance mapModules_ε_isIso : IsIso (Functor.LaxMonoidal.ε (mapModules F (A := A))) :=
  inferInstanceAs (IsIso (mapModulesUnitHom F))

instance mapModules_μ_isIso (M N : Mod_ C A) :
    IsIso (Functor.LaxMonoidal.μ (mapModules F) M N) :=
  inferInstanceAs (IsIso (mapModulesTensorHom F M N))

/-- An actual braided tensor functor preserving balancing coequalizers
induces an actual strong tensor functor on internal modules. -/
instance mapModulesMonoidal : (mapModules F (A := A)).Monoidal :=
  (Functor.CoreMonoidal.ofLaxMonoidal (mapModules F)).toMonoidal

@[reassoc] theorem π_mapModules_μ (M N : Mod_ C A) :
    π (mapModuleObj F M) (mapModuleObj F N) ≫
      (Functor.LaxMonoidal.μ (mapModules F) M N).hom =
        Functor.LaxMonoidal.μ F M.X N.X ≫ F.map (π M N) := π_mapModulesTensorHom F M N

end Paper18.Category.InternalModule
