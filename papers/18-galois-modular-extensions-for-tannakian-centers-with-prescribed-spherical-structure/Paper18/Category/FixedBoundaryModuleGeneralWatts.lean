import Paper18.Category.FixedBoundaryModuleFaithful

/-!
# Actual Eilenberg--Watts isomorphisms with arbitrary module target

For a genuine native left module category M, a strong module functor from
the regular module C to M is represented by its value at the unit. The
representing functor uses the actual action of C on that value.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped MonoidalLeftAction
universe v u v' u'
namespace Paper18.Category.ModuleFunctor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {M : Type u'} [Category.{v'} M] [MonoidalLeftAction C M]

/-- The actual action-on-an-object functor is a strong module functor. -/
instance actionRightLeftLinear (U : M) :
    (MonoidalLeftAction.actionRight C U).LeftLinear C where
  μₗ X Y := (αₗ X Y U).inv
  μₗ_naturality_left {X X'} f Y := by
    change (f ⊵ₗ (Y ⊙ₗ U)) ≫ (αₗ X' Y U).inv =
      (αₗ X Y U).inv ≫ ((f ▷ Y) ⊵ₗ U)
    simp only [MonoidalLeftAction.actionHomLeft_action, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  μₗ_naturality_right X {Y Y'} f := by
    change X ⊴ₗ (f ⊵ₗ U) ≫ (αₗ X Y' U).inv =
      (αₗ X Y U).inv ≫ ((X ◁ f) ⊵ₗ U)
    rw [MonoidalLeftAction.whiskerLeft_actionHomLeft]
    simp
  μₗ_associativity X Y Z := by
    change (αₗ (X ⊗ Y) Z U).inv ≫ ((α_ X Y Z).hom ⊵ₗ U) =
      (αₗ X Y (Z ⊙ₗ U)).hom ≫ X ⊴ₗ (αₗ Y Z U).inv ≫
        (αₗ X (Y ⊗ Z) U).inv
    apply (cancel_epi (αₗ (X ⊗ Y) Z U).hom).mp
    apply (cancel_mono (αₗ X (Y ⊗ Z) U).hom).mp
    apply (cancel_mono (X ⊴ₗ (αₗ Y Z U).hom)).mp
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
      Category.id_comp, Category.comp_id, MonoidalLeftAction.actionHomRight_inv_hom] using
      MonoidalLeftAction.associator_actionHom X Y Z U
  μₗ_unitality Y := by
    change (λₗ (Y ⊙ₗ U)).hom = (αₗ (𝟙_ C) Y U).inv ≫ ((λ_ Y).hom ⊵ₗ U)
    rw [MonoidalLeftAction.leftUnitor_actionHom]
    simp
  δₗ X Y := (αₗ X Y U).hom
  δₗ_naturality_left {X X'} f Y := by
    change ((f ▷ Y) ⊵ₗ U) ≫ (αₗ X' Y U).hom =
      (αₗ X Y U).hom ≫ (f ⊵ₗ (Y ⊙ₗ U))
    rw [MonoidalLeftAction.whiskerRight_actionHomLeft]
    simp
  δₗ_naturality_right X {Y Y'} f := by
    change ((X ◁ f) ⊵ₗ U) ≫ (αₗ X Y' U).hom =
      (αₗ X Y U).hom ≫ X ⊴ₗ (f ⊵ₗ U)
    rw [MonoidalLeftAction.whiskerLeft_actionHomLeft]
    simp
  δₗ_associativity X Y Z := by
    change (αₗ (X ⊗ Y) Z U).hom ≫ (αₗ X Y (Z ⊙ₗ U)).hom =
      ((α_ X Y Z).hom ⊵ₗ U) ≫ (αₗ X (Y ⊗ Z) U).hom ≫
        X ⊴ₗ (αₗ Y Z U).hom
    exact (MonoidalLeftAction.associator_actionHom X Y Z U).symm
  δₗ_unitality_inv Y := by
    change (λₗ (Y ⊙ₗ U)).inv = ((λ_ Y).inv ⊵ₗ U) ≫ (αₗ (𝟙_ C) Y U).hom
    apply (cancel_mono (λₗ (Y ⊙ₗ U)).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id]
    rw [← MonoidalLeftAction.leftUnitor_actionHom]
    exact (MonoidalLeftAction.inv_hom_actionHomLeft (λ_ Y) U).symm
  μₗ_comp_δₗ X Y := (αₗ X Y U).inv_hom_id
  δₗ_comp_μₗ X Y := (αₗ X Y U).hom_inv_id

variable (F : C ⥤ M) [F.LeftLinear C]

/-- The actual representing isomorphism in an arbitrary module category. -/
def actionRepresentationIso : F ≅ MonoidalLeftAction.actionRight C (F.obj (𝟙_ C)) :=
  NatIso.ofComponents (fun X =>
    (F.mapIso (ρ_ X)).symm ≪≫ (Functor.LeftLinear.μₗIso F X (𝟙_ C)).symm)
    (fun {X Y} f => by
      change F.map f ≫ (F.map (ρ_ Y).inv ≫ Functor.OplaxLeftLinear.δₗ F Y (𝟙_ C)) =
        (F.map (ρ_ X).inv ≫ Functor.OplaxLeftLinear.δₗ F X (𝟙_ C)) ≫
          (f ⊵ₗ F.obj (𝟙_ C))
      rw [← Category.assoc, ← F.map_comp, rightUnitor_inv_naturality, F.map_comp]
      simp only [Category.assoc]
      exact congrArg (fun t => F.map (ρ_ X).inv ≫ t)
        (Functor.OplaxLeftLinear.δₗ_naturality_left F f (𝟙_ C)))

@[simp] theorem actionRepresentationIso_hom (X : C) :
    (actionRepresentationIso F).hom.app X =
      F.map (ρ_ X).inv ≫ Functor.OplaxLeftLinear.δₗ F X (𝟙_ C) := rfl

instance actionRepresentationIso_moduleNatural :
    IsModuleNatural C (actionRepresentationIso F).hom where
  lineator X Y := by
    change Functor.LaxLeftLinear.μₗ F X Y ≫
        (F.map (ρ_ (X ⊗ Y)).inv ≫ Functor.OplaxLeftLinear.δₗ F (X ⊗ Y) (𝟙_ C)) =
      X ⊴ₗ (F.map (ρ_ Y).inv ≫ Functor.OplaxLeftLinear.δₗ F Y (𝟙_ C)) ≫
        (αₗ X Y (F.obj (𝟙_ C))).inv
    apply (cancel_mono (αₗ X Y (F.obj (𝟙_ C))).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have ha := Functor.OplaxLeftLinear.δₗ_associativity F X Y (𝟙_ C)
    change Functor.OplaxLeftLinear.δₗ F (X ⊗ Y) (𝟙_ C) ≫
        (αₗ X Y (F.obj (𝟙_ C))).hom = F.map (α_ X Y (𝟙_ C)).hom ≫
        Functor.OplaxLeftLinear.δₗ F X (Y ⊗ (𝟙_ C)) ≫
        X ⊴ₗ Functor.OplaxLeftLinear.δₗ F Y (𝟙_ C) at ha
    rw [ha]
    simp only [← F.map_comp_assoc]
    have hr : (ρ_ (X ⊗ Y)).inv ≫ (α_ X Y (𝟙_ C)).hom = X ◁ (ρ_ Y).inv := by monoidal
    rw [hr]
    have hn := Functor.LaxLeftLinear.μₗ_naturality_right F X (ρ_ Y).inv
    change X ⊴ₗ F.map (ρ_ Y).inv ≫ Functor.LaxLeftLinear.μₗ F X (Y ⊗ (𝟙_ C)) =
      Functor.LaxLeftLinear.μₗ F X Y ≫ F.map (X ◁ (ρ_ Y).inv) at hn
    slice_lhs 1 2 => rw [← hn]
    simp only [Category.assoc]
    erw [Functor.LeftLinear.μₗ_comp_δₗ_assoc]
    rw [MonoidalLeftAction.actionHomRight_comp]

variable {F} {H : C ⥤ M} [H.LeftLinear C]

/-- The representing isomorphism is natural for actual module maps. -/
theorem actionRepresentationIso_natural (τ : F ⟶ H) [IsModuleNatural C τ] (X : C) :
    τ.app X ≫ (actionRepresentationIso H).hom.app X =
      (actionRepresentationIso F).hom.app X ≫ (X ⊴ₗ τ.app (𝟙_ C)) := by
  rw [actionRepresentationIso_hom, actionRepresentationIso_hom]
  rw [← Category.assoc, ← τ.naturality, Category.assoc]
  have hd := IsModuleNatural.inverse_lineator C τ X (𝟙_ C)
  change τ.app (X ⊗ (𝟙_ C)) ≫ Functor.OplaxLeftLinear.δₗ H X (𝟙_ C) =
    Functor.OplaxLeftLinear.δₗ F X (𝟙_ C) ≫ X ⊴ₗ τ.app (𝟙_ C) at hd
  rw [hd, Category.assoc]

/-- Actual module maps out of the regular module are determined at the unit. -/
theorem actionModuleNatTrans_ext (τ σ : F ⟶ H) [IsModuleNatural C τ] [IsModuleNatural C σ]
    (h : τ.app (𝟙_ C) = σ.app (𝟙_ C)) : τ = σ := by
  ext X
  apply (cancel_mono ((actionRepresentationIso H).hom.app X)).mp
  rw [actionRepresentationIso_natural, actionRepresentationIso_natural, h]

end Paper18.Category.ModuleFunctor
