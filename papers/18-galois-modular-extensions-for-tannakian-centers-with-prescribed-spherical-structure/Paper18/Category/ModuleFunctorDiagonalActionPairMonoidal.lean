import Paper18.Category.ModuleFunctorDiagonalActionPairLinear
/-! # Native coherence of the actual post/precomposition pair action -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalLeftAction MonoidalOpposite
open Paper18.Category.ModuleAlphaInduction
open scoped MonoidalLeftAction
universe v u vM uM vN uN
namespace Paper18.Category.ModuleFunctor.DiagonalAction
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {M : Type uM} [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction C M]
  {N : Type uN} [Category.{vN} N] [Preadditive N] [Linear ℂ N]
  [MonoidalLeftAction C N]
  [∀ X : C, (actionLeft M X).Additive] [∀ X : C, (actionLeft M X).Linear ℂ]
  [∀ X : C, (actionLeft N X).Additive] [∀ X : C, (actionLeft N X).Linear ℂ]
omit [BraidedCategory C]
  [∀ X : C, (actionLeft M X).Additive] [∀ X : C, (actionLeft M X).Linear ℂ]
  [∀ X : C, (actionLeft N X).Additive] [∀ X : C, (actionLeft N X).Linear ℂ] in
@[simp] lemma ordinary_comp_apply {F G H : Ordinary C M N} (f : F ⟶ G) (g : G ⟶ H) (m : M) :
    (f ≫ g).app m = f.app m ≫ g.app m := rfl
omit [BraidedCategory C]
  [∀ X : C, (actionLeft M X).Additive] [∀ X : C, (actionLeft M X).Linear ℂ]
  [∀ X : C, (actionLeft N X).Additive] [∀ X : C, (actionLeft N X).Linear ℂ] in
@[simp] lemma ordinary_id_apply (F : Ordinary C M N) (m : M) :
    (show toFunctor F ⟶ toFunctor F from (𝟙 F : F ⟶ F)).app m =
      𝟙 ((toFunctor F).obj m) := rfl
@[simp] lemma pairObject_map_app (X Y : C) (F : Ordinary C M N)
    {m n : M} (f : m ⟶ n) :
    (toFunctor (pairObject X Y F)).map f = X ⊴ₗ (toFunctor F).map (Y ⊴ₗ f) := rfl
@[simp] lemma pairBifunctor_obj_toFunctor (P : C × Cᴹᵒᵖ) :
    LinearEnd.toFunctor (pairBifunctor.obj P).unmop = pairEnd (M := M) (N := N) P.1 P.2.unmop := rfl
@[simp] lemma pairBifunctor_map_app {P Q : C × Cᴹᵒᵖ} (f : P ⟶ Q)
    (F : Ordinary C M N) (m : M) :
    (forget.map ((LinearEnd.forget.map (pairBifunctor.map f).unmop).app F)).app m =
      (f.1 ⊵ₗ (toFunctor F).obj (P.2.unmop ⊙ₗ m)) ≫
        Q.1 ⊴ₗ (toFunctor F).map (f.2.unmop ⊵ₗ m) := rfl
@[simp] lemma pairEnd_map_app (X Y : C) {F G : Ordinary C M N} (f : F ⟶ G) (m : M) :
    (forget.map ((pairEnd X Y).map f)).app m = X ⊴ₗ f.app (Y ⊙ₗ m) := rfl
@[simp] lemma pairTensorIso_hom_app (X Y X' Y' : C) (F : Ordinary C M N) (m : M) :
    ((pairTensorIso X Y X' Y').hom.app F).app m =
      X ⊴ₗ X' ⊴ₗ (toFunctor F).map (αₗ Y' Y m).inv ≫
        (αₗ X X' ((toFunctor F).obj ((Y' ⊗ Y) ⊙ₗ m))).inv := rfl
@[simp] lemma pairUnitIso_hom_app (F : Ordinary C M N) (m : M) :
    (pairUnitIso.hom.app F).app m =
      (toFunctor F).map (λₗ[C] m).inv ≫
        (λₗ[C] ((toFunctor F).obj ((𝟙_ C) ⊙ₗ m))).inv := rfl
@[simp] lemma pairBifunctor_map_app_raw {P Q : C × Cᴹᵒᵖ} (f : P ⟶ Q)
    (F : Ordinary C M N) (m : M) :
    ((pairBifunctor.map f).unmop.app F).app m =
      (f.1 ⊵ₗ (toFunctor F).obj (P.2.unmop ⊙ₗ m)) ≫
        Q.1 ⊴ₗ (toFunctor F).map (f.2.unmop ⊵ₗ m) := rfl
@[simp] lemma pairCoreTensor_app (X Y X' Y' : C) (F : Ordinary C M N) (m : M) :
    (forget.map ((LinearEnd.forget.map
      (show LinearEnd.tensor (LinearEnd.ofFunctor (pairEnd X' Y'))
        (LinearEnd.ofFunctor (pairEnd X Y)) ≅
        LinearEnd.ofFunctor (pairEnd (X ⊗ X') (Y' ⊗ Y)) from
          InducedCategory.isoMk (pairTensorIso X Y X' Y')).hom).app F)).app m =
      X ⊴ₗ X' ⊴ₗ (toFunctor F).map (αₗ Y' Y m).inv ≫
        (αₗ X X' ((toFunctor F).obj ((Y' ⊗ Y) ⊙ₗ m))).inv := rfl
@[simp] lemma pairCoreUnit_app (F : Ordinary C M N) (m : M) :
    (forget.map ((LinearEnd.forget.map
      (show LinearEnd.unit (D := Ordinary C M N) ≅
        LinearEnd.ofFunctor (pairEnd (𝟙_ C) (𝟙_ C)) from
          InducedCategory.isoMk pairUnitIso).hom).app F)).app m =
      (toFunctor F).map (λₗ[C] m).inv ≫
        (λₗ[C] ((toFunctor F).obj ((𝟙_ C) ⊙ₗ m))).inv := rfl
omit [BraidedCategory C]
  [∀ X : C, (actionLeft M X).Additive] [∀ X : C, (actionLeft M X).Linear ℂ]
  [∀ X : C, (actionLeft N X).Additive] [∀ X : C, (actionLeft N X).Linear ℂ] in
lemma pair_right_unit_eq (X Y : C) (F : Ordinary C M N) (m : M) :
    𝟙 (X ⊙ₗ (toFunctor F).obj (Y ⊙ₗ m)) =
      (X ⊴ₗ ((toFunctor F).map (λₗ[C] (Y ⊙ₗ m)).inv ≫
        (λₗ[C] ((toFunctor F).obj ((𝟙_ C) ⊙ₗ Y ⊙ₗ m))).inv)) ≫
      (X ⊴ₗ (𝟙_ C) ⊴ₗ (toFunctor F).map (αₗ (𝟙_ C) Y m).inv) ≫
      (αₗ X (𝟙_ C) ((toFunctor F).obj (((𝟙_ C) ⊗ Y) ⊙ₗ m))).inv ≫
      (ρ_ X).hom ⊵ₗ (toFunctor F).obj (((𝟙_ C) ⊗ Y) ⊙ₗ m) ≫
      X ⊴ₗ (toFunctor F).map ((λ_ Y).hom ⊵ₗ m) := by
  simp only [actionHomRight_comp, assoc]
  have hu := congrArg (fun f => X ⊴ₗ f)
    (actionUnitIso_inv_naturality (C := C) ((toFunctor F).map (αₗ (𝟙_ C) Y m).inv))
  simp only [actionHomRight_comp] at hu
  rw [reassoc_of% hu, rightUnitor_actionHom]
  simp only [assoc, Iso.inv_hom_id_assoc, ← actionHomRight_comp]
  rw [← Functor.map_comp, ← Functor.map_comp, leftUnitor_actionHom]
  simp only [ Iso.inv_hom_id_assoc, Iso.inv_hom_id]
  erw [(toFunctor F).map_id]
  exact (actionHomRight_id X _).symm
def pairCoreMonoidal : (pairBifunctor (C := C) (M := M) (N := N)).CoreMonoidal where
  εIso := (show LinearEnd.unit (D := Ordinary C M N) ≅
    LinearEnd.ofFunctor (pairEnd (𝟙_ C) (𝟙_ C)) from
      InducedCategory.isoMk pairUnitIso).mop
  μIso P Q := (show LinearEnd.tensor
      (LinearEnd.ofFunctor (pairEnd Q.1 Q.2.unmop))
      (LinearEnd.ofFunctor (pairEnd P.1 P.2.unmop)) ≅
      LinearEnd.ofFunctor (pairEnd (P.1 ⊗ Q.1) (Q.2.unmop ⊗ P.2.unmop)) from
    InducedCategory.isoMk (pairTensorIso P.1 P.2.unmop Q.1 Q.2.unmop)).mop
  μIso_hom_natural_left {P Q} f R := by
    apply Quiver.Hom.unmop_inj
    ext F m
    change
      ((f.1 ⊵ₗ (R.1 ⊙ₗ (toFunctor F).obj (R.2.unmop ⊙ₗ P.2.unmop ⊙ₗ m))) ≫
        (Q.1 ⊴ₗ R.1 ⊴ₗ (toFunctor F).map (R.2.unmop ⊴ₗ f.2.unmop ⊵ₗ m))) ≫
        ((Q.1 ⊴ₗ R.1 ⊴ₗ (toFunctor F).map (αₗ R.2.unmop Q.2.unmop m).inv) ≫
          (αₗ Q.1 R.1 ((toFunctor F).obj ((R.2.unmop ⊗ Q.2.unmop) ⊙ₗ m))).inv) =
      ((P.1 ⊴ₗ R.1 ⊴ₗ (toFunctor F).map (αₗ R.2.unmop P.2.unmop m).inv) ≫
          (αₗ P.1 R.1 ((toFunctor F).obj ((R.2.unmop ⊗ P.2.unmop) ⊙ₗ m))).inv) ≫
        ((f.1 ▷ R.1) ⊵ₗ (toFunctor F).obj ((R.2.unmop ⊗ P.2.unmop) ⊙ₗ m) ≫
          (Q.1 ⊗ R.1) ⊴ₗ (toFunctor F).map ((R.2.unmop ◁ f.2.unmop) ⊵ₗ m))
    have hpre := actionAssoc_inv_naturality_middle R.2.unmop f.2.unmop m
    have hpreF :
        Q.1 ⊴ₗ R.1 ⊴ₗ (toFunctor F).map (R.2.unmop ⊴ₗ f.2.unmop ⊵ₗ m) ≫
          Q.1 ⊴ₗ R.1 ⊴ₗ (toFunctor F).map (αₗ R.2.unmop Q.2.unmop m).inv =
        Q.1 ⊴ₗ R.1 ⊴ₗ (toFunctor F).map (αₗ R.2.unmop P.2.unmop m).inv ≫
          Q.1 ⊴ₗ R.1 ⊴ₗ (toFunctor F).map ((R.2.unmop ◁ f.2.unmop) ⊵ₗ m) := by
      simp only [← actionHomRight_comp, ← Functor.map_comp]
      rw [hpre]
    have hpost :
        f.1 ⊵ₗ (R.1 ⊙ₗ (toFunctor F).obj ((R.2.unmop ⊗ P.2.unmop) ⊙ₗ m)) ≫
          (αₗ Q.1 R.1 ((toFunctor F).obj ((R.2.unmop ⊗ P.2.unmop) ⊙ₗ m))).inv =
        (αₗ P.1 R.1 ((toFunctor F).obj ((R.2.unmop ⊗ P.2.unmop) ⊙ₗ m))).inv ≫
          (f.1 ▷ R.1) ⊵ₗ (toFunctor F).obj ((R.2.unmop ⊗ P.2.unmop) ⊙ₗ m) := by
      rw [whiskerRight_actionHomLeft]
      simp only [← assoc, Iso.inv_hom_id, id_comp]
    simp only [assoc]
    rw [reassoc_of% hpreF, actionAssoc_inv_naturality_right]
    rw [← action_exchange_assoc, reassoc_of% hpost]
  μIso_hom_natural_right {P Q} R f := by
    apply Quiver.Hom.unmop_inj
    ext F m
    change
      (R.1 ⊴ₗ ((f.1 ⊵ₗ (toFunctor F).obj (P.2.unmop ⊙ₗ R.2.unmop ⊙ₗ m)) ≫
        Q.1 ⊴ₗ (toFunctor F).map (f.2.unmop ⊵ₗ (R.2.unmop ⊙ₗ m)))) ≫
        ((R.1 ⊴ₗ Q.1 ⊴ₗ (toFunctor F).map (αₗ Q.2.unmop R.2.unmop m).inv) ≫
          (αₗ R.1 Q.1 ((toFunctor F).obj ((Q.2.unmop ⊗ R.2.unmop) ⊙ₗ m))).inv) =
      ((R.1 ⊴ₗ P.1 ⊴ₗ (toFunctor F).map (αₗ P.2.unmop R.2.unmop m).inv) ≫
          (αₗ R.1 P.1 ((toFunctor F).obj ((P.2.unmop ⊗ R.2.unmop) ⊙ₗ m))).inv) ≫
        ((R.1 ◁ f.1) ⊵ₗ (toFunctor F).obj ((P.2.unmop ⊗ R.2.unmop) ⊙ₗ m) ≫
          (R.1 ⊗ Q.1) ⊴ₗ (toFunctor F).map ((f.2.unmop ▷ R.2.unmop) ⊵ₗ m))
    have hpre :
        f.2.unmop ⊵ₗ (R.2.unmop ⊙ₗ m) ≫ (αₗ Q.2.unmop R.2.unmop m).inv =
        (αₗ P.2.unmop R.2.unmop m).inv ≫ (f.2.unmop ▷ R.2.unmop) ⊵ₗ m := by
      rw [whiskerRight_actionHomLeft]
      simp only [← assoc, Iso.inv_hom_id, id_comp]
    have hpreF :
        R.1 ⊴ₗ Q.1 ⊴ₗ (toFunctor F).map (f.2.unmop ⊵ₗ (R.2.unmop ⊙ₗ m)) ≫
          R.1 ⊴ₗ Q.1 ⊴ₗ (toFunctor F).map (αₗ Q.2.unmop R.2.unmop m).inv =
        R.1 ⊴ₗ Q.1 ⊴ₗ (toFunctor F).map (αₗ P.2.unmop R.2.unmop m).inv ≫
          R.1 ⊴ₗ Q.1 ⊴ₗ (toFunctor F).map ((f.2.unmop ▷ R.2.unmop) ⊵ₗ m) := by
      simp only [← actionHomRight_comp, ← Functor.map_comp]
      rw [hpre]
    have hex :
        R.1 ⊴ₗ (f.1 ⊵ₗ (toFunctor F).obj (P.2.unmop ⊙ₗ R.2.unmop ⊙ₗ m)) ≫
          R.1 ⊴ₗ Q.1 ⊴ₗ (toFunctor F).map (αₗ P.2.unmop R.2.unmop m).inv =
        R.1 ⊴ₗ P.1 ⊴ₗ (toFunctor F).map (αₗ P.2.unmop R.2.unmop m).inv ≫
          R.1 ⊴ₗ (f.1 ⊵ₗ (toFunctor F).obj ((P.2.unmop ⊗ R.2.unmop) ⊙ₗ m)) := by
      rw [← actionHomRight_comp, ← actionHomRight_comp, ← action_exchange]
    simp only [actionHomRight_comp, assoc]
    rw [reassoc_of% hpreF, actionAssoc_inv_naturality_right,
      reassoc_of% hex, actionAssoc_inv_naturality_middle_assoc]
  associativity P Q R := by
    apply Quiver.Hom.unmop_inj
    ext F m
    simp only [unmop_comp, unmop_whiskerLeft, unmop_whiskerRight, unmop_hom_associator,
      Iso.mop, CategoryTheory.Functor.mapIso_hom, mopFunctor_map, Quiver.Hom.unmop_mop,
       
        pairBifunctor_obj_toFunctor,
      CategoryTheory.Functor.map_comp, LinearEnd.forget_whiskerLeft,
      LinearEnd.forget_whiskerRight, LinearEnd.forget_associator_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_inv_app,  
      pairEnd, forget, inducedFunctor]
    dsimp only [LinearEnd.forget, forget, inducedFunctor]
    simp only [InducedCategory.isoMk_hom, ordinary_comp_apply, ordinary_id_apply,
        Functor.whiskerLeft_app, Functor.whiskerRight_app,
      pairTensorIso_hom_app,  pairBifunctor_map_app_raw,
      pairObject_obj, pairObject_map_app]
    simp (config := { failIfUnchanged := false }) only [assoc]
    change
      (P.1 ⊴ₗ Q.1 ⊴ₗ R.1 ⊴ₗ (toFunctor F).map
        (R.2.unmop ⊴ₗ (αₗ Q.2.unmop P.2.unmop m).inv)) ≫
      (αₗ P.1 Q.1 (R.1 ⊙ₗ (toFunctor F).obj (R.2.unmop ⊙ₗ (Q.2.unmop ⊗ P.2.unmop) ⊙ₗ m))).inv ≫
      ((P.1 ⊗ Q.1) ⊴ₗ R.1 ⊴ₗ (toFunctor F).map (αₗ R.2.unmop (Q.2.unmop ⊗ P.2.unmop) m).inv) ≫
      (αₗ (P.1 ⊗ Q.1) R.1 ((toFunctor F).obj ((R.2.unmop ⊗ (Q.2.unmop ⊗ P.2.unmop)) ⊙ₗ m))).inv ≫
      (α_ P.1 Q.1 R.1).hom ⊵ₗ (toFunctor F).obj ((R.2.unmop ⊗ (Q.2.unmop ⊗ P.2.unmop)) ⊙ₗ m) ≫
      (P.1 ⊗ (Q.1 ⊗ R.1)) ⊴ₗ (toFunctor F).map ((α_ R.2.unmop Q.2.unmop P.2.unmop).inv ⊵ₗ m) =
      𝟙 _ ≫ (P.1 ⊴ₗ ((Q.1 ⊴ₗ R.1 ⊴ₗ (toFunctor F).map
        (αₗ R.2.unmop Q.2.unmop (P.2.unmop ⊙ₗ m)).inv) ≫
        (αₗ Q.1 R.1 ((toFunctor F).obj ((R.2.unmop ⊗ Q.2.unmop) ⊙ₗ P.2.unmop ⊙ₗ m))).inv)) ≫
      (P.1 ⊴ₗ (Q.1 ⊗ R.1) ⊴ₗ (toFunctor F).map
        (αₗ (R.2.unmop ⊗ Q.2.unmop) P.2.unmop m).inv) ≫
      (αₗ P.1 (Q.1 ⊗ R.1) ((toFunctor F).obj (((R.2.unmop ⊗ Q.2.unmop) ⊗ P.2.unmop) ⊙ₗ m))).inv
    rw [Category.id_comp]
    simp only [actionHomRight_comp, assoc]
    rw [← actionAssoc_inv_naturality_right_assoc]
    rw [associator_action_hom]
    simp only [assoc, Iso.inv_hom_id_assoc]
    rw [← actionAssoc_inv_naturality_right]
    have h₁ := congrArg (fun f => P.1 ⊴ₗ f)
      (actionAssoc_inv_naturality_right Q.1 R.1
        ((toFunctor F).map ((α_ R.2.unmop Q.2.unmop P.2.unmop).inv ⊵ₗ m)))
    have h₂ := congrArg (fun f => P.1 ⊴ₗ f)
      (actionAssoc_inv_naturality_right Q.1 R.1
        ((toFunctor F).map (αₗ (R.2.unmop ⊗ Q.2.unmop) P.2.unmop m).inv))
    simp only [actionHomRight_comp] at h₁ h₂
    rw [← reassoc_of% h₁, ← reassoc_of% h₂]
    have hp :
        R.2.unmop ⊴ₗ (αₗ Q.2.unmop P.2.unmop m).inv ≫
          (αₗ R.2.unmop (Q.2.unmop ⊗ P.2.unmop) m).inv ≫
            (α_ R.2.unmop Q.2.unmop P.2.unmop).inv ⊵ₗ m =
        (αₗ R.2.unmop Q.2.unmop (P.2.unmop ⊙ₗ m)).inv ≫
          (αₗ (R.2.unmop ⊗ Q.2.unmop) P.2.unmop m).inv := by
      rw [associator_action_inv]
      simp only [ Iso.inv_hom_id_assoc, actionHomRight_inv_hom_assoc]
    have hpf := congrArg (fun f => P.1 ⊴ₗ Q.1 ⊴ₗ R.1 ⊴ₗ (toFunctor F).map f) hp
    simp only [CategoryTheory.Functor.map_comp, actionHomRight_comp] at hpf
    simpa only [assoc] using congrArg (fun f => f ≫
      P.1 ⊴ₗ (αₗ Q.1 R.1 ((toFunctor F).obj
        (((R.2.unmop ⊗ Q.2.unmop) ⊗ P.2.unmop) ⊙ₗ m))).inv ≫
      (αₗ P.1 (Q.1 ⊗ R.1) ((toFunctor F).obj
        (((R.2.unmop ⊗ Q.2.unmop) ⊗ P.2.unmop) ⊙ₗ m))).inv) hpf
  left_unitality P := by
    apply Quiver.Hom.unmop_inj
    ext F m
    simp only [unmop_comp,  unmop_whiskerRight, 
      Iso.mop, CategoryTheory.Functor.mapIso_hom, mopFunctor_map, Quiver.Hom.unmop_mop,
      unmop_hom_leftUnitor,   LinearEnd.forget_rightUnitor,
       Functor.rightUnitor_hom_app,
        pairBifunctor_obj_toFunctor,
      CategoryTheory.Functor.map_comp, LinearEnd.forget_whiskerLeft,
      NatTrans.comp_app, Functor.whiskerLeft_app, 
         
      pairEnd, forget, inducedFunctor]
    dsimp only [LinearEnd.forget, forget, inducedFunctor]
    simp only [InducedCategory.isoMk_hom, ordinary_comp_apply, ordinary_id_apply,
      pairTensorIso_hom_app, pairUnitIso_hom_app, pairBifunctor_map_app_raw,
      pairObject_obj, pairObject_map_app]
    simp (config := { failIfUnchanged := false }) only [assoc]
    change 𝟙 _ =
      (P.1 ⊴ₗ (toFunctor F).map (P.2.unmop ⊴ₗ (λₗ[C] m).inv)) ≫
      (λₗ[C] (P.1 ⊙ₗ (toFunctor F).obj (P.2.unmop ⊙ₗ (𝟙_ C) ⊙ₗ m))).inv ≫
      ((𝟙_ C) ⊴ₗ P.1 ⊴ₗ (toFunctor F).map (αₗ P.2.unmop (𝟙_ C) m).inv) ≫
      (αₗ (𝟙_ C) P.1 ((toFunctor F).obj ((P.2.unmop ⊗ (𝟙_ C)) ⊙ₗ m))).inv ≫
      (λ_ P.1).hom ⊵ₗ (toFunctor F).obj ((P.2.unmop ⊗ (𝟙_ C)) ⊙ₗ m) ≫
      P.1 ⊴ₗ (toFunctor F).map ((ρ_ P.2.unmop).hom ⊵ₗ m)
    rw [actionUnitIso_inv_naturality_assoc, leftUnitor_actionHom]
    simp only [assoc, Iso.inv_hom_id_assoc]
    rw [← actionHomRight_comp, ← actionHomRight_comp, ← Functor.map_comp, ← Functor.map_comp,
      rightUnitor_actionHom]
    simp
  right_unitality P := by
    apply Quiver.Hom.unmop_inj
    ext F m
    simp only [unmop_comp, unmop_whiskerLeft,  
      Iso.mop, CategoryTheory.Functor.mapIso_hom, mopFunctor_map, Quiver.Hom.unmop_mop,
       unmop_hom_rightUnitor, LinearEnd.forget_leftUnitor, 
      Functor.leftUnitor_hom_app, 
        pairBifunctor_obj_toFunctor,
      CategoryTheory.Functor.map_comp, 
      LinearEnd.forget_whiskerRight, 
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
         
      pairEnd, forget, inducedFunctor]
    dsimp only [LinearEnd.forget, forget, inducedFunctor]
    simp only [InducedCategory.isoMk_hom, ordinary_comp_apply, ordinary_id_apply,
      pairTensorIso_hom_app, pairUnitIso_hom_app, pairBifunctor_map_app_raw,
      pairObject_obj]
    simp (config := { failIfUnchanged := false }) only [assoc]
    change 𝟙 _ =
      (P.1 ⊴ₗ ((toFunctor F).map (λₗ[C] (P.2.unmop ⊙ₗ m)).inv ≫
        (λₗ[C] ((toFunctor F).obj ((𝟙_ C) ⊙ₗ P.2.unmop ⊙ₗ m))).inv)) ≫
      (P.1 ⊴ₗ (𝟙_ C) ⊴ₗ (toFunctor F).map (αₗ (𝟙_ C) P.2.unmop m).inv) ≫
      (αₗ P.1 (𝟙_ C) ((toFunctor F).obj (((𝟙_ C) ⊗ P.2.unmop) ⊙ₗ m))).inv ≫
      (ρ_ P.1).hom ⊵ₗ (toFunctor F).obj (((𝟙_ C) ⊗ P.2.unmop) ⊙ₗ m) ≫
      P.1 ⊴ₗ (toFunctor F).map ((λ_ P.2.unmop).hom ⊵ₗ m)
    exact pair_right_unit_eq P.1 P.2.unmop F m
instance pairBifunctorMonoidal :
    (pairBifunctor (C := C) (M := M) (N := N)).Monoidal := pairCoreMonoidal.toMonoidal
end Paper18.Category.ModuleFunctor.DiagonalAction
