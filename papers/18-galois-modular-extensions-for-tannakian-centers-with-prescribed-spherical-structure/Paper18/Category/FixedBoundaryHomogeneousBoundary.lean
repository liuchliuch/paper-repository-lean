import Paper18.Category.FixedBoundaryOddModule
import Paper18.Category.FixedBoundaryBasic
import Paper18.Category.FixedBoundaryModuleStrong

/-!
# Actual boundary-preserving functors on homogeneous module categories

The specified monoidal boundary comparison supplies the native module
lineator on the original autoequivalence restricted to a homogeneous
component. The boundary component is used explicitly, so its chosen value
is retained in this construction.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonoidalLeftAction
universe v u
namespace Paper18.Category.FixedBoundary
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasFiniteBiproducts C]
  (χ : 𝟭 C ≅ 𝟭 C) [NatTrans.IsMonoidal χ.hom]
  (F : C ⥤ C) [F.Monoidal] [F.IsEquivalence] [F.Additive] [F.Linear ℂ]

/-- The actual autoequivalence restricted to its preserved component. -/
def homogeneousBoundaryFunctor
    (a : SignKernel.inclusion χ ⋙ F ≅ SignKernel.inclusion χ) (d : ZMod 2)
    (hF : ∀ X : C, Homogeneous χ d X → Homogeneous χ d (F.obj X)) :
    HomogeneousCategory χ d ⥤ HomogeneousCategory χ d where
  obj X := ⟨F.obj X.obj, hF X.obj X.property⟩
  map f := F.map f
  map_id X := F.map_id X.obj
  map_comp f g := F.map_comp f g

variable (a : SignKernel.inclusion χ ⋙ F ≅ SignKernel.inclusion χ)
  [NatTrans.IsMonoidal a.hom] (d : ZMod 2)
  (hF : ∀ X : C, Homogeneous χ d X → Homogeneous χ d (F.obj X))

instance homogeneousFunctor_faithful : (homogeneousBoundaryFunctor χ F a d hF).Faithful where
  map_injective h := F.map_injective h

instance homogeneousFunctor_full : (homogeneousBoundaryFunctor χ F a d hF).Full where
  map_surjective f := ⟨F.preimage f, F.map_preimage f⟩

instance homogeneousFunctor_additive : (homogeneousBoundaryFunctor χ F a d hF).Additive where
  map_add := F.map_add

instance homogeneousFunctor_linear : (homogeneousBoundaryFunctor χ F a d hF).Linear ℂ where
  map_smul f r := F.map_smul r f

private theorem boundary_inv_tensor (X Y : SignKernel.Positive χ) :
    a.inv.app (X ⊗ Y) =
      (a.inv.app X ⊗ₘ a.inv.app Y) ≫
        Functor.LaxMonoidal.μ F X.obj Y.obj := by
  have h := NatTrans.IsMonoidal.tensor (τ := a.inv) X Y
  change (𝟙 _ ≫ a.inv.app (X ⊗ Y)) =
    (a.inv.app X ⊗ₘ a.inv.app Y) ≫
      (Functor.LaxMonoidal.μ F X.obj Y.obj ≫ F.map (𝟙 _)) at h
  simpa only [F.map_id, Category.comp_id, Category.id_comp] using h

private theorem boundary_inv_unit :
    a.inv.app (𝟙_ (SignKernel.Positive χ)) = Functor.LaxMonoidal.ε F := by
  have h := NatTrans.IsMonoidal.unit (τ := a.inv)
  change (𝟙 _ ≫ a.inv.app (𝟙_ (SignKernel.Positive χ))) =
    Functor.LaxMonoidal.ε F ≫ F.map (𝟙 _) at h
  simpa only [F.map_id, Category.id_comp, Category.comp_id] using h

/-- The actual boundary comparison gives the strong module lineator. -/
instance homogeneousFunctor_laxLeftLinear :
    (homogeneousBoundaryFunctor χ F a d hF).LaxLeftLinear (SignKernel.Positive χ) where
  μₗ X Y := (show X.obj ⊗ F.obj Y.obj ⟶ F.obj (X.obj ⊗ Y.obj) from
    a.inv.app X ▷ F.obj Y.obj ≫
      Functor.LaxMonoidal.μ F X.obj Y.obj)
  μₗ_naturality_left {X X'} f Y := by
    change (show X.obj ⟶ X'.obj from f) ▷ F.obj Y.obj ≫
        (a.inv.app X' ▷ F.obj Y.obj ≫
          Functor.LaxMonoidal.μ F X'.obj Y.obj) =
      (a.inv.app X ▷ F.obj Y.obj ≫
        Functor.LaxMonoidal.μ F X.obj Y.obj) ≫
          F.map ((show X.obj ⟶ X'.obj from f) ▷ Y.obj)
    have hn := a.inv.naturality f
    change (show X.obj ⟶ X'.obj from f) ≫ a.inv.app X' =
      a.inv.app X ≫ F.map (show X.obj ⟶ X'.obj from f) at hn
    rw [← comp_whiskerRight_assoc, hn, comp_whiskerRight]
    simp only [Category.assoc]
    rw [Functor.LaxMonoidal.μ_natural_left]
    rfl
  μₗ_naturality_right X {Y Y'} f := by
    change (X.obj ◁ F.map (show Y.obj ⟶ Y'.obj from f)) ≫
        (a.inv.app X ▷ F.obj Y'.obj ≫
          Functor.LaxMonoidal.μ F X.obj Y'.obj) =
      (a.inv.app X ▷ F.obj Y.obj ≫
        Functor.LaxMonoidal.μ F X.obj Y.obj) ≫
          F.map (X.obj ◁ (show Y.obj ⟶ Y'.obj from f))
    rw [← Category.assoc, whisker_exchange]
    simp only [Category.assoc]
    let ax : X.obj ⟶ F.obj X.obj := a.inv.app X
    let ff : Y.obj ⟶ Y'.obj := f
    change (ax ▷ F.obj Y.obj) ≫
        (F.obj X.obj ◁ F.map ff) ≫
        Functor.LaxMonoidal.μ F X.obj Y'.obj =
      (ax ▷ F.obj Y.obj) ≫ Functor.LaxMonoidal.μ F X.obj Y.obj ≫
        F.map (X.obj ◁ ff)
    rw [Functor.LaxMonoidal.μ_natural_right]
  μₗ_associativity X Y Z := by
    change (a.inv.app (X ⊗ Y) ▷ F.obj Z.obj ≫
        Functor.LaxMonoidal.μ F (X.obj ⊗ Y.obj) Z.obj) ≫
          F.map (α_ X.obj Y.obj Z.obj).hom =
      (α_ X.obj Y.obj (F.obj Z.obj)).hom ≫
        (X.obj ◁ (a.inv.app Y ▷ F.obj Z.obj ≫
          Functor.LaxMonoidal.μ F Y.obj Z.obj)) ≫
        (a.inv.app X ▷ F.obj (Y.obj ⊗ Z.obj) ≫
          Functor.LaxMonoidal.μ F X.obj (Y.obj ⊗ Z.obj))
    rw [boundary_inv_tensor χ F a X Y, comp_whiskerRight]
    simp only [Category.assoc]
    rw [Functor.LaxMonoidal.associativity]
    let ax : X.obj ⟶ F.obj X.obj := a.inv.app X
    let ay : Y.obj ⟶ F.obj Y.obj := a.inv.app Y
    change ((ax ⊗ₘ ay) ▷ F.obj Z.obj) ≫
        (α_ (F.obj X.obj) (F.obj Y.obj) (F.obj Z.obj)).hom ≫
        (F.obj X.obj ◁ Functor.LaxMonoidal.μ F Y.obj Z.obj) ≫
        Functor.LaxMonoidal.μ F X.obj (Y.obj ⊗ Z.obj) =
      (α_ X.obj Y.obj (F.obj Z.obj)).hom ≫
        (X.obj ◁ (ay ▷ F.obj Z.obj ≫ Functor.LaxMonoidal.μ F Y.obj Z.obj)) ≫
        (ax ▷ F.obj (Y.obj ⊗ Z.obj) ≫
          Functor.LaxMonoidal.μ F X.obj (Y.obj ⊗ Z.obj))
    have hn := associator_naturality ax ay (𝟙 (F.obj Z.obj))
    simp only [tensorHom_id] at hn
    rw [reassoc_of% hn]
    simp only [tensorHom_def', whiskerLeft_comp, Category.assoc]
    rw [← whisker_exchange_assoc]
  μₗ_unitality Y := by
    change (λ_ (F.obj Y.obj)).hom =
      (a.inv.app (𝟙_ (SignKernel.Positive χ)) ▷ F.obj Y.obj ≫
        Functor.LaxMonoidal.μ F (𝟙_ C) Y.obj) ≫ F.map (λ_ Y.obj).hom
    rw [boundary_inv_unit χ F a]
    simpa only [Category.assoc] using Functor.LaxMonoidal.left_unitality F Y.obj

instance homogeneousFunctor_lineator_isIso (X : SignKernel.Positive χ)
    (Y : HomogeneousCategory χ d) :
    IsIso (Functor.LaxLeftLinear.μₗ (homogeneousBoundaryFunctor χ F a d hF) X Y) := by
  haveI : IsIso ((ObjectProperty.ι (Homogeneous χ d)).map
      (Functor.LaxLeftLinear.μₗ (homogeneousBoundaryFunctor χ F a d hF) X Y)) := by
    change IsIso (a.inv.app X ▷ F.obj Y.obj ≫
      Functor.LaxMonoidal.μ F X.obj Y.obj)
    infer_instance
  exact isIso_of_reflects_iso _ (ObjectProperty.ι (Homogeneous χ d))

/-- All eight native module-functor coherence laws hold for the actual
restricted boundary-preserving autoequivalence. -/
instance homogeneousFunctor_leftLinear :
    (homogeneousBoundaryFunctor χ F a d hF).LeftLinear (SignKernel.Positive χ) :=
  ModuleFunctor.leftLinearOfLax (homogeneousBoundaryFunctor χ F a d hF)

/-- Reflection of the degree upgrades the actual restricted fully faithful
functor to an actual equivalence. -/
def homogeneousFunctor_essSurj
    (hreflect : ∀ X : C, Homogeneous χ d (F.obj X) → Homogeneous χ d X) :
    (homogeneousBoundaryFunctor χ F a d hF).EssSurj where
  mem_essImage X := by
    let Y := F.objPreimage X.obj
    let e := F.objObjPreimageIso X.obj
    have hY : Homogeneous χ d Y := hreflect Y (homogeneous_iso χ e X.property)
    refine ⟨⟨Y, hY⟩, ⟨ObjectProperty.isoMk (Homogeneous χ d) e⟩⟩

end Paper18.Category.FixedBoundary
