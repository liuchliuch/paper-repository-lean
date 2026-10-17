import Paper18.Category.SphericalizationFunctorCoherence
import Paper18.Category.SphericalizationLinear

/-! # The actual braided tensor lift to sphericalization -/
noncomputable section
universe v u v₁ u₁
namespace Paper18.Category
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [BraidedCategory C]
  {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [RightRigidCategory D]
  [BraidedCategory D] (F : C ⥤ D) [F.Braided]

namespace Sphericalized

/-- A braided tensor functor sends an actual Radford square root to its
image, using the canonical comparison with the chosen double dual. -/
def mapObj (X : Sphericalized C) : Sphericalized D :=
  ⟨⟨F.obj X.obj.obj, F.mapIso X.obj.phi ≪≫ doubleDualComparison F X.obj.obj⟩, by
    change (F.map X.obj.phi.hom ≫ (doubleDualComparison F X.obj.obj).hom) ≫
      (doubleDualFunctor D).map
        (F.map X.obj.phi.hom ≫ (doubleDualComparison F X.obj.obj).hom) = _
    rw [Functor.map_comp, assoc]
    rw [← reassoc_of% (doubleDualComparison_naturality F X.obj.phi.hom)]
    rw [← assoc, ← F.map_comp, X.property]
    exact doubleDualComparison_radford F X.obj.obj⟩

/-- The lift acts on genuine commuting morphisms by the original functor. -/
def mapFunctor : Sphericalized C ⥤ Sphericalized D where
  obj := mapObj F
  map {X Y} f := ⟨F.map f.hom, by
    change F.map f.hom ≫ (F.map Y.obj.phi.hom ≫ _) =
      (F.map X.obj.phi.hom ≫ _) ≫ (doubleDualFunctor D).map (F.map f.hom)
    rw [← assoc, ← F.map_comp, f.comm, F.map_comp, assoc,
      doubleDualComparison_naturality, assoc]⟩
  map_id X := Pivotalized.Hom.ext (F.map_id X.obj.obj)
  map_comp f g := Pivotalized.Hom.ext (F.map_comp f.hom g.hom)

instance map_faithful [F.Faithful] : (mapFunctor F).Faithful where
  map_injective h := Pivotalized.Hom.ext (F.map_injective (congrArg Pivotalized.Hom.hom h))

instance map_full [F.Full] [F.Faithful] : (mapFunctor F).Full where
  map_surjective {X Y} f := by
    refine ⟨⟨F.preimage f.hom, ?_⟩, Pivotalized.Hom.ext (F.map_preimage f.hom)⟩
    apply F.map_injective
    apply (cancel_mono (doubleDualComparison F Y.obj.obj).hom).mp
    rw [F.map_comp, F.map_comp, assoc, assoc,
      doubleDualComparison_naturality, F.map_preimage]
    simpa only [mapFunctor, mapObj, Iso.trans_hom, Functor.mapIso_hom, assoc] using f.comm

/-- The actual unit comparison is the original functor's unit comparison. -/
def mapUnitIso : 𝟙_ (Sphericalized D) ≅ (mapFunctor F).obj (𝟙_ (Sphericalized C)) :=
  radfordSquareProperty.isoMk (Pivotalized.mkIso (εIso F) (by
    change ε F ≫ (F.map (ε (doubleDualFunctor C)) ≫
      (doubleDualComparison F (𝟙_ C)).hom) =
        ε (doubleDualFunctor D) ≫ (doubleDualFunctor D).map (ε F)
    simpa only [Functor.LaxMonoidal.comp_ε, assoc] using doubleDualComparison_unit F))

/-- The actual tensor comparison is the original functor's tensor comparison;
commutation with the square roots follows from canonical dual coherence. -/
def mapTensorIso (X Y : Sphericalized C) :
    (mapFunctor F).obj X ⊗ (mapFunctor F).obj Y ≅ (mapFunctor F).obj (X ⊗ Y) :=
  radfordSquareProperty.isoMk (Pivotalized.mkIso (μIso F X.obj.obj Y.obj.obj) (by
    change μ F X.obj.obj Y.obj.obj ≫
      (F.map ((X.obj.phi.hom ⊗ₘ Y.obj.phi.hom) ≫
        μ (doubleDualFunctor C) X.obj.obj Y.obj.obj) ≫
          (doubleDualComparison F (X.obj.obj ⊗ Y.obj.obj)).hom) =
      (((F.map X.obj.phi.hom ≫ (doubleDualComparison F X.obj.obj).hom) ⊗ₘ
        (F.map Y.obj.phi.hom ≫ (doubleDualComparison F Y.obj.obj).hom)) ≫
          μ (doubleDualFunctor D) (F.obj X.obj.obj) (F.obj Y.obj.obj)) ≫
            (doubleDualFunctor D).map (μ F X.obj.obj Y.obj.obj)
    rw [F.map_comp, ← assoc, ← assoc, ← μ_natural,
      assoc, assoc]
    have hc := doubleDualComparison_tensor F X.obj.obj Y.obj.obj
    simp only [Functor.LaxMonoidal.comp_μ, assoc] at hc
    rw [hc]
    simp only [tensorHom_comp_tensorHom_assoc, assoc]))

/-- Tensor coherence is exactly the original functor's ambient coherence. -/
def mapCoreMonoidal : (mapFunctor F).CoreMonoidal where
  εIso := mapUnitIso F
  μIso := mapTensorIso F
  μIso_hom_natural_left f Y := by
    apply Pivotalized.Hom.ext
    change (F.map f.hom ⊗ₘ 𝟙 _) ≫ μ F _ _ = μ F _ _ ≫ F.map (f.hom ⊗ₘ 𝟙 _)
    simpa only [tensorHom_id] using μ_natural_left F f.hom Y.obj.obj
  μIso_hom_natural_right X f := by
    apply Pivotalized.Hom.ext
    change (𝟙 _ ⊗ₘ F.map f.hom) ≫ μ F _ _ = μ F _ _ ≫ F.map (𝟙 _ ⊗ₘ f.hom)
    simpa only [id_tensorHom] using μ_natural_right F X.obj.obj f.hom
  associativity X Y Z := by
    apply Pivotalized.Hom.ext
    change (μ F _ _ ⊗ₘ 𝟙 _) ≫ μ F _ _ ≫ F.map (α_ _ _ _).hom =
      (α_ _ _ _).hom ≫ (𝟙 _ ⊗ₘ μ F _ _) ≫ μ F _ _
    simpa only [tensorHom_id, id_tensorHom] using
      Functor.LaxMonoidal.associativity F X.obj.obj Y.obj.obj Z.obj.obj
  left_unitality X := by
    apply Pivotalized.Hom.ext
    change (λ_ _).hom = (ε F ⊗ₘ 𝟙 _) ≫ μ F _ _ ≫ F.map (λ_ _).hom
    simpa only [tensorHom_id] using Functor.LaxMonoidal.left_unitality F X.obj.obj
  right_unitality X := by
    apply Pivotalized.Hom.ext
    change (ρ_ _).hom = (𝟙 _ ⊗ₘ ε F) ≫ μ F _ _ ≫ F.map (ρ_ _).hom
    simpa only [id_tensorHom] using Functor.LaxMonoidal.right_unitality F X.obj.obj

instance map_monoidal : (mapFunctor F).Monoidal := (mapCoreMonoidal F).toMonoidal

instance map_braided : (mapFunctor F).Braided where
  braided X Y := by
    apply Pivotalized.Hom.ext
    exact Functor.LaxBraided.braided (F := F) X.obj.obj Y.obj.obj

/-- The canonical dual comparison of the lifted tensor functor has exactly
the underlying canonical comparison of the original tensor functor. -/
lemma map_dualComparison_hom (X : Sphericalized C) :
    (forget (C := D)).map (dualComparison (mapFunctor F) X).hom =
      (dualComparison F X.obj.obj).hom := by
  apply pairing_hom_ext
    (inferInstanceAs (ExactPairing (F.obj X.obj.obj) (dual D (F.obj X.obj.obj))))
  have hc := dualComparison_evaluation (mapFunctor F) X
  have hh := congrArg (fun t => (forget (C := D)).map t) hc
  change (((forget (C := D)).map (dualComparison (mapFunctor F) X).hom) ⊗ₘ
      𝟙 (F.obj X.obj.obj)) ≫ ε_ (F.obj X.obj.obj) (dual D (F.obj X.obj.obj)) =
    μ F (dual C X.obj.obj) X.obj.obj ≫
      F.map (ε_ X.obj.obj (dual C X.obj.obj)) ≫ η F at hh
  rw [dualComparison_evaluation]
  simpa only [tensorHom_id] using hh

lemma map_dualComparison_inv (X : Sphericalized C) :
    (forget (C := D)).map (dualComparison (mapFunctor F) X).inv =
      (dualComparison F X.obj.obj).inv := by
  have hi : (forget (C := D)).mapIso (dualComparison (mapFunctor F) X) =
      dualComparison F X.obj.obj := Iso.ext (map_dualComparison_hom F X)
  exact congrArg Iso.inv hi

lemma map_doubleDualComparison_hom (X : Sphericalized C) :
    (forget (C := D)).map (doubleDualComparison (mapFunctor F) X).hom =
      (doubleDualComparison F X.obj.obj).hom := by
  dsimp only [doubleDualComparison, Iso.trans_hom, Iso.symm_hom, dualMapIso]
  rw [Functor.map_comp, map_dualComparison_hom]
  have hd : (forget (C := D)).map
      (dualMap (Sphericalized D) (dualComparison (mapFunctor F) X).inv) =
        dualMap D ((forget (C := D)).map (dualComparison (mapFunctor F) X).inv) :=
    Pivotalized.dualMap_hom _
  rw [hd, map_dualComparison_inv]
  rfl

/-- The lifted functor preserves the actual spherical pivotal structures
through the canonical chosen-dual comparison. -/
theorem map_preservesPivotal : PreservesPivotal (mapFunctor F)
    (pivotalStructure (C := C)) (pivotalStructure (C := D)) := by
  intro X
  apply (forget (C := D)).map_injective
  rw [Functor.map_comp, map_doubleDualComparison_hom]
  rfl

/-- The lifted construction has the expected actual underlying functor. -/
lemma map_comp_forget : mapFunctor F ⋙ forget = forget ⋙ F := rfl

/-- Actual right traces are preserved by the sphericalization lift. -/
lemma map_rightTrace {X : Sphericalized C} (f : X ⟶ X) :
    ε (mapFunctor F) ≫ (mapFunctor F).map (pivotalStructure.rightTrace f) ≫
      η (mapFunctor F) = pivotalStructure.rightTrace ((mapFunctor F).map f) :=
  (map_preservesPivotal F).rightTrace f

/-- Actual left traces are preserved by the same canonical pivotal equation. -/
lemma map_leftTrace {X : Sphericalized C} (f : X ⟶ X) :
    ε (mapFunctor F) ≫ (mapFunctor F).map (pivotalStructure.leftTrace f) ≫
      η (mapFunctor F) = pivotalStructure.leftTrace ((mapFunctor F).map f) :=
  (map_preservesPivotal F).leftTrace f

section Linear
variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]

instance map_additive [F.Additive] : (mapFunctor F).Additive where
  map_add := Pivotalized.Hom.ext F.map_add

instance map_linear [F.Linear ℂ] : (mapFunctor F).Linear ℂ where
  map_smul f c := Pivotalized.Hom.ext (F.map_smul c f.hom)

end Linear

end Sphericalized
end Paper18.Category
