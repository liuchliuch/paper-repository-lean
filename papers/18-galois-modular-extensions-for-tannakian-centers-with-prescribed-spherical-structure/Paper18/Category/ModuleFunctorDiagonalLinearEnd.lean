import Paper18.Category.ModuleFunctorDiagonalActionBasic
import Mathlib.CategoryTheory.Monoidal.Transport

/-! # Additive complex-linear endofunctors with ordinary transformations -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u
namespace Paper18.Category.ModuleFunctor.DiagonalAction
namespace LinearEnd
variable (D : Type u) [Category.{v} D] [Preadditive D] [Linear ℂ D]

/-- The restriction to additive linear objects makes composition bilinear. -/
structure Object where
  toFunctor : D ⥤ D
  additive : toFunctor.Additive
  linear : toFunctor.Linear ℂ
attribute [instance] Object.additive Object.linear

def Cat := InducedCategory (D ⥤ D) (fun F : Object D => F.toFunctor)
instance : Category (Cat D) := inferInstanceAs
  (Category (InducedCategory (D ⥤ D) (fun F : Object D => F.toFunctor)))
instance : Preadditive (Cat D) := inferInstanceAs
  (Preadditive (InducedCategory (D ⥤ D) (fun F : Object D => F.toFunctor)))
instance : Linear ℂ (Cat D) := inferInstanceAs
  (Linear ℂ (InducedCategory (D ⥤ D) (fun F : Object D => F.toFunctor)))

variable {D}
def underlying (F : Cat D) : Object D := F
abbrev toFunctor (F : Cat D) : D ⥤ D := (underlying F).toFunctor
instance (F : Cat D) : (toFunctor F).Additive := (underlying F).additive
instance (F : Cat D) : (toFunctor F).Linear ℂ := (underlying F).linear
def ofFunctor (F : D ⥤ D) [F.Additive] [F.Linear ℂ] : Cat D :=
  ({ toFunctor := F, additive := inferInstance, linear := inferInstance } : Object D)
def forget : Cat D ⥤ (D ⥤ D) := inducedFunctor _
instance : (forget (D := D)).Faithful :=
  (fullyFaithfulInducedFunctor (fun F : Object D => F.toFunctor)).faithful
instance : (forget (D := D)).Full :=
  (fullyFaithfulInducedFunctor (fun F : Object D => F.toFunctor)).full

@[ext] lemma hom_ext {F G : Cat D} (f g : F ⟶ G)
    (h : ∀ d, (forget.map f).app d = (forget.map g).app d) : f = g := by
  apply forget.map_injective
  exact NatTrans.ext (funext h)

def tensor (F G : Cat D) : Cat D := ofFunctor (toFunctor F ⋙ toFunctor G)
def unit : Cat D := ofFunctor (𝟭 D)

instance monoidalStruct : MonoidalCategoryStruct (Cat D) where
  tensorObj := tensor
  tensorUnit := unit
  whiskerLeft F {_ _} τ := Functor.whiskerLeft (toFunctor F) τ
  whiskerRight τ F := Functor.whiskerRight τ (toFunctor F)
  tensorHom τ σ := τ ◫ σ
  associator F G H := InducedCategory.isoMk
    (Functor.associator (toFunctor F) (toFunctor G) (toFunctor H))
  leftUnitor F := InducedCategory.isoMk (Functor.leftUnitor (toFunctor F))
  rightUnitor F := InducedCategory.isoMk (Functor.rightUnitor (toFunctor F))

attribute [local instance] CategoryTheory.endofunctorMonoidalCategory

def inducingData : Monoidal.InducingFunctorData (forget (D := D)) where
  μIso _ _ := Iso.refl _
  εIso := Iso.refl _
  whiskerLeft_eq F {G H} τ := by
    change Functor.whiskerLeft (toFunctor F) τ =
      𝟙 _ ≫ Functor.whiskerLeft (toFunctor F) τ ≫ 𝟙 _
    simp only [id_comp, comp_id]
  whiskerRight_eq {F G} τ H := by
    change Functor.whiskerRight τ (toFunctor H) =
      𝟙 _ ≫ Functor.whiskerRight τ (toFunctor H) ≫ 𝟙 _
    simp only [id_comp, comp_id]
  tensorHom_eq {_ _ _ _} τ σ := by
    change (τ ◫ σ) = 𝟙 _ ≫ (τ ◫ σ) ≫ 𝟙 _
    simp only [id_comp, comp_id]
  associator_eq F G H := by
    ext d
    dsimp [forget, monoidalStruct, InducedCategory.isoMk, tensor, unit,
      ofFunctor, toFunctor, underlying]
    simp
  leftUnitor_eq F := by
    ext d
    dsimp [forget, monoidalStruct, InducedCategory.isoMk, tensor, unit,
      ofFunctor, toFunctor, underlying]
    simp
  rightUnitor_eq F := by
    ext d
    dsimp [forget, monoidalStruct, InducedCategory.isoMk, tensor, unit,
      ofFunctor, toFunctor, underlying]
    simp

instance monoidal : MonoidalCategory (Cat D) :=
  Monoidal.induced (forget (D := D)) inducingData
instance forgetMonoidal : (forget (D := D)).Monoidal :=
  Monoidal.fromInducedMonoidal (forget (D := D)) inducingData

@[simp] lemma forget_whiskerLeft (F : Cat D) {G H : Cat D} (τ : G ⟶ H) :
    forget.map (F ◁ τ) = Functor.whiskerLeft (toFunctor F) (forget.map τ) := rfl
@[simp] lemma forget_whiskerRight {F G : Cat D} (τ : F ⟶ G) (H : Cat D) :
    forget.map (τ ▷ H) = Functor.whiskerRight (forget.map τ) (toFunctor H) := rfl
@[simp] lemma forget_associator_hom (F G H : Cat D) :
    forget.map (α_ F G H).hom =
      (Functor.associator (toFunctor F) (toFunctor G) (toFunctor H)).hom := rfl
@[simp] lemma forget_associator_inv (F G H : Cat D) :
    forget.map (α_ F G H).inv =
      (Functor.associator (toFunctor F) (toFunctor G) (toFunctor H)).inv := rfl
@[simp] lemma forget_leftUnitor (F : Cat D) :
    forget.map (λ_ F).hom = (Functor.leftUnitor (toFunctor F)).hom := rfl
@[simp] lemma forget_rightUnitor (F : Cat D) :
    forget.map (ρ_ F).hom = (Functor.rightUnitor (toFunctor F)).hom := rfl

instance monoidalPreadditive : MonoidalPreadditive (Cat D) where
  whiskerLeft_zero := by
    intros
    apply (forget (D := D)).map_injective
    ext d
    rfl
  zero_whiskerRight := by
    intro F G H
    apply (forget (D := D)).map_injective
    ext d
    exact (toFunctor F).map_zero _ _
  whiskerLeft_add := by
    intros
    apply (forget (D := D)).map_injective
    ext d
    rfl
  add_whiskerRight := by
    intro F G H τ σ
    apply (forget (D := D)).map_injective
    ext d
    exact (toFunctor F).map_add

instance monoidalLinear : MonoidalLinear ℂ (Cat D) where
  whiskerLeft_smul := by
    intros
    apply (forget (D := D)).map_injective
    ext d
    rfl
  smul_whiskerRight := by
    intro r F G τ H
    apply (forget (D := D)).map_injective
    ext d
    exact (toFunctor H).map_smul _ _

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
variable [HasFiniteBiproducts D]

def sumUnderlying {I : Type} [Fintype I] (F : I → Cat D) : D ⥤ D :=
  ⨁ fun i => toFunctor (F i)

lemma sum_hom_ext {I : Type} [Fintype I] (F : I → Cat D) (d : D) {X : D}
    (f g : X ⟶ (sumUnderlying F).obj d)
    (h : ∀ i, f ≫ (biproduct.π (fun i => toFunctor (F i)) i).app d =
      g ≫ (biproduct.π (fun i => toFunctor (F i)) i).app d) : f = g := by
  have ht : (∑ i, (biproduct.π (fun i => toFunctor (F i)) i).app d ≫
      (biproduct.ι (fun i => toFunctor (F i)) i).app d) =
        𝟙 ((sumUnderlying F).obj d) := by
    simpa only [NatTrans.app_sum, NatTrans.comp_app, NatTrans.id_app] using
      congrArg (fun a : sumUnderlying F ⟶ sumUnderlying F => a.app d)
        (biproduct.total (f := fun i : I => toFunctor (F i)))
  calc
    f = ∑ i, (f ≫ (biproduct.π (fun i => toFunctor (F i)) i).app d) ≫
      (biproduct.ι (fun i => toFunctor (F i)) i).app d := by
        simp only [assoc]
        rw [← Preadditive.comp_sum, ht, comp_id]
    _ = ∑ i, (g ≫ (biproduct.π (fun i => toFunctor (F i)) i).app d) ≫
      (biproduct.ι (fun i => toFunctor (F i)) i).app d := by simp_rw [h]
    _ = g := by
      simp only [assoc]
      rw [← Preadditive.comp_sum, ht, comp_id]

instance sum_additive {I : Type} [Fintype I] (F : I → Cat D) :
    (sumUnderlying F).Additive where
  map_add {d e} f g := by
    apply sum_hom_ext F e
    intro i
    change (sumUnderlying F).map (f + g) ≫ _ =
      ((sumUnderlying F).map f + (sumUnderlying F).map g) ≫ _
    simp only [sumUnderlying, (biproduct.π (fun i => toFunctor (F i)) i).naturality,
      Preadditive.add_comp]
    erw [(toFunctor (F i)).map_add]
    exact Preadditive.comp_add _ _ _ _ _ _

instance sum_linear {I : Type} [Fintype I] (F : I → Cat D) :
    (sumUnderlying F).Linear ℂ where
  map_smul {d e} f z := by
    apply sum_hom_ext F e
    intro i
    change (sumUnderlying F).map (z • f) ≫ _ = (z • (sumUnderlying F).map f) ≫ _
    simp only [sumUnderlying, (biproduct.π (fun i => toFunctor (F i)) i).naturality,
      Linear.smul_comp]
    erw [(toFunctor (F i)).map_smul]
    exact Linear.comp_smul _ _ _ _ _ _

def sumBicone {I : Type} [Fintype I] (F : I → Cat D) : Bicone F where
  pt := ofFunctor (sumUnderlying F)
  π i := biproduct.π (fun j => toFunctor (F j)) i
  ι i := biproduct.ι (fun j => toFunctor (F j)) i
  ι_π i j := by
    by_cases h : i = j
    · subst j
      simp only [dif_pos rfl, eqToHom_refl]
      change biproduct.ι (fun j => toFunctor (F j)) i ≫
        biproduct.π (fun j => toFunctor (F j)) i = 𝟙 (toFunctor (F i))
      exact biproduct.ι_π_self _ _
    · simpa only [dif_neg h] using (biproduct.ι_π_ne (fun k => toFunctor (F k)) h)

instance hasFiniteBiproducts : HasFiniteBiproducts (Cat D) where
  out n := ⟨fun F => hasBiproduct_of_total (sumBicone F) (by
    exact biproduct.total (f := fun i => toFunctor (F i)))⟩

end LinearEnd
end Paper18.Category.ModuleFunctor.DiagonalAction
