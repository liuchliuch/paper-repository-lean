import Paper18.Category.EquivariantInduction

/-!
# The monoidal equivariantization of a weak monoidal group action

Monoidality of the translating functors and of the weak-action natural
isomorphisms is used explicitly. The forgetful functor is strong monoidal.
-/

noncomputable section
open Classical CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
universe v u w
namespace Paper18.Category

section MonoidalNatural
variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  {F H : C ⥤ D} [F.Monoidal] [H.Monoidal] (τ : F ⟶ H) [NatTrans.IsMonoidal τ]

/-- A monoidal natural transformation commutes also with the inverse
unit comparisons of strong monoidal functors. -/
@[reassoc]
theorem monoidalNatTrans_eta : τ.app (𝟙_ C) ≫ η H = η F := by
  apply (cancel_epi (ε F)).mp
  simp [NatTrans.IsMonoidal.unit_assoc]

/-- A monoidal natural transformation commutes with the inverse tensor
comparisons of strong monoidal functors. -/
@[reassoc]
theorem monoidalNatTrans_delta (X Y : C) :
    τ.app (X ⊗ Y) ≫ δ H X Y = δ F X Y ≫ (τ.app X ⊗ₘ τ.app Y) := by
  apply (cancel_epi (μ F X Y)).mp
  simp [NatTrans.IsMonoidal.tensor_assoc]
end MonoidalNatural

namespace WeakAction
variable {G : Type w} [Group G] {C : Type u} [Category.{v} C] [MonoidalCategory C]
  (A : WeakAction G C) [∀ g : G, (A.ρ g).Monoidal]

/-- A weak action is monoidal when its unit and multiplication natural
isomorphisms are monoidal natural transformations. -/
class IsMonoidal : Prop where
  unit_monoidal : NatTrans.IsMonoidal A.unitIso.hom
  mul_monoidal : ∀ g h, NatTrans.IsMonoidal (A.mulIso g h).hom

attribute [instance] IsMonoidal.unit_monoidal IsMonoidal.mul_monoidal
variable [A.IsMonoidal]

namespace Equivariant

/-- Lift an actual object isomorphism whose forward map is equivariant. -/
def mkIso {X Y : A.Equivariant} (e : X.obj ≅ Y.obj)
    (h : ∀ g, (A.ρ g).map e.hom ≫ (Y.structureIso g).hom =
      (X.structureIso g).hom ≫ e.hom) : X ≅ Y where
  hom := ⟨e.hom, h⟩
  inv := ⟨e.inv, by
    intro g
    apply (cancel_mono e.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← h g, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp]⟩
  hom_inv_id := by apply Hom.ext; exact e.hom_inv_id
  inv_hom_id := by apply Hom.ext; exact e.inv_hom_id

/-- The actual tensor unit with its induced equivariant structure. -/
def tensorUnit : A.Equivariant where
  obj := 𝟙_ C
  structureIso g := (Functor.Monoidal.εIso (A.ρ g)).symm
  unit := by
    have h := monoidalNatTrans_eta A.unitIso.hom
    simpa using h.symm
  mul g h := by
    have e := monoidalNatTrans_eta (A.mulIso g h).hom
    simpa using e.symm

/-- The tensor product of actual equivariant objects. -/
def tensorObj (X Y : A.Equivariant) : A.Equivariant where
  obj := X.obj ⊗ Y.obj
  structureIso g := (Functor.Monoidal.μIso (A.ρ g) X.obj Y.obj).symm ≪≫
    (X.structureIso g ⊗ᵢ Y.structureIso g)
  unit := by
    have h := monoidalNatTrans_delta A.unitIso.hom X.obj Y.obj
    simpa [X.unit, Y.unit] using h.symm
  mul g h := by
    dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.Monoidal.μIso_inv, tensorIso_hom]
    rw [Functor.map_comp, Category.assoc, ← Functor.OplaxMonoidal.δ_natural_assoc,
      tensorHom_comp_tensorHom]
    rw [X.mul, Y.mul, ← tensorHom_comp_tensorHom]
    have e := monoidalNatTrans_delta (A.mulIso g h).hom X.obj Y.obj
    simpa only [Functor.OplaxMonoidal.comp_δ, Category.assoc] using
      (e =≫ ((X.structureIso (g * h)).hom ⊗ₘ (Y.structureIso (g * h)).hom)).symm

/-- Tensor product of actual equivariant morphisms. -/
def tensorHom {X X' Y Y' : A.Equivariant} (f : X ⟶ X') (h : Y ⟶ Y') :
    tensorObj A X Y ⟶ tensorObj A X' Y' where
  hom := f.hom ⊗ₘ h.hom
  comm g := by
    dsimp only [tensorObj, Iso.trans_hom, Iso.symm_hom, Functor.Monoidal.μIso_inv,
      tensorIso_hom]
    rw [← Functor.OplaxMonoidal.δ_natural_assoc, tensorHom_comp_tensorHom,
      f.comm, h.comm]
    simp only [Category.assoc, tensorHom_comp_tensorHom]

/-- The ambient associator is an actual equivariant isomorphism. -/
def associator (X Y Z : A.Equivariant) :
    tensorObj A (tensorObj A X Y) Z ≅ tensorObj A X (tensorObj A Y Z) :=
  mkIso A (α_ X.obj Y.obj Z.obj) (by
    intro g
    dsimp only [tensorObj, Iso.trans_hom, Iso.symm_hom, Functor.Monoidal.μIso_inv,
      tensorIso_hom]
    simp only [tensorHom_def, MonoidalCategory.whiskerLeft_comp,
      MonoidalCategory.comp_whiskerRight, Category.assoc]
    rw [← whisker_exchange_assoc, ← Functor.OplaxMonoidal.associativity_assoc]
    have ha := (associator_naturality (X.structureIso g).hom
      (Y.structureIso g).hom (Z.structureIso g).hom).symm
    simpa only [tensorHom_def, MonoidalCategory.comp_whiskerRight,
      MonoidalCategory.whiskerLeft_comp, Category.assoc] using
      (δ (A.ρ g) (X.obj ⊗ Y.obj) Z.obj ≫
        δ (A.ρ g) X.obj Y.obj ▷ (A.ρ g).obj Z.obj) ≫= ha)

/-- The ambient left unitor is equivariant. -/
def leftUnitor (X : A.Equivariant) : tensorObj A (tensorUnit A) X ≅ X :=
  mkIso A (λ_ X.obj) (by
    intro g
    dsimp only [tensorObj, tensorUnit, Iso.trans_hom, Iso.symm_hom,
      Functor.Monoidal.μIso_inv, Functor.Monoidal.εIso_inv, tensorIso_hom]
    rw [Category.assoc, Functor.OplaxMonoidal.δ_comp_η_tensorHom_assoc]
    simp)

/-- The ambient right unitor is equivariant. -/
def rightUnitor (X : A.Equivariant) : tensorObj A X (tensorUnit A) ≅ X :=
  mkIso A (ρ_ X.obj) (by
    intro g
    dsimp only [tensorObj, tensorUnit, Iso.trans_hom, Iso.symm_hom,
      Functor.Monoidal.μIso_inv, Functor.Monoidal.εIso_inv, tensorIso_hom]
    rw [Category.assoc, Functor.OplaxMonoidal.δ_comp_tensorHom_η_assoc]
    simp)

/-- Tensor operations and coherence isomorphisms on equivariant objects. -/
instance monoidalStruct : MonoidalCategoryStruct A.Equivariant where
  tensorObj := tensorObj A
  tensorHom := tensorHom A
  whiskerLeft X _ _ f := tensorHom A (𝟙 X) f
  whiskerRight f Y := tensorHom A f (𝟙 Y)
  tensorUnit := tensorUnit A
  associator := associator A
  leftUnitor := leftUnitor A
  rightUnitor := rightUnitor A

/-- The forgetful functor preserves all the actual tensor operations. -/
def inducingData : Monoidal.InducingFunctorData A.forget where
  μIso _ _ := Iso.refl _
  εIso := Iso.refl _
  whiskerLeft_eq := by
    intros
    simp [forget, monoidalStruct, tensorHom]
    erw [Category.id_comp]
  whiskerRight_eq := by
    intros
    simp [forget, monoidalStruct, tensorHom]
    erw [Category.id_comp]
  tensorHom_eq := by
    intros
    simp [forget, monoidalStruct, tensorHom]
    erw [Category.id_comp]
  associator_eq := by intros; simp [forget, monoidalStruct, associator, mkIso, tensorObj, Category.id_comp]
  leftUnitor_eq := by
    intros
    simp [forget, monoidalStruct, leftUnitor, mkIso, tensorUnit]
    erw [Category.id_comp]
  rightUnitor_eq := by
    intros
    simp [forget, monoidalStruct, rightUnitor, mkIso, tensorUnit]
    erw [Category.id_comp]

/-- All monoidal coherence laws follow under the faithful forgetful functor. -/
instance monoidalCategory : MonoidalCategory A.Equivariant :=
  Monoidal.induced A.forget (inducingData A)

end Equivariant

/-- The actual forgetful functor is strong monoidal. -/
instance forget_monoidal : A.forget.Monoidal :=
  Monoidal.fromInducedMonoidal A.forget (Equivariant.inducingData A)

@[simp] theorem forget_ε : ε A.forget = 𝟙 (𝟙_ C) := rfl
@[simp] theorem forget_η : η A.forget = 𝟙 (𝟙_ C) := rfl
@[simp] theorem forget_μ (X Y : A.Equivariant) : μ A.forget X Y = 𝟙 (X.obj ⊗ Y.obj) := rfl
@[simp] theorem forget_δ (X Y : A.Equivariant) : δ A.forget X Y = 𝟙 (X.obj ⊗ Y.obj) := rfl

section Linear
variable [Preadditive C] [Linear ℂ C]
  [∀ g : G, (A.ρ g).Additive] [∀ g : G, (A.ρ g).Linear ℂ]
  [MonoidalPreadditive C]

instance equivariant_monoidalPreadditive : MonoidalPreadditive A.Equivariant where
  whiskerLeft_zero := by
    intro X Y Z
    apply Equivariant.Hom.ext
    change (𝟙 X.obj ⊗ₘ (0 : Y.obj ⟶ Z.obj)) = 0
    simp
  zero_whiskerRight := by
    intro X Y Z
    apply Equivariant.Hom.ext
    change ((0 : Y.obj ⟶ Z.obj) ⊗ₘ 𝟙 X.obj) = 0
    simp
  whiskerLeft_add := by
    intro X Y Z f h
    apply Equivariant.Hom.ext
    change (𝟙 X.obj ⊗ₘ (f.hom + h.hom)) =
      (𝟙 X.obj ⊗ₘ f.hom) + (𝟙 X.obj ⊗ₘ h.hom)
    simp [MonoidalPreadditive.tensor_add]
  add_whiskerRight := by
    intro X Y Z f h
    apply Equivariant.Hom.ext
    change ((f.hom + h.hom) ⊗ₘ 𝟙 X.obj) =
      (f.hom ⊗ₘ 𝟙 X.obj) + (h.hom ⊗ₘ 𝟙 X.obj)
    simp

instance equivariant_monoidalLinear [MonoidalLinear ℂ C] :
    MonoidalLinear ℂ A.Equivariant :=
  CategoryTheory.monoidalLinearOfFaithful ℂ A.forget

end Linear
end WeakAction
end Paper18.Category
