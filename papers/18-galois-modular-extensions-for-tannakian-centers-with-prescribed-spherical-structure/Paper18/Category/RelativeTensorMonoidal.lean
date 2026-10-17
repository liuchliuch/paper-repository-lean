import Paper18.Category.RelativeTensorBimod
import Mathlib.CategoryTheory.Monoidal.Subcategory
import Mathlib.CategoryTheory.Monoidal.Transport

/-!
# The actual monoidal category of modules over a commutative algebra

The canonical bimodules form a monoidal full subcategory of the actual
bimodule category. Tensor closure follows from the balancing coequalizer.
An explicit equivalence transports this checked monoidal structure to the
actual mathlib category of left modules.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open CategoryTheory.BraidedCategory
open scoped MonObj
universe v u
namespace Paper18.Category.RelativeTensor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [HasCoequalizers C] {A : C} [MonObj A] [IsCommMonObj A]

local instance bimodBicategory : Bicategory (Mon C) := Bimod.monBicategory
local instance bimodMonoidal : MonoidalCategory (Bimod (Mon.mk A) (Mon.mk A)) :=
  inferInstanceAs (MonoidalCategory (EndMonoidal (Mon.mk A)))

/-- The full subcategory of bimodules whose actual right action is induced
by the braiding from their actual left action. -/
def Canonical : ObjectProperty (Bimod (Mon.mk A) (Mon.mk A)) :=
  fun M => M.actRight = (β_ M.X A).hom ≫ M.actLeft

omit [IsCommMonObj A] in
/-- Balancing identifies the right action on the tensor product with the
one induced from its left action. -/
theorem canonical_tensor (M N : Bimod (Mon.mk A) (Mon.mk A))
    (hM : Canonical M) (hN : Canonical N) : Canonical (M.tensorBimod N) := by
  change (M.tensorBimod N).actRight =
    (β_ (M.tensorBimod N).X A).hom ≫ (M.tensorBimod N).actLeft
  letI : Epi (coequalizer.π (M.actRight ▷ N.X)
    ((α_ M.X A N.X).hom ≫ (M.X ◁ N.actLeft)) ▷ A) :=
    inferInstanceAs (Epi ((tensorRight A).map (coequalizer.π (M.actRight ▷ N.X)
      ((α_ M.X A N.X).hom ≫ (M.X ◁ N.actLeft)))))
  apply (cancel_epi (coequalizer.π (M.actRight ▷ N.X)
    ((α_ M.X A N.X).hom ≫ (M.X ◁ N.actLeft)) ▷ A)).mp
  change coequalizer.π (M.actRight ▷ N.X)
    ((α_ M.X A N.X).hom ≫ (M.X ◁ N.actLeft)) ▷ A ≫ Bimod.TensorBimod.actRight M N =
      coequalizer.π (M.actRight ▷ N.X)
        ((α_ M.X A N.X).hom ≫ (M.X ◁ N.actLeft)) ▷ A ≫
          (β_ (Bimod.TensorBimod.X M N) A).hom ≫ Bimod.TensorBimod.actLeft M N
  rw [Bimod.TensorBimod.π_tensor_id_actRight M N]
  dsimp only [Bimod.TensorBimod.X]
  rw [braiding_naturality_left_assoc, Bimod.TensorBimod.whiskerLeft_π_actLeft M N,
    braiding_tensor_left_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight_assoc]
  change M.actRight = (β_ M.X A).hom ≫ M.actLeft at hM
  change N.actRight = (β_ N.X A).hom ≫ N.actLeft at hN
  rw [← hM, coequalizer.condition]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [hN, whiskerLeft_comp]
  simp only [Category.assoc]

instance canonical_isMonoidal : (Canonical (A := A)).IsMonoidal where
  prop_unit := by
    change μ[A] = (β_ A A).hom ≫ μ[A]
    exact (IsCommMonObj.mul_comm A).symm
  prop_tensor M N hM hN := canonical_tensor M N hM hN

/-- Lift an actual module to its canonical actual bimodule. -/
def canonicalLift : Mod_ C A ⥤ (Canonical (A := A)).FullSubcategory where
  obj M := ⟨toBimodObj M, rfl⟩
  map f := toBimod.map f

/-- Retain the actual left action of a canonical bimodule. -/
def canonicalForget : (Canonical (A := A)).FullSubcategory ⥤ Mod_ C A :=
  (Canonical (A := A)).ι ⋙ fromBimod

/-- Retaining the left action recovers the actual original module. -/
def canonicalUnitIso (M : Mod_ C A) : M ≅ canonicalForget.obj (canonicalLift.obj M) where
  hom := Mod_.Hom.mk' (𝟙 M.X) (by
    change γ[A,M.X] ≫ 𝟙 _ = (A ◁ 𝟙 _) ≫ γ[A,M.X]
    simp)
  inv := Mod_.Hom.mk' (𝟙 M.X) (by
    change γ[A,M.X] ≫ 𝟙 _ = (A ◁ 𝟙 _) ≫ γ[A,M.X]
    simp)
  hom_inv_id := by apply Mod_.Hom.ext; change 𝟙 _ ≫ 𝟙 _ = 𝟙 _; simp
  inv_hom_id := by apply Mod_.Hom.ext; change 𝟙 _ ≫ 𝟙 _ = 𝟙 _; simp

/-- A canonical bimodule is recovered from its actual left action. -/
def canonicalCounitIso (M : (Canonical (A := A)).FullSubcategory) :
    canonicalLift.obj (canonicalForget.obj M) ≅ M :=
  (Canonical (A := A)).isoMk (Bimod.isoOfIso (Iso.refl M.obj.X)
    (by change M.obj.actLeft ≫ 𝟙 _ = (A ◁ 𝟙 _) ≫ M.obj.actLeft; simp)
    (by
      change ((β_ M.obj.X A).hom ≫ M.obj.actLeft) ≫ 𝟙 _ =
        𝟙 _ ▷ A ≫ M.obj.actRight
      simpa only [Category.comp_id, id_whiskerRight, Category.id_comp] using M.property.symm))

/-- The canonical-bimodule lift and left-action forgetful functor give an
actual equivalence of categories. -/
def canonicalEquivalence : Mod_ C A ≌ (Canonical (A := A)).FullSubcategory where
  functor := canonicalLift
  inverse := canonicalForget
  unitIso := NatIso.ofComponents canonicalUnitIso (by
    intro M N f
    apply Mod_.Hom.ext
    change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
    simp)
  counitIso := NatIso.ofComponents canonicalCounitIso (by
    intro M N f
    apply Bimod.Hom.ext
    change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
    simp)
  functor_unitIso_comp M := by
    apply Bimod.Hom.ext
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    simp

/-- The actual relative-coequalizer monoidal structure on actual modules. -/
instance moduleMonoidal : MonoidalCategory (Mod_ C A) :=
  Monoidal.transport (canonicalEquivalence (A := A)).symm

/-- The transported tensor has exactly the previously constructed actual
relative coequalizer module as its value on objects. -/
@[simp]
theorem tensorObj_eq (M N : Mod_ C A) : M ⊗ N = tensorObj M N := rfl

/-- The unit module is the actual algebra acting on itself. -/
@[simp]
theorem tensorUnit_eq : (𝟙_ (Mod_ C A)) = Mod_.regular A := rfl

end Paper18.Category.RelativeTensor
