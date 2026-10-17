import Paper18.Category.ModuleFunctorFiniteInternalHomRightModulesBasic
import Mathlib.CategoryTheory.Monoidal.Mod_

/-! # Actual algebras of the right-tensor monad are actual right modules -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalOpposite
open scoped MonObj
universe v u
namespace Paper18.Category.ModuleInternalHom
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  (A : C) [MonObj A]

/-- An actual monad algebra supplies the actual native module action. -/
def rightMonadModule (B : Monad.Algebra (rightTensorMonad A)) :
    Mod_ Cᴹᵒᵖ (mop A) :=
  letI : ModObj (mop A) (mop B.A) :=
    { smul := B.a.mop
      one_smul' := by
        apply Quiver.Hom.unmop_inj
        change (B.A ◁ η[A]) ≫ B.a = (ρ_ B.A).hom
        apply (cancel_epi (ρ_ B.A).inv).mp
        simpa only [rightTensorMonad_unit, Category.assoc, Iso.inv_hom_id] using B.unit
      mul_smul' := by
        apply Quiver.Hom.unmop_inj
        change (B.A ◁ μ[A]) ≫ B.a =
          (α_ B.A A A).inv ≫ B.a ▷ A ≫ B.a
        apply (cancel_epi (α_ B.A A A).hom).mp
        simpa only [rightTensorMonad_mul, rightTensorMonad_map, Category.assoc,
          Iso.hom_inv_id_assoc] using B.assoc }
  ⟨mop B.A⟩

/-- The actual algebra morphisms are precisely actual native module maps. -/
def rightMonadToModules : Monad.Algebra (rightTensorMonad A) ⥤ Mod_ Cᴹᵒᵖ (mop A) where
  obj := rightMonadModule A
  map f := Mod_.Hom.mk' f.f.mop (by
    apply Quiver.Hom.unmop_inj
    change _ ≫ f.f = f.f ▷ A ≫ _
    exact f.h.symm)
  map_id B := by apply Mod_.Hom.ext; rfl
  map_comp f g := by apply Mod_.Hom.ext; rfl

/-- An actual native right module supplies an actual monad algebra. -/
def rightModuleMonadAlgebra (M : Mod_ Cᴹᵒᵖ (mop A)) :
    Monad.Algebra (rightTensorMonad A) where
  A := M.X.unmop
  a := γ[mop A,M.X].unmop
  unit := by
    have h := congrArg Quiver.Hom.unmop (ModObj.one_smul (M := mop A) M.X)
    change (M.X.unmop ◁ η[A]) ≫ γ[mop A,M.X].unmop = (ρ_ M.X.unmop).hom at h
    rw [rightTensorMonad_unit, Category.assoc, h, Iso.inv_hom_id]
    rfl
  assoc := by
    have h := congrArg Quiver.Hom.unmop (ModObj.mul_smul (M := mop A) M.X)
    change (M.X.unmop ◁ μ[A]) ≫ γ[mop A,M.X].unmop =
      (α_ M.X.unmop A A).inv ≫ γ[mop A,M.X].unmop ▷ A ≫ γ[mop A,M.X].unmop at h
    rw [rightTensorMonad_mul, rightTensorMonad_map, Category.assoc, h,
      Iso.hom_inv_id_assoc]

/-- Actual module morphisms become actual monad algebra morphisms. -/
def rightModulesToMonad : Mod_ Cᴹᵒᵖ (mop A) ⥤ Monad.Algebra (rightTensorMonad A) where
  obj := rightModuleMonadAlgebra A
  map f :=
    { f := f.hom.unmop
      h := by
        have h := congrArg Quiver.Hom.unmop (IsMod_Hom.smul_hom (A := mop A) (f := f.hom))
        exact h.symm }
  map_id M := by apply Monad.Algebra.Hom.ext; rfl
  map_comp f g := by apply Monad.Algebra.Hom.ext; rfl

/-- The genuine right-tensor monad algebra category is equivalent to
native internal left modules in the monoidal opposite. -/
def rightMonadModuleEquivalence :
    Monad.Algebra (rightTensorMonad A) ≌ Mod_ Cᴹᵒᵖ (mop A) where
  functor := rightMonadToModules A
  inverse := rightModulesToMonad A
  unitIso := NatIso.ofComponents
    (fun B => Monad.Algebra.isoMk (Iso.refl _) (by
      change (𝟙 B.A) ▷ A ≫ B.a = B.a ≫ 𝟙 B.A
      simp))
    (fun f => by apply Monad.Algebra.Hom.ext; change f.f ≫ 𝟙 _ = 𝟙 _ ≫ f.f; simp)
  counitIso := NatIso.ofComponents
    (fun M =>
      { hom := Mod_.Hom.mk' (𝟙 M.X) (by
          change γ[mop A,M.X] ≫ 𝟙 M.X = (mop A ◁ 𝟙 M.X) ≫ γ[mop A,M.X]
          simp)
        inv := Mod_.Hom.mk' (𝟙 M.X) (by
          change γ[mop A,M.X] ≫ 𝟙 M.X = (mop A ◁ 𝟙 M.X) ≫ γ[mop A,M.X]
          simp)
        hom_inv_id := by apply Mod_.Hom.ext; change 𝟙 M.X ≫ 𝟙 M.X = 𝟙 M.X; simp
        inv_hom_id := by apply Mod_.Hom.ext; change 𝟙 M.X ≫ 𝟙 M.X = 𝟙 M.X; simp })
    (fun f => by apply Mod_.Hom.ext; change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom; simp)
  functor_unitIso_comp B := by
    apply Mod_.Hom.ext
    change (𝟙 (mop B.A)) ≫ 𝟙 (mop B.A) = 𝟙 (mop B.A)
    simp

end Paper18.Category.ModuleInternalHom
