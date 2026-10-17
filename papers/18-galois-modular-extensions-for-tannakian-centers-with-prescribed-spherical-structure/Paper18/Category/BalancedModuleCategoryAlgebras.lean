import Paper18.Category.BalancedModuleCategoryAdjunction

/-! # Native bimodules are the actual algebras of the constructed monad -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u
namespace Paper18.Category.BalancedModuleCategory
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  {A B : D} [MonObj A] [MonObj B]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

def toAlgebraObj (P : BimoduleRelativeTensor.Native A B) :
    Monad.Algebra (outerMonad (A := A) (B := B)) where
  A := P.X
  a := γ[mop B,P.X]
  unit := by
    apply Mod_.Hom.ext
    simp only [Mod_.comp_hom', outerMonad_unit_hom, Mod_.id_hom']
    have hu := congrArg Mod_.Hom.hom (ModObj.one_smul (M := mop B) P.X)
    change P.X.X ◁ η[B] ≫ γ[mop B,P.X].hom = (ρ_ P.X.X).hom at hu
    rw [assoc, hu, Iso.inv_hom_id]
    rfl
  assoc := by
    apply Mod_.Hom.ext
    simp only [Mod_.comp_hom', outerMonad_multiplication_hom]
    change ((α_ P.X.X B B).hom ≫ P.X.X ◁ μ[B]) ≫ γ[mop B,P.X].hom =
      γ[mop B,P.X].hom ▷ B ≫ γ[mop B,P.X].hom
    have hm := congrArg Mod_.Hom.hom (ModObj.mul_smul (M := mop B) P.X)
    change P.X.X ◁ μ[B] ≫ γ[mop B,P.X].hom =
      (α_ P.X.X B B).inv ≫ γ[mop B,P.X].hom ▷ B ≫ γ[mop B,P.X].hom at hm
    rw [assoc, hm, Iso.hom_inv_id_assoc]

/-- The forward comparison uses the genuine native right action. -/
def toAlgebras : BimoduleRelativeTensor.Native A B ⥤ Monad.Algebra (outerMonad (A := A) (B := B)) where
  obj := toAlgebraObj
  map f := ⟨f.hom, f.isMod_Hom.smul_hom.symm⟩

def algebraModObj (P : Monad.Algebra (outerMonad (A := A) (B := B))) : ModObj (mop B) P.A where
  smul := P.a
  one_smul' := by
    apply Mod_.Hom.ext
    change P.A.X ◁ η[B] ≫ P.a.hom = (ρ_ P.A.X).hom
    have h := congrArg Mod_.Hom.hom P.unit
    simp only [Mod_.comp_hom', outerMonad_unit_hom, Mod_.id_hom'] at h
    apply (cancel_epi (ρ_ P.A.X).inv).mp
    simpa only [assoc, Iso.inv_hom_id] using h
  mul_smul' := by
    apply Mod_.Hom.ext
    change P.A.X ◁ μ[B] ≫ P.a.hom =
      (α_ P.A.X B B).inv ≫ P.a.hom ▷ B ≫ P.a.hom
    have h := congrArg Mod_.Hom.hom P.assoc
    simp only [Mod_.comp_hom', outerMonad_multiplication_hom] at h
    apply (cancel_epi (α_ P.A.X B B).hom).mp
    simpa only [assoc, Iso.hom_inv_id_assoc] using h

def fromAlgebraObj (P : Monad.Algebra (outerMonad (A := A) (B := B))) :
    BimoduleRelativeTensor.Native A B :=
  letI := algebraModObj P
  ⟨P.A⟩

/-- The algebra action is installed as the genuine second native module
action; its module laws have just been derived from the actual monad laws. -/
def fromAlgebras : Monad.Algebra (outerMonad (A := A) (B := B)) ⥤ BimoduleRelativeTensor.Native A B where
  obj := fromAlgebraObj
  map f := Mod_.Hom.mk' f.f f.h.symm

def nativeAlgebraRoundtripIso (P : BimoduleRelativeTensor.Native A B) :
    fromAlgebraObj (toAlgebraObj P) ≅ P := Iso.refl P

def algebraNativeRoundtripIso (P : Monad.Algebra (outerMonad (A := A) (B := B))) :
    toAlgebraObj (fromAlgebraObj P) ≅ P := Iso.refl P

/-- The native model is proved equivalent to the actual Eilenberg-Moore
category. This equivalence is an output, not a universal-product premise. -/
def nativeAlgebraEquivalence : BimoduleRelativeTensor.Native A B ≌
    Monad.Algebra (outerMonad (A := A) (B := B)) :=
  CategoryTheory.Equivalence.mk toAlgebras fromAlgebras
    (NatIso.ofComponents (fun P => (nativeAlgebraRoundtripIso P).symm)
      (fun f => by
        apply Mod_.Hom.ext
        change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
        rw [comp_id, id_comp]))
    (NatIso.ofComponents algebraNativeRoundtripIso
      (fun f => by
        apply Monad.Algebra.Hom.ext
        change f.f ≫ 𝟙 _ = 𝟙 _ ≫ f.f
        rw [comp_id, id_comp]))

end Paper18.Category.BalancedModuleCategory
