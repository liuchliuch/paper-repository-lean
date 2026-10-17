import Paper18.Category.ModuleFunctorSemisimpleBimodules
import Mathlib.CategoryTheory.Monoidal.Bimod

/-! # Actual bimodules and iterated native modules

The two descriptions carry exactly the same two commuting actions. This
bridge permits the actual relative tensor product and its proved bicategory
coherence to be used with native iterated internal modules.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u
namespace Paper18.Category.BimoduleRelativeTensor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  (R S : D) [MonObj R] [MonObj S]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

/-- An actual left R, right S bimodule as two native commuting actions. -/
abbrev Native := Mod_ (Mod_ D R) (mop S)

/-- The actual two-sided action data extracted from native iterated modules. -/
def toBimodObj (M : Native R S) : Bimod (Mon.mk R) (Mon.mk S) where
  X := M.X.X
  actLeft := γ[R,M.X.X]
  one_actLeft := ModObj.one_smul (M := R) M.X.X
  left_assoc := ModObj.mul_smul (M := R) M.X.X
  actRight := γ[mop S,M.X].hom
  actRight_one := by
    have h := congrArg Mod_.Hom.hom (ModObj.one_smul (M := mop S) M.X)
    exact h
  right_assoc := by
    have h := congrArg Mod_.Hom.hom (ModObj.mul_smul (M := mop S) M.X)
    exact h
  middle_assoc := by
    have h : ((α_ R M.X.X S).inv ≫ γ[R,M.X.X] ▷ S) ≫ γ[mop S,M.X].hom =
      R ◁ γ[mop S,M.X].hom ≫ γ[R,M.X.X] :=
      (γ[mop S,M.X]).isMod_Hom.smul_hom
    apply (cancel_epi (α_ R M.X.X S).inv).mp
    simpa only [assoc, Iso.inv_hom_id_assoc] using h

/-- The actual functor from native iterated modules to two-sided actions. -/
def toBimod : Native R S ⥤ Bimod (Mon.mk R) (Mon.mk S) where
  obj := toBimodObj R S
  map f :=
    { hom := f.hom.hom
      left_act_hom := f.hom.isMod_Hom.smul_hom
      right_act_hom := congrArg Mod_.Hom.hom f.isMod_Hom.smul_hom }
  map_id _ := by apply Bimod.hom_ext; rfl
  map_comp _ _ := by apply Bimod.hom_ext; rfl

/-- The actual left action underlying a two-sided bimodule. -/
def leftModObj (P : Bimod (Mon.mk R) (Mon.mk S)) : ModObj R P.X where
  smul := P.actLeft
  one_smul' := P.one_actLeft
  mul_smul' := P.left_assoc

/-- The actual native left module underlying a two-sided bimodule. -/
def leftModule (P : Bimod (Mon.mk R) (Mon.mk S)) : Mod_ D R :=
  letI := leftModObj R S P
  ⟨P.X⟩

/-- The actual right action is linear for the actual left action. -/
def rightActionHom (P : Bimod (Mon.mk R) (Mon.mk S)) :
    (mop S) ⊙ₗ leftModule R S P ⟶ leftModule R S P :=
  Mod_.Hom.mk' P.actRight (by
    change ((α_ R P.X S).inv ≫ P.actLeft ▷ S) ≫ P.actRight =
      R ◁ P.actRight ≫ P.actLeft
    rw [assoc, P.middle_assoc, Iso.inv_hom_id_assoc])

/-- The commuting actual right action gives the second native module. -/
def rightModObj (P : Bimod (Mon.mk R) (Mon.mk S)) :
    ModObj (mop S) (leftModule R S P) where
  smul := rightActionHom R S P
  one_smul' := by apply Mod_.Hom.ext; exact P.actRight_one
  mul_smul' := by apply Mod_.Hom.ext; exact P.right_assoc

/-- Two-sided bimodule data give actual native iterated internal modules. -/
def fromBimodObj (P : Bimod (Mon.mk R) (Mon.mk S)) : Native R S :=
  letI := rightModObj R S P
  ⟨leftModule R S P⟩

end Paper18.Category.BimoduleRelativeTensor
