import Paper18.Category.BimoduleRelativeTensorBlockRestriction
import Paper18.Category.ModuleFunctorDualDimensionBlockAlgebra

/-! # Actual two-sided restriction and the regular quotient block -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u
namespace Paper18.Category.BimoduleRelativeTensor.Block
open ModuleFunctor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  {R B : D} [MonObj R] [MonObj B] (p : R ⟶ B) [IsMonHom p]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

instance mop_isMonHom : IsMonHom p.mop where
  one_hom := by apply Quiver.Hom.unmop_inj; exact IsMonHom.one_hom p
  mul_hom := by apply Quiver.Hom.unmop_inj; exact IsMonHom.mul_hom p

/-- Both actual algebra actions are restricted along the actual quotient. -/
def bimoduleRestriction : Native B B ⥤ Native R R := by
  letI := restrictionLeftLinear p
  exact mapActionModules (A := mop B) (Mod_.comap (D := D) p) ⋙
    Mod_.comap (D := Mod_ D R) p.mop

instance bimoduleRestriction_faithful : (bimoduleRestriction p).Faithful where
  map_injective {M N} f g h := by
    apply Mod_.Hom.ext
    apply Mod_.Hom.ext
    exact congrArg (fun k : (bimoduleRestriction p).obj M ⟶
      (bimoduleRestriction p).obj N => k.hom.hom) h

def bimoduleRestrictionPreimage [IsSplitEpi p] {M N : Native B B}
    (f : (bimoduleRestriction p).obj M ⟶ (bimoduleRestriction p).obj N) : M ⟶ N :=
  Mod_.Hom.mk' (restrictionPreimage p f.hom) (by
    apply Mod_.Hom.ext
    letI : IsSplitEpi (M.X.X ◁ p) :=
      inferInstanceAs (IsSplitEpi ((tensorLeft M.X.X).map p))
    change γ[mop B,M.X].hom ≫ f.hom.hom = f.hom.hom ▷ B ≫ γ[mop B,N.X].hom
    apply (cancel_epi (M.X.X ◁ p)).mp
    have h := congrArg Mod_.Hom.hom f.isMod_Hom.smul_hom
    change (M.X.X ◁ p ≫ (𝟙 _ ≫ γ[mop B,M.X].hom)) ≫ f.hom.hom =
      f.hom.hom ▷ R ≫ N.X.X ◁ p ≫ (𝟙 _ ≫ γ[mop B,N.X].hom) at h
    rw [whisker_exchange_assoc]
    simpa only [assoc, id_comp] using h)

instance bimoduleRestriction_full [IsSplitEpi p] : (bimoduleRestriction p).Full where
  map_surjective f := ⟨bimoduleRestrictionPreimage p f, by
    apply Mod_.Hom.ext; apply Mod_.Hom.ext; rfl⟩

def bimoduleRestrictionFullyFaithful [IsSplitEpi p] :
    (bimoduleRestriction p).FullyFaithful := Functor.FullyFaithful.ofFullyFaithful _

section Linear
variable [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]

instance bimoduleRestriction_additive : (bimoduleRestriction p).Additive where
  map_add := by intros; apply Mod_.Hom.ext; apply Mod_.Hom.ext; rfl

instance bimoduleRestriction_linear : (bimoduleRestriction p).Linear ℂ where
  map_smul _ _ := by apply Mod_.Hom.ext; apply Mod_.Hom.ext; rfl

end Linear
end Paper18.Category.BimoduleRelativeTensor.Block
