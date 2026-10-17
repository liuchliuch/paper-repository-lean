import Paper18.Category.GraphPicardMoritaClassificationImageModules
import Paper18.Category.FixedBoundaryRestriction

/-! # Actual algebra transport for genuine internal right modules

An actual algebra isomorphism gives an actual equivalence of native
internal right-module categories. No braiding, commutativity or pivotal
structure is used. Both directions are additive and complex linear.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u w
namespace Paper18.Category.GraphPicard

section AlgebraTransport
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {A B : C} [MonObj A] [MonObj B] (e : A ≅ B) [IsMonHom e.hom]

/-- An actual algebra isomorphism acts on genuine internal right
modules through the monoidal opposite, without braiding assumptions. -/
def rightAlgebraRestrictionEquivalence :
    Mod_ Cᴹᵒᵖ (mop B) ≌ Mod_ Cᴹᵒᵖ (mop A) := by
  letI : IsMonHom e.hom.mop :=
    { one_hom := by apply Quiver.Hom.unmop_inj; exact IsMonHom.one_hom e.hom
      mul_hom := by apply Quiver.Hom.unmop_inj; exact IsMonHom.mul_hom e.hom }
  let em : mop A ≅ mop B :=
    { hom := e.hom.mop
      inv := e.inv.mop
      hom_inv_id := by apply Quiver.Hom.unmop_inj; exact e.hom_inv_id
      inv_hom_id := by apply Quiver.Hom.unmop_inj; exact e.inv_hom_id }
  exact InternalModule.algebraRestrictionEquivalence em

variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

instance rightAlgebraRestrictionEquivalence_additive :
    (rightAlgebraRestrictionEquivalence e).functor.Additive where
  map_add {X Y f g} := by apply Mod_.Hom.ext; rfl
instance rightAlgebraRestrictionEquivalence_linear :
    (rightAlgebraRestrictionEquivalence e).functor.Linear ℂ where
  map_smul f r := by apply Mod_.Hom.ext; rfl

instance rightAlgebraRestrictionEquivalence_inverse_additive :
    (rightAlgebraRestrictionEquivalence e).inverse.Additive :=
  Equivalence.inverse_additive (rightAlgebraRestrictionEquivalence e)
instance rightAlgebraRestrictionEquivalence_inverse_linear :
    (rightAlgebraRestrictionEquivalence e).inverse.Linear ℂ :=
  Equivalence.inverseLinear ℂ (rightAlgebraRestrictionEquivalence e)
end AlgebraTransport

end Paper18.Category.GraphPicard
