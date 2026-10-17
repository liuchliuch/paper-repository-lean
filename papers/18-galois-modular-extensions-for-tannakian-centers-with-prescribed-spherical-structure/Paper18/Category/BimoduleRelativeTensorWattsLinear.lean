import Paper18.Category.BimoduleRelativeTensorWattsInverse

/-! # Complex linearity of the actual monoidal Eilenberg--Watts equivalence -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u
namespace Paper18.Category.BimoduleRelativeTensor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [HasCoequalizers D] [LeftRigidCategory D] [RightRigidCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction nativeMonoidal
variable {R S : D} [MonObj R] [MonObj S]

instance tensorRepresentation_additive :
    (tensorRepresentation (R := R) (S := S)).Additive where
  map_add {P Q} f g := by
    apply Subtype.ext
    apply NatTrans.ext
    funext N
    apply Mod_.Hom.ext
    change ((tensorNat (f + g)).app N).hom =
      ((tensorNat f).app N).hom + ((tensorNat g).app N).hom
    apply (cancel_epi (moduleπ P N)).mp
    rw [Preadditive.comp_add, moduleπ_tensorNat, moduleπ_tensorNat, moduleπ_tensorNat]
    change (f.hom.hom + g.hom.hom) ▷ N.X ≫ moduleπ Q N = _
    rw [MonoidalPreadditive.add_whiskerRight, Preadditive.add_comp]

instance tensorRepresentation_linear :
    (tensorRepresentation (R := R) (S := S)).Linear ℂ where
  map_smul {P Q} f z := by
    apply Subtype.ext
    apply NatTrans.ext
    funext N
    apply Mod_.Hom.ext
    change ((tensorNat (z • f)).app N).hom = z • ((tensorNat f).app N).hom
    apply (cancel_epi (moduleπ P N)).mp
    rw [Linear.comp_smul, moduleπ_tensorNat, moduleπ_tensorNat]
    change (z • f.hom.hom) ▷ N.X ≫ moduleπ Q N = _
    rw [MonoidalLinear.smul_whiskerRight, Linear.smul_comp]

instance reverseRepresentation_additive : (reverseRepresentation R).Additive := by
  unfold reverseRepresentation
  infer_instance

instance reverseRepresentation_linear : (reverseRepresentation R).Linear ℂ := by
  unfold reverseRepresentation
  infer_instance

instance reverseWattsEquivalence_additive (Sep : SeparableAlgebra R) :
    (reverseWattsEquivalence Sep).functor.Additive :=
  reverseRepresentation_additive

instance reverseWattsEquivalence_linear (Sep : SeparableAlgebra R) :
    (reverseWattsEquivalence Sep).functor.Linear ℂ :=
  reverseRepresentation_linear

end Paper18.Category.BimoduleRelativeTensor
