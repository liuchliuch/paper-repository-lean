import Paper18.Category.ModuleAlphaInductionMonoidal
import Paper18.Category.InvertibleFunctor

/-! # Actual inverses reflected through alpha induction

These constructions use actual tensor isomorphisms and the actual strong
monoidal structure.  No rigidity or pivotal structure on the acting
category is needed to reflect an already constructed inverse.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.Monoidal MonoidalOpposite
universe v u v' u' vM uM
namespace Paper18.Category.ModuleAlphaInduction
section Reflection
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal] [F.Full] [F.Faithful] [F.EssSurj]

/-- A strong fully faithful essentially surjective functor reflects actual
two-sided tensor inverse data. -/
def tensorInverseOfImage {X : C} (A : TensorInverse (F.obj X)) : TensorInverse X where
  inverse := F.objPreimage A.inverse
  left := F.preimageIso
    ((μIso F (F.objPreimage A.inverse) X).symm ≪≫
      (F.objObjPreimageIso A.inverse ⊗ᵢ Iso.refl _) ≪≫ A.left ≪≫ εIso F)
  right := F.preimageIso
    ((μIso F X (F.objPreimage A.inverse)).symm ≪≫
      (Iso.refl _ ⊗ᵢ F.objObjPreimageIso A.inverse) ≪≫ A.right ≪≫ εIso F)

/-- The same reflection after an actual representing isomorphism. -/
def tensorInverseOfImageIso {X : C} {Y : D} (e : F.obj X ≅ Y)
    (A : TensorInverse Y) : TensorInverse X :=
  tensorInverseOfImage F
    { inverse := A.inverse
      left := (Iso.refl _ ⊗ᵢ e) ≪≫ A.left
      right := (e ⊗ᵢ Iso.refl _) ≪≫ A.right }
end Reflection

/-- Monoidal opposition reverses the two actual inverse equations. -/
def tensorInverseMop {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
    {X : D} (A : TensorInverse X) : TensorInverse (mop X) where
  inverse := mop A.inverse
  left := Iso.mop A.right
  right := Iso.mop A.left

section Alpha
variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  (M : Type uM) [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction C M]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Additive]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Linear ℂ]
  [(negative C M).IsEquivalence]

/-- The actual ordinary alpha equivalence is still an equivalence after
changing the tensor convention in its target. -/
instance negativeMopIsEquivalence : (negativeMop C M).IsEquivalence := by
  letI : (mopFunctor (End C M)).IsEquivalence := (mopEquiv (End C M)).isEquivalence_functor
  change (negative C M ⋙ mopFunctor (End C M)).IsEquivalence
  infer_instance

/-- The actual strong monoidal alpha equivalence. -/
def negativeMonoidalEquivalence : C ≌ (End C M)ᴹᵒᵖ := (negativeMop C M).asEquivalence

instance negativeMonoidalEquivalenceFunctorMonoidal :
    (negativeMonoidalEquivalence C M).functor.Monoidal :=
  inferInstanceAs (negativeMop C M).Monoidal

/-- The inverse equivalence inherits a genuine strong monoidal structure. -/
def negativeInverseMonoidal : (negativeMonoidalEquivalence C M).inverse.Monoidal :=
  (negativeMonoidalEquivalence C M).inverseMonoidal

/-- The derived inverse makes the actual equivalence monoidal, including
its genuine unit and counit compatibility. -/
def negativeMonoidalEquivalenceIsMonoidal :
    letI := negativeInverseMonoidal C M
    (negativeMonoidalEquivalence C M).IsMonoidal := by
  letI := negativeInverseMonoidal C M
  infer_instance

/-- An actual source object representing an actual strong module functor. -/
def negativeRepresentingObject (F : End C M) : C :=
  (negativeMop C M).objPreimage (mop F)

/-- The actual module-natural representing isomorphism. -/
def negativeRepresentationIso (F : End C M) :
    (negative C M).obj (negativeRepresentingObject C M F) ≅ F :=
  Iso.unmop ((negativeMop C M).objObjPreimageIso (mop F))

/-- An actual inverse of a module functor makes its actual neutral
representing object tensor-invertible. -/
def negativeRepresenterTensorInverse (F : End C M) (A : TensorInverse F) :
    TensorInverse (negativeRepresentingObject C M F) :=
  tensorInverseOfImageIso (negativeMop C M)
    ((negativeMop C M).objObjPreimageIso (mop F)) (tensorInverseMop A)

end Alpha
end Paper18.Category.ModuleAlphaInduction
