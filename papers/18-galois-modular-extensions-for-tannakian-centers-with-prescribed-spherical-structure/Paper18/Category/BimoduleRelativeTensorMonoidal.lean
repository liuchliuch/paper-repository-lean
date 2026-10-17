import Paper18.Category.BimoduleRelativeTensorMonoidalCoherence

/-! # Strong monoidal relative tensor representation into reversed endofunctors -/
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
variable (R : D) [MonObj R]

/-- The actual quotient associator and action contractions give a strong
monoidal functor into the reversed composition convention. -/
def reverseRepresentationMonoidal : (reverseRepresentation R).Monoidal := by
  letI := reverseRepresentationOplax R
  letI : IsIso (Functor.OplaxMonoidal.η (reverseRepresentation R)) :=
    (reverseUnitIso R).isIso_hom
  letI (P Q : Native R R) :
      IsIso (Functor.OplaxMonoidal.δ (reverseRepresentation R) P Q) :=
    (reverseTensorIso R P Q).isIso_hom
  exact Functor.Monoidal.ofOplaxMonoidal (reverseRepresentation R)

/-- The strong tensorator is precisely the inverse actual quotient
associator; the order reversal is visible in `reverseTensorIso`. -/
lemma reverseRepresentation_μ (P Q : Native R R) :
    letI := reverseRepresentationMonoidal R
    Functor.LaxMonoidal.μ (reverseRepresentation R) P Q =
      (reverseTensorIso R P Q).inv := by
  change inv (reverseTensorIso R P Q).hom = (reverseTensorIso R P Q).inv
  simp

lemma reverseRepresentation_ε :
    letI := reverseRepresentationMonoidal R
    Functor.LaxMonoidal.ε (reverseRepresentation R) = (reverseUnitIso R).inv := by
  change inv (reverseUnitIso R).hom = (reverseUnitIso R).inv
  simp

end Paper18.Category.BimoduleRelativeTensor
