import Paper18.Category.DrinfeldPivotalFactorizationBasic

/-! # Actual pivotal preservation of the Deligne factorization functor -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u v' u' w
namespace Paper18.Category.Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual

section Matrix
variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℂ B]
  [MonoidalCategory B] [MonoidalPreadditive B] [MonoidalLinear ℂ B]
  [RightRigidCategory B] [BraidedCategory B]
  {E : Type u'} [Category.{v'} E] [Preadditive E] [Linear ℂ E]
  [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalLinear ℂ E]
  [RightRigidCategory E] [BraidedCategory E] [HasFiniteBiproducts E]
  (F : B ⥤ E) [F.Additive] [F.Linear ℂ] [F.Monoidal]
  (θ : 𝟭 B ≅ 𝟭 B) (K : PivotalStructure E)

/-- The actual additive lift preserves a diagonal balancing whenever each
actual summand does. This is proved using actual biproduct injections. -/
lemma linearMatLift_twist
    (h : ∀ X, F.map (θ.hom.app X) = (K.twistIso (F.obj X)).hom) (X : Mat_ B) :
    (linearMatLift F).map ((LinearMat.matrixTwist θ).hom.app X) =
      (K.twistIso ((linearMatLift F).obj X)).hom := by
  apply biproduct.hom_ext'
  intro i
  change biproduct.ι (fun i => F.obj (X.X i)) i ≫
      (linearMatLift F).map (LinearMat.indexEquivHom (Equiv.refl X.ι)
        (fun i => θ.hom.app (X.X i))) = _
  rw [LinearMat.lift_ι_map_indexEquivHom, h]
  exact (K.twist_naturality (biproduct.ι (fun i => F.obj (X.X i)) i)).symm

end Matrix

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [LeftRigidCategory C] [BraidedCategory C]
  [HasFiniteBiproducts C]

/-- The actual Deligne factorization carries the prescribed reverse-second
product twist to the actual lifted center twist. -/
lemma deligneFactorization_twist (J : PivotalStructure C) (X : DeligneProduct C C) :
    letI : BraidedCategory (DeligneProduct C C) := deligneReverseSecondBraiding C
    (deligneFactorization C).map ((reverseSecondPivotal J).twistIso X).hom =
      ((centerPivotal J).twistIso ((deligneFactorization C).obj X)).hom := by
  letI : BraidedCategory (DeligneProduct C C) := deligneReverseSecondBraiding C
  change (deligneFactorization C).map ((reverseSecondPivotal J).twistNatIso.hom.app X) = _
  rw [reverseSecondPivotal_twist]
  exact linearMatLift_twist (linearFactorization C) (reverseSecondTwist J)
    (centerPivotal J) (linearFactorization_twist J) X

/-- The actual strong braided Deligne factorization preserves the actual
prescribed product pivotal structure through its canonical double-dual
comparison. No preservation datum is supplied. -/
theorem deligneFactorization_preservesPivotal (J : PivotalStructure C) :
    PreservesPivotal (deligneFactorization C) (reverseSecondPivotal J) (centerPivotal J) := by
  letI : BraidedCategory (DeligneProduct C C) := deligneReverseSecondBraiding C
  letI : (deligneFactorization C).Braided := deligneFactorizationBraided C
  exact preservesPivotal_of_twist _ _ _ (deligneFactorization_twist J)

section Spherical
variable [HasKernels C] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

include S in
/-- The prescribed reverse-second product pivotal structure is actually
spherical whenever the original prescribed structure is spherical. -/
theorem reverseSecondPivotal_spherical (J : PivotalStructure C) (hJ : J.Spherical) :
    (reverseSecondPivotal J).Spherical := by
  exact @DeligneProduct.pivotal_spherical C _ _ _ _ _ _ _ inferInstance
    C _ _ _ _ _ _ _ (reverseBraiding C) J J
    _ _ _ _ _ _ _ _ ι _ S ι _ S hJ hJ

end Spherical
end Paper18.Category.Drinfeld
