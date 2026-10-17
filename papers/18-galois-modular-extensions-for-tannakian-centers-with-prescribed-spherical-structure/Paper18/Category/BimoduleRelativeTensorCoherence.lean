import Paper18.Category.BimoduleRelativeTensorProduct

/-! # Actual associators and unitors of native bimodule composition -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u
namespace Paper18.Category.BimoduleRelativeTensor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [HasCoequalizers D] [LeftRigidCategory D] [RightRigidCategory D]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
variable {R S T U V : D} [MonObj R] [MonObj S] [MonObj T] [MonObj U] [MonObj V]

/-- The actual regular two-sided bimodule, in native form. -/
def regular (R : D) [MonObj R] : Native R R :=
  fromBimodObj R R (Bimod.regular (Mon.mk R))

/-- Actual left whiskering of a bimodule morphism. -/
def whiskerLeft (M : Native R S) {N N' : Native S T} (f : N ⟶ N') :
    tensor M N ⟶ tensor M N' :=
  (fromBimod R T).map (Bimod.whiskerLeft (toBimodObj R S M) ((toBimod S T).map f))

/-- Actual right whiskering of a bimodule morphism. -/
def whiskerRight {M M' : Native R S} (f : M ⟶ M') (N : Native S T) :
    tensor M N ⟶ tensor M' N :=
  (fromBimod R T).map (Bimod.whiskerRight ((toBimod R S).map f) (toBimodObj S T N))

/-- The actual associator of balancing coequalizers, linear for both
outer actions. -/
def associator (M : Native R S) (N : Native S T) (P : Native T U) :
    tensor (tensor M N) P ≅ tensor M (tensor N P) :=
  (fromBimod R U).mapIso
    (Bimod.associatorBimod (toBimodObj R S M) (toBimodObj S T N) (toBimodObj T U P))

/-- The actual left unitor contracts the actual left action. -/
def leftUnitor (M : Native R S) : tensor (regular R) M ≅ M :=
  (fromBimod R S).mapIso (Bimod.leftUnitorBimod (toBimodObj R S M))

/-- The actual right unitor contracts the actual right action. -/
def rightUnitor (M : Native R S) : tensor M (regular S) ≅ M :=
  (fromBimod R S).mapIso (Bimod.rightUnitorBimod (toBimodObj R S M))

/-- The actual relative associator satisfies the pentagon, inherited
from the proved universal-coequalizer calculation for two-sided actions. -/
lemma pentagon (M : Native R S) (N : Native S T) (P : Native T U) (Q : Native U V) :
    whiskerRight (associator M N P).hom Q ≫
      (associator M (tensor N P) Q).hom ≫
        whiskerLeft M (associator N P Q).hom =
      (associator (tensor M N) P Q).hom ≫ (associator M N (tensor P Q)).hom := by
  apply Mod_.Hom.ext
  apply Mod_.Hom.ext
  exact congrArg Bimod.Hom.hom (Bimod.pentagon_bimod
    (toBimodObj R S M) (toBimodObj S T N) (toBimodObj T U P) (toBimodObj U V Q))

/-- The actual relative associator and contraction unitors satisfy
the triangle law. -/
lemma triangle (M : Native R S) (N : Native S T) :
    (associator M (regular S) N).hom ≫ whiskerLeft M (leftUnitor N).hom =
      whiskerRight (rightUnitor M).hom N := by
  apply Mod_.Hom.ext
  apply Mod_.Hom.ext
  exact congrArg Bimod.Hom.hom (Bimod.triangle_bimod (toBimodObj R S M) (toBimodObj S T N))

end Paper18.Category.BimoduleRelativeTensor
