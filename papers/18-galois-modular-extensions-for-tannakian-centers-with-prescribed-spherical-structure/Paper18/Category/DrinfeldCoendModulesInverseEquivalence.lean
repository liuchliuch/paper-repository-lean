import Paper18.Category.DrinfeldCoendModulesInverseLinear
import Paper18.Category.DrinfeldCoendModulesFunctor

/-! # The actual no-pivotal center/coend-module equivalence -/
noncomputable section
set_option maxHeartbeats 2000000
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj
universe v u w
namespace Paper18.Category.DrinfeldCoendModules
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)

/-- On actual central objects, cap transposition recovers the given
half-braiding, by an actual identity-underlying central isomorphism. -/
def centerRoundtripIso : toModules S ⋙ fromModules S ≅ 𝟭 (Center D) :=
  NatIso.ofComponents
    (fun Z => recoveredCenterIso S ((toModules S).obj Z) Z.2 rfl)
    (fun f => by
      apply Center.Hom.ext
      change f.f ≫ 𝟙 _ = 𝟙 _ ≫ f.f
      simp)

/-- On actual modules, coend generation proves that the recovered
central structure returns exactly the original action. -/
def moduleRoundtripComponent (M : Mod_ D (algebra S)) :
    (toModules S).obj ((fromModules S).obj M) ≅ M where
  hom := Mod_.Hom.mk' (𝟙 M.X) (by
    change action S ((fromModules S).obj M) ≫ 𝟙 M.X =
      algebra S ◁ 𝟙 M.X ≫ γ[algebra S,M.X]
    rw [fromModules_action]
    simp only [whiskerLeft_id, id_comp]
    exact comp_id _)
  inv := Mod_.Hom.mk' (𝟙 M.X) (by
    change γ[algebra S,M.X] ≫ 𝟙 M.X =
      algebra S ◁ 𝟙 M.X ≫ action S ((fromModules S).obj M)
    rw [fromModules_action]
    simp only [comp_id, whiskerLeft_id, id_comp])
  hom_inv_id := by apply Mod_.Hom.ext; exact id_comp _
  inv_hom_id := by apply Mod_.Hom.ext; exact id_comp _

/-- The actual module roundtrip is natural, with identity underlying components. -/
def moduleRoundtripIso : fromModules S ⋙ toModules S ≅ 𝟭 (Mod_ D (algebra S)) :=
  NatIso.ofComponents (moduleRoundtripComponent S) (fun f => by
    apply Mod_.Hom.ext
    change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
    simp)

instance toModules_essSurj : (toModules S).EssSurj where
  mem_essImage M := ⟨(fromModules S).obj M, ⟨moduleRoundtripComponent S M⟩⟩

instance fromModules_essSurj : (fromModules S).EssSurj where
  mem_essImage Z := ⟨(toModules S).obj Z, ⟨(centerRoundtripIso S).app Z⟩⟩

instance toModules_isEquivalence : (toModules S).IsEquivalence where

instance fromModules_isEquivalence : (fromModules S).IsEquivalence where

/-- The actual center is equivalent to actual modules over the proved
separable coend algebra. No pivotal structure is supplied or constructed
as an intermediate assumption. -/
def equivalence : Center D ≌ Mod_ D (algebra S) :=
  CategoryTheory.Equivalence.mk (toModules S) (fromModules S)
    (centerRoundtripIso S).symm (moduleRoundtripIso S)

@[simp] lemma equivalence_functor : (equivalence S).functor = toModules S := rfl

@[simp] lemma equivalence_inverse : (equivalence S).inverse = fromModules S := rfl

instance equivalence_additive : (equivalence S).functor.Additive :=
  inferInstanceAs (toModules S).Additive

instance equivalence_linear : (equivalence S).functor.Linear ℂ :=
  inferInstanceAs ((toModules S).Linear ℂ)

instance equivalence_inverse_additive : (equivalence S).inverse.Additive :=
  inferInstanceAs (fromModules S).Additive

instance equivalence_inverse_linear : (equivalence S).inverse.Linear ℂ :=
  inferInstanceAs ((fromModules S).Linear ℂ)

end Paper18.Category.DrinfeldCoendModules
