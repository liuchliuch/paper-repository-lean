import Paper18.Category.DrinfeldCoendModulesInverseNaturality
import Paper18.Category.DrinfeldCoendModulesInverseRigid

/-! # The crossing recovered from the actual module action -/
noncomputable section
set_option maxHeartbeats 2000000
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory CategoryTheory.Limits
open scoped MonObj
universe v u w
namespace Paper18.Category.DrinfeldCoendModules
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)

/-- The recovered inverse-oriented crossing. Both factors are actual
morphisms constructed from the module action and ambient braiding. -/
def moduleInverseCrossing (M : Mod_ D (algebra S)) (T : D) : T ⊗ M.X ⟶ M.X ⊗ T :=
  moduleHolonomy S M T ≫ (β_ T M.X).hom

lemma moduleInverseCrossing_naturality (M : Mod_ D (algebra S)) {T U : D} (f : T ⟶ U) :
    f ▷ M.X ≫ moduleInverseCrossing S M U =
      moduleInverseCrossing S M T ≫ M.X ◁ f := by
  dsimp only [moduleInverseCrossing]
  rw [reassoc_of% (moduleHolonomy_naturality S M f),
    braiding_naturality_left, assoc]

lemma moduleInverseCrossing_unit (M : Mod_ D (algebra S)) :
    moduleInverseCrossing S M (𝟙_ D) = (λ_ M.X).hom ≫ (ρ_ M.X).inv := by
  rw [moduleInverseCrossing, moduleHolonomy_unit, id_comp, braiding_tensorUnit_left]

omit [Simple (𝟙_ D)] in
lemma moduleInverseCrossing_map {M N : Mod_ D (algebra S)} (f : M ⟶ N) (T : D) :
    T ◁ f.hom ≫ moduleInverseCrossing S N T =
      moduleInverseCrossing S M T ≫ f.hom ▷ T := by
  dsimp only [moduleInverseCrossing]
  rw [reassoc_of% (moduleHolonomy_map S f T), braiding_naturality_right, assoc]

/-- If the module action is the annular action of an actual central
structure, the actual transpose recovers that structure's holonomy. -/
lemma moduleHolonomy_eq_holonomy (M : Mod_ D (algebra S)) (b : HalfBraiding M.X)
    (h : γ[algebra S,M.X] = action S ⟨M.X,b⟩) (T : D) :
    moduleHolonomy S M T = (holonomy ⟨M.X,b⟩ T).hom := by
  have hi : injection S T ▷ M.X ≫ action S ⟨M.X,b⟩ = actionComponent ⟨M.X,b⟩ T :=
    injection_action S ⟨M.X,b⟩ T
  rw [moduleHolonomy, moduleCap, h, hi]
  exact actionComponent_transpose ⟨M.X,b⟩ T

/-- The recovered crossing on an actual annular module is exactly the
inverse of its given half-braiding. -/
lemma moduleInverseCrossing_eq_inv (M : Mod_ D (algebra S)) (b : HalfBraiding M.X)
    (h : γ[algebra S,M.X] = action S ⟨M.X,b⟩) (T : D) :
    moduleInverseCrossing S M T = (b.β T).inv := by
  rw [moduleInverseCrossing, moduleHolonomy_eq_holonomy S M b h]
  dsimp only [holonomy, Iso.trans_hom, Iso.symm_hom]
  rw [assoc, Iso.inv_hom_id, comp_id]

end Paper18.Category.DrinfeldCoendModules
