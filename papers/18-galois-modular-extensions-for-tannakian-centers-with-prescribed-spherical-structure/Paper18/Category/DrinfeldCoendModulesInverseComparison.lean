import Paper18.Category.DrinfeldCoendModulesInverseFunctor

/-! # Actual comparison of recovered and original half-braidings -/
noncomputable section
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

/-- Rigid transposition recovers the original actual half-braiding when
the module action is its actual descended annular action. -/
lemma moduleHalfBraiding_hom_eq_of_action (M : Mod_ D (algebra S)) (b : HalfBraiding M.X)
    (h : γ[algebra S,M.X] = action S ⟨M.X,b⟩) (T : D) :
    ((moduleHalfBraiding S M).β T).hom = (b.β T).hom := by
  have he : ((moduleHalfBraiding S M).β T).symm = (b.β T).symm := by
    apply Iso.ext
    exact (moduleHalfBraiding_inv S M T).trans (moduleInverseCrossing_eq_inv S M b h T)
  exact congrArg Iso.inv he

/-- The actual recovered central object is isomorphic to the original
one by the identity on its underlying object. -/
def recoveredCenterIso (M : Mod_ D (algebra S)) (b : HalfBraiding M.X)
    (h : γ[algebra S,M.X] = action S ⟨M.X,b⟩) :
    (fromModules S).obj M ≅ ⟨M.X,b⟩ := by
  let f : (fromModules S).obj M ⟶ ⟨M.X,b⟩ := {
    f := 𝟙 M.X
    comm T := by
      change 𝟙 M.X ▷ T ≫ (b.β T).hom =
        ((moduleHalfBraiding S M).β T).hom ≫ T ◁ 𝟙 M.X
      rw [id_whiskerRight, whiskerLeft_id, id_comp, comp_id]
      exact (moduleHalfBraiding_hom_eq_of_action S M b h T).symm }
  haveI : IsIso f.f := by change IsIso (𝟙 M.X); infer_instance
  exact Center.isoMk f

@[simp] lemma recoveredCenterIso_hom_f (M : Mod_ D (algebra S)) (b : HalfBraiding M.X)
    (h : γ[algebra S,M.X] = action S ⟨M.X,b⟩) :
    (recoveredCenterIso S M b h).hom.f = 𝟙 M.X := rfl

end Paper18.Category.DrinfeldCoendModules
