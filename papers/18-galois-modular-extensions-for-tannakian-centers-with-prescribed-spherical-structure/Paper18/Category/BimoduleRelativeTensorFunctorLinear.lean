import Paper18.Category.BimoduleRelativeTensorFunctorBasic

/-! # Actual complex linearity of relative tensor functors -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u
namespace Paper18.Category.BimoduleRelativeTensor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [HasCoequalizers D] [LeftRigidCategory D] [RightRigidCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
variable {R S : D} [MonObj R] [MonObj S] (P : Native R S)

instance tensorFunctor_additive : (tensorFunctor P).Additive where
  map_add := by
    intro N N' f g
    apply Mod_.Hom.ext
    apply (cancel_epi (moduleπ P N)).mp
    change moduleπ P N ≫ ((tensorFunctor P).map (f + g)).hom =
      moduleπ P N ≫ (((tensorFunctor P).map f).hom + ((tensorFunctor P).map g).hom)
    rw [Preadditive.comp_add, moduleπ_map, moduleπ_map, moduleπ_map]
    change P.X.X ◁ (f.hom + g.hom) ≫ moduleπ P N' = _
    rw [MonoidalPreadditive.whiskerLeft_add, Preadditive.add_comp]

instance tensorFunctor_linear : (tensorFunctor P).Linear ℂ where
  map_smul := by
    intro N N' f z
    apply Mod_.Hom.ext
    apply (cancel_epi (moduleπ P N)).mp
    change moduleπ P N ≫ ((tensorFunctor P).map (z • f)).hom =
      moduleπ P N ≫ (z • ((tensorFunctor P).map f).hom)
    rw [Linear.comp_smul, moduleπ_map, moduleπ_map]
    change P.X.X ◁ (z • f.hom) ≫ moduleπ P N' = _
    rw [MonoidalLinear.whiskerLeft_smul, Linear.smul_comp]

/-- Evaluating the actual relative tensor functor on the regular module
contracts its actual right action. -/
def tensorFunctorRegularIso : (tensorFunctor P).obj (Mod_.regular S) ≅ P.X where
  hom := (rightUnitor P).hom.hom
  inv := (rightUnitor P).inv.hom
  hom_inv_id := congrArg Mod_.Hom.hom (rightUnitor P).hom_inv_id
  inv_hom_id := congrArg Mod_.Hom.hom (rightUnitor P).inv_hom_id

@[reassoc (attr := simp)]
lemma moduleπ_regular :
    moduleπ P (Mod_.regular S) ≫ (tensorFunctorRegularIso P).hom.hom = γ[mop S,P.X].hom :=
  π_rightUnitor P

end Paper18.Category.BimoduleRelativeTensor
