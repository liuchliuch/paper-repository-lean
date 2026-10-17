import Paper18.Category.PointedRepEquivalenceBasic
import Paper18.Category.TensorCharacters

/-! # Actual braided tensor structure of the center sign-representation functor -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.Monoidal
namespace Paper18.Category.AppendixBPointed
open RepresentationZ2

def centerRepUnitIso : 𝟙_ (FDRep ℂ H) ≅ centerRepFunctor.obj (𝟙_ BCenter) :=
  Action.mkIso (εIso centerFiberFunctor) (fun g => by
    rcases eq_one_or_generator g with rfl | rfl
    · simp
    · change 𝟙 _ ≫ ε centerFiberFunctor = ε centerFiberFunctor ≫ totalParity (𝟙_ BCenter)
      rw [totalParity, TensorAutomorphism.unit_component centerParity,
        CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id])

def centerRepTensorIso (X Y : BCenter) :
    centerRepFunctor.obj X ⊗ centerRepFunctor.obj Y ≅ centerRepFunctor.obj (X ⊗ Y) :=
  Action.mkIso (μIso centerFiberFunctor X Y) (fun g => by
    rcases eq_one_or_generator g with rfl | rfl
    · simp
    · change (totalParity X ⊗ₘ totalParity Y) ≫ μ centerFiberFunctor X Y =
        μ centerFiberFunctor X Y ≫ totalParity (X ⊗ Y)
      unfold totalParity
      rw [Functor.LaxMonoidal.μ_natural,
        ← TensorAutomorphism.tensor_component centerParity X Y])

def centerRepFunctorCoreMonoidal : centerRepFunctor.CoreMonoidal where
  εIso := centerRepUnitIso
  μIso := centerRepTensorIso
  μIso_hom_natural_left f X := by
    apply Action.Hom.ext
    exact Functor.LaxMonoidal.μ_natural_left centerFiberFunctor f X
  μIso_hom_natural_right X f := by
    apply Action.Hom.ext
    exact Functor.LaxMonoidal.μ_natural_right centerFiberFunctor X f
  associativity X Y Z := by
    apply Action.Hom.ext
    simpa [centerRepTensorIso] using
      Functor.LaxMonoidal.associativity centerFiberFunctor X Y Z
  left_unitality X := by
    apply Action.Hom.ext
    simpa [centerRepUnitIso, centerRepTensorIso] using
      Functor.LaxMonoidal.left_unitality centerFiberFunctor X
  right_unitality X := by
    apply Action.Hom.ext
    simpa [centerRepUnitIso, centerRepTensorIso] using
      Functor.LaxMonoidal.right_unitality centerFiberFunctor X

instance centerRepFunctor_monoidal : centerRepFunctor.Monoidal :=
  centerRepFunctorCoreMonoidal.toMonoidal

/-- On the actual center support, the specified Appendix B braiding becomes
the ordinary vector-space flip under the total-vector functor. -/
instance centerFiberFunctor_braided : centerFiberFunctor.Braided where
  toMonoidal := centerFiberFunctor_monoidal
  braided X Y := by
    change PointedVec.totalTensorHom X.obj.obj Y.obj.obj ≫
        PointedVec.totalFunctor.map (PointedVec.bicharacterBraiding bicharacter X.obj.obj Y.obj.obj).hom =
      (β_ (⨁ X.obj.obj) (⨁ Y.obj.obj)).hom ≫
        PointedVec.totalTensorHom Y.obj.obj X.obj.obj
    apply PointedVec.totalTensor_hom_ext X.obj.obj Y.obj.obj
    intro a b
    by_cases hb0 : b = 0
    · subst b
      rw [PointedVec.totalTensorHom_ι_assoc, PointedVec.totalFunctor_ι_map,
        PointedVec.inclusion_bicharacterBraiding_assoc,
        BraidedCategory.braiding_naturality_assoc]
      erw [PointedVec.totalTensorHom_ι_of_add Y.obj.obj X.obj.obj 0 a (a + 0) (by simp)]
      simp [bicharacter_val, braidingScalar]
    · by_cases hbf : b = Paper18.f
      · subst b
        rw [PointedVec.totalTensorHom_ι_assoc, PointedVec.totalFunctor_ι_map,
          PointedVec.inclusion_bicharacterBraiding_assoc,
          BraidedCategory.braiding_naturality_assoc]
        erw [PointedVec.totalTensorHom_ι_of_add Y.obj.obj X.obj.obj Paper18.f a
          (a + Paper18.f) (add_comm _ _)]
        simp [bicharacter_val, braidingScalar, Paper18.f]
      · have hz : IsZero (X.obj.obj a ⊗ Y.obj.obj b) :=
          (tensorLeft (X.obj.obj a)).map_isZero (bCenter_fiber_isZero Y b hb0 hbf)
        exact hz.eq_of_src _ _

/-- The actual sign-representation functor preserves the full braiding. -/
instance centerRepFunctor_braided : centerRepFunctor.Braided where
  toMonoidal := centerRepFunctor_monoidal
  braided X Y := by
    apply Action.Hom.ext
    exact Functor.LaxBraided.braided (F := centerFiberFunctor) X Y

end Paper18.Category.AppendixBPointed
