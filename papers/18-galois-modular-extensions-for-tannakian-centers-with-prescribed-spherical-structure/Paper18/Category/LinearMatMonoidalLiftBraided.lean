import Paper18.Category.LinearMatMonoidalLiftCoherence
import Paper18.Category.LinearMatMonoidalBraided

/-! # Braidedness of the actual additive-envelope lift -/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory CategoryTheory.Limits
universe v u v' u'
namespace Paper18.Category.LinearMat
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] [BraidedCategory C]
  {E : Type u'} [Category.{v'} E] [Preadditive E] [Linear ℂ E]
  [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalLinear ℂ E] [BraidedCategory E]
  [HasFiniteBiproducts E] (F : C ⥤ E) [F.Additive] [F.Linear ℂ] [F.Braided]

instance liftBraided : (linearMatLift F).Braided where
  braided X Y := by
    change (liftTensorIso F X Y).hom ≫ (linearMatLift F).map (β_ X Y).hom =
      (β_ ((linearMatLift F).obj X) ((linearMatLift F).obj Y)).hom ≫
        (liftTensorIso F Y X).hom
    apply tensorBiproduct_hom_ext
    intro i j
    rw [tensor_ι_liftTensorIso_assoc F X Y]
    have hb := lift_ι_map_indexEquivHom F
      (X := X ⊗ Y) (Y := Y ⊗ X) (Equiv.prodComm X.ι Y.ι)
      (fun p => (β_ (X.X p.1) (Y.X p.2)).hom) (i,j)
    change biproduct.ι (fun p : X.ι × Y.ι => F.obj (X.X p.1 ⊗ Y.X p.2)) (i,j) ≫
        (linearMatLift F).map (β_ X Y).hom =
      F.map (β_ (X.X i) (Y.X j)).hom ≫
        biproduct.ι (fun p : Y.ι × X.ι => F.obj (Y.X p.1 ⊗ X.X p.2)) (j,i) at hb
    rw [hb]
    have hn := BraidedCategory.braiding_naturality
      (biproduct.ι (fun i => F.obj (X.X i)) i)
      (biproduct.ι (fun j => F.obj (Y.X j)) j)
    calc
      _ = (β_ (F.obj (X.X i)) (F.obj (Y.X j))).hom ≫
          Functor.LaxMonoidal.μ F (Y.X j) (X.X i) ≫
            biproduct.ι (fun p : Y.ι × X.ι => F.obj (Y.X p.1 ⊗ X.X p.2)) (j,i) := by
        rw [Functor.LaxBraided.braided_assoc]
      _ = _ := by
        have hg := congrArg (fun z => (β_ (F.obj (X.X i)) (F.obj (Y.X j))).hom ≫ z)
          (tensor_ι_liftTensorIso F Y X j i)
        have hh := congrArg (fun z => z ≫ (liftTensorIso F Y X).hom) hn
        simp only [assoc] at hh
        exact hg.symm.trans hh.symm

end Paper18.Category.LinearMat
