import Paper18.Category.LinearMatMonoidalLift

/-! # Coherence of the strong monoidal additive-envelope lift -/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u v' u'
namespace Paper18.Category.LinearMat
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  {E : Type u'} [Category.{v'} E] [Preadditive E] [Linear ℂ E]
  [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalLinear ℂ E]
  [HasFiniteBiproducts E] (F : C ⥤ E) [F.Additive] [F.Linear ℂ] [F.Monoidal]

/-- Associativity of the actual tensorator follows on triple generators
from the source functor's actual associativity equation. -/
lemma liftTensorIso_associativity (X Y Z : Mat_ C) :
    (liftTensorIso F X Y).hom ▷ (linearMatLift F).obj Z ≫
      (liftTensorIso F (X ⊗ Y) Z).hom ≫ (linearMatLift F).map (α_ X Y Z).hom =
    (α_ ((linearMatLift F).obj X) ((linearMatLift F).obj Y) ((linearMatLift F).obj Z)).hom ≫
      (linearMatLift F).obj X ◁ (liftTensorIso F Y Z).hom ≫
      (liftTensorIso F X (Y ⊗ Z)).hom := by
  apply tripleTensorBiproduct_hom_ext
  intro i j k
  rw [liftTensorIso_left_generator_assoc F X Y Z,
    liftTensorIso_right_generator F X Y Z]
  have hh := lift_ι_map_indexEquivHom F
    (X := (X ⊗ Y) ⊗ Z) (Y := X ⊗ (Y ⊗ Z))
    (Equiv.prodAssoc X.ι Y.ι Z.ι)
    (fun p => (α_ (X.X p.1.1) (Y.X p.1.2) (Z.X p.2)).hom) ((i,j),k)
  change biproduct.ι (fun p : (X.ι × Y.ι) × Z.ι =>
      F.obj ((X.X p.1.1 ⊗ Y.X p.1.2) ⊗ Z.X p.2)) ((i,j),k) ≫
      (linearMatLift F).map (α_ X Y Z).hom =
    F.map (α_ (X.X i) (Y.X j) (Z.X k)).hom ≫
      biproduct.ι (fun p : X.ι × (Y.ι × Z.ι) =>
        F.obj (X.X p.1 ⊗ (Y.X p.2.1 ⊗ Z.X p.2.2))) (i,(j,k)) at hh
  rw [hh]
  simpa only [assoc] using congrArg (fun z => z ≫
    biproduct.ι (fun p : X.ι × (Y.ι × Z.ι) =>
      F.obj (X.X p.1 ⊗ (Y.X p.2.1 ⊗ Z.X p.2.2))) (i,(j,k)))
      (Functor.LaxMonoidal.associativity F (X.X i) (Y.X j) (Z.X k))

lemma lift_leftUnit_generator (X : Mat_ C) (i : X.ι) :
    (𝟙_ E) ◁ biproduct.ι (fun i => F.obj (X.X i)) i ≫
      (liftUnitIso F).hom ▷ (linearMatLift F).obj X ≫
      (liftTensorIso F (𝟙_ (Mat_ C)) X).hom ≫ (linearMatLift F).map (λ_ X).hom =
    Functor.LaxMonoidal.ε F ▷ F.obj (X.X i) ≫
      Functor.LaxMonoidal.μ F (𝟙_ C) (X.X i) ≫ F.map (λ_ (X.X i)).hom ≫
      biproduct.ι (fun i => F.obj (X.X i)) i := by
  have hp : (𝟙_ E) ◁ biproduct.ι (fun i => F.obj (X.X i)) i ≫
      (liftUnitIso F).hom ▷ (linearMatLift F).obj X =
      (liftUnitIso F).hom ⊗ₘ biproduct.ι (fun i => F.obj (X.X i)) i :=
    (tensorHom_def' _ _).symm
  rw [← assoc, hp, liftUnitIso_hom]
  calc
    _ = Functor.LaxMonoidal.ε F ▷ F.obj (X.X i) ≫
        (biproduct.ι (fun _ : PUnit => F.obj (𝟙_ C)) PUnit.unit ⊗ₘ
          biproduct.ι (fun i => F.obj (X.X i)) i) ≫
        (liftTensorIso F (𝟙_ (Mat_ C)) X).hom ≫ (linearMatLift F).map (λ_ X).hom := by
      simp only [tensorHom_def, comp_whiskerRight, assoc]
      rfl
    _ = _ := by
      have ht := tensor_ι_liftTensorIso F (𝟙_ (Mat_ C)) X PUnit.unit i
      change (biproduct.ι (fun _ : PUnit => F.obj (𝟙_ C)) PUnit.unit ⊗ₘ
          biproduct.ι (fun i => F.obj (X.X i)) i) ≫
          (liftTensorIso F (𝟙_ (Mat_ C)) X).hom =
        Functor.LaxMonoidal.μ F (𝟙_ C) (X.X i) ≫
          biproduct.ι (fun p : PUnit × X.ι => F.obj ((𝟙_ C) ⊗ X.X p.2)) (PUnit.unit,i) at ht
      rw [reassoc_of% ht]
      have hl := lift_ι_map_indexEquivHom F
        (X := (𝟙_ (Mat_ C)) ⊗ X) (Y := X) (Equiv.punitProd X.ι)
        (fun p => (λ_ (X.X p.2)).hom) (PUnit.unit,i)
      change biproduct.ι (fun p : PUnit × X.ι => F.obj ((𝟙_ C) ⊗ X.X p.2)) (PUnit.unit,i) ≫
          (linearMatLift F).map (λ_ X).hom = F.map (λ_ (X.X i)).hom ≫
          biproduct.ι (fun i => F.obj (X.X i)) i at hl
      rw [hl]

lemma lift_rightUnit_generator (X : Mat_ C) (i : X.ι) :
    biproduct.ι (fun i => F.obj (X.X i)) i ▷ (𝟙_ E) ≫
      (linearMatLift F).obj X ◁ (liftUnitIso F).hom ≫
      (liftTensorIso F X (𝟙_ (Mat_ C))).hom ≫ (linearMatLift F).map (ρ_ X).hom =
    F.obj (X.X i) ◁ Functor.LaxMonoidal.ε F ≫
      Functor.LaxMonoidal.μ F (X.X i) (𝟙_ C) ≫ F.map (ρ_ (X.X i)).hom ≫
      biproduct.ι (fun i => F.obj (X.X i)) i := by
  have hp : biproduct.ι (fun i => F.obj (X.X i)) i ▷ (𝟙_ E) ≫
      (linearMatLift F).obj X ◁ (liftUnitIso F).hom =
      biproduct.ι (fun i => F.obj (X.X i)) i ⊗ₘ (liftUnitIso F).hom :=
    (tensorHom_def _ _).symm
  rw [← assoc, hp, liftUnitIso_hom]
  calc
    _ = F.obj (X.X i) ◁ Functor.LaxMonoidal.ε F ≫
        (biproduct.ι (fun i => F.obj (X.X i)) i ⊗ₘ
          biproduct.ι (fun _ : PUnit => F.obj (𝟙_ C)) PUnit.unit) ≫
        (liftTensorIso F X (𝟙_ (Mat_ C))).hom ≫ (linearMatLift F).map (ρ_ X).hom := by
      simp only [tensorHom_def', whiskerLeft_comp, assoc]
      rfl
    _ = _ := by
      have ht := tensor_ι_liftTensorIso F X (𝟙_ (Mat_ C)) i PUnit.unit
      change (biproduct.ι (fun i => F.obj (X.X i)) i ⊗ₘ
          biproduct.ι (fun _ : PUnit => F.obj (𝟙_ C)) PUnit.unit) ≫
          (liftTensorIso F X (𝟙_ (Mat_ C))).hom =
        Functor.LaxMonoidal.μ F (X.X i) (𝟙_ C) ≫
          biproduct.ι (fun p : X.ι × PUnit => F.obj (X.X p.1 ⊗ (𝟙_ C))) (i,PUnit.unit) at ht
      rw [reassoc_of% ht]
      have hr := lift_ι_map_indexEquivHom F
        (X := X ⊗ (𝟙_ (Mat_ C))) (Y := X) (Equiv.prodPUnit X.ι)
        (fun p => (ρ_ (X.X p.1)).hom) (i,PUnit.unit)
      change biproduct.ι (fun p : X.ι × PUnit => F.obj (X.X p.1 ⊗ (𝟙_ C))) (i,PUnit.unit) ≫
          (linearMatLift F).map (ρ_ X).hom = F.map (ρ_ (X.X i)).hom ≫
          biproduct.ι (fun i => F.obj (X.X i)) i at hr
      rw [hr]

/-- The actual additive lift of an actual strong monoidal functor is strong
monoidal; all coherence follows from injections and the actual base coherence. -/
def liftCoreMonoidal : (linearMatLift F).CoreMonoidal where
  εIso := liftUnitIso F
  μIso := liftTensorIso F
  μIso_hom_natural_left := by
    intro X Y f Z
    have hh := liftTensorIso_natural F f (𝟙 Z)
    rw [(linearMatLift F).map_id Z] at hh
    simpa only [MonoidalCategory.tensorHom_id] using hh
  μIso_hom_natural_right := by
    intro X Y Z f
    have hh := liftTensorIso_natural F (𝟙 Z) f
    rw [(linearMatLift F).map_id Z] at hh
    simpa only [MonoidalCategory.id_tensorHom] using hh
  associativity := liftTensorIso_associativity F
  left_unitality := by
    intro X
    apply leftDistributor_ext_left
    intro i
    rw [lift_leftUnit_generator F X i]
    simpa only [assoc] using (MonoidalCategory.leftUnitor_naturality
      (biproduct.ι (fun i => F.obj (X.X i)) i)).trans
      (congrArg (fun z => z ≫ biproduct.ι (fun i => F.obj (X.X i)) i)
        (Functor.LaxMonoidal.left_unitality F (X.X i)))
  right_unitality := by
    intro X
    apply rightDistributor_ext_left
    intro i
    rw [lift_rightUnit_generator F X i]
    simpa only [assoc] using (MonoidalCategory.rightUnitor_naturality
      (biproduct.ι (fun i => F.obj (X.X i)) i)).trans
      (congrArg (fun z => z ≫ biproduct.ι (fun i => F.obj (X.X i)) i)
        (Functor.LaxMonoidal.right_unitality F (X.X i)))

instance liftMonoidal : (linearMatLift F).Monoidal := (liftCoreMonoidal F).toMonoidal

end Paper18.Category.LinearMat
