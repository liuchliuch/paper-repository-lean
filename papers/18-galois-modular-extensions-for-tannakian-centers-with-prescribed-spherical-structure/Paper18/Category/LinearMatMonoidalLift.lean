import Paper18.Category.LinearMatMonoidalEmbedding

/-! # The actual strong monoidal lift out of the additive envelope -/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u v' u'
namespace Paper18.Category.LinearMat

section BiprodTensor
variable {E : Type u'} [Category.{v'} E] [Preadditive E]
  [MonoidalCategory E] [MonoidalPreadditive E] [HasFiniteBiproducts E]
  {I J : Type} [Fintype I] [Fintype J] (f : I → E) (g : J → E)

/-- Tensor products of biproduct injections jointly detect morphisms. -/
lemma tensorBiproduct_hom_ext {P : E} {a b : (⨁ f) ⊗ (⨁ g) ⟶ P}
    (h : ∀ i j, (biproduct.ι f i ⊗ₘ biproduct.ι g j) ≫ a =
      (biproduct.ι f i ⊗ₘ biproduct.ι g j) ≫ b) : a = b := by
  apply rightDistributor_ext_left
  intro i
  apply leftDistributor_ext_left
  intro j
  simpa only [← assoc, ← tensorHom_def'] using h i j

/-- Distributing tensor over two actual finite biproducts. -/
def biproductTensorHom : (⨁ f) ⊗ (⨁ g) ⟶ ⨁ (fun p : I × J => f p.1 ⊗ g p.2) :=
  biproduct.lift fun p => biproduct.π f p.1 ⊗ₘ biproduct.π g p.2

@[reassoc (attr := simp)] lemma tensor_ι_biproductTensorHom (i : I) (j : J) :
    (biproduct.ι f i ⊗ₘ biproduct.ι g j) ≫ biproductTensorHom f g =
      biproduct.ι (fun p : I × J => f p.1 ⊗ g p.2) (i,j) := by
  apply biproduct.hom_ext
  rintro ⟨k,l⟩
  simp only [assoc, biproductTensorHom, biproduct.lift_π,
    MonoidalCategory.tensorHom_comp_tensorHom]
  by_cases hi : i = k
  · subst k
    by_cases hj : j = l
    · subst l; simp
    · have hp : (i,j) ≠ (i,l) := fun he => hj (congrArg Prod.snd he)
      simp [biproduct.ι_π_ne _ hj, biproduct.ι_π_ne _ hp]
  · have hp : (i,j) ≠ (k,l) := fun he => hi (congrArg Prod.fst he)
    simp [biproduct.ι_π_ne _ hi, biproduct.ι_π_ne _ hp]

def biproductTensorIso : (⨁ f) ⊗ (⨁ g) ≅ ⨁ (fun p : I × J => f p.1 ⊗ g p.2) where
  hom := biproductTensorHom f g
  inv := biproduct.desc fun p => biproduct.ι f p.1 ⊗ₘ biproduct.ι g p.2
  hom_inv_id := by
    apply tensorBiproduct_hom_ext
    intro i j
    simp
  inv_hom_id := by
    apply biproduct.hom_ext'
    rintro ⟨i,j⟩
    simp

@[reassoc (attr := simp)] lemma tensor_ι_biproductTensorIso_hom (i : I) (j : J) :
    (biproduct.ι f i ⊗ₘ biproduct.ι g j) ≫ (biproductTensorIso f g).hom =
      biproduct.ι (fun p : I × J => f p.1 ⊗ g p.2) (i,j) :=
  tensor_ι_biproductTensorHom f g i j
/-- Triple tensors of the actual injections jointly detect morphisms. -/
lemma tripleTensorBiproduct_hom_ext {K : Type} [Fintype K] (h : K → E)
    {P : E} {a b : ((⨁ f) ⊗ (⨁ g)) ⊗ (⨁ h) ⟶ P}
    (he : ∀ i j k, ((biproduct.ι f i ⊗ₘ biproduct.ι g j) ⊗ₘ biproduct.ι h k) ≫ a =
      ((biproduct.ι f i ⊗ₘ biproduct.ι g j) ⊗ₘ biproduct.ι h k) ≫ b) : a = b := by
  apply (cancel_epi ((biproductTensorIso f g).inv ▷ (⨁ h))).1
  apply tensorBiproduct_hom_ext
  rintro ⟨i,j⟩ k
  simp only [← assoc, ← MonoidalCategory.tensorHom_id,
    MonoidalCategory.tensorHom_comp_tensorHom, id_comp]
  simpa [biproductTensorIso] using he i j k

end BiprodTensor

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  {E : Type u'} [Category.{v'} E] [Preadditive E] [Linear ℂ E]
  [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalLinear ℂ E]
  [HasFiniteBiproducts E] (F : C ⥤ E) [F.Additive] [F.Linear ℂ] [F.Monoidal]

/-- The tensorator of the actual additive-envelope lift. -/
def liftTensorIso (X Y : Mat_ C) :
    (linearMatLift F).obj X ⊗ (linearMatLift F).obj Y ≅
      (linearMatLift F).obj (X ⊗ Y) :=
  biproductTensorIso (fun i => F.obj (X.X i)) (fun j => F.obj (Y.X j)) ≪≫
    biproduct.mapIso (fun p : X.ι × Y.ι => Functor.Monoidal.μIso F (X.X p.1) (Y.X p.2))

@[reassoc (attr := simp)] lemma tensor_ι_liftTensorIso (X Y : Mat_ C) (i : X.ι) (j : Y.ι) :
    (biproduct.ι (fun i => F.obj (X.X i)) i ⊗ₘ biproduct.ι (fun j => F.obj (Y.X j)) j) ≫
      (liftTensorIso F X Y).hom =
    Functor.LaxMonoidal.μ F (X.X i) (Y.X j) ≫
      biproduct.ι (fun p : X.ι × Y.ι => F.obj (X.X p.1 ⊗ Y.X p.2)) (i,j) := by
  simp [liftTensorIso]

/-- The unit tensorator is the strong unit map followed by the singleton
biproduct identification. -/
def liftUnitIso : 𝟙_ E ≅ (linearMatLift F).obj (𝟙_ (Mat_ C)) :=
  Functor.Monoidal.εIso F ≪≫ (biproductUniqueIso (fun _ : PUnit => F.obj (𝟙_ C))).symm

@[reassoc (attr := simp)] lemma lift_ι_map {X Y : Mat_ C} (f : X ⟶ Y) (i : X.ι) :
    biproduct.ι (fun i => F.obj (X.X i)) i ≫ (linearMatLift F).map f =
      ∑ j, F.map (f i j) ≫ biproduct.ι (fun j => F.obj (Y.X j)) j := by
  apply biproduct.hom_ext
  intro j
  simp [linearMatLift, Preadditive.sum_comp, biproduct.ι_π, comp_dite]

@[reassoc (attr := simp)] lemma lift_ι_map_indexEquivHom {X Y : Mat_ C}
    (e : X.ι ≃ Y.ι) (f : ∀ i, X.X i ⟶ Y.X (e i)) (i : X.ι) :
    biproduct.ι (fun i => F.obj (X.X i)) i ≫ (linearMatLift F).map (indexEquivHom e f) =
      F.map (f i) ≫ biproduct.ι (fun j => F.obj (Y.X j)) (e i) := by
  rw [lift_ι_map]
  simp [indexEquivHom, dite_comp]

/-- Naturality of the actual tensorator for arbitrary matrices. -/
lemma liftTensorIso_natural {X X' Y Y' : Mat_ C} (f : X ⟶ X') (g : Y ⟶ Y') :
    ((linearMatLift F).map f ⊗ₘ (linearMatLift F).map g) ≫ (liftTensorIso F X' Y').hom =
      (liftTensorIso F X Y).hom ≫ (linearMatLift F).map (f ⊗ₘ g) := by
  apply tensorBiproduct_hom_ext
  intro i j
  calc
    _ = ∑ k, ∑ l, Functor.LaxMonoidal.μ F (X.X i) (Y.X j) ≫
        F.map (f i k ⊗ₘ g j l) ≫
          biproduct.ι (fun p : X'.ι × Y'.ι => F.obj (X'.X p.1 ⊗ Y'.X p.2)) (k,l) := by
      rw [← assoc, MonoidalCategory.tensorHom_comp_tensorHom, lift_ι_map, lift_ι_map]
      simp only [sum_tensor, tensor_sum, Preadditive.sum_comp,
        ← MonoidalCategory.tensorHom_comp_tensorHom, assoc]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      calc
        _ = (F.map (f i k) ⊗ₘ F.map (g j l)) ≫
            Functor.LaxMonoidal.μ F (X'.X k) (Y'.X l) ≫
              biproduct.ι (fun p : X'.ι × Y'.ι => F.obj (X'.X p.1 ⊗ Y'.X p.2)) (k,l) :=
          congrArg (fun z => (F.map (f i k) ⊗ₘ F.map (g j l)) ≫ z)
            (tensor_ι_liftTensorIso F X' Y' k l)
        _ = _ := Functor.LaxMonoidal.μ_natural_assoc F (f i k) (g j l) _
    _ = _ := by
      rw [tensor_ι_liftTensorIso_assoc F X Y]
      have hh := congrArg (fun z => Functor.LaxMonoidal.μ F (X.X i) (Y.X j) ≫ z)
        (lift_ι_map F (f ⊗ₘ g) (i,j))
      change Functor.LaxMonoidal.μ F (X.X i) (Y.X j) ≫
          biproduct.ι (fun p : X.ι × Y.ι => F.obj (X.X p.1 ⊗ Y.X p.2)) (i,j) ≫
          (linearMatLift F).map (f ⊗ₘ g) =
        Functor.LaxMonoidal.μ F (X.X i) (Y.X j) ≫
          ∑ p : X'.ι × Y'.ι, F.map (f i p.1 ⊗ₘ g j p.2) ≫
            biproduct.ι (fun p : X'.ι × Y'.ι => F.obj (X'.X p.1 ⊗ Y'.X p.2)) p at hh
      simpa only [Fintype.sum_prod_type, Preadditive.comp_sum] using hh.symm

/-- Collapse the left-associated tensorator composite on actual generators. -/
@[reassoc] lemma liftTensorIso_left_generator (X Y Z : Mat_ C) (i : X.ι) (j : Y.ι) (k : Z.ι) :
    ((biproduct.ι (fun i => F.obj (X.X i)) i ⊗ₘ
      biproduct.ι (fun j => F.obj (Y.X j)) j) ⊗ₘ
      biproduct.ι (fun k => F.obj (Z.X k)) k) ≫
      (liftTensorIso F X Y).hom ▷ (linearMatLift F).obj Z ≫
      (liftTensorIso F (X ⊗ Y) Z).hom =
    Functor.LaxMonoidal.μ F (X.X i) (Y.X j) ▷ F.obj (Z.X k) ≫
      Functor.LaxMonoidal.μ F (X.X i ⊗ Y.X j) (Z.X k) ≫
      biproduct.ι (fun p : (X.ι × Y.ι) × Z.ι =>
        F.obj ((X.X p.1.1 ⊗ Y.X p.1.2) ⊗ Z.X p.2)) ((i,j),k) := by
  dsimp only [linearMatLift]
  rw [← MonoidalCategory.tensorHom_id, ← assoc,
    MonoidalCategory.tensorHom_comp_tensorHom, comp_id, tensor_ι_liftTensorIso F X Y]
  calc
    _ = Functor.LaxMonoidal.μ F (X.X i) (Y.X j) ▷ F.obj (Z.X k) ≫
        (biproduct.ι (fun p : X.ι × Y.ι => F.obj (X.X p.1 ⊗ Y.X p.2)) (i,j) ⊗ₘ
          biproduct.ι (fun k => F.obj (Z.X k)) k) ≫
        (liftTensorIso F (X ⊗ Y) Z).hom := by
      simp only [tensorHom_def, comp_whiskerRight, assoc]
      rfl
    _ = _ := congrArg (fun z => Functor.LaxMonoidal.μ F (X.X i) (Y.X j) ▷ F.obj (Z.X k) ≫ z)
      (tensor_ι_liftTensorIso F (X ⊗ Y) Z (i,j) k)

/-- Collapse the right-associated tensorator composite on actual generators. -/
lemma liftTensorIso_right_generator (X Y Z : Mat_ C) (i : X.ι) (j : Y.ι) (k : Z.ι) :
    ((biproduct.ι (fun i => F.obj (X.X i)) i ⊗ₘ
      biproduct.ι (fun j => F.obj (Y.X j)) j) ⊗ₘ
      biproduct.ι (fun k => F.obj (Z.X k)) k) ≫
      (α_ ((linearMatLift F).obj X) ((linearMatLift F).obj Y)
        ((linearMatLift F).obj Z)).hom ≫
      (linearMatLift F).obj X ◁ (liftTensorIso F Y Z).hom ≫
      (liftTensorIso F X (Y ⊗ Z)).hom =
    (α_ (F.obj (X.X i)) (F.obj (Y.X j)) (F.obj (Z.X k))).hom ≫
      F.obj (X.X i) ◁ Functor.LaxMonoidal.μ F (Y.X j) (Z.X k) ≫
      Functor.LaxMonoidal.μ F (X.X i) (Y.X j ⊗ Z.X k) ≫
      biproduct.ι (fun p : X.ι × (Y.ι × Z.ι) =>
        F.obj (X.X p.1 ⊗ (Y.X p.2.1 ⊗ Z.X p.2.2))) (i,(j,k)) := by
  dsimp only [linearMatLift]
  rw [MonoidalCategory.associator_naturality_assoc]
  rw [← MonoidalCategory.id_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom_assoc, comp_id, tensor_ι_liftTensorIso F Y Z]
  calc
    _ = (α_ (F.obj (X.X i)) (F.obj (Y.X j)) (F.obj (Z.X k))).hom ≫
        F.obj (X.X i) ◁ Functor.LaxMonoidal.μ F (Y.X j) (Z.X k) ≫
        (biproduct.ι (fun i => F.obj (X.X i)) i ⊗ₘ
          biproduct.ι (fun p : Y.ι × Z.ι => F.obj (Y.X p.1 ⊗ Z.X p.2)) (j,k)) ≫
        (liftTensorIso F X (Y ⊗ Z)).hom := by
      simp only [tensorHom_def', whiskerLeft_comp, assoc]
      rfl
    _ = _ := congrArg (fun z =>
        (α_ (F.obj (X.X i)) (F.obj (Y.X j)) (F.obj (Z.X k))).hom ≫
        F.obj (X.X i) ◁ Functor.LaxMonoidal.μ F (Y.X j) (Z.X k) ≫ z)
      (tensor_ι_liftTensorIso F X (Y ⊗ Z) i (j,k))

@[simp] lemma liftUnitIso_hom : (liftUnitIso F).hom =
    Functor.LaxMonoidal.ε F ≫
      biproduct.ι (fun _ : PUnit => F.obj (𝟙_ C)) PUnit.unit := by
  simp only [liftUnitIso, Iso.trans_hom, Iso.symm_hom, Functor.Monoidal.εIso_hom,
    biproductUniqueIso, Iso.symm_inv, biproduct.uniqueUpToIso_hom]
  congr 1
  apply biproduct.hom_ext
  rintro ⟨⟩
  simp [limitBiconeOfUnique]

end Paper18.Category.LinearMat
