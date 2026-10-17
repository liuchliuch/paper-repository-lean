import Paper18.Category.LinearMatMonoidalLiftCoherence
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-! # Extending actual natural isomorphisms from singleton matrices -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u v' u'
namespace Paper18.Category.DeligneTensorProductMap
variable {C : Type u} [Category.{v} C] [Preadditive C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasFiniteBiproducts D]

/-- The actual inclusion of a singleton summand into a matrix object. -/
def matInclusion (M : Mat_ C) (i : M.ι) : (Mat_.embedding C).obj (M.X i) ⟶ M :=
  biproduct.ι (fun i => (Mat_.embedding C).obj (M.X i)) i ≫
    (Mat_.isoBiproductEmbedding M).inv

@[simp] lemma matInclusion_singleton (X : C) :
    matInclusion ((Mat_.embedding C).obj X) PUnit.unit = 𝟙 _ := by
  dsimp only [matInclusion, Mat_.isoBiproductEmbedding]
  rw [biproduct.ι_desc]
  ext ⟨⟩ ⟨⟩
  simp

variable (F G : Mat_ C ⥤ D) [F.Additive] [G.Additive]

/-- The image decomposition with independent source and target Hom universes. -/
def objDecomp (M : Mat_ C) : F.obj M ≅
    ⨁ fun i => F.obj ((Mat_.embedding C).obj (M.X i)) :=
  F.mapIso (Mat_.isoBiproductEmbedding M) ≪≫ F.mapBiproduct _

@[reassoc (attr := simp)] lemma objDecomp_hom_π (M : Mat_ C) (i : M.ι) :
    (objDecomp F M).hom ≫ biproduct.π _ i =
      F.map ((Mat_.isoBiproductEmbedding M).hom ≫ biproduct.π _ i) := by
  dsimp [objDecomp]
  rw [biproduct.lift_π, Category.assoc]
  erw [biproduct.lift_π, ← F.map_comp]
  simp

@[reassoc (attr := simp)] lemma ι_objDecomp_inv (M : Mat_ C) (i : M.ι) :
    biproduct.ι _ i ≫ (objDecomp F M).inv = F.map (matInclusion M i) := by
  dsimp [objDecomp, Functor.mapBiproduct, Functor.mapBicone, matInclusion]
  simp only [biproduct.ι_desc, biproduct.ι_desc_assoc, ← F.map_comp]

@[reassoc] lemma objDecomp_naturality {M N : Mat_ C} (f : M ⟶ N) :
    F.map f ≫ (objDecomp F N).hom = (objDecomp F M).hom ≫
      biproduct.matrix (fun i j => F.map ((Mat_.embedding C).map (f i j))) := by
  ext i : 1
  simp only [Category.assoc, objDecomp_hom_π, Mat_.isoBiproductEmbedding_hom,
    Mat_.embedding_obj_ι, Mat_.embedding_obj_X, biproduct.lift_π, biproduct.matrix_π,
    ← cancel_epi (objDecomp F M).inv, Iso.inv_hom_id_assoc]
  ext j : 1
  simp only [ι_objDecomp_inv_assoc, matInclusion, Mat_.isoBiproductEmbedding_inv,
    biproduct.ι_desc, ← F.map_comp]
  congr 1
  funext ⟨⟩ ⟨⟩
  simp [Mat_.comp_apply, dite_comp, comp_dite]

@[reassoc] lemma objDecomp_naturality' {M N : Mat_ C} (f : M ⟶ N) :
    (objDecomp F M).inv ≫ F.map f =
      biproduct.matrix (fun i j => F.map ((Mat_.embedding C).map (f i j))) ≫
        (objDecomp F N).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, objDecomp_naturality]

@[reassoc] lemma map_matInclusion (M : Mat_ C) (i : M.ι) :
    F.map (matInclusion M i) =
      biproduct.ι (fun i => F.obj ((Mat_.embedding C).obj (M.X i))) i ≫
        (objDecomp F M).inv :=
  (ι_objDecomp_inv F M i).symm

/-- The extension uses the actual biproduct decompositions of both functor images. -/
def extendIso (α : Mat_.embedding C ⋙ F ≅ Mat_.embedding C ⋙ G) : F ≅ G :=
  NatIso.ofComponents
    (fun M => objDecomp F M ≪≫
      biproduct.mapIso (fun i => α.app (M.X i)) ≪≫
        (objDecomp G M).symm)
    (fun f => by
      dsimp only [Iso.trans_hom, Iso.symm_hom, biproduct.mapIso_hom]
      simp only [objDecomp_naturality_assoc,
        biproduct.matrix_map_assoc, Category.assoc,
        objDecomp_naturality', biproduct.map_matrix_assoc]
      congr 3
      ext i j
      exact α.hom.naturality (f i j))

@[reassoc] lemma map_matInclusion_extendIso
    (α : Mat_.embedding C ⋙ F ≅ Mat_.embedding C ⋙ G) (M : Mat_ C) (i : M.ι) :
    F.map (matInclusion M i) ≫ (extendIso F G α).hom.app M =
      (α.app (M.X i)).hom ≫ G.map (matInclusion M i) := by
  rw [map_matInclusion]
  dsimp only [extendIso, NatIso.ofComponents_hom_app, Iso.trans_hom, Iso.symm_hom,
    biproduct.mapIso_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, biproduct.ι_map_assoc]
  rw [map_matInclusion]
  rfl

@[simp] lemma extendIso_hom_singleton
    (α : Mat_.embedding C ⋙ F ≅ Mat_.embedding C ⋙ G) (X : C) :
    (extendIso F G α).hom.app ((Mat_.embedding C).obj X) = (α.app X).hom := by
  have h := map_matInclusion_extendIso F G α ((Mat_.embedding C).obj X) PUnit.unit
  simp only [matInclusion_singleton, F.map_id, G.map_id,
    Category.id_comp, Mat_.embedding_obj_X] at h
  erw [Category.comp_id] at h
  exact h

section Monoidal
variable [MonoidalCategory C] [MonoidalPreadditive C]
  [MonoidalCategory D] [MonoidalPreadditive D]
  [F.Monoidal] [G.Monoidal]

/-- Tensor products of the mapped actual singleton inclusions jointly
detect morphisms from the tensor product of two functor images. -/
lemma mapped_tensor_hom_ext (X Y : Mat_ C) {P : D}
    {a b : F.obj X ⊗ F.obj Y ⟶ P}
    (h : ∀ i j, (F.map (matInclusion X i) ⊗ₘ F.map (matInclusion Y j)) ≫ a =
      (F.map (matInclusion X i) ⊗ₘ F.map (matInclusion Y j)) ≫ b) : a = b := by
  apply (cancel_epi
    (((objDecomp F X).symm ⊗ᵢ
      (objDecomp F Y).symm).hom)).mp
  apply LinearMat.tensorBiproduct_hom_ext
  intro i j
  simpa only [tensorIso_hom, Iso.symm_hom, ← Category.assoc,
    tensorHom_comp_tensorHom, ← map_matInclusion] using h i j

/-- Actual monoidality is detected after the singleton strong monoidal
embedding, because all matrix objects are actual finite biproducts. -/
theorem isMonoidal_of_singletons (τ : F ⟶ G)
    [NatTrans.IsMonoidal (Functor.whiskerLeft (Mat_.embedding C) τ)] :
    NatTrans.IsMonoidal τ where
  unit := by
    have h := NatTrans.IsMonoidal.unit
      (τ := Functor.whiskerLeft (Mat_.embedding C) τ)
    have he : Functor.LaxMonoidal.ε (Mat_.embedding C) = 𝟙 (𝟙_ (Mat_ C)) := rfl
    simpa only [Functor.LaxMonoidal.comp_ε, Functor.comp_obj,
      Functor.whiskerLeft_app, he, F.map_id, G.map_id, Category.comp_id] using h
  tensor X Y := by
    apply mapped_tensor_hom_ext F X Y
    intro i j
    let A := (Mat_.embedding C).obj (X.X i)
    let B := (Mat_.embedding C).obj (Y.X j)
    have hs : Functor.LaxMonoidal.μ F A B ≫ τ.app (A ⊗ B) =
        (τ.app A ⊗ₘ τ.app B) ≫ Functor.LaxMonoidal.μ G A B := by
      have h := NatTrans.IsMonoidal.tensor
        (τ := Functor.whiskerLeft (Mat_.embedding C) τ) (X.X i) (Y.X j)
      dsimp only [Functor.LaxMonoidal.comp_μ, Functor.whiskerLeft_app,
        Functor.comp_obj] at h
      rw [Category.assoc, τ.naturality] at h
      exact (cancel_mono (G.map (Functor.LaxMonoidal.μ (Mat_.embedding C)
        (X.X i) (Y.X j)))).mp (by simpa only [Category.assoc] using h)
    rw [Functor.LaxMonoidal.μ_natural_assoc, τ.naturality, ← Category.assoc, hs]
    rw [Category.assoc, ← Functor.LaxMonoidal.μ_natural, ← Category.assoc]
    have ht := congrArg₂ (fun a b => a ⊗ₘ b)
      (τ.naturality (matInclusion X i)) (τ.naturality (matInclusion Y j))
    dsimp only at ht
    rw [← tensorHom_comp_tensorHom, ← tensorHom_comp_tensorHom] at ht
    simpa only [Category.assoc] using
      congrArg (fun a => a ≫ Functor.LaxMonoidal.μ G X Y) ht.symm

end Monoidal
end Paper18.Category.DeligneTensorProductMap
