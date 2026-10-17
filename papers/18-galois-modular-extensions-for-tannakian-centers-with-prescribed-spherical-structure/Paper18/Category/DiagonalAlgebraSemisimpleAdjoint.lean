import Paper18.Category.SemisimpleSplitting
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Actual right adjoints of finite semisimple linear functors

A genuine representing object is assembled from bases of the actual Hom
spaces out of images of simple representatives. Its Hom equivalence and
naturality are proved from actual simple decompositions.
-/
noncomputable section
set_option maxHeartbeats 1000000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open scoped BigOperators
universe v u w v' u'
namespace Paper18.Category.DiagonalAlgebra
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [HasFiniteBiproducts D] [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (F : C ⥤ D) [F.Additive] [F.Linear ℂ]

/-- Linearity supplies naturality with respect to all simple-simple maps. -/
lemma imageSimpleFamily_natural {X : C} {Y : D}
    (φ : ∀ i, (S.simpleObject i ⟶ X) →ₗ[ℂ] (F.obj (S.simpleObject i) ⟶ Y))
    {i j : ι} (a : S.simpleObject i ⟶ S.simpleObject j) (b : S.simpleObject j ⟶ X) :
    F.map a ≫ φ j b = φ i (a ≫ b) := by
  by_cases hij : i = j
  · subst j
    obtain ⟨c, rfl⟩ := CategoryTheory.endomorphism_simple_eq_smul_id ℂ a
    simp
  · have ha : a = 0 := by
      by_contra h
      letI := CategoryTheory.isIso_of_hom_simple h
      exact hij (S.iso_injective i j ⟨asIso a⟩)
    simp [ha]

/-- Assemble an actual map out of an image object from its linear
values on simple inclusions. -/
def homFromImageSimpleFamily {X : C} {Y : D}
    (φ : ∀ i, (S.simpleObject i ⟶ X) →ₗ[ℂ] (F.obj (S.simpleObject i) ⟶ Y)) : F.obj X ⟶ Y :=
  F.map (S.decomposition X).hom ≫
    (F.mapBiproduct (fun a : Fin (S.length X) => S.simpleObject (S.label X a))).hom ≫
      biproduct.desc (fun a : Fin (S.length X) => φ (S.label X a)
        (biproduct.ι (fun b : Fin (S.length X) => S.simpleObject (S.label X b)) a ≫
          (S.decomposition X).inv))

lemma map_comp_homFromImageSimpleFamily {X : C} {Y : D}
    (φ : ∀ i, (S.simpleObject i ⟶ X) →ₗ[ℂ] (F.obj (S.simpleObject i) ⟶ Y))
    (i : ι) (g : S.simpleObject i ⟶ X) :
    F.map g ≫ homFromImageSimpleFamily S F φ = φ i g := by
  let f : Fin (S.length X) → C := fun a => S.simpleObject (S.label X a)
  have htotal : ∑ a : Fin (S.length X),
      (g ≫ (S.decomposition X).hom ≫ biproduct.π f a) ≫
        (biproduct.ι f a ≫ (S.decomposition X).inv) = g := by
    simp only [← Category.assoc, ← Preadditive.sum_comp]
    simp only [Category.assoc, ← Preadditive.comp_sum, biproduct.total]
    change g ≫ (S.decomposition X).hom ≫ 𝟙 _ ≫ (S.decomposition X).inv = g
    simp only [id_comp, Iso.hom_inv_id, comp_id]
  calc
    _ = ∑ a : Fin (S.length X),
        F.map (g ≫ (S.decomposition X).hom ≫ biproduct.π f a) ≫
          φ (S.label X a) (biproduct.ι f a ≫ (S.decomposition X).inv) := by
      unfold homFromImageSimpleFamily
      rw [biproduct.desc_eq]
      simp only [Preadditive.comp_sum, Functor.map_comp, Category.assoc]
      apply Finset.sum_congr rfl
      intro a _
      simp only [Functor.mapBiproduct_hom]
      erw [biproduct.lift_π_assoc]
    _ = ∑ a : Fin (S.length X), φ i
        ((g ≫ (S.decomposition X).hom ≫ biproduct.π f a) ≫
          (biproduct.ι f a ≫ (S.decomposition X).inv)) := by
      apply Finset.sum_congr rfl
      intro a _
      exact imageSimpleFamily_natural S F φ _ _
    _ = φ i g := by rw [← map_sum, htotal]

/-- Actual mapped simple inclusions detect maps out of image objects. -/
lemma image_hom_ext {X : C} {Y : D} (f g : F.obj X ⟶ Y)
    (h : ∀ i (a : S.simpleObject i ⟶ X), F.map a ≫ f = F.map a ≫ g) : f = g := by
  apply (cancel_epi (F.map (S.decomposition X).inv)).mp
  apply (cancel_epi (F.mapBiproduct
    (fun a : Fin (S.length X) => S.simpleObject (S.label X a))).inv).mp
  apply biproduct.hom_ext'
  intro a
  have hh := h (S.label X a) (biproduct.ι
    (fun b : Fin (S.length X) => S.simpleObject (S.label X b)) a ≫ (S.decomposition X).inv)
  simpa only [Category.assoc, Functor.map_comp, Functor.mapBiproduct_inv, biproduct.ι_desc_assoc] using hh

/-- A basis index in the actual target Hom spaces. -/
abbrev RightAdjointIndex (Y : D) := Σ i : ι, Fin (Module.finrank ℂ (F.obj (S.simpleObject i) ⟶ Y))

/-- A genuine finite biproduct representing the right-adjoint object. -/
def semisimpleRightAdjointObj (Y : D) : C :=
  ⨁ fun a : RightAdjointIndex S F Y => S.simpleObject a.1

lemma finrank_rightAdjointObj (Y : D) (i : ι) :
    Module.finrank ℂ (S.simpleObject i ⟶ semisimpleRightAdjointObj S F Y) =
      Module.finrank ℂ (F.obj (S.simpleObject i) ⟶ Y) := by
  unfold semisimpleRightAdjointObj
  rw [finrank_hom_biproduct]
  simp only [RightAdjointIndex, Fintype.sum_sigma, S.finrank_simple_hom_simple]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

/-- Actual basis coordinates in the representing object. -/
def rightAdjointSimpleEquiv (Y : D) (i : ι) :
    (S.simpleObject i ⟶ semisimpleRightAdjointObj S F Y) ≃ₗ[ℂ]
      (F.obj (S.simpleObject i) ⟶ Y) :=
  Classical.choice (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
    (finrank_rightAdjointObj S F Y i))

/-- Transpose an actual target morphism into the representing object. -/
def semisimpleAdjointTranspose {X : C} {Y : D} (g : F.obj X ⟶ Y) :
    X ⟶ semisimpleRightAdjointObj S F Y :=
  S.homFromSimpleFamily (fun i => (rightAdjointSimpleEquiv S F Y i).symm.toLinearMap.comp
    ((CategoryTheory.Linear.rightComp ℂ (F.obj (S.simpleObject i)) g).comp
      (F.mapLinearMap ℂ)))

/-- Evaluate an actual map to the representing object. -/
def semisimpleAdjointEvaluate {X : C} {Y : D} (h : X ⟶ semisimpleRightAdjointObj S F Y) :
    F.obj X ⟶ Y :=
  homFromImageSimpleFamily S F (fun i => (rightAdjointSimpleEquiv S F Y i).toLinearMap.comp
    (CategoryTheory.Linear.rightComp ℂ (S.simpleObject i) h))

@[simp] lemma comp_semisimpleAdjointTranspose {X : C} {Y : D} (g : F.obj X ⟶ Y)
    (i : ι) (a : S.simpleObject i ⟶ X) :
    a ≫ semisimpleAdjointTranspose S F g =
      (rightAdjointSimpleEquiv S F Y i).symm (F.map a ≫ g) :=
  by
    unfold semisimpleAdjointTranspose
    exact S.comp_homFromSimpleFamily _ i a

@[simp] lemma map_comp_semisimpleAdjointEvaluate {X : C} {Y : D}
    (h : X ⟶ semisimpleRightAdjointObj S F Y) (i : ι) (a : S.simpleObject i ⟶ X) :
    F.map a ≫ semisimpleAdjointEvaluate S F h = rightAdjointSimpleEquiv S F Y i (a ≫ h) :=
  map_comp_homFromImageSimpleFamily S F _ i a

/-- The actual representing Hom correspondence. -/
def semisimpleAdjointHomEquiv (X : C) (Y : D) :
    (F.obj X ⟶ Y) ≃ (X ⟶ semisimpleRightAdjointObj S F Y) where
  toFun := semisimpleAdjointTranspose S F
  invFun := semisimpleAdjointEvaluate S F
  left_inv g := by
    apply image_hom_ext S F
    intro i a
    rw [map_comp_semisimpleAdjointEvaluate, comp_semisimpleAdjointTranspose,
      LinearEquiv.apply_symm_apply]
  right_inv h := by
    apply S.hom_ext_simples
    intro i a
    rw [comp_semisimpleAdjointTranspose, map_comp_semisimpleAdjointEvaluate,
      LinearEquiv.symm_apply_apply]

/-- The representing Hom equivalence respects the actual complex vector
space structures. -/
def semisimpleAdjointHomLinearEquiv (X : C) (Y : D) :
    (F.obj X ⟶ Y) ≃ₗ[ℂ] (X ⟶ semisimpleRightAdjointObj S F Y) where
  toEquiv := semisimpleAdjointHomEquiv S F X Y
  map_add' g h := by
    apply S.hom_ext_simples
    intro i a
    change a ≫ semisimpleAdjointTranspose S F (g + h) =
      a ≫ (semisimpleAdjointTranspose S F g + semisimpleAdjointTranspose S F h)
    simp only [Preadditive.comp_add, comp_semisimpleAdjointTranspose, map_add]
  map_smul' c g := by
    apply S.hom_ext_simples
    intro i a
    change a ≫ semisimpleAdjointTranspose S F (c • g) =
      a ≫ (c • semisimpleAdjointTranspose S F g)
    simp only [Linear.comp_smul, comp_semisimpleAdjointTranspose, map_smul]

lemma semisimpleAdjointHomEquiv_naturality {X X' : C} (Y : D)
    (f : X' ⟶ X) (g : F.obj X ⟶ Y) :
    semisimpleAdjointHomEquiv S F X' Y (F.map f ≫ g) =
      f ≫ semisimpleAdjointHomEquiv S F X Y g := by
  apply S.hom_ext_simples
  intro i a
  change a ≫ semisimpleAdjointTranspose S F _ = a ≫ f ≫ semisimpleAdjointTranspose S F g
  rw [← assoc a f]
  rw [comp_semisimpleAdjointTranspose, comp_semisimpleAdjointTranspose]
  simp only [Functor.map_comp, Category.assoc]

/-- The actual right-adjoint functor, derived from the finite semisimple
representing objects and their proved Hom equivalences. -/
def semisimpleRightAdjoint : D ⥤ C :=
  Adjunction.rightAdjointOfEquiv (semisimpleAdjointHomEquiv S F)
    (fun _ _ Y f g => semisimpleAdjointHomEquiv_naturality S F Y f g)

/-- The actual right adjunction with no adjoint-existence premise. -/
def semisimpleRightAdjunction : F ⊣ semisimpleRightAdjoint S F :=
  Adjunction.adjunctionOfEquivRight (semisimpleAdjointHomEquiv S F)
    (fun _ _ Y f g => semisimpleAdjointHomEquiv_naturality S F Y f g)

@[simp] lemma semisimpleRightAdjoint_obj (Y : D) :
    (semisimpleRightAdjoint S F).obj Y = semisimpleRightAdjointObj S F Y := rfl

@[simp] lemma semisimpleRightAdjunction_homEquiv (X : C) (Y : D) :
    (semisimpleRightAdjunction S F).homEquiv X Y = semisimpleAdjointHomEquiv S F X Y := by
  unfold semisimpleRightAdjunction Adjunction.adjunctionOfEquivRight
  rw [Adjunction.mkOfHomEquiv_homEquiv]

lemma semisimpleRightAdjoint_map {Y Y' : D} (g : Y ⟶ Y') :
    (semisimpleRightAdjoint S F).map g =
      semisimpleAdjointHomEquiv S F (semisimpleRightAdjointObj S F Y) Y'
        ((semisimpleAdjointHomEquiv S F (semisimpleRightAdjointObj S F Y) Y).symm
          (𝟙 _) ≫ g) := rfl

instance semisimpleRightAdjoint_additive : (semisimpleRightAdjoint S F).Additive where
  map_add {Y Y'} g h := by
    simp only [semisimpleRightAdjoint_map, Preadditive.comp_add]
    exact (semisimpleAdjointHomLinearEquiv S F _ _).map_add _ _

instance semisimpleRightAdjoint_linear : (semisimpleRightAdjoint S F).Linear ℂ where
  map_smul g c := by
    simp only [semisimpleRightAdjoint_map, Linear.comp_smul]
    exact (semisimpleAdjointHomLinearEquiv S F _ _).map_smul c _

end Paper18.Category.DiagonalAlgebra
