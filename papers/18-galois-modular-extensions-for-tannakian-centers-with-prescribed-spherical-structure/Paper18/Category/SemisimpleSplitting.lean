import Paper18.Category.Multiplicity
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Splitting morphisms in an actual finite semisimple category

The simple-Hom functor is full: a family of linear maps on the Hom spaces
out of simple representatives is represented by a categorical morphism.
Splittings of monomorphisms follow from linear left inverses.
-/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category
namespace FiniteSemisimpleSkeleton
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- Every linear family on simple Hom spaces automatically commutes with
morphisms between the chosen simple representatives, by Schur's lemma. -/
lemma simpleHomFamily_natural {X Y : C}
    (φ : ∀ i, (S.simpleObject i ⟶ X) →ₗ[ℂ] (S.simpleObject i ⟶ Y))
    {i j : ι} (a : S.simpleObject i ⟶ S.simpleObject j)
    (b : S.simpleObject j ⟶ X) : a ≫ φ j b = φ i (a ≫ b) := by
  by_cases hij : i = j
  · subst j
    obtain ⟨c, rfl⟩ := CategoryTheory.endomorphism_simple_eq_smul_id ℂ a
    simp
  · have ha : a = 0 := by
      by_contra h
      letI := CategoryTheory.isIso_of_hom_simple h
      exact hij (S.iso_injective i j ⟨asIso a⟩)
    simp [ha]

/-- A categorical morphism representing a family of linear maps on simple
Hom spaces; it is constructed from actual biproduct inclusions. -/
def homFromSimpleFamily {X Y : C}
    (φ : ∀ i, (S.simpleObject i ⟶ X) →ₗ[ℂ] (S.simpleObject i ⟶ Y)) : X ⟶ Y :=
  (S.decomposition X).hom ≫ biproduct.desc
    (fun a : Fin (S.length X) => φ (S.label X a)
      (biproduct.ι (fun b : Fin (S.length X) => S.simpleObject (S.label X b)) a ≫
        (S.decomposition X).inv))

lemma comp_homFromSimpleFamily {X Y : C}
    (φ : ∀ i, (S.simpleObject i ⟶ X) →ₗ[ℂ] (S.simpleObject i ⟶ Y))
    (i : ι) (g : S.simpleObject i ⟶ X) :
    g ≫ S.homFromSimpleFamily φ = φ i g := by
  let f : Fin (S.length X) → C := fun a => S.simpleObject (S.label X a)
  have htotal : ∑ a : Fin (S.length X),
      (g ≫ (S.decomposition X).hom ≫ biproduct.π f a) ≫
        (biproduct.ι f a ≫ (S.decomposition X).inv) = g := by
    simp only [← Category.assoc, ← Preadditive.sum_comp]
    simp only [Category.assoc, ← Preadditive.comp_sum, biproduct.total]
    change g ≫ (S.decomposition X).hom ≫ 𝟙 _ ≫ (S.decomposition X).inv = g
    simp only [Category.id_comp, Iso.hom_inv_id, Category.comp_id]
  calc
    g ≫ S.homFromSimpleFamily φ =
        ∑ a : Fin (S.length X),
          (g ≫ (S.decomposition X).hom ≫ biproduct.π f a) ≫
            φ (S.label X a) (biproduct.ι f a ≫ (S.decomposition X).inv) := by
      unfold homFromSimpleFamily
      rw [biproduct.desc_eq]
      simp only [Preadditive.comp_sum, Category.assoc]
      rfl
    _ = ∑ a : Fin (S.length X), φ i
        ((g ≫ (S.decomposition X).hom ≫ biproduct.π f a) ≫
          (biproduct.ι f a ≫ (S.decomposition X).inv)) := by
      apply Finset.sum_congr rfl
      intro a _
      exact S.simpleHomFamily_natural φ _ _
    _ = φ i g := by rw [← map_sum, htotal]

omit [Linear ℂ C] [HasKernels C] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] in
/-- Morphisms are determined by precomposition with maps out of the simple
representatives. -/
lemma hom_ext_simples {X Y : C} (f g : X ⟶ Y)
    (h : ∀ i (a : S.simpleObject i ⟶ X), a ≫ f = a ≫ g) : f = g := by
  apply (cancel_epi (S.decomposition X).inv).mp
  apply biproduct.hom_ext'
  intro a
  simpa only [Category.assoc] using h (S.label X a)
    (biproduct.ι (fun b : Fin (S.length X) => S.simpleObject (S.label X b)) a ≫
      (S.decomposition X).inv)

/-- Every monomorphism in the actual finite semisimple category splits. -/
def splitMono {X Y : C} (f : X ⟶ Y) [Mono f] : SplitMono f := by
  have hinj (i : ι) : Function.Injective
      (CategoryTheory.Linear.rightComp ℂ (S.simpleObject i) f) := by
    intro a b hab
    exact (cancel_mono f).mp hab
  let L (i : ι) := CategoryTheory.Linear.rightComp ℂ (S.simpleObject i) f
  let φ : ∀ i, (S.simpleObject i ⟶ Y) →ₗ[ℂ] (S.simpleObject i ⟶ X) :=
    fun i => Classical.choose ((L i).exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr (hinj i)))
  have hφ (i : ι) (g : S.simpleObject i ⟶ X) : φ i (g ≫ f) = g :=
    LinearMap.congr_fun (Classical.choose_spec
      ((L i).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr (hinj i)))) g
  refine ⟨S.homFromSimpleFamily φ, ?_⟩
  apply S.hom_ext_simples
  intro i g
  rw [← Category.assoc, S.comp_homFromSimpleFamily, Category.comp_id, hφ]

/-- The contravariant simple-Hom version of Schur naturality. -/
lemma toSimpleHomFamily_natural {X Y : C}
    (φ : ∀ i, (X ⟶ S.simpleObject i) →ₗ[ℂ] (Y ⟶ S.simpleObject i))
    {i j : ι} (a : S.simpleObject i ⟶ S.simpleObject j)
    (b : X ⟶ S.simpleObject i) : φ i b ≫ a = φ j (b ≫ a) := by
  by_cases hij : i = j
  · subst j
    obtain ⟨c, rfl⟩ := CategoryTheory.endomorphism_simple_eq_smul_id ℂ a
    simp
  · have ha : a = 0 := by
      by_contra h
      letI := CategoryTheory.isIso_of_hom_simple h
      exact hij (S.iso_injective i j ⟨asIso a⟩)
    simp [ha]

/-- A categorical morphism representing linear maps on Hom spaces into
simple representatives. -/
def homToSimpleFamily {X Y : C}
    (φ : ∀ i, (X ⟶ S.simpleObject i) →ₗ[ℂ] (Y ⟶ S.simpleObject i)) : Y ⟶ X :=
  biproduct.lift (fun a : Fin (S.length X) => φ (S.label X a)
    ((S.decomposition X).hom ≫
      biproduct.π (fun b : Fin (S.length X) => S.simpleObject (S.label X b)) a)) ≫
        (S.decomposition X).inv

lemma homToSimpleFamily_comp {X Y : C}
    (φ : ∀ i, (X ⟶ S.simpleObject i) →ₗ[ℂ] (Y ⟶ S.simpleObject i))
    (i : ι) (g : X ⟶ S.simpleObject i) :
    S.homToSimpleFamily φ ≫ g = φ i g := by
  let f : Fin (S.length X) → C := fun a => S.simpleObject (S.label X a)
  have htotal : ∑ a : Fin (S.length X),
      ((S.decomposition X).hom ≫ biproduct.π f a) ≫
        (biproduct.ι f a ≫ (S.decomposition X).inv ≫ g) = g := by
    simp only [← Category.assoc, ← Preadditive.sum_comp]
    simp only [Category.assoc, ← Preadditive.comp_sum, biproduct.total]
    change (S.decomposition X).hom ≫ 𝟙 _ ≫ (S.decomposition X).inv ≫ g = g
    simp only [Category.id_comp, Iso.hom_inv_id_assoc]
  calc
    S.homToSimpleFamily φ ≫ g =
        ∑ a : Fin (S.length X),
          φ (S.label X a) ((S.decomposition X).hom ≫ biproduct.π f a) ≫
            (biproduct.ι f a ≫ (S.decomposition X).inv ≫ g) := by
      unfold homToSimpleFamily
      rw [biproduct.lift_eq]
      simp only [Preadditive.sum_comp, Category.assoc]
      rfl
    _ = ∑ a : Fin (S.length X), φ i
        (((S.decomposition X).hom ≫ biproduct.π f a) ≫
          (biproduct.ι f a ≫ (S.decomposition X).inv ≫ g)) := by
      apply Finset.sum_congr rfl
      intro a _
      exact S.toSimpleHomFamily_natural φ _ _
    _ = φ i g := by rw [← map_sum, htotal]

omit [Linear ℂ C] [HasKernels C] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] in
/-- Morphisms are also determined by postcomposition with maps into simple
representatives. -/
lemma hom_ext_to_simples {X Y : C} (f g : X ⟶ Y)
    (h : ∀ i (a : Y ⟶ S.simpleObject i), f ≫ a = g ≫ a) : f = g := by
  apply (cancel_mono (S.decomposition Y).hom).mp
  apply biproduct.hom_ext
  intro a
  simpa only [Category.assoc] using h (S.label Y a)
    ((S.decomposition Y).hom ≫
      biproduct.π (fun b : Fin (S.length Y) => S.simpleObject (S.label Y b)) a)

/-- Every epimorphism in the actual finite semisimple category splits. -/
def splitEpi {X Y : C} (f : X ⟶ Y) [Epi f] : SplitEpi f := by
  have hinj (i : ι) : Function.Injective
      (CategoryTheory.Linear.leftComp ℂ (S.simpleObject i) f) := by
    intro a b hab
    exact (cancel_epi f).mp hab
  let L (i : ι) := CategoryTheory.Linear.leftComp ℂ (S.simpleObject i) f
  let φ : ∀ i, (X ⟶ S.simpleObject i) →ₗ[ℂ] (Y ⟶ S.simpleObject i) :=
    fun i => Classical.choose ((L i).exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr (hinj i)))
  have hφ (i : ι) (g : Y ⟶ S.simpleObject i) : φ i (f ≫ g) = g :=
    LinearMap.congr_fun (Classical.choose_spec
      ((L i).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr (hinj i)))) g
  refine ⟨S.homToSimpleFamily φ, ?_⟩
  apply S.hom_ext_to_simples
  intro i g
  rw [Category.assoc, S.homToSimpleFamily_comp, Category.id_comp, hφ]

end FiniteSemisimpleSkeleton
end Paper18.Category
