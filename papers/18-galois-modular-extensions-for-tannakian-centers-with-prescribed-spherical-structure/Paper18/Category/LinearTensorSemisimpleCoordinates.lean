import Paper18.Category.LinearTensorSemisimpleBasic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.GradedObject

/-! # Actual Hom coordinates for the finite linear tensor product -/
noncomputable section
set_option maxHeartbeats 800000
open Classical CategoryTheory CategoryTheory.Limits
open scoped BigOperators
universe v u w v' u' w' z
namespace Paper18.Category.DeligneProduct
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)

lemma pairHomFamily_natural {X Y : DeligneProduct C D}
    (φ : ∀ p : ι × κ, (pairObject S T p.1 p.2 ⟶ X) →ₗ[ℂ]
      (pairObject S T p.1 p.2 ⟶ Y))
    {p q : ι × κ} (a : pairObject S T p.1 p.2 ⟶ pairObject S T q.1 q.2)
    (b : pairObject S T q.1 q.2 ⟶ X) : a ≫ φ q b = φ p (a ≫ b) := by
  by_cases hpq : p = q
  · subst q
    obtain ⟨c, rfl⟩ := pair_end_eq_smul S T p a
    simp
  · rw [pair_hom_eq_zero S T hpq a]
    simp

/-- A family of linear maps on the actual pair Hom spaces is represented
by a categorical morphism, using the actual finite biproduct presentation. -/
def homFromPairFamily {X Y : DeligneProduct C D}
    (φ : ∀ p : ι × κ, (pairObject S T p.1 p.2 ⟶ X) →ₗ[ℂ]
      (pairObject S T p.1 p.2 ⟶ Y)) : X ⟶ Y :=
  (presentationIso S T X).hom ≫ biproduct.desc
    (fun a : PresentationIndex S T X => φ (presentationLabel S T X a)
      (biproduct.ι (fun b : PresentationIndex S T X =>
        pairObject S T (presentationLabel S T X b).1 (presentationLabel S T X b).2) a ≫
          (presentationIso S T X).inv))

lemma comp_homFromPairFamily {X Y : DeligneProduct C D}
    (φ : ∀ p : ι × κ, (pairObject S T p.1 p.2 ⟶ X) →ₗ[ℂ]
      (pairObject S T p.1 p.2 ⟶ Y))
    (p : ι × κ) (g : pairObject S T p.1 p.2 ⟶ X) :
    g ≫ homFromPairFamily S T φ = φ p g := by
  let f : PresentationIndex S T X → DeligneProduct C D := fun a =>
    pairObject S T (presentationLabel S T X a).1 (presentationLabel S T X a).2
  have htotal : ∑ a : PresentationIndex S T X,
      (g ≫ (presentationIso S T X).hom ≫ biproduct.π f a) ≫
        (biproduct.ι f a ≫ (presentationIso S T X).inv) = g := by
    simp only [← Category.assoc, ← Preadditive.sum_comp]
    simp only [Category.assoc, ← Preadditive.comp_sum, biproduct.total]
    change g ≫ (presentationIso S T X).hom ≫ 𝟙 _ ≫ (presentationIso S T X).inv = g
    simp only [Category.id_comp, Iso.hom_inv_id, Category.comp_id]
  calc
    g ≫ homFromPairFamily S T φ = ∑ a : PresentationIndex S T X,
        (g ≫ (presentationIso S T X).hom ≫ biproduct.π f a) ≫
          φ (presentationLabel S T X a) (biproduct.ι f a ≫ (presentationIso S T X).inv) := by
      unfold homFromPairFamily
      rw [biproduct.desc_eq]
      simp only [Preadditive.comp_sum, Category.assoc]
      rfl
    _ = ∑ a : PresentationIndex S T X, φ p
        ((g ≫ (presentationIso S T X).hom ≫ biproduct.π f a) ≫
          (biproduct.ι f a ≫ (presentationIso S T X).inv)) := by
      apply Finset.sum_congr rfl
      intro a _
      exact pairHomFamily_natural S T φ _ _
    _ = φ p g := by rw [← map_sum, htotal]

omit [HasKernels C] [HasKernels D]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] in
/-- The pair Hom functor detects all actual morphisms. -/
lemma hom_ext_pairs {X Y : DeligneProduct C D} (f g : X ⟶ Y)
    (h : ∀ (p : ι × κ) (a : pairObject S T p.1 p.2 ⟶ X), a ≫ f = a ≫ g) : f = g := by
  apply (cancel_epi (presentationIso S T X).inv).mp
  apply biproduct.hom_ext'
  intro a
  simpa only [Category.assoc] using h (presentationLabel S T X a)
    (biproduct.ι (fun b : PresentationIndex S T X =>
      pairObject S T (presentationLabel S T X b).1 (presentationLabel S T X b).2) a ≫
        (presentationIso S T X).inv)

/-- Actual finite-dimensional Hom spaces from all embedded simple pairs. -/
def coordinates : DeligneProduct C D ⥤ GradedObject (ι × κ) (FGModuleCat.{max v v'} ℂ) where
  obj X p := FGModuleCat.of ℂ (pairObject S T p.1 p.2 ⟶ X)
  map f p := FGModuleCat.ofHom (CategoryTheory.Linear.rightComp ℂ (pairObject S T p.1 p.2) f)
  map_id X := by
    funext p
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    exact Category.comp_id g
  map_comp f g := by
    funext p
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact (Category.assoc a f g).symm

instance coordinates_faithful : (coordinates S T).Faithful where
  map_injective {X Y} f g h := by
    apply hom_ext_pairs S T f g
    intro p a
    exact LinearMap.congr_fun (congrArg (fun k => (k p).hom) h) a

instance coordinates_full : (coordinates S T).Full where
  map_surjective {X Y} φ := by
    refine ⟨homFromPairFamily S T (fun p => (φ p).hom), ?_⟩
    funext p
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact comp_homFromPairFamily S T _ p a

/-- A finite ordinal indexes the pair labels even when their original types
live in arbitrary universes. -/
abbrev PairOrdinal := Fin (Fintype.card (ι × κ))

/-- A finite list of basis lines for a family of finite-dimensional spaces. -/
abbrev CoordinateIndex (F : GradedObject (ι × κ) (FGModuleCat.{z} ℂ)) :=
  Σ p : PairOrdinal (ι := ι) (κ := κ),
    Fin (Module.finrank ℂ (F ((Fintype.equivFin (ι × κ)).symm p)))

/-- Realize a family of vector spaces by a genuine finite biproduct of pairs. -/
def realizeCoordinates (F : GradedObject (ι × κ) (FGModuleCat.{max v v'} ℂ)) :
    DeligneProduct C D :=
  ⨁ fun a : CoordinateIndex F => pairObject S T
    (((Fintype.equivFin (ι × κ)).symm a.1).1)
    (((Fintype.equivFin (ι × κ)).symm a.1).2)

/-- Orthogonality computes the dimensions of the actual realization's Hom spaces. -/
theorem finrank_realizeCoordinates (F : GradedObject (ι × κ) (FGModuleCat.{max v v'} ℂ))
    (q : ι × κ) :
    Module.finrank ℂ (pairObject S T q.1 q.2 ⟶ realizeCoordinates S T F) =
      Module.finrank ℂ (F q) := by
  unfold realizeCoordinates
  rw [finrank_hom_biproduct]
  simp_rw [finrank_pair_hom]
  obtain ⟨p, rfl⟩ := (Fintype.equivFin (ι × κ)).symm.surjective q
  simp only [CoordinateIndex, Fintype.sum_sigma,
    (Fintype.equivFin (ι × κ)).symm.injective.eq_iff]
  rw [Finset.sum_eq_single p]
  · simp
  · intro b _ hbp
    simp [Ne.symm hbp]
  · simp

/-- Actual componentwise linear isomorphisms identify the realization with
the prescribed finite-dimensional coordinate spaces. -/
def coordinatesRealizationIso
    (F : GradedObject (ι × κ) (FGModuleCat.{max v v'} ℂ)) :
    (coordinates S T).obj (realizeCoordinates S T F) ≅ F where
  hom p := (Classical.choice (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
    (finrank_realizeCoordinates S T F p))).toFGModuleCatIso.hom
  inv p := (Classical.choice (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
    (finrank_realizeCoordinates S T F p))).toFGModuleCatIso.inv
  hom_inv_id := by
    funext p
    exact (Classical.choice (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
      (finrank_realizeCoordinates S T F p))).toFGModuleCatIso.hom_inv_id
  inv_hom_id := by
    funext p
    exact (Classical.choice (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
      (finrank_realizeCoordinates S T F p))).toFGModuleCatIso.inv_hom_id

instance coordinates_essSurj : (coordinates S T).EssSurj where
  mem_essImage F := ⟨realizeCoordinates S T F, ⟨coordinatesRealizationIso S T F⟩⟩

instance coordinates_isEquivalence : (coordinates S T).IsEquivalence where

/-- The actual linear tensor category is equivalent to finite families of
finite-dimensional vector spaces, with coordinates given by genuine Homs. -/
def coordinateEquivalence :
    DeligneProduct C D ≌ GradedObject (ι × κ) (FGModuleCat.{max v v'} ℂ) :=
  (coordinates S T).asEquivalence

end Paper18.Category.DeligneProduct
