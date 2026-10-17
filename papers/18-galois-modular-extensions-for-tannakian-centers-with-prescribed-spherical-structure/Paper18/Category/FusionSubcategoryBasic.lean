import Paper18.Category.CentralizerClosure
import Paper18.Category.SemisimpleSplitting

/-!
# Actual additive full subcategories of finite semisimple categories

The closure predicates concern actual retract diagrams and actual biproducts.
The inherited decomposition and simple representatives are constructed below.
-/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

/-- Closure of an actual full subcategory under summands and finite sums. -/
class IsAdditiveFullProperty (P : ObjectProperty C) : Prop where
  of_retract : ∀ {X Y : C}, Retract X Y → P Y → P X
  biproduct : ∀ {J : Type} [Fintype J] (f : J → C), (∀ j, P (f j)) → P (⨁ f)

namespace IsAdditiveFullProperty
variable (P : ObjectProperty C) [IsAdditiveFullProperty P]

lemma of_iso {X Y : C} (e : X ≅ Y) (hY : P Y) : P X :=
  of_retract (Retract.ofIso e) hY

/-- The ambient biproduct bicone, regarded in the actual full subcategory. -/
def bicone {J : Type} [Fintype J] (f : J → P.FullSubcategory) : Bicone f where
  pt := ⟨⨁ (fun j => (f j).obj), biproduct _ (fun j => (f j).property)⟩
  π j := biproduct.π (fun j => (f j).obj) j
  ι j := biproduct.ι (fun j => (f j).obj) j
  ι_π j j' := by
    change biproduct.ι (fun j => (f j).obj) j ≫ biproduct.π (fun j => (f j).obj) j' = _
    rw [biproduct.ι_π]
    split_ifs with h
    · subst j'
      rfl
    · rfl

instance hasFiniteBiproducts : HasFiniteBiproducts P.FullSubcategory where
  out n := ⟨fun f => hasBiproduct_of_total (bicone P f) (by
    change ∑ j : Fin n, biproduct.π (fun j => (f j).obj) j ≫
      biproduct.ι (fun j => (f j).obj) j = _
    exact biproduct.total)⟩

end IsAdditiveFullProperty

namespace FiniteSemisimpleSkeleton
variable [Linear ℂ C] [HasKernels C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (P : ObjectProperty C) [IsAdditiveFullProperty P]

include S in
/-- An ambient kernel is a summand of its source, hence belongs to every
summand-closed full subcategory containing the source. -/
lemma property_kernel {X Y : P.FullSubcategory} (f : X ⟶ Y) :
    P (kernel (P.ι.map f)) := by
  let r : Retract (kernel (P.ι.map f)) X.obj :=
    { i := kernel.ι (P.ι.map f)
      r := (S.splitMono (kernel.ι (P.ι.map f))).retraction
      retract := (S.splitMono (kernel.ι (P.ι.map f))).id }
  exact IsAdditiveFullProperty.of_retract r X.property

include S in
/-- Inclusions of summand-closed full subcategories of a semisimple category
preserve monomorphisms. The ambient kernel itself lies in the subcategory. -/
lemma mono_inclusion {X Y : P.FullSubcategory} (f : X ⟶ Y) [Mono f] :
    Mono (P.ι.map f) := by
  apply Preadditive.mono_of_kernel_zero
  let K : P.FullSubcategory := ⟨kernel (P.ι.map f), S.property_kernel P f⟩
  let k : K ⟶ X := kernel.ι (P.ι.map f)
  have hk : k ≫ f = 0 := kernel.condition (P.ι.map f)
  have hz : k = 0 := (cancel_mono f).mp (by simpa using hk)
  exact hz

include S in
/-- Ambient simple objects remain simple in a summand-closed full
subcategory. -/
def simple_in_fullSubcategory (X : C) (hX : P X) [Simple X] :
    Simple (⟨X, hX⟩ : P.FullSubcategory) where
  mono_isIso_iff_nonzero {Y} f _ := by
    letI : Simple (P.ι.obj (⟨X, hX⟩ : P.FullSubcategory)) :=
      (inferInstance : Simple X)
    letI := S.mono_inclusion P f
    constructor
    · intro hf hz
      letI := hf
      have h := (CategoryTheory.Simple.mono_isIso_iff_nonzero (P.ι.map f)).mp
        (by infer_instance)
      exact h hz
    · intro hf
      letI : IsIso (P.ι.map f) := CategoryTheory.isIso_of_mono_of_nonzero hf
      exact isIso_of_fully_faithful P.ι f

/-- Kernels of actual subcategory morphisms are obtained from their ambient
kernels and the universal lifting maps. -/
def fullSubcategoryHasKernels : HasKernels P.FullSubcategory where
  has_limit f := by
    let K : P.FullSubcategory := ⟨kernel (P.ι.map f), S.property_kernel P f⟩
    let k : K ⟶ _ := kernel.ι (P.ι.map f)
    have hk : k ≫ f = 0 := kernel.condition (P.ι.map f)
    exact HasLimit.mk
      { cone := KernelFork.ofι k hk
        isLimit := KernelFork.IsLimit.ofι k hk
          (fun g hg => kernel.lift (P.ι.map f) g hg)
          (fun g hg => kernel.lift_ι _ _ _)
          (fun g hg m hm => by
            apply (cancel_mono (kernel.ι (P.ι.map f))).mp
            exact hm.trans (kernel.lift_ι (P.ι.map f) g hg).symm) }

omit [Linear ℂ C] [HasKernels C] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] in
/-- The simple representative occurring in every chosen summand of an
object in the subcategory also belongs to the subcategory. -/
lemma property_label (X : P.FullSubcategory) (a : Fin (S.length X.obj)) :
    P (S.simpleObject (S.label X.obj a)) := by
  apply IsAdditiveFullProperty.of_retract (Y := X.obj) _ X.property
  exact
    { i := biproduct.ι (fun b : Fin (S.length X.obj) =>
        S.simpleObject (S.label X.obj b)) a ≫ (S.decomposition X.obj).inv
      r := (S.decomposition X.obj).hom ≫ biproduct.π
        (fun b : Fin (S.length X.obj) => S.simpleObject (S.label X.obj b)) a
      retract := by simp }

/-- An actual inherited finite semisimple skeleton, indexed by the ambient
simple representatives lying in the full subcategory. -/
def fullSubcategorySkeleton :
    FiniteSemisimpleSkeleton P.FullSubcategory {i : ι // P (S.simpleObject i)} where
  simpleObject i := ⟨S.simpleObject i.val, i.property⟩
  simple i := S.simple_in_fullSubcategory P _ _
  iso_injective i j h := by
    apply Subtype.ext
    exact S.iso_injective i.val j.val (h.map (P.ι.mapIso))
  length X := S.length X.obj
  label X a := ⟨S.label X.obj a, S.property_label P X a⟩
  decomposition X := by
    let f : Fin (S.length X.obj) → P.FullSubcategory := fun a =>
      ⟨S.simpleObject (S.label X.obj a), S.property_label P X a⟩
    exact P.isoMk (S.decomposition X.obj ≪≫ (P.ι.mapBiproduct f).symm)

end FiniteSemisimpleSkeleton

variable [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C]
instance centralizerProperty_isAdditive (T : Set C) :
    IsAdditiveFullProperty (centralizerProperty T) where
  of_retract := centralizer_retract
  biproduct := centralizer_biproduct

end Paper18.Category
