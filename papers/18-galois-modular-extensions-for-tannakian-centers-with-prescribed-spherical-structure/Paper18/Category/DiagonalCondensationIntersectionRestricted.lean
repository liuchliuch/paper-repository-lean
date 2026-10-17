import Paper18.Category.DiagonalCondensationIntersection
import Paper18.Category.FusionSubcategoryBasic

/-! # Intersections after restricting the two actual free images -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators TensorProduct MonObj
universe v u v' u' vE uE w wC wD wM
namespace Paper18.Category.DiagonalCondensation
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [BraidedCategory D] [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  {E : Type uE} [Category.{vE} E] [Preadditive E] [Linear ℂ E]
  [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalLinear ℂ E]
  [RightRigidCategory E] [HasKernels E] [HasFiniteBiproducts E]
  [∀ X Y : E, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ E)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton E ι)
  (F : E ⥤ C) [F.Monoidal] [F.Full] [F.Faithful] [F.Additive] [F.Linear ℂ]
  (G : E ⥤ D) [G.Monoidal] [G.Full] [G.Faithful] [G.Additive] [G.Linear ℂ]


variable [HasKernels C] [HasFiniteBiproducts C]
  {κ : Type wC} [Fintype κ] (T : FiniteSemisimpleSkeleton C κ)
  [HasKernels D] [HasFiniteBiproducts D]
  {ν : Type wD} [Fintype ν] (U : FiniteSemisimpleSkeleton D ν)
  {A : DeligneProduct C D} [MonObj A]
  (e : A ≅ ⨁ fun i => pair (F.obj (S.simpleObject i))
    (G.obj (dual E (S.simpleObject i))))


variable {ζ : Type wM} [Fintype ζ]
  (K : FiniteSemisimpleSkeleton (Mod_ (DeligneProduct C D) A) ζ)


variable (P : ObjectProperty C) [IsAdditiveFullProperty P]
  (Q : ObjectProperty D) [IsAdditiveFullProperty Q]

/-- The actual restriction on the common category detected in both factors. -/
def sharedRestriction : ObjectProperty E := fun X => P (F.obj X) ∧ Q (G.obj X)

/-- The actual common-category functor with its source restricted in both
factors. -/
def restrictedSharedFunctor : (sharedRestriction F G P Q).FullSubcategory ⥤
    Mod_ (DeligneProduct C D) A :=
  (sharedRestriction F G P Q).ι ⋙ F ⋙ leftFreeFunctor

include T U e K in
/-- The actual essential images of the restricted free embeddings intersect
in precisely the actual common subcategory satisfying both restrictions. -/
theorem restrictedFreeImages_intersection (M : Mod_ (DeligneProduct C D) A) :
    ((P.ι ⋙ leftFreeFunctor (A := A)).essImage M ∧
      (Q.ι ⋙ rightFreeFunctor (A := A)).essImage M) ↔
        (restrictedSharedFunctor F G P Q (A := A)).essImage M := by
  constructor
  · rintro ⟨⟨X, ⟨hx⟩⟩, ⟨V, ⟨hv⟩⟩⟩
    obtain ⟨Y, ⟨hy⟩⟩ := (freeImages_intersection S F G T U e K M).mp
      ⟨⟨X.obj, ⟨hx⟩⟩, ⟨V.obj, ⟨hv⟩⟩⟩
    have hp : P (F.obj Y) := IsAdditiveFullProperty.of_iso P
      ((leftFreeFunctorFullyFaithful S F G e T).preimageIso (hy ≪≫ hx.symm)) X.property
    have hq : Q (G.obj Y) := IsAdditiveFullProperty.of_iso Q
      ((rightFreeFunctorFullyFaithful S F G e U).preimageIso
        ((sharedImageIso S F G T U e K Y).symm ≪≫ hy ≪≫ hv.symm)) V.property
    exact ⟨⟨Y, hp, hq⟩, ⟨hy⟩⟩
  · rintro ⟨X, ⟨hx⟩⟩
    exact ⟨⟨⟨F.obj X.obj, X.property.1⟩, ⟨hx⟩⟩,
      ⟨⟨G.obj X.obj, X.property.2⟩,
        ⟨(sharedImageIso S F G T U e K X.obj).symm ≪≫ hx⟩⟩⟩

end Paper18.Category.DiagonalCondensation
