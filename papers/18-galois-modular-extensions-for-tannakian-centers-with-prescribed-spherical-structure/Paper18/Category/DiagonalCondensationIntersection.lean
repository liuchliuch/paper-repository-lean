import Paper18.Category.DiagonalCondensationIntersectionRecognition
import Paper18.Category.LinearTensorSemisimple
import Paper18.Category.SeparableModulesKernels

/-! # The actual intersection of the two diagonal free images -/
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

/-- The left and right free images of an actual shared simple object are
actually isomorphic. A nonzero mixed Hom map is supplied by the proved
rank-one Hom calculation, and genuine target simplicity makes it invertible. -/
def sharedSimpleIso (i : ι) :
    (leftFreeFunctor (A := A)).obj (F.obj (S.simpleObject i)) ≅
      (rightFreeFunctor (A := A)).obj (G.obj (S.simpleObject i)) := by
  letI := DeligneProduct.hasKernels T U
  letI := (leftFreeFunctorFullyFaithful S F G e T).full
  letI := (leftFreeFunctorFullyFaithful S F G e T).faithful
  letI := (rightFreeFunctorFullyFaithful S F G e U).full
  letI := (rightFreeFunctorFullyFaithful S F G e U).faithful
  letI : Simple ((leftFreeFunctor (A := A)).obj (F.obj (S.simpleObject i))) :=
    K.simple_map (F ⋙ leftFreeFunctor (A := A)) (S.simpleObject i)
  letI : Simple ((rightFreeFunctor (A := A)).obj (G.obj (S.simpleObject i))) :=
    K.simple_map (G ⋙ rightFreeFunctor (A := A)) (S.simpleObject i)
  have hp : 0 < Module.finrank ℂ
      ((leftFreeFunctor (A := A)).obj (F.obj (S.simpleObject i)) ⟶
        (rightFreeFunctor (A := A)).obj (G.obj (S.simpleObject i))) := by
    rw [finrank_freeMixedHom_common S F G e,
      CategoryTheory.finrank_endomorphism_simple_eq_one ℂ]
    exact zero_lt_one
  let f := Classical.choose (Module.finrank_pos_iff_exists_ne_zero.mp hp)
  have hf := Classical.choose_spec (Module.finrank_pos_iff_exists_ne_zero.mp hp)
  letI := CategoryTheory.isIso_of_hom_simple hf
  exact asIso f

/-- Finite actual simple decompositions extend the shared-simple
isomorphisms to every actual object of the common category. -/
def sharedImageIso (X : E) :
    (leftFreeFunctor (A := A)).obj (F.obj X) ≅
      (rightFreeFunctor (A := A)).obj (G.obj X) := by
  let L := F ⋙ leftFreeFunctor (A := A)
  let R := G ⋙ rightFreeFunctor (A := A)
  let q : Fin (S.length X) → E := fun a => S.simpleObject (S.label X a)
  exact L.mapIso (S.decomposition X) ≪≫ L.mapBiproduct q ≪≫
    biproduct.mapIso (fun a => sharedSimpleIso S F G T U e K (S.label X a)) ≪≫
      (R.mapBiproduct q).symm ≪≫ (R.mapIso (S.decomposition X)).symm

include T U e K in
/-- The intersection of the two actual essential images is exactly the
actual common-category image. Both directions are proved on objects and
actual isomorphisms, without an intersection or dimension certificate. -/
theorem freeImages_intersection (M : Mod_ (DeligneProduct C D) A) :
    ((leftFreeFunctor (A := A)).essImage M ∧ (rightFreeFunctor (A := A)).essImage M) ↔
      (F ⋙ leftFreeFunctor (A := A)).essImage M := by
  constructor
  · rintro ⟨⟨X, ⟨hx⟩⟩, ⟨V, ⟨hv⟩⟩⟩
    obtain ⟨Y, ⟨hy⟩⟩ := left_source_in_image_of_iso S F G T e X V ⟨hx ≪≫ hv.symm⟩
    exact ⟨Y, ⟨(leftFreeFunctor (A := A)).mapIso hy ≪≫ hx⟩⟩
  · rintro ⟨X, ⟨hx⟩⟩
    exact ⟨⟨F.obj X, ⟨hx⟩⟩,
      ⟨G.obj X, ⟨(sharedImageIso S F G T U e K X).symm ≪≫ hx⟩⟩⟩

end Paper18.Category.DiagonalCondensation
