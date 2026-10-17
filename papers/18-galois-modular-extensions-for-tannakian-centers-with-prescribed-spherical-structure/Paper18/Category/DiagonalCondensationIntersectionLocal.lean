import Paper18.Category.DiagonalCondensationIntersectionRestricted
import Paper18.Category.DiagonalCondensationEmbeddingFactors

/-! # The actual intersection inside the local-module category -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators TensorProduct MonObj
universe v u v' u' vE uE w wC wD wM
namespace Paper18.Category.DiagonalCondensation
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] [BraidedCategory C]
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


variable [P.IsMonoidal] [Q.IsMonoidal] [IsCommMonObj A]
  [RightRigidCategory (DeligneProduct C D)] [HasCoequalizers (DeligneProduct C D)]
  (hP : ∀ X : P.FullSubcategory, ∀ i,
    Centralizes (F.obj (S.simpleObject i)) X.obj)
  (hQ : ∀ X : Q.FullSubcategory, ∀ i,
    Centralizes (G.obj (dual E (S.simpleObject i))) X.obj)

/-- The actual first restricted free embedding into local modules. -/
def restrictedLeftLocal := leftLocalFunctor
  (fun i => F.obj (S.simpleObject i)) (fun i => G.obj (dual E (S.simpleObject i))) e P.ι hP

/-- The actual second restricted free embedding into local modules. -/
def restrictedRightLocal := rightLocalFunctor
  (fun i => F.obj (S.simpleObject i)) (fun i => G.obj (dual E (S.simpleObject i))) e Q.ι hQ

instance restrictedLeftLocal_braided : (restrictedLeftLocal S F G e P hP).Braided := by
  dsimp [restrictedLeftLocal]; infer_instance
instance restrictedLeftLocal_additive : (restrictedLeftLocal S F G e P hP).Additive := by
  dsimp [restrictedLeftLocal]; infer_instance
instance restrictedLeftLocal_linear : (restrictedLeftLocal S F G e P hP).Linear ℂ := by
  dsimp [restrictedLeftLocal]; infer_instance
instance restrictedRightLocal_braided : (restrictedRightLocal S F G e Q hQ).Braided := by
  dsimp [restrictedRightLocal]; infer_instance
instance restrictedRightLocal_additive : (restrictedRightLocal S F G e Q hQ).Additive := by
  dsimp [restrictedRightLocal]; infer_instance
instance restrictedRightLocal_linear : (restrictedRightLocal S F G e Q hQ).Linear ℂ := by
  dsimp [restrictedRightLocal]; infer_instance

/-- The actual functor from the common category satisfying both restrictions
into the first local free image. -/
def restrictedSharedLocal : (sharedRestriction F G P Q).FullSubcategory ⥤ LocalModules A :=
  ObjectProperty.lift P ((sharedRestriction F G P Q).ι ⋙ F) (fun X => X.property.1) ⋙
    restrictedLeftLocal S F G e P hP

/-- The restricted first-factor local functor is fully faithful by the
proved actual diagonal Hom theorem. -/
def restrictedLeftLocalFullyFaithful : (restrictedLeftLocal S F G e P hP).FullyFaithful :=
  leftLocalFunctorFullyFaithful _ _ e P.ι hP (leftFreeFunctorFullyFaithful S F G e T)

/-- The restricted second-factor local functor is fully faithful by the
proved actual diagonal Hom theorem. -/
def restrictedRightLocalFullyFaithful : (restrictedRightLocal S F G e Q hQ).FullyFaithful :=
  rightLocalFunctorFullyFaithful _ _ e Q.ι hQ (rightFreeFunctorFullyFaithful S F G e U)

include T U e K in
/-- The two actual restricted local free images intersect in precisely the
actual shared restriction. The full local inclusion lifts the module
isomorphisms furnished by the actual mixed Hom calculation. -/
theorem restrictedLocalImages_intersection (M : LocalModules A) :
    ((restrictedLeftLocal S F G e P hP).essImage M ∧
      (restrictedRightLocal S F G e Q hQ).essImage M) ↔
        (restrictedSharedLocal S F G e P Q hP).essImage M := by
  let V := (localModuleProperty (A := A)).ι
  constructor
  · rintro ⟨⟨X, ⟨hx⟩⟩, ⟨Y, ⟨hy⟩⟩⟩
    obtain ⟨Z, ⟨hz⟩⟩ := (restrictedFreeImages_intersection S F G T U e K P Q M.obj).mp
      ⟨⟨X, ⟨V.mapIso hx⟩⟩, ⟨Y, ⟨V.mapIso hy⟩⟩⟩
    exact ⟨Z, ⟨V.preimageIso hz⟩⟩
  · rintro ⟨X, ⟨hx⟩⟩
    let lx : P.FullSubcategory := ⟨F.obj X.obj, X.property.1⟩
    let rx : Q.FullSubcategory := ⟨G.obj X.obj, X.property.2⟩
    let hs : (restrictedLeftLocal S F G e P hP).obj lx ≅
        (restrictedRightLocal S F G e Q hQ).obj rx :=
      (localModuleProperty (A := A)).isoMk (sharedImageIso S F G T U e K X.obj)
    exact ⟨⟨lx, ⟨hx⟩⟩, ⟨rx, ⟨hs.symm ≪≫ hx⟩⟩⟩

end Paper18.Category.DiagonalCondensation
