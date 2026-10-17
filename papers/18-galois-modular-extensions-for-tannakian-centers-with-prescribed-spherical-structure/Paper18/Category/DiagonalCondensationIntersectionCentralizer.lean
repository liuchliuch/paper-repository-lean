import Paper18.Category.DiagonalCondensationIntersectionLocal
import Paper18.Category.CentralizerSimples

/-! # The actual common part of a centralizer after diagonal condensation

When the first subcategory centralizes the common diagonal category, its
common objects automatically lie in the second centralizer. This is proved
by actual braided reflection on all chosen simples, rather than an assumed
intersection equality. In Case 2 the resulting first-factor inverse image
is the actual subcategory E intersect K-plus.
-/
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
  [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalLinear ℂ E] [BraidedCategory E]
  [RightRigidCategory E] [HasKernels E] [HasFiniteBiproducts E]
  [∀ X Y : E, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ E)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton E ι)
  (F : E ⥤ C) [F.Braided] [F.Full] [F.Faithful] [F.Additive] [F.Linear ℂ]
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

variable [P.IsMonoidal] [IsCommMonObj A]
  [RightRigidCategory (DeligneProduct C D)] [HasCoequalizers (DeligneProduct C D)]
  (hP : ∀ X : P.FullSubcategory, ∀ i,
    Centralizes (F.obj (S.simpleObject i)) X.obj)
  (hG : ∀ X Y : E, Centralizes X Y → Centralizes (G.obj X) (G.obj Y))

/-- The actual centralizer of the common-category image in the second factor. -/
abbrev secondCentralizer : ObjectProperty D := centralizerProperty (Set.range G.obj)

/-- Membership in that actual centralizer supplies every dual-diagonal
centralization needed for locality of the right free image. -/
lemma secondCentralizer_local_condition
    (X : (secondCentralizer G).FullSubcategory) (i : ι) :
    Centralizes (G.obj (dual E (S.simpleObject i))) X.obj :=
  (X.property _ ⟨dual E (S.simpleObject i), rfl⟩).symm

include hP hG in
/-- The second centralizer restriction is automatic on the first common
part: faithfulness reflects first-factor monodromy and the other braided
inclusion transports it. -/
lemma sharedRestriction_centralizer_iff (X : E) :
    sharedRestriction F G P (secondCentralizer G) X ↔ P (F.obj X) := by
  constructor
  · exact And.left
  · intro h
    refine ⟨h, ?_⟩
    apply (mem_centralizer_functor_iff_simples S G (G.obj X)).mpr
    intro i
    apply hG X (S.simpleObject i)
    apply (centralizes_map_iff F X (S.simpleObject i)).mp
    exact (hP ⟨F.obj X, h⟩ i).symm

/-- The actual first-factor inverse image inside the common category. -/
def commonPartProperty : ObjectProperty E := fun X => P (F.obj X)

instance commonPartProperty_isAdditive : IsAdditiveFullProperty (commonPartProperty F P) where
  of_retract r h := IsAdditiveFullProperty.of_retract (P := P) (r.map F) h
  biproduct q hq := IsAdditiveFullProperty.of_iso P (F.mapBiproduct q)
    (IsAdditiveFullProperty.biproduct (P := P) (fun i => F.obj (q i)) hq)

instance commonPartProperty_isMonoidal : (commonPartProperty F P).IsMonoidal where
  prop_unit := IsAdditiveFullProperty.of_iso P (Functor.Monoidal.εIso F).symm
    (ObjectProperty.prop_unit P)
  prop_tensor X Y hX hY := IsAdditiveFullProperty.of_iso P
    (Functor.Monoidal.μIso F X Y).symm (ObjectProperty.prop_tensor hX hY)

/-- The actual pullback full subcategory embeds into the first restriction
by the given actual fully faithful tensor functor. -/
def commonPartToFirst : (commonPartProperty F P).FullSubcategory ⥤ P.FullSubcategory :=
  fullSubcategoryLift P ((commonPartProperty F P).ι ⋙ F) (fun X => X.property)

instance commonPartToFirst_braided : (commonPartToFirst F P).Braided := by
  dsimp [commonPartToFirst]; infer_instance
instance commonPartToFirst_additive : (commonPartToFirst F P).Additive := by
  dsimp [commonPartToFirst]; infer_instance
instance commonPartToFirst_linear : (commonPartToFirst F P).Linear ℂ := by
  dsimp [commonPartToFirst]; infer_instance
instance commonPartToFirst_full : (commonPartToFirst F P).Full := by
  dsimp [commonPartToFirst]; infer_instance
instance commonPartToFirst_faithful : (commonPartToFirst F P).Faithful := by
  dsimp [commonPartToFirst]; infer_instance

/-- Its actual local free embedding. -/
def commonPartLocal : (commonPartProperty F P).FullSubcategory ⥤ LocalModules A :=
  commonPartToFirst F P ⋙ restrictedLeftLocal S F G e P hP

instance commonPartLocal_braided : (commonPartLocal S F G e P hP).Braided := by
  dsimp [commonPartLocal]; infer_instance
instance commonPartLocal_additive : (commonPartLocal S F G e P hP).Additive := by
  dsimp [commonPartLocal]; infer_instance
instance commonPartLocal_linear : (commonPartLocal S F G e P hP).Linear ℂ := by
  dsimp [commonPartLocal]; infer_instance

/-- The actual common-part local embedding is fully faithful. -/
def commonPartLocalFullyFaithful : (commonPartLocal S F G e P hP).FullyFaithful :=
  (Functor.FullyFaithful.ofFullyFaithful (commonPartToFirst F P)).comp
    (restrictedLeftLocalFullyFaithful S F G T e P hP)

include T U e K hG in
/-- The actual first local image and the actual second centralizer image
intersect in precisely the first common part. This is the categorical
intersection statement underlying E intersect I-reverse = E-plus. -/
theorem centralizerLocalImages_intersection (M : LocalModules A) :
    ((restrictedLeftLocal S F G e P hP).essImage M ∧
      (restrictedRightLocal S F G e (secondCentralizer G)
        (secondCentralizer_local_condition S G)).essImage M) ↔
          (commonPartLocal S F G e P hP).essImage M := by
  rw [restrictedLocalImages_intersection S F G T U e K P (secondCentralizer G)
    hP (secondCentralizer_local_condition S G)]
  constructor
  · rintro ⟨X, ⟨hx⟩⟩
    exact ⟨⟨X.obj, X.property.1⟩, ⟨hx⟩⟩
  · rintro ⟨X, ⟨hx⟩⟩
    have hp := (sharedRestriction_centralizer_iff S F G P hP hG X.obj).mpr X.property
    exact ⟨⟨X.obj, hp⟩, ⟨hx⟩⟩

end Paper18.Category.DiagonalCondensation
