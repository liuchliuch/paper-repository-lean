import Paper18.Category.DiagonalCondensationEmbeddingLocal
import Paper18.Category.DeligneProductNondegenerateBasic

/-! # Actual local embeddings of the centralizing Deligne factors -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators MonObj
universe v u v' u' w vB uB vB' uB'
namespace Paper18.Category.DiagonalCondensation
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] [BraidedCategory C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D] [BraidedCategory D]
  {ι : Type w} [Fintype ι] (f : ι → C) (g : ι → D)
  {A : DeligneProduct C D} (e : A ≅ ⨁ fun i => pair (f i) (g i))

include e in
/-- Centralization of a finite diagonal sum is proved on its actual
summands, with arbitrary index universes handled by actual reindexing. -/
lemma centralizes_diagonal_left (X : C) (h : ∀ i, Centralizes (f i) X) :
    Centralizes A (pair X (𝟙_ D)) := by
  let q := Fintype.equivFin ι
  have hs : Centralizes (⨁ fun j : Fin (Fintype.card ι) =>
      pair (f (q.symm j)) (g (q.symm j))) (pair X (𝟙_ D)) := by
    apply centralizes_biproduct_left
    intro j
    exact (DeligneProduct.raw_centralizes (h (q.symm j))
      (centralizes_unit_right (g (q.symm j)))).map (Mat_.embedding (LinearTensor C D))
  exact hs.of_iso_left (e ≪≫
    (reindexIso q.symm (fun i => pair (f i) (g i))).symm)

include e in
/-- The corresponding actual second-factor centralization criterion. -/
lemma centralizes_diagonal_right (V : D) (h : ∀ i, Centralizes (g i) V) :
    Centralizes A (pair (𝟙_ C) V) := by
  let q := Fintype.equivFin ι
  have hs : Centralizes (⨁ fun j : Fin (Fintype.card ι) =>
      pair (f (q.symm j)) (g (q.symm j))) (pair (𝟙_ C) V) := by
    apply centralizes_biproduct_left
    intro j
    exact (DeligneProduct.raw_centralizes (centralizes_unit_right (f (q.symm j)))
      (h (q.symm j))).map (Mat_.embedding (LinearTensor C D))
  exact hs.of_iso_left (e ≪≫
    (reindexIso q.symm (fun i => pair (f i) (g i))).symm)

variable [MonObj A] [IsCommMonObj A] [RightRigidCategory (DeligneProduct C D)]
  [HasCoequalizers (DeligneProduct C D)]
  {B : Type uB} [Category.{vB} B] [Preadditive B] [Linear ℂ B]
  [MonoidalCategory B] [BraidedCategory B]
  (H : B ⥤ C) [H.Braided] [H.Additive] [H.Linear ℂ]
  (hH : ∀ X i, Centralizes (f i) (H.obj X))

/-- Actual local free modules give the first-factor braided tensor functor. -/
def leftLocalFunctor : B ⥤ LocalModules A :=
  localFreeAlong (H ⋙ DeligneProduct.left) (fun X =>
    centralizes_diagonal_left f g e (H.obj X) (hH X))

instance leftLocalFunctor_braided : (leftLocalFunctor f g e H hH).Braided := by
  dsimp [leftLocalFunctor]; infer_instance
instance leftLocalFunctor_additive : (leftLocalFunctor f g e H hH).Additive := by
  dsimp [leftLocalFunctor]; infer_instance
instance leftLocalFunctor_linear : (leftLocalFunctor f g e H hH).Linear ℂ := by
  dsimp [leftLocalFunctor]; infer_instance

/-- Actual full faithfulness of the module-valued first-factor free
functor yields actual full faithfulness of its braided local lift. -/
def leftLocalFunctorFullyFaithful [H.Full] [H.Faithful]
    (h : (leftFreeFunctor (A := A)).FullyFaithful) :
    (leftLocalFunctor f g e H hH).FullyFaithful :=
  localFreeAlongFullyFaithful _ _ ((Functor.FullyFaithful.ofFullyFaithful H).comp h)

variable {B' : Type uB'} [Category.{vB'} B'] [Preadditive B'] [Linear ℂ B']
  [MonoidalCategory B'] [BraidedCategory B']
  (K : B' ⥤ D) [K.Braided] [K.Additive] [K.Linear ℂ]
  (hK : ∀ X i, Centralizes (g i) (K.obj X))

/-- Actual local free modules give the second-factor braided tensor functor. -/
def rightLocalFunctor : B' ⥤ LocalModules A :=
  localFreeAlong (K ⋙ DeligneProduct.right) (fun X =>
    centralizes_diagonal_right f g e (K.obj X) (hK X))

instance rightLocalFunctor_braided : (rightLocalFunctor f g e K hK).Braided := by
  dsimp [rightLocalFunctor]; infer_instance
instance rightLocalFunctor_additive : (rightLocalFunctor f g e K hK).Additive := by
  dsimp [rightLocalFunctor]; infer_instance
instance rightLocalFunctor_linear : (rightLocalFunctor f g e K hK).Linear ℂ := by
  dsimp [rightLocalFunctor]; infer_instance

/-- The actual second-factor local lift inherits proved full faithfulness. -/
def rightLocalFunctorFullyFaithful [K.Full] [K.Faithful]
    (h : (rightFreeFunctor (A := A)).FullyFaithful) :
    (rightLocalFunctor f g e K hK).FullyFaithful :=
  localFreeAlongFullyFaithful _ _ ((Functor.FullyFaithful.ofFullyFaithful K).comp h)

/-- The two actual local free images centralize one another, by actual
Deligne monodromy and preservation by the braided local free functor. -/
lemma local_left_right_centralizes (X : B) (Y : B') :
    Centralizes ((leftLocalFunctor f g e H hH).obj X)
      ((rightLocalFunctor f g e K hK).obj Y) := by
  let p := (centralizingLift (H ⋙ DeligneProduct.left)
    (fun X => centralizes_diagonal_left f g e (H.obj X) (hH X))).obj X
  let q := (centralizingLift (K ⋙ DeligneProduct.right)
    (fun X => centralizes_diagonal_right f g e (K.obj X) (hK X))).obj Y
  have hpq : Centralizes p q := by
    apply (centralizes_map_iff (centralizerInclusion ({A} : Set (DeligneProduct C D))) p q).mp
    exact DeligneProduct.left_right_centralizes (H.obj X) (K.obj Y)
  exact hpq.map (localFreeFunctor (A := A))

end Paper18.Category.DiagonalCondensation
