import Paper18.Category.RelativeTensorFree
import Paper18.Category.LinearTensorMonoidal
import Paper18.Category.LinearMatMonoidalEmbedding
import Paper18.Category.Multiplicity

/-! # Actual free-module Hom spaces for a diagonal biproduct

The algebra is specified by its actual underlying biproduct isomorphism.
No nondegeneracy or fullness conclusion is part of the input.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators TensorProduct MonObj
universe v u v' u' w w'
namespace Paper18.Category.DiagonalCondensation
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]

/-- An actual external pair in the additive linear tensor category. -/
abbrev pair (X : C) (Y : D) : DeligneProduct C D :=
  (Mat_.embedding (LinearTensor C D)).obj ⟨X,Y⟩

/-- Hom between actual external pairs is the tensor product of actual
factor Hom spaces. -/
def pairHomLinearEquiv (X Y : C) (U V : D) :
    (pair X U ⟶ pair Y V) ≃ₗ[ℂ] ((X ⟶ Y) ⊗[ℂ] (U ⟶ V)) where
  toFun f := f PUnit.unit PUnit.unit
  invFun f _ _ := f
  left_inv f := by ext ⟨⟩ ⟨⟩; rfl
  right_inv f := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The tensor product of two actual external pairs is an external pair. -/
def pairTensorIso (X Y : C) (U V : D) :
    pair X U ⊗ pair Y V ≅ pair (X ⊗ Y) (U ⊗ V) :=
  Functor.Monoidal.μIso (Mat_.embedding (LinearTensor C D)) ⟨X,U⟩ ⟨Y,V⟩

/-- Reindexing a genuine biproduct across an equivalence in arbitrary
index universes, using its actual inclusion/projection universal property. -/
def reindexIso {α : Type w} {β : Type w'} (q : α ≃ β)
    (h : β → DeligneProduct C D) [HasBiproduct h] [HasBiproduct (h ∘ q)] :
    (⨁ h ∘ q) ≅ ⨁ h where
  hom := biproduct.desc fun a => biproduct.ι h (q a)
  inv := biproduct.lift fun a => biproduct.π h (q a)
  hom_inv_id := by
    apply biproduct.hom_ext'
    intro a
    apply biproduct.hom_ext
    intro b
    simp only [assoc, biproduct.ι_desc_assoc, biproduct.lift_π, id_comp]
    by_cases hab : a = b
    · subst b; simp
    · have hq : q a ≠ q b := fun hh => hab (q.injective hh)
      simp [biproduct.ι_π_ne _ hab, biproduct.ι_π_ne _ hq]
  inv_hom_id := by
    apply biproduct.hom_ext'
    intro b
    obtain ⟨a, rfl⟩ := q.surjective b
    have ha : biproduct.ι h (q a) ≫
        biproduct.lift (f := h ∘ q) (fun c : α => biproduct.π h (q c)) = biproduct.ι (h ∘ q) a := by
      apply biproduct.hom_ext
      intro c
      simp only [assoc, biproduct.lift_π]
      by_cases hac : a = c
      · subst c; simp
      · have hq : q a ≠ q c := fun hh => hac (q.injective hh)
        simp [biproduct.ι_π_ne _ hac, biproduct.ι_π_ne _ hq]
    rw [← assoc, ha, biproduct.ι_desc, comp_id]

variable {ι : Type w} [Fintype ι] (f : ι → C) (g : ι → D)
  {A : DeligneProduct C D} (e : A ≅ ⨁ fun i => pair (f i) (g i))

/-- Finite tensor distribution with an index in any universe is reduced
to the standard finite-ordinal distributor by actual reindexing isomorphisms. -/
def rightDistributorIso (Y : DeligneProduct C D) :
    (⨁ fun i => pair (f i) (g i)) ⊗ Y ≅
      ⨁ fun i => (pair (f i) (g i) ⊗ Y) := by
  let q := Fintype.equivFin ι
  let h : (⨁ fun j : Fin (Fintype.card ι) =>
      (pair (f (q.symm j)) (g (q.symm j)) ⊗ Y)) ≅
      ⨁ fun i : ι => (pair (f i) (g i) ⊗ Y) :=
    reindexIso q.symm (fun i : ι => (pair (f i) (g i) ⊗ Y))
  exact whiskerRightIso (reindexIso q.symm (fun i => pair (f i) (g i))).symm Y ≪≫
    rightDistributor (fun j : Fin (Fintype.card ι) => pair (f (q.symm j)) (g (q.symm j))) Y ≪≫ h

/-- The genuine tensor-distribution isomorphism associated with the
actual diagonal decomposition. -/
def diagonalTensorIso (Y : C) (V : D) :
    A ⊗ pair Y V ≅ ⨁ fun i => pair (f i ⊗ Y) (g i ⊗ V) :=
  whiskerRightIso e (pair Y V) ≪≫
    rightDistributorIso f g (pair Y V) ≪≫
      biproduct.mapIso (fun i => pairTensorIso (f i) Y (g i) V)

/-- The actual free-forgetful universal property and actual diagonal
biproduct give all mixed Hom coordinates at once. -/
def freePairHomLinearEquiv [MonObj A] (X Y : C) (U V : D) :
    (InternalModule.free A (pair X U) ⟶ InternalModule.free A (pair Y V)) ≃ₗ[ℂ]
      (∀ i, (X ⟶ f i ⊗ Y) ⊗[ℂ] (U ⟶ g i ⊗ V)) :=
  (RelativeTensor.freeHomLinearEquiv _ _).trans
    ((CategoryTheory.Linear.homCongr ℂ (Iso.refl _) (diagonalTensorIso f g e Y V)).trans
      ((homBiproductLinearEquiv _ _).trans
        (LinearEquiv.piCongrRight fun i => pairHomLinearEquiv X (f i ⊗ Y) U (g i ⊗ V))))

include e in
/-- The finite Hom rank formula is derived from the actual linear Hom
isomorphism, not supplied as an algebra certificate. -/
lemma finrank_freePairHom [MonObj A]
    [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
    [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
    (X Y : C) (U V : D) :
    Module.finrank ℂ (InternalModule.free A (pair X U) ⟶
      InternalModule.free A (pair Y V)) =
      ∑ i, Module.finrank ℂ (X ⟶ f i ⊗ Y) *
        Module.finrank ℂ (U ⟶ g i ⊗ V) := by
  rw [(freePairHomLinearEquiv f g e X Y U V).finrank_eq,
    Module.finrank_pi_fintype]
  simp only [Module.finrank_tensorProduct]

end Paper18.Category.DiagonalCondensation
