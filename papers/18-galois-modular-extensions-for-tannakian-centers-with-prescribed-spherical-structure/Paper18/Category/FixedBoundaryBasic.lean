import Paper18.Category.TannakianDeequivariantNondegenerate
import Paper18.Category.TannakianDescentMonoidal

/-!
# Actual fixed-boundary extension data for Lemma A.1

These definitions state the original categorical problem. A boundary
identification is a specified monoidal natural isomorphism, and morphisms
retain its componentwise equality. No classification or extension existence
assertion is included as input data.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u w v' u' w'
namespace Paper18.Category

section Boundary
variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℂ A]
  [MonoidalCategory A] [BraidedCategory A]
  {N : Type u'} [Category.{v'} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N]
  (i : A ⥤ N) [i.Monoidal]

/-- A braided tensor autoequivalence with its specified identification
on the actual boundary functor. -/
structure BoundaryAutoequivalence where
  functor : N ⥤ N
  [equivalence : functor.IsEquivalence]
  [additive : functor.Additive]
  [linear : functor.Linear ℂ]
  [braided : functor.Braided]
  boundary : i ⋙ functor ≅ i
  [boundaryMonoidal : NatTrans.IsMonoidal boundary.hom]

attribute [instance] BoundaryAutoequivalence.equivalence BoundaryAutoequivalence.additive
  BoundaryAutoequivalence.linear BoundaryAutoequivalence.braided
  BoundaryAutoequivalence.boundaryMonoidal

/-- The identity autoequivalence with its actual identity boundary comparison. -/
def BoundaryAutoequivalence.identity : BoundaryAutoequivalence i where
  functor := 𝟭 N
  boundary := i.rightUnitor

/-- A morphism in the fixed-boundary groupoid is an actual monoidal natural
isomorphism satisfying the specified boundary equality (paper equation A.1). -/
@[ext] structure BoundaryIso (P Q : BoundaryAutoequivalence i) where
  iso : P.functor ≅ Q.functor
  [monoidal : NatTrans.IsMonoidal iso.hom]
  boundary : ∀ X : A, iso.hom.app (i.obj X) ≫ Q.boundary.hom.app X = P.boundary.hom.app X

attribute [instance] BoundaryIso.monoidal

def BoundaryIso.refl (P : BoundaryAutoequivalence i) : BoundaryIso i P P where
  iso := Iso.refl _
  monoidal := by change NatTrans.IsMonoidal (𝟙 P.functor); infer_instance
  boundary X := Category.id_comp _

def BoundaryIso.trans {P Q R : BoundaryAutoequivalence i}
    (f : BoundaryIso i P Q) (g : BoundaryIso i Q R) : BoundaryIso i P R where
  iso := f.iso ≪≫ g.iso
  monoidal := by change NatTrans.IsMonoidal (f.iso.hom ≫ g.iso.hom); infer_instance
  boundary X := by
    change (f.iso.hom.app (i.obj X) ≫ g.iso.hom.app (i.obj X)) ≫ _ = _
    rw [Category.assoc, g.boundary, f.boundary]

def BoundaryIso.symm {P Q : BoundaryAutoequivalence i}
    (f : BoundaryIso i P Q) : BoundaryIso i Q P where
  iso := f.iso.symm
  monoidal := by change NatTrans.IsMonoidal f.iso.inv; infer_instance
  boundary X := by
    change f.iso.inv.app (i.obj X) ≫ P.boundary.hom.app X = _
    rw [← f.boundary X, ← Category.assoc, f.iso.inv_hom_id_app, Category.id_comp]

/-- The actual groupoid of braided autoequivalences with fixed boundary. -/
instance boundaryAutoequivalenceGroupoid : Groupoid (BoundaryAutoequivalence i) where
  Hom P Q := BoundaryIso i P Q
  id := BoundaryIso.refl i
  comp f g := BoundaryIso.trans i f g
  inv f := BoundaryIso.symm i f
  id_comp f := by
    apply BoundaryIso.ext
    change Iso.refl _ ≪≫ f.iso = f.iso
    exact Iso.refl_trans _
  comp_id f := by
    apply BoundaryIso.ext
    change f.iso ≪≫ Iso.refl _ = f.iso
    exact Iso.trans_refl _
  assoc f g h := by
    apply BoundaryIso.ext
    change (f.iso ≪≫ g.iso) ≪≫ h.iso = f.iso ≪≫ (g.iso ≪≫ h.iso)
    exact Iso.trans_assoc _ _ _
  inv_comp f := by
    apply BoundaryIso.ext
    apply Iso.ext
    change f.iso.inv ≫ f.iso.hom = 𝟙 _
    exact f.iso.inv_hom_id
  comp_inv f := by
    apply BoundaryIso.ext
    apply Iso.ext
    change f.iso.hom ≫ f.iso.inv = 𝟙 _
    exact f.iso.hom_inv_id

/-- The original fixed-boundary conclusion at a specified pair. -/
def BoundaryAutoequivalence.Trivializable (P : BoundaryAutoequivalence i) : Prop :=
  Nonempty (BoundaryIso i P (BoundaryAutoequivalence.identity i))

omit [Preadditive A] [Linear ℂ A] [BraidedCategory A] in
/-- A trivialization has precisely the componentwise equality required
in Lemma A.1, including the prescribed value of the boundary comparison. -/
theorem BoundaryIso.to_identity_boundary {P : BoundaryAutoequivalence i}
    (f : BoundaryIso i P (BoundaryAutoequivalence.identity i)) (X : A) :
    f.iso.hom.app (i.obj X) = P.boundary.hom.app X := by
  have h := f.boundary X
  change f.iso.hom.app (i.obj X) ≫ 𝟙 (i.obj X) = P.boundary.hom.app X at h
  exact (Category.comp_id _).symm.trans h

end Boundary

section Extension
variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℂ A]
  [HasKernels A] [HasFiniteBiproducts A]
  [∀ X Y : A, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory A] [BraidedCategory A] [MonoidalPreadditive A] [MonoidalLinear ℂ A]
  [RightRigidCategory A] [Simple (𝟙_ A)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton A ι)

/-- An actual minimal nondegenerate braided extension for a boundary whose
Müger center is `Rep(C₂)`. Minimality is the actual FP-dimension equality. -/
structure MinimalBraidedExtension where
  ambient : Type u'
  [category : Category.{v'} ambient]
  [preadditive : Preadditive ambient]
  [linear : Linear ℂ ambient]
  [kernels : HasKernels ambient]
  [biproducts : HasFiniteBiproducts ambient]
  [finiteHom : ∀ X Y : ambient, FiniteDimensional ℂ (X ⟶ Y)]
  [monoidal : MonoidalCategory ambient]
  [monoidalPreadditive : MonoidalPreadditive ambient]
  [monoidalLinear : MonoidalLinear ℂ ambient]
  [rightRigid : RightRigidCategory ambient]
  [simpleUnit : Simple (𝟙_ ambient)]
  [braiding : BraidedCategory ambient]
  index : Type w'
  [finiteIndex : Fintype index]
  skeleton : FiniteSemisimpleSkeleton ambient index
  inclusion : A ⥤ ambient
  [inclusionAdditive : inclusion.Additive]
  [inclusionLinear : inclusion.Linear ℂ]
  [inclusionBraided : inclusion.Braided]
  [inclusionFull : inclusion.Full]
  [inclusionFaithful : inclusion.Faithful]
  nondegenerate : IsNondegenerate (C := ambient)
  minimal : skeleton.fusionBasis.totalFPdim = 2 * S.fusionBasis.totalFPdim

attribute [instance] MinimalBraidedExtension.category MinimalBraidedExtension.preadditive
  MinimalBraidedExtension.linear MinimalBraidedExtension.kernels MinimalBraidedExtension.biproducts
  MinimalBraidedExtension.finiteHom MinimalBraidedExtension.monoidal
  MinimalBraidedExtension.monoidalPreadditive MinimalBraidedExtension.monoidalLinear
  MinimalBraidedExtension.rightRigid MinimalBraidedExtension.simpleUnit
  MinimalBraidedExtension.braiding MinimalBraidedExtension.finiteIndex
  MinimalBraidedExtension.inclusionAdditive MinimalBraidedExtension.inclusionLinear
  MinimalBraidedExtension.inclusionBraided MinimalBraidedExtension.inclusionFull
  MinimalBraidedExtension.inclusionFaithful

/-- The exact original categorical goal of Lemma A.1: existence of an
actual minimal extension, and trivialization of every specified pair in
every such extension. This is a proposition, not an assumed classification. -/
def LemmaA1Statement : Prop :=
  Nonempty (TannakianCenter A (Multiplicative (ZMod 2))) →
    Nonempty (MinimalBraidedExtension.{v,u,w,v',u',w'} S) ∧
      ∀ E : MinimalBraidedExtension.{v,u,w,v',u',w'} S,
        ∀ P : BoundaryAutoequivalence E.inclusion, P.Trivializable

end Extension
end Paper18.Category
