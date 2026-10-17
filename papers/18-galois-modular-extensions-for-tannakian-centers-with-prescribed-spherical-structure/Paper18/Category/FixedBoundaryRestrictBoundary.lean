import Paper18.Category.FixedBoundaryBasic

/-! # Restriction retains the prescribed boundary identification -/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
universe v u v' u' v'' u''
namespace Paper18.Category

section Whisker
variable {B : Type u} [Category.{v} B] [MonoidalCategory B]
  {A : Type u'} [Category.{v'} A] [MonoidalCategory A]
  {N : Type u''} [Category.{v''} N] [MonoidalCategory N]
  (K : B ⥤ A) [K.Monoidal] {F G : A ⥤ N} [F.Monoidal] [G.Monoidal]
  (τ : F ⟶ G) [NatTrans.IsMonoidal τ]

instance fixedBoundaryWhiskerLeftMonoidal : NatTrans.IsMonoidal (Functor.whiskerLeft K τ) where
  unit := by
    simp only [Functor.LaxMonoidal.comp_ε, Functor.whiskerLeft_app, Category.assoc]
    rw [τ.naturality, NatTrans.IsMonoidal.unit_assoc]
  tensor X Y := by
    simp only [Functor.LaxMonoidal.comp_μ, Functor.whiskerLeft_app, Category.assoc]
    rw [τ.naturality, NatTrans.IsMonoidal.tensor_assoc]

end Whisker

section Restrict
variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℂ B]
  [MonoidalCategory B] [BraidedCategory B]
  {A : Type u'} [Category.{v'} A] [Preadditive A] [Linear ℂ A]
  [MonoidalCategory A] [BraidedCategory A]
  {N : Type u''} [Category.{v''} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N]
  {i : A ⥤ N} [i.Monoidal] (K : B ⥤ A) [K.Monoidal]

/-- Restricting the boundary retains the actual `α` components. -/
def BoundaryAutoequivalence.restrictBoundary (P : BoundaryAutoequivalence i) :
    BoundaryAutoequivalence (K ⋙ i) where
  functor := P.functor
  boundary := Functor.associator K i P.functor ≪≫ Functor.isoWhiskerLeft K P.boundary
  boundaryMonoidal := by
    change NatTrans.IsMonoidal
      ((Functor.associator K i P.functor).hom ≫ Functor.whiskerLeft K P.boundary.hom)
    infer_instance

@[simp] theorem BoundaryAutoequivalence.restrictBoundary_app
    (P : BoundaryAutoequivalence i) (X : B) :
    (P.restrictBoundary K).boundary.hom.app X = P.boundary.hom.app (K.obj X) := by
  change 𝟙 _ ≫ P.boundary.hom.app (K.obj X) = _
  exact Category.id_comp _

/-- A boundary-preserving isomorphism remains boundary preserving after
restriction; the underlying actual natural isomorphism is unchanged. -/
def BoundaryIso.restrictBoundary {P Q : BoundaryAutoequivalence i}
    (f : BoundaryIso i P Q) : BoundaryIso (K ⋙ i) (P.restrictBoundary K) (Q.restrictBoundary K) where
  iso := f.iso
  boundary X := by
    rw [BoundaryAutoequivalence.restrictBoundary_app, BoundaryAutoequivalence.restrictBoundary_app]
    exact f.boundary (K.obj X)

end Restrict
end Paper18.Category
