import Paper18.Category.FixedBoundaryFreeComparison

/-! # Actual generators of the specified free-module comparison -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped MonObj Obj
universe v u v' u'
namespace Paper18.Category
open RelativeTensor
variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℂ A]
  [MonoidalCategory A] [BraidedCategory A]
  {N : Type u'} [Category.{v'} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N]
  [RightRigidCategory N] [HasCoequalizers N]
  {i : A ⥤ N} [i.Braided] (P : BoundaryAutoequivalence i) (R : A)
  [MonObj R] [IsCommMonObj R]

/-- The inverse specified algebra component preserves the actual unit. -/
@[reassoc] theorem BoundaryAutoequivalence.boundaryAlgebraIso_inv_unit :
    η[i.obj R] ≫ (P.boundaryAlgebraIso R).inv =
      Functor.LaxMonoidal.ε P.functor ≫ P.functor.map η[i.obj R] := by
  letI := P.boundaryAlgebraIsoInvIsMonHom R
  exact IsMonHom.one_hom (P.boundaryAlgebraIso R).inv

/-- On actual free generators, the comparison is exactly the original
functor applied to the original free generator. -/
@[reassoc] theorem BoundaryAutoequivalence.freeUnit_moduleFreeIso (X : N) :
    freeUnit (A := i.obj R) (P.functor.obj X) ≫ (P.moduleFreeIso R X).hom.hom =
      P.functor.map (freeUnit (A := i.obj R) X) := by
  rw [P.moduleFreeIso_hom]
  unfold freeUnit
  rw [Category.assoc, ← comp_whiskerRight_assoc, P.boundaryAlgebraIso_inv_unit R,
    comp_whiskerRight]
  rw [Category.assoc, Functor.LaxMonoidal.μ_natural_left]
  have hu := Functor.LaxMonoidal.left_unitality P.functor X
  have hu' : (λ_ (P.functor.obj X)).inv ≫
      Functor.LaxMonoidal.ε P.functor ▷ P.functor.obj X ≫
      Functor.LaxMonoidal.μ P.functor (𝟙_ N) X = P.functor.map (λ_ X).inv := by
    apply (cancel_mono (P.functor.map (λ_ X).hom)).mp
    rw [← P.functor.map_comp, Iso.inv_hom_id, P.functor.map_id]
    simpa only [Category.assoc, Iso.inv_hom_id] using
      congrArg (fun f => (λ_ (P.functor.obj X)).inv ≫ f) hu.symm
  simpa only [Category.assoc, P.functor.map_comp] using
    congrArg (fun f => f ≫ P.functor.map (η[i.obj R] ▷ X)) hu'

@[reassoc] theorem BoundaryAutoequivalence.freeUnit_freeFunctor_unit :
    η[i.obj R] ≫ (Functor.LaxMonoidal.ε (InternalModule.freeFunctor (A := i.obj R))).hom =
      freeUnit (A := i.obj R) (𝟙_ N) := by
  rw [freeFunctor_ε_eq]
  change η[i.obj R] ≫ (ρ_ (i.obj R)).inv = (λ_ (𝟙_ N)).inv ≫ η[i.obj R] ▷ (𝟙_ N)
  rw [rightUnitor_inv_naturality]
  monoidal

/-- Actual tensor generators are carried to the generator of their tensor. -/
@[reassoc] theorem BoundaryAutoequivalence.freeUnit_freeFunctor_tensor (X Y : N) :
    (freeUnit (A := i.obj R) X ⊗ₘ freeUnit (A := i.obj R) Y) ≫
      π (InternalModule.free (i.obj R) X) (InternalModule.free (i.obj R) Y) ≫
      (Functor.LaxMonoidal.μ (InternalModule.freeFunctor (A := i.obj R)) X Y).hom =
      freeUnit (A := i.obj R) (X ⊗ Y) := by
  rw [freeFunctor_μ_eq]
  have hi := congrArg Mod_.Hom.hom (freeTensorIso (A := i.obj R) X Y).inv_hom_id
  change (freeTensorIso X Y).inv.hom ≫ (freeTensorIso X Y).hom.hom = 𝟙 _ at hi
  calc
    _ = (freeUnit (X ⊗ Y) ≫ (freeTensorIso X Y).inv.hom) ≫
        (freeTensorIso X Y).hom.hom :=
      by simpa only [Category.assoc] using
        congrArg (fun f => f ≫ (freeTensorIso X Y).hom.hom)
          (freeUnit_freeTensorIso_inv (A := i.obj R) X Y).symm
    _ = _ := by rw [Category.assoc, hi, Category.comp_id]

end Paper18.Category
