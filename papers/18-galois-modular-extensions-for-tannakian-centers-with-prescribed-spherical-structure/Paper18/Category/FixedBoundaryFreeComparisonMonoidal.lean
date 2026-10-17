import Paper18.Category.FixedBoundaryFreeComparisonMonoidalBasic
import Paper18.Category.TannakianActionMonoidal

/-! # Monoidality of the actual specified free-module comparison -/
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

/-- The algebra unit and the actual free generators prove the unit law;
the balancing quotient and the original tensorator prove the tensor law. -/
instance BoundaryAutoequivalence.moduleFreeNatIsoMonoidal :
    NatTrans.IsMonoidal (P.moduleFreeNatIso R).hom where
  unit := by
    apply (cancel_epi (freeUnitIso (A := i.obj R)).inv).mp
    apply free_hom_ext
    simp only [Functor.LaxMonoidal.comp_ε, Mod_.comp_hom, Category.assoc]
    change freeUnit (A := i.obj R) (𝟙_ N) ≫ (freeUnitIso (A := i.obj R)).inv.hom ≫
        (Functor.LaxMonoidal.ε (InternalModule.freeFunctor (A := i.obj R))).hom ≫
        (InternalModule.freeMap (Functor.LaxMonoidal.ε P.functor)).hom ≫
        (P.moduleFreeIso R (𝟙_ N)).hom.hom =
      freeUnit (A := i.obj R) (𝟙_ N) ≫ (freeUnitIso (A := i.obj R)).inv.hom ≫
        (Functor.LaxMonoidal.ε (P.moduleFunctor R)).hom ≫
        P.functor.map (Functor.LaxMonoidal.ε (InternalModule.freeFunctor (A := i.obj R))).hom
    simp only [freeUnit_freeUnitIso_inv_assoc]
    rw [BoundaryAutoequivalence.freeUnit_freeFunctor_unit_assoc,
      freeUnit_naturality_assoc, P.freeUnit_moduleFreeIso,
      P.moduleFunctor_ε_hom, P.boundaryAlgebraIso_inv_unit_assoc R]
    rw [← P.functor.map_comp,
      BoundaryAutoequivalence.freeUnit_freeFunctor_unit]
  tensor X Y := by
    apply (cancel_epi (freeTensorIso (A := i.obj R) (P.functor.obj X)
      (P.functor.obj Y)).inv).mp
    apply free_hom_ext
    simp only [Functor.LaxMonoidal.comp_μ, Mod_.comp_hom, Category.assoc]
    change freeUnit (A := i.obj R) (P.functor.obj X ⊗ P.functor.obj Y) ≫
        (freeTensorIso (A := i.obj R) (P.functor.obj X) (P.functor.obj Y)).inv.hom ≫
        (Functor.LaxMonoidal.μ (InternalModule.freeFunctor (A := i.obj R))
          (P.functor.obj X) (P.functor.obj Y)).hom ≫
        (InternalModule.freeMap (Functor.LaxMonoidal.μ P.functor X Y)).hom ≫
        (P.moduleFreeIso R (X ⊗ Y)).hom.hom =
      freeUnit (A := i.obj R) (P.functor.obj X ⊗ P.functor.obj Y) ≫
        (freeTensorIso (A := i.obj R) (P.functor.obj X) (P.functor.obj Y)).inv.hom ≫
        ((P.moduleFreeIso R X).hom ⊗ₘ (P.moduleFreeIso R Y).hom).hom ≫
        (Functor.LaxMonoidal.μ (P.moduleFunctor R)
          (InternalModule.free (i.obj R) X) (InternalModule.free (i.obj R) Y)).hom ≫
        P.functor.map (Functor.LaxMonoidal.μ (InternalModule.freeFunctor (A := i.obj R)) X Y).hom
    simp only [freeUnit_freeTensorIso_inv_assoc]
    rw [BoundaryAutoequivalence.freeUnit_freeFunctor_tensor_assoc,
      freeUnit_naturality_assoc, P.freeUnit_moduleFreeIso, π_tensorHom_assoc,
      P.π_moduleFunctor_μ_assoc, tensorHom_comp_tensorHom_assoc,
      P.freeUnit_moduleFreeIso, P.freeUnit_moduleFreeIso,
      Functor.LaxMonoidal.μ_natural_assoc]
    simp only [Category.assoc, ← P.functor.map_comp]
    rw [BoundaryAutoequivalence.freeUnit_freeFunctor_tensor]

end Paper18.Category
