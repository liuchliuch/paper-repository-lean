import Paper18.Category.FixedBoundaryNeutral
import Paper18.Category.FixedBoundaryModuleFunctorMonoidal
import Paper18.Category.TannakianActionMonoidal

/-!
# The specified de-equivariant neutral comparison is monoidal

The tensor equation descends through the actual relative-tensor quotient
maps from the original monoidality of α. The unit equation is precisely
the cancellation of α_R with the chosen algebra comparison α_R inverse.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj Obj
universe v u v' u'
namespace Paper18.Category
open RelativeTensor
variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℂ A]
  [MonoidalCategory A] [BraidedCategory A] [RightRigidCategory A] [HasCoequalizers A]
  {N : Type u'} [Category.{v'} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N] [RightRigidCategory N] [HasCoequalizers N]
  {i : A ⥤ N} [i.Braided] [PreservesColimitsOfShape WalkingParallelPair i]
  (P : BoundaryAutoequivalence i) (R : A) [MonObj R] [IsCommMonObj R]

/-- The actual neutral-boundary module comparison retains the original
specified α and is a genuine monoidal natural isomorphism. -/
instance BoundaryAutoequivalence.moduleBoundaryNatIsoMonoidal :
    NatTrans.IsMonoidal (P.moduleBoundaryNatIso R).hom where
  unit := by
    apply Mod_.Hom.ext
    simp only [Functor.LaxMonoidal.comp_ε, Mod_.comp_hom, Category.assoc]
    change (Functor.LaxMonoidal.ε (P.moduleFunctor R)).hom ≫
      P.functor.map (𝟙 (i.obj R)) ≫ P.boundary.hom.app R = 𝟙 (i.obj R)
    rw [P.moduleFunctor_ε_hom]
    change (P.boundaryAlgebraIso R).inv ≫ P.functor.map (𝟙 (i.obj R)) ≫
      P.boundary.hom.app R = 𝟙 (i.obj R)
    rw [P.functor.map_id, Category.id_comp, ← P.boundaryAlgebraIso_hom R,
      Iso.inv_hom_id]
  tensor M L := by
    apply module_hom_ext
    simp only [Functor.LaxMonoidal.comp_μ, Mod_.comp_hom, Category.assoc]
    change π ((P.moduleFunctor R).obj ((InternalModule.mapModules i).obj M))
        ((P.moduleFunctor R).obj ((InternalModule.mapModules i).obj L)) ≫
        (Functor.LaxMonoidal.μ (P.moduleFunctor R)
          ((InternalModule.mapModules i).obj M) ((InternalModule.mapModules i).obj L)).hom ≫
        P.functor.map (Functor.LaxMonoidal.μ (InternalModule.mapModules i) M L).hom ≫
        P.boundary.hom.app (M ⊗ L).X =
      π ((P.moduleFunctor R).obj ((InternalModule.mapModules i).obj M))
        ((P.moduleFunctor R).obj ((InternalModule.mapModules i).obj L)) ≫
        ((P.moduleBoundaryNatIso R).hom.app M ⊗ₘ
          (P.moduleBoundaryNatIso R).hom.app L).hom ≫
        (Functor.LaxMonoidal.μ (InternalModule.mapModules i) M L).hom
    have hi : π ((InternalModule.mapModules i).obj M) ((InternalModule.mapModules i).obj L) ≫
        (Functor.LaxMonoidal.μ (InternalModule.mapModules i) M L).hom =
        Functor.LaxMonoidal.μ i M.X L.X ≫ i.map (π M L) :=
      InternalModule.π_mapModules_μ i M L
    rw [P.π_moduleFunctor_μ_assoc, π_tensorHom_assoc, hi]
    rw [← P.functor.map_comp_assoc, hi,
      P.functor.map_comp]
    simp only [Category.assoc]
    have hn := P.boundary.hom.naturality (π M L)
    change P.functor.map (i.map (π M L)) ≫ P.boundary.hom.app (M ⊗ L).X =
      P.boundary.hom.app (M.X ⊗ L.X) ≫ i.map (π M L) at hn
    rw [hn]
    change Functor.LaxMonoidal.μ P.functor (i.obj M.X) (i.obj L.X) ≫
        P.functor.map (Functor.LaxMonoidal.μ i M.X L.X) ≫
        P.boundary.hom.app (M.X ⊗ L.X) ≫ i.map (π M L) =
      (P.boundary.hom.app M.X ⊗ₘ P.boundary.hom.app L.X) ≫
        Functor.LaxMonoidal.μ i M.X L.X ≫ i.map (π M L)
    slice_lhs 1 2 => rw [← Functor.LaxMonoidal.comp_μ]
    rw [NatTrans.IsMonoidal.tensor]
    simp only [Category.assoc]

end Paper18.Category
