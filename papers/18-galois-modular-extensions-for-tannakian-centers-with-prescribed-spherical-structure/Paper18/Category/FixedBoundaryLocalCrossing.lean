import Paper18.Category.FixedBoundaryModuleFunctorMonoidal
import Paper18.Category.LocalModulesCenterLinear
import Paper18.Category.CentralizerClosure

/-!
# The actual boundary functor preserves neutral/odd crossings

The braided ambient functor and the specified comparison on the algebra
preserve locality. Its actual relative tensorator intertwines the positive
crossing, hence also the inverse crossing defining the central lift. No
braiding on the category of all modules is used.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
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

/-- Locality is preserved by the actual specified-boundary module functor. -/
theorem BoundaryAutoequivalence.moduleFunctor_isLocal
    (M : Mod_ N (i.obj R)) (hM : IsLocalModule M) :
    IsLocalModule ((P.moduleFunctor R).obj M) := by
  rw [isLocalModule_iff]
  change (doubleBraiding (i.obj R) (P.functor.obj M.X)).hom ≫
      ((P.boundaryAlgebraIso R).inv ▷ P.functor.obj M.X) ≫
        Functor.LaxMonoidal.μ P.functor (i.obj R) M.X ≫
          P.functor.map γ[i.obj R,M.X] = _
  rw [← doubleBraiding_naturality_left_assoc,
    ← reassoc_of% (tensorator_map_doubleBraiding P.functor (i.obj R) M.X),
    ← P.functor.map_comp]
  rw [(isLocalModule_iff M).mp hM]
  rfl

/-- The actual relative tensorator preserves the positive local crossing. -/
theorem BoundaryAutoequivalence.moduleFunctor_localCrossing
    (M L : Mod_ N (i.obj R)) (hL : IsLocalModule L) :
    Functor.LaxMonoidal.μ (P.moduleFunctor R) M L ≫
        (P.moduleFunctor R).map (localBraidingHom M L hL) =
      localBraidingHom ((P.moduleFunctor R).obj M) ((P.moduleFunctor R).obj L)
        (P.moduleFunctor_isLocal R L hL) ≫
          Functor.LaxMonoidal.μ (P.moduleFunctor R) L M := by
  apply module_hom_ext
  change π ((P.moduleFunctor R).obj M) ((P.moduleFunctor R).obj L) ≫
      (Functor.LaxMonoidal.μ (P.moduleFunctor R) M L).hom ≫
        P.functor.map (localBraidingHom M L hL).hom =
    π ((P.moduleFunctor R).obj M) ((P.moduleFunctor R).obj L) ≫
      (localBraidingHom ((P.moduleFunctor R).obj M) ((P.moduleFunctor R).obj L)
        (P.moduleFunctor_isLocal R L hL)).hom ≫
          (Functor.LaxMonoidal.μ (P.moduleFunctor R) L M).hom
  rw [P.π_moduleFunctor_μ_assoc, ← P.functor.map_comp,
    π_localBraidingHom, P.functor.map_comp,
    π_localBraidingHom_assoc, P.π_moduleFunctor_μ]
  exact Functor.LaxBraided.braided_assoc M.X L.X _

/-- The inverse crossing giving the actual local central lift is preserved
as well, with the same specified-boundary tensorator. -/
theorem BoundaryAutoequivalence.moduleFunctor_localHalfBraiding
    (S : SeparableAlgebra (i.obj R))
    (M Y : Mod_ N (i.obj R)) (hM : IsLocalModule M) :
    Functor.LaxMonoidal.μ (P.moduleFunctor R) M Y ≫
        (P.moduleFunctor R).map ((S.localHalfBraiding M hM).β Y).hom =
      ((S.localHalfBraiding ((P.moduleFunctor R).obj M)
        (P.moduleFunctor_isLocal R M hM)).β ((P.moduleFunctor R).obj Y)).hom ≫
          Functor.LaxMonoidal.μ (P.moduleFunctor R) Y M := by
  let c := S.localCrossingIso M Y hM
  let c' := S.localCrossingIso ((P.moduleFunctor R).obj M)
    ((P.moduleFunctor R).obj Y) (P.moduleFunctor_isLocal R M hM)
  change Functor.LaxMonoidal.μ (P.moduleFunctor R) M Y ≫
      (P.moduleFunctor R).map c.inv =
    c'.inv ≫ Functor.LaxMonoidal.μ (P.moduleFunctor R) Y M
  apply (cancel_epi c'.hom).mp
  have hc : Functor.LaxMonoidal.μ (P.moduleFunctor R) Y M ≫
      (P.moduleFunctor R).map c.hom =
    c'.hom ≫ Functor.LaxMonoidal.μ (P.moduleFunctor R) M Y :=
    P.moduleFunctor_localCrossing R Y M hM
  rw [← Category.assoc, ← hc, Category.assoc, ← Functor.map_comp,
    c.hom_inv_id, (P.moduleFunctor R).map_id, Category.comp_id, Iso.hom_inv_id_assoc]

/-- Inserting the specified comparison on a local object gives the
actual left/right module-lineator compatibility. The comparison is an
actual module isomorphism, so its central commutation law is proved by
the already constructed local center functor. -/
theorem BoundaryAutoequivalence.moduleFunctor_localHalfBraiding_boundary
    (S : SeparableAlgebra (i.obj R))
    (M Y : Mod_ N (i.obj R)) (hM : IsLocalModule M)
    (a : (P.moduleFunctor R).obj M ≅ M) :
    (a.inv ▷ (P.moduleFunctor R).obj Y) ≫
        Functor.LaxMonoidal.μ (P.moduleFunctor R) M Y ≫
          (P.moduleFunctor R).map ((S.localHalfBraiding M hM).β Y).hom =
      ((S.localHalfBraiding M hM).β ((P.moduleFunctor R).obj Y)).hom ≫
        ((P.moduleFunctor R).obj Y ◁ a.inv) ≫
          Functor.LaxMonoidal.μ (P.moduleFunctor R) Y M := by
  rw [P.moduleFunctor_localHalfBraiding]
  have ha := (S.localCenterMap
    (M := ⟨M, hM⟩)
    (N := ⟨(P.moduleFunctor R).obj M, P.moduleFunctor_isLocal R M hM⟩) a.inv).comm
      ((P.moduleFunctor R).obj Y)
  change (a.inv ▷ (P.moduleFunctor R).obj Y) ≫
      ((S.localHalfBraiding ((P.moduleFunctor R).obj M)
        (P.moduleFunctor_isLocal R M hM)).β ((P.moduleFunctor R).obj Y)).hom =
    ((S.localHalfBraiding M hM).β ((P.moduleFunctor R).obj Y)).hom ≫
      ((P.moduleFunctor R).obj Y ◁ a.inv) at ha
  exact (reassoc_of% ha) _

end Paper18.Category
