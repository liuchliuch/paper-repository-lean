import Paper18.Category.FixedBoundaryBasic
import Paper18.Category.FixedBoundaryModules

/-!
# The specified boundary identifies the actual regular algebra

For every internal boundary algebra `R`, the given monoidal natural
isomorphism `α` induces an actual algebra isomorphism `F(iR) ≅ iR`.
Consequently the fixed-boundary pair acts on actual internal `iR`-modules.
-/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped MonObj Obj
universe v u v' u'
namespace Paper18.Category
variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℂ A]
  [MonoidalCategory A] [BraidedCategory A]
  {N : Type u'} [Category.{v'} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N]
  {i : A ⥤ N} [i.Monoidal] (P : BoundaryAutoequivalence i) (R : A) [MonObj R]

/-- The boundary comparison lifted to an isomorphism of actual internal
monoid objects, with the composite tensorator comparison included. -/
def BoundaryAutoequivalence.boundaryAlgebraMonIso :
    P.functor.mapMon.obj (i.mapMon.obj (Mon.mk R)) ≅ i.mapMon.obj (Mon.mk R) :=
  (Functor.mapMonCompIso (F := i) (G := P.functor)).symm.app (Mon.mk R) ≪≫
    (Functor.mapMonNatIso P.boundary).app (Mon.mk R)

/-- The actual isomorphism on the underlying boundary algebra. -/
def BoundaryAutoequivalence.boundaryAlgebraIso :
    P.functor.obj (i.obj R) ≅ i.obj R :=
  (Mon.forget N).mapIso (P.boundaryAlgebraMonIso R)

instance BoundaryAutoequivalence.boundaryAlgebraIsoIsMonHom :
    IsMonHom (P.boundaryAlgebraIso R).hom :=
  (P.boundaryAlgebraMonIso R).hom.isMonHom_hom

instance BoundaryAutoequivalence.boundaryAlgebraIsoInvIsMonHom :
    IsMonHom (P.boundaryAlgebraIso R).inv :=
  (P.boundaryAlgebraMonIso R).inv.isMonHom_hom

omit [Preadditive A] [Linear ℂ A] [BraidedCategory A] in
@[simp] theorem BoundaryAutoequivalence.boundaryAlgebraIso_hom :
    (P.boundaryAlgebraIso R).hom = P.boundary.hom.app R := by
  change 𝟙 _ ≫ P.boundary.hom.app R = _
  exact Category.id_comp _

omit [Preadditive A] [Linear ℂ A] [BraidedCategory A] in
@[simp] theorem BoundaryAutoequivalence.boundaryAlgebraIso_inv :
    (P.boundaryAlgebraIso R).inv = P.boundary.inv.app R := by
  change P.boundary.inv.app R ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- The actual functor on internal modules induced by the specified pair
`(F,α)`. Restriction uses precisely `α_R⁻¹`, retaining the chosen boundary. -/
def BoundaryAutoequivalence.moduleFunctor : Mod_ N (i.obj R) ⥤ Mod_ N (i.obj R) :=
  InternalModule.mapModules P.functor ⋙ Mod_.comap (P.boundaryAlgebraIso R).inv

omit [Preadditive A] [Linear ℂ A] [BraidedCategory A] in
@[simp] theorem BoundaryAutoequivalence.moduleFunctor_obj_X (M : Mod_ N (i.obj R)) :
    ((P.moduleFunctor R).obj M).X = P.functor.obj M.X := rfl

omit [Preadditive A] [Linear ℂ A] [BraidedCategory A] in
@[simp] theorem BoundaryAutoequivalence.moduleFunctor_map_hom
    {M L : Mod_ N (i.obj R)} (f : M ⟶ L) :
    ((P.moduleFunctor R).map f).hom = P.functor.map f.hom := rfl

variable {P} {Q : BoundaryAutoequivalence i}

/-- Equation A.1 identifies the inverse algebra comparisons exactly. -/
theorem BoundaryIso.inverse_algebra (f : BoundaryIso i P Q) :
    (P.boundaryAlgebraIso R).inv ≫ f.iso.hom.app (i.obj R) =
      (Q.boundaryAlgebraIso R).inv := by
  apply (cancel_mono (Q.boundaryAlgebraIso R).hom).mp
  rw [Category.assoc]
  have hb : f.iso.hom.app (i.obj R) ≫ (Q.boundaryAlgebraIso R).hom =
      (P.boundaryAlgebraIso R).hom := by
    simpa only [BoundaryAutoequivalence.boundaryAlgebraIso_hom] using f.boundary R
  rw [hb, Iso.inv_hom_id, Iso.inv_hom_id]

/-- A fixed-boundary natural isomorphism induces an actual module map on
every module, with the chosen boundary algebra comparisons respected. -/
def BoundaryIso.moduleHom (f : BoundaryIso i P Q) (M : Mod_ N (i.obj R)) :
    (P.moduleFunctor R).obj M ⟶ (Q.moduleFunctor R).obj M :=
  Mod_.Hom.mk' (f.iso.hom.app M.X) (by
    change ((P.boundaryAlgebraIso R).inv ▷ P.functor.obj M.X ≫
        Functor.LaxMonoidal.μ P.functor (i.obj R) M.X ≫ P.functor.map γ[i.obj R,M.X]) ≫
          f.iso.hom.app M.X =
      (i.obj R ◁ f.iso.hom.app M.X) ≫ (Q.boundaryAlgebraIso R).inv ▷ Q.functor.obj M.X ≫
        Functor.LaxMonoidal.μ Q.functor (i.obj R) M.X ≫ Q.functor.map γ[i.obj R,M.X]
    simp only [Category.assoc]
    rw [f.iso.hom.naturality]
    rw [NatTrans.IsMonoidal.tensor_assoc]
    simp only [MonoidalCategory.tensorHom_def, Category.assoc]
    rw [← comp_whiskerRight_assoc, f.inverse_algebra R]
    rw [whisker_exchange_assoc])

/-- The induced actual module isomorphism. -/
def BoundaryIso.moduleIso (f : BoundaryIso i P Q) (M : Mod_ N (i.obj R)) :
    (P.moduleFunctor R).obj M ≅ (Q.moduleFunctor R).obj M where
  hom := f.moduleHom R M
  inv := (f.symm i).moduleHom R M
  hom_inv_id := by
    apply Mod_.Hom.ext
    exact f.iso.hom_inv_id_app M.X
  inv_hom_id := by
    apply Mod_.Hom.ext
    exact f.iso.inv_hom_id_app M.X

/-- Fixed-boundary morphisms induce actual natural isomorphisms on the
module categories used for de-equivariantization. -/
def BoundaryIso.moduleNatIso (f : BoundaryIso i P Q) :
    P.moduleFunctor R ≅ Q.moduleFunctor R :=
  NatIso.ofComponents (f.moduleIso R) (fun {M L} g => by
    apply Mod_.Hom.ext
    exact f.iso.hom.naturality g.hom)

/-- The specified-boundary groupoid acts functorially on actual module
categories. This is a categorical construction, without a cochain model. -/
def fixedBoundaryModuleFunctor : BoundaryAutoequivalence i ⥤
    (Mod_ N (i.obj R) ⥤ Mod_ N (i.obj R)) where
  obj P := P.moduleFunctor R
  map f := (f.moduleNatIso R).hom
  map_id P := by
    ext M
    rfl
  map_comp f g := by
    ext M
    rfl

end Paper18.Category
