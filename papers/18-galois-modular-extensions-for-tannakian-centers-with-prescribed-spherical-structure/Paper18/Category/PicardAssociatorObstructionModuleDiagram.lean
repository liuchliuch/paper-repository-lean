import Paper18.Category.PicardAssociatorObstructionScalar
import Paper18.Category.PicardAssociatorObstructionAssociahedron
import Paper18.Category.ModuleFunctorFiniteBasic

/-! # Scalar defects derived from actual module-functor diagrams

All twenty-one arrows are actual module natural isomorphisms. Each of the
six defects is extracted by component Schur theory; neither the defects nor
their cocycle equation are fields of the diagram.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonoidalLeftAction
universe v u vM uM vN uN w
namespace Paper18.Category.PicardAssociatorObstruction
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  {M : Type uM} [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [HasKernels M] [HasFiniteBiproducts M]
  [∀ X Y : M, FiniteDimensional ℂ (X ⟶ Y)] [MonoidalLeftAction C M]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Additive]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Linear ℂ]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton M ι) (i : ι)
  {N : Type uN} [Category.{vN} N] [Preadditive N] [Linear ℂ N] [MonoidalLeftAction C N]
  [∀ X : C, (MonoidalLeftAction.actionLeft N X).Additive]
  [∀ X : C, (MonoidalLeftAction.actionLeft N X).Linear ℂ]

/-- The actual underlying natural isomorphism, with explicit functor endpoints. -/
def underlyingIso
    {F H : ModuleFunctor.Bundled C (ModuleComponent.Component (C := C) S i) N}
    (a : F ≅ H) : F.toFunctor ≅ H.toFunctor where
  hom := a.hom.val
  inv := a.inv.val
  hom_inv_id := congrArg Subtype.val a.hom_inv_id
  inv_hom_id := congrArg Subtype.val a.inv_hom_id

instance underlyingIso_moduleNatural
    {F H : ModuleFunctor.Bundled C (ModuleComponent.Component (C := C) S i) N}
    (a : F ≅ H) : ModuleFunctor.IsModuleNatural C (underlyingIso S i a).hom :=
  a.hom.property

/-- The unique complex-unit ratio of two actual bundled module comparisons. -/
def bundledComparisonScalar {F H : ModuleFunctor.Bundled C (ModuleComponent.Component (C := C) S i) N} [F.toFunctor.Full] [F.toFunctor.Faithful]
    (a b : F ≅ H) : ℂˣ :=
  comparisonScalar S i (underlyingIso S i a) (underlyingIso S i b)

lemma bundledComparisonScalar_spec {F H : ModuleFunctor.Bundled C (ModuleComponent.Component (C := C) S i) N} [F.toFunctor.Full] [F.toFunctor.Faithful]
    (a b : F ≅ H) : a.hom = (bundledComparisonScalar S i a b : ℂ) • b.hom := by
  apply Subtype.ext
  apply NatTrans.ext
  funext X
  exact comparisonScalar_spec S i (underlyingIso S i a) (underlyingIso S i b) X

lemma bundledComparisonScalar_eq
    {F H : ModuleFunctor.Bundled C (ModuleComponent.Component (C := C) S i) N}
    [F.toFunctor.Full] [F.toFunctor.Faithful] (a b : F ≅ H) (z : ℂˣ)
    (h : a.hom = (z : ℂ) • b.hom) : bundledComparisonScalar S i a b = z := by
  apply comparisonScalar_eq S i (underlyingIso S i a) (underlyingIso S i b) z
  intro X
  exact congrArg (fun f => f.val.app X) h

omit [RightRigidCategory C]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Linear ℂ] in
lemma bundled_id_ne_zero (F : ModuleFunctor.Bundled C (ModuleComponent.Component (C := C) S i) N) [F.toFunctor.Faithful] : 𝟙 F ≠ 0 := by
  intro h
  have hh := congrArg (fun f : F ⟶ F => f.val.app (ModuleComponent.base (C := C) S i)) h
  have hz : 𝟙 (F.toFunctor.obj (ModuleComponent.base (C := C) S i)) = 0 := hh
  apply CategoryTheory.id_nonzero (ModuleComponent.base (C := C) S i)
  apply F.toFunctor.map_injective
  simpa only [F.toFunctor.map_id, F.toFunctor.map_zero] using hz

variable (D : AssociahedronDiagram
  (ModuleFunctor.Bundled C (ModuleComponent.Component (C := C) S i) N))
  [(D.obj 0).toFunctor.Full] [(D.obj 0).toFunctor.Faithful]
  [(D.obj 1).toFunctor.Full] [(D.obj 1).toFunctor.Faithful]
  [(D.obj 2).toFunctor.Full] [(D.obj 2).toFunctor.Faithful]
  [(D.obj 5).toFunctor.Full] [(D.obj 5).toFunctor.Faithful]
  [(D.obj 9).toFunctor.Full] [(D.obj 9).toFunctor.Faithful]

/-- The six face defects, extracted from actual comparison isomorphisms. -/
def moduleFaceScalars : Fin 6 → ℂˣ
  | 0 => bundledComparisonScalar S i (D.q ≪≫ D.s ≪≫ D.z) (D.r ≪≫ D.t)
  | 1 => bundledComparisonScalar S i (D.b ≪≫ D.g ≪≫ D.n) (D.c ≪≫ D.l)
  | 2 => bundledComparisonScalar S i (D.d ≪≫ D.i ≪≫ D.r) (D.e ≪≫ D.m)
  | 3 => bundledComparisonScalar S i (D.f ≪≫ D.j ≪≫ D.s) (D.g ≪≫ D.o)
  | 4 => bundledComparisonScalar S i (D.k ≪≫ D.m ≪≫ D.t) (D.l ≪≫ D.p)
  | 5 => bundledComparisonScalar S i (D.a ≪≫ D.d ≪≫ D.h) (D.b ≪≫ D.f)

/-- Component Schur theory and five-input path cancellation derive the
four-cocycle relation. Only the three disjoint-move interchange squares
are required; no pentagonal face is assumed to commute. -/
theorem moduleFaceScalars_cocycle
    (sq₁ : D.a.hom ≫ D.e.hom = D.c.hom ≫ D.k.hom)
    (sq₂ : D.h.hom ≫ D.j.hom = D.i.hom ≫ D.q.hom)
    (sq₃ : D.n.hom ≫ D.p.hom = D.o.hom ≫ D.z.hom) :
    moduleFaceScalars S i D 0 * moduleFaceScalars S i D 2 * moduleFaceScalars S i D 4 =
      moduleFaceScalars S i D 1 * moduleFaceScalars S i D 3 * moduleFaceScalars S i D 5 := by
  apply D.scalar_faces_cocycle (moduleFaceScalars S i D)
    (bundled_id_ne_zero S i _) sq₁ sq₂ sq₃
  · exact bundledComparisonScalar_spec S i (D.q ≪≫ D.s ≪≫ D.z) (D.r ≪≫ D.t)
  · exact bundledComparisonScalar_spec S i (D.b ≪≫ D.g ≪≫ D.n) (D.c ≪≫ D.l)
  · exact bundledComparisonScalar_spec S i (D.d ≪≫ D.i ≪≫ D.r) (D.e ≪≫ D.m)
  · exact bundledComparisonScalar_spec S i (D.f ≪≫ D.j ≪≫ D.s) (D.g ≪≫ D.o)
  · exact bundledComparisonScalar_spec S i (D.k ≪≫ D.m ≪≫ D.t) (D.l ≪≫ D.p)
  · exact bundledComparisonScalar_spec S i (D.a ≪≫ D.d ≪≫ D.h) (D.b ≪≫ D.f)

end Paper18.Category.PicardAssociatorObstruction
