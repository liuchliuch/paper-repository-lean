import Paper18.Category.FixedBoundaryTensoratorTannakian
import Paper18.Category.FixedBoundaryCrossedActionComparison

/-! # Genuine regular-action compatibility of the actual comparison -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj Obj MonoidalLeftAction
universe v u w v' u' w'
namespace Paper18.Category.FixedBoundary
variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℂ A]
  [MonoidalCategory A] [BraidedCategory A] [MonoidalPreadditive A] [MonoidalLinear ℂ A]
  [HasKernels A] [HasFiniteBiproducts A] [RightRigidCategory A] [HasCoequalizers A]
  [∀ X Y : A, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (SA : FiniteSemisimpleSkeleton A ι)
  (TC : TannakianCenter A RepresentationZ2.H)
  {N : Type u'} [Category.{v'} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N] [MonoidalPreadditive N] [MonoidalLinear ℂ N]
  [RightRigidCategory N] [HasCoequalizers N] [HasKernels N] [HasFiniteBiproducts N]
  (i : A ⥤ N) [i.Braided] [i.Full] [i.Faithful] [i.Additive] [i.Linear ℂ]
  (P : BoundaryAutoequivalence i)
local instance equivariantTensoratorImageTannakianMonObj : MonObj (i.obj TC.regularAlgebra) := Functor.monObjObj (F := i) TC.regularAlgebra
local instance equivariantTensoratorImageTannakianCommMonObj : IsCommMonObj (i.obj TC.regularAlgebra) := Functor.isCommMonObj_obj
variable (B : TensorInverse (i.obj (TC.c2Generator)))
  (himage : ∀ X : A, Centralizes (i.obj (TC.c2Generator)) (i.obj X))
  (hfull : ∀ Y : N, Centralizes (i.obj (TC.c2Generator)) Y →
    ∃ X : A, Nonempty (i.obj X ≅ Y))
  (e : P.functor.obj (i.obj (TC.c2Generator)) ≅
    i.obj (TC.c2Generator))


variable [RightRigidCategory (Mod_ N (i.obj TC.regularAlgebra))]
  [Simple (𝟙_ (Mod_ N (i.obj TC.regularAlgebra)))]
  [∀ X Y : Mod_ N (i.obj TC.regularAlgebra), FiniteDimensional ℂ (X ⟶ Y)]
  {κ : Type w'} [Fintype κ]
  (SD : FiniteSemisimpleSkeleton (Mod_ N (i.obj TC.regularAlgebra)) κ)


include B himage in
omit [MonoidalPreadditive A] [MonoidalLinear ℂ A] [HasKernels A]
  [HasFiniteBiproducts A] [RightRigidCategory A] [HasCoequalizers A]
  [∀ X Y : A, FiniteDimensional ℂ (X ⟶ Y)]
  [RightRigidCategory N] [HasCoequalizers N] [HasKernels N] [HasFiniteBiproducts N]
  [i.Full] [i.Faithful]
  [RightRigidCategory (Mod_ N (i.obj TC.regularAlgebra))]
  [Simple (𝟙_ (Mod_ N (i.obj TC.regularAlgebra)))]
  [∀ X Y : Mod_ N (i.obj TC.regularAlgebra), FiniteDimensional ℂ (X ⟶ Y)] in
/-- The actual regular algebra monodromy on an actual homogeneous module
is its genuine degree translation. This uses the actual constants/sign
resolution of Fun(C₂). -/
lemma module_regular_monodromy_of_homogeneous (d : ZMod 2)
    (Y : Mod_ N (i.obj TC.regularAlgebra))
    (hY : Homogeneous (neutralModuleCharacter i TC.regularAlgebra B himage) d Y) :
    (doubleBraiding (i.obj TC.regularAlgebra) Y.X).hom =
      i.map (regularTranslation TC.inclusion (Multiplicative.ofAdd d)) ▷ Y.X := by
  have hh := congrArg (fun f : Y ⟶ Y => f.hom) hY
  have hx : Homogeneous B.monodromyCharacter d Y.X := hh
  exact regular_doubleBraiding_eq_degreeTranslation (TC.inclusion ⋙ i) B d Y.X hx

include SD in
/-- Actual crossed preservation and rigid contraction force every monoidal
comparison to commute with both actual C₂ regular translations. There is
no scalar action-defect or action-coherence premise. -/
theorem moduleComparison_regular_equivariant
    (β : P.moduleFunctor TC.regularAlgebra ≅ 𝟭 (Mod_ N (i.obj TC.regularAlgebra)))
    [NatTrans.IsMonoidal β.hom]
    (j : κ)
    (hj : Homogeneous (neutralModuleCharacter i TC.regularAlgebra B himage) 1
      (SD.simpleObject j))
    (g : RepresentationZ2.H) (M : Mod_ N (i.obj TC.regularAlgebra)) :
    (P.moduleComapComparison TC.regularAlgebra (regularTranslation TC.inclusion g)).hom.app M ≫
        (Mod_.comap (i.map (regularTranslation TC.inclusion g))).map (β.hom.app M) =
      β.hom.app ((Mod_.comap (i.map (regularTranslation TC.inclusion g))).obj M) := by
  rcases RepresentationZ2.eq_one_or_generator g with rfl | rfl
  · have hn := module_regular_monodromy_of_homogeneous TC i B himage 0
      (𝟙_ (Mod_ N (i.obj TC.regularAlgebra)))
      (homogeneous_unit (neutralModuleCharacter i TC.regularAlgebra B himage))
    exact P.moduleComparison_comap_of_crossed TC.regularAlgebra
      (regularTranslationIso TC.inclusion 1) SD β (𝟙_ (Mod_ N (i.obj TC.regularAlgebra))) hn M
  · have hn := module_regular_monodromy_of_homogeneous TC i B himage 1
      (SD.simpleObject j) hj
    exact P.moduleComparison_comap_of_crossed TC.regularAlgebra
      (regularTranslationIso TC.inclusion RepresentationZ2.generator) SD β
      (SD.simpleObject j) hn M

include SD in
/-- Restriction of scalars does not change the underlying comparison
component. This equality is convenient for genuine equivariant descent. -/
theorem moduleComparison_regular_underlying
    (β : P.moduleFunctor TC.regularAlgebra ≅ 𝟭 (Mod_ N (i.obj TC.regularAlgebra)))
    [NatTrans.IsMonoidal β.hom]
    (j : κ)
    (hj : Homogeneous (neutralModuleCharacter i TC.regularAlgebra B himage) 1
      (SD.simpleObject j))
    (g : RepresentationZ2.H) (M : Mod_ N (i.obj TC.regularAlgebra)) :
    (β.hom.app ((Mod_.comap (i.map (regularTranslation TC.inclusion g))).obj M)).hom =
      (β.hom.app M).hom := by
  have h := congrArg (fun f => f.hom)
    (moduleComparison_regular_equivariant TC i P B himage SD β j hj g M)
  change 𝟙 _ ≫ (β.hom.app M).hom =
    (β.hom.app ((Mod_.comap (i.map (regularTranslation TC.inclusion g))).obj M)).hom at h
  simpa only [Category.id_comp] using h.symm

include SA SD in
/-- The actual specified Tannakian C₂ boundary has an actual monoidal and
regular-action compatible comparison. Every neutral component remains
the prescribed alpha. All crossed compatibility is proved internally. -/
theorem tannakianModule_equivariant_monoidal_comparison
    (W : Mod_ N (i.obj TC.regularAlgebra))
    (hW : (neutralModuleCharacter i TC.regularAlgebra B himage).hom.app W ≠ 𝟙 W) :
    ∃ β : P.moduleFunctor TC.regularAlgebra ≅ 𝟭 (Mod_ N (i.obj TC.regularAlgebra)),
      NatTrans.IsMonoidal β.hom ∧
        (∀ X : SignKernel.Positive (neutralModuleCharacter i TC.regularAlgebra B himage),
          β.hom.app X.obj =
            (neutralComparisonUnderlying i P TC.regularAlgebra B himage
              TC.regularAlgebraSeparable hfull e).hom.app X) ∧
        ∀ (g : RepresentationZ2.H) (M : Mod_ N (i.obj TC.regularAlgebra)),
          (β.hom.app ((Mod_.comap (i.map (regularTranslation TC.inclusion g))).obj M)).hom =
            (β.hom.app M).hom := by
  obtain ⟨β, hβ, ha⟩ := tannakianModule_monoidal_comparison SA TC i P B himage hfull e SD W hW
  letI := hβ
  have hchi : ∀ X : Mod_ N (i.obj TC.regularAlgebra),
      (neutralModuleCharacter i TC.regularAlgebra B himage).hom.app X ≫
        (neutralModuleCharacter i TC.regularAlgebra B himage).hom.app X = 𝟙 X :=
    B.moduleMonodromy_involutive (i.obj TC.regularAlgebra) (himage TC.regularAlgebra)
      (TensorInverse.mapSquare i TC.c2GeneratorSquareIso)
  obtain ⟨j, hj⟩ := SignKernel.exists_negative_label SD
    (neutralModuleCharacter i TC.regularAlgebra B himage) hchi W hW
  have hj' : Homogeneous (neutralModuleCharacter i TC.regularAlgebra B himage) 1
      (SD.simpleObject (SD.label W j)) := by
    simpa only [Homogeneous, paritySign_one, neg_one_smul] using hj
  exact ⟨β, hβ, ha, moduleComparison_regular_underlying TC i P B himage SD β (SD.label W j) hj'⟩

variable [Simple (𝟙_ N)] [∀ X Y : N, FiniteDimensional ℂ (X ⟶ Y)]
  {LabelN : Type*} [Fintype LabelN] (SN : FiniteSemisimpleSkeleton N LabelN)

include SA SD SN in
/-- The actual ambient nondegeneracy supplies the odd witness, so no odd
object or scalar action-defect is an input to equivariant monoidal
comparison for the specified boundary pair. -/
theorem tannakianModule_equivariant_monoidal_comparison_of_nondegenerate
    (hN : IsNondegenerate (C := N)) :
    ∃ β : P.moduleFunctor TC.regularAlgebra ≅ 𝟭 (Mod_ N (i.obj TC.regularAlgebra)),
      NatTrans.IsMonoidal β.hom ∧
        (∀ X : SignKernel.Positive (neutralModuleCharacter i TC.regularAlgebra B himage),
          β.hom.app X.obj =
            (neutralComparisonUnderlying i P TC.regularAlgebra B himage
              TC.regularAlgebraSeparable hfull e).hom.app X) ∧
        ∀ (g : RepresentationZ2.H) (M : Mod_ N (i.obj TC.regularAlgebra)),
          (β.hom.app ((Mod_.comap (i.map (regularTranslation TC.inclusion g))).obj M)).hom =
            (β.hom.app M).hom := by
  obtain ⟨W, hW⟩ := tannakian_exists_negative_module TC i B himage SN hN
  exact tannakianModule_equivariant_monoidal_comparison SA TC i P B himage hfull e SD W hW

end Paper18.Category.FixedBoundary
