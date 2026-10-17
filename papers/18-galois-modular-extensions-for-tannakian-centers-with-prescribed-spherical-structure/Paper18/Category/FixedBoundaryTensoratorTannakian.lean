import Paper18.Category.ModuleFunctorCrossedTransparencyNative

/-! # Actual monoidal comparison for a specified Tannakian C₂ boundary -/
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
local instance tensoratorImageTannakianMonObj : MonObj (i.obj TC.regularAlgebra) := Functor.monObjObj (F := i) TC.regularAlgebra
local instance tensoratorImageTannakianCommMonObj : IsCommMonObj (i.obj TC.regularAlgebra) := Functor.isCommMonObj_obj
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

include SA SD in
/-- The actual Tannakian C₂ boundary admits an actual monoidal comparison
on all modules. Its neutral components are exactly the specified alpha.
The odd representative, its transparency and unit isomorphism, scalar
exhaustivity, normalized cocycle, and H² correction are all derived.
There is no braiding hypothesis on the category of all modules. -/
theorem tannakianModule_monoidal_comparison
    (W : Mod_ N (i.obj TC.regularAlgebra))
    (hW : (neutralModuleCharacter i TC.regularAlgebra B himage).hom.app W ≠ 𝟙 W) :
    ∃ β : P.moduleFunctor TC.regularAlgebra ≅ 𝟭 (Mod_ N (i.obj TC.regularAlgebra)),
      NatTrans.IsMonoidal β.hom ∧
        ∀ X : SignKernel.Positive (neutralModuleCharacter i TC.regularAlgebra B himage),
          β.hom.app X.obj =
            (neutralComparisonUnderlying i P TC.regularAlgebra B himage
              TC.regularAlgebraSeparable hfull e).hom.app X := by
  letI := neutralModuleBraided i TC.regularAlgebra B himage
    TC.regularAlgebraSeparable hfull TC.regularAlgebra_transparent
  obtain ⟨bEnd⟩ := tannakianOddBoundaryComparison SA TC i P B himage hfull e SD W hW
  let b := tannakianOddComparison SA TC i P B himage hfull e bEnd
  have hb : NativeOddComparisonNatural SA i P TC.regularAlgebra B himage
      TC.regularAlgebraSeparable hfull e b :=
    tannakianOddComparison_native SA TC i P B himage hfull e bEnd
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
  exact nativeModule_monoidal_comparison SA i P TC.regularAlgebra B himage
    TC.regularAlgebraSeparable hfull TC.regularAlgebra_transparent e hchi b hb
    SD (SD.label W j) hj'

variable [Simple (𝟙_ N)] [∀ X Y : N, FiniteDimensional ℂ (X ⟶ Y)]
  {LabelN : Type*} [Fintype LabelN] (SN : FiniteSemisimpleSkeleton N LabelN)

include SA SD SN in
/-- Nondegeneracy of the original ambient extension supplies a genuine odd
module internally. Consequently every actual specified boundary pair has
an actual monoidal all-module comparison, with no grading witness input. -/
theorem tannakianModule_monoidal_comparison_of_nondegenerate
    (hN : IsNondegenerate (C := N)) :
    ∃ β : P.moduleFunctor TC.regularAlgebra ≅ 𝟭 (Mod_ N (i.obj TC.regularAlgebra)),
      NatTrans.IsMonoidal β.hom ∧
        ∀ X : SignKernel.Positive (neutralModuleCharacter i TC.regularAlgebra B himage),
          β.hom.app X.obj =
            (neutralComparisonUnderlying i P TC.regularAlgebra B himage
              TC.regularAlgebraSeparable hfull e).hom.app X := by
  obtain ⟨W, hW⟩ := tannakian_exists_negative_module TC i B himage SN hN
  exact tannakianModule_monoidal_comparison SA TC i P B himage hfull e SD W hW

end Paper18.Category.FixedBoundary
