import Paper18.Category.ModuleFunctorCrossedTransparencyComparison
import Paper18.Category.TannakianC2GeneratorBasic
import Paper18.Category.FixedBoundaryOrdinaryExtraction
import Paper18.Category.FixedBoundaryRegularFaithful

/-! # The actual Tannakian boundary has an actual odd comparison

The actual Tannakian de-equivariantization supplies neutral nondegeneracy.
No transparency or representative premise is needed.
-/
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
local instance imageTannakianMonObj : MonObj (i.obj TC.regularAlgebra) := Functor.monObjObj (F := i) TC.regularAlgebra
local instance imageTannakianCommMonObj : IsCommMonObj (i.obj TC.regularAlgebra) := Functor.isCommMonObj_obj
variable (B : TensorInverse (i.obj (TC.c2Generator)))
  (himage : ∀ X : A, Centralizes (i.obj (TC.c2Generator)) (i.obj X))
  (hfull : ∀ Y : N, Centralizes (i.obj (TC.c2Generator)) Y →
    ∃ X : A, Nonempty (i.obj X ≅ Y))
  (e : P.functor.obj (i.obj (TC.c2Generator)) ≅
    i.obj (TC.c2Generator))
  [modRigid : RightRigidCategory (Mod_ N (i.obj TC.regularAlgebra))] [modUnit : Simple (𝟙_ (Mod_ N (i.obj TC.regularAlgebra)))]
  [modFinite : ∀ X Y : Mod_ N (i.obj TC.regularAlgebra), FiniteDimensional ℂ (X ⟶ Y)]
  {κ : Type w'} [Fintype κ]
  (SD : FiniteSemisimpleSkeleton (Mod_ N (i.obj TC.regularAlgebra)) κ)

local notation "s" => TC.regularAlgebraSeparable
local notation "hR" => TC.regularAlgebra_transparent
local notation "chi" => neutralModuleCharacter i TC.regularAlgebra B himage
local notation "Pos" => SignKernel.Positive chi
local notation "Odd" => HomogeneousCategory chi 1
local notation "G" => oddBoundaryModuleEnd SA i P TC.regularAlgebra B himage s hfull e
local notation "Alpha" => ModuleAlphaInduction.negative Pos Odd



include SD modRigid modUnit modFinite in
/-- The original actual Tannakian C₂ boundary yields an actual native
odd-module comparison with the identity. -/
theorem tannakianOddBoundaryComparison
    (W : Mod_ N (i.obj TC.regularAlgebra)) (hW : (chi).hom.app W ≠ 𝟙 W) :
    letI := neutralModuleBraided i TC.regularAlgebra B himage s hfull hR
    Nonempty (G ≅ 𝟙_ (ModuleAlphaInduction.End Pos Odd)) := by
  letI := neutralModuleBraided i TC.regularAlgebra B himage s hfull hR
  let qR : TC.regularAlgebra ≅ regularAlgebra TC.inclusion := Iso.refl _
  letI : IsMonHom qR.hom := inferInstanceAs (IsMonHom (𝟙 TC.regularAlgebra))
  exact regularOddBoundaryComparison SA TC.inclusion i P TC.regularAlgebra qR B himage s hfull hR e SD
    (TensorInverse.mapSquare i TC.c2GeneratorSquareIso) W hW
    (tannakianNeutralNondegenerate SA TC i B himage hfull)

/-- Forgetting the actual native odd module comparison retains a genuine
ordinary natural isomorphism, with all original actual components. -/
def tannakianOddComparison
    (b : G ≅ 𝟙_ (ModuleAlphaInduction.End Pos Odd)) :
    oddBoundaryModuleFunctor i P TC.regularAlgebra B himage s hfull e ≅ 𝟭 Odd :=
  ModuleFunctor.forget.mapIso b

section AmbientFusion
variable [Simple (𝟙_ N)] [∀ X Y : N, FiniteDimensional ℂ (X ⟶ Y)]
  {LabelN : Type*} [Fintype LabelN] (SN : FiniteSemisimpleSkeleton N LabelN)

include SN in
/-- The actual ambient nondegeneracy and faithful regular free extension
force a nonzero odd component of the actual module category. -/
theorem tannakian_exists_negative_module (hN : IsNondegenerate (C := N)) :
    ∃ W : Mod_ N (i.obj TC.regularAlgebra), (chi).hom.app W ≠ 𝟙 W := by
  have hne : ¬ Nonempty (i.obj TC.c2Generator ≅ 𝟙_ N) := by
    rintro ⟨q⟩
    exact TC.c2Generator_nonunit ⟨i.preimageIso (q ≪≫ Functor.Monoidal.εIso i)⟩
  have hB := B.monodromy_nontrivial SN hN hne
  let aug : i.obj TC.regularAlgebra ⟶ 𝟙_ N :=
    i.map (regularAugmentation TC.inclusion) ≫ (Functor.Monoidal.εIso i).inv
  have haug : η[i.obj TC.regularAlgebra] ≫ aug = 𝟙 _ := by
    change (Functor.LaxMonoidal.ε i ≫ i.map η[TC.regularAlgebra]) ≫
      (i.map (regularAugmentation TC.inclusion) ≫ (Functor.Monoidal.εIso i).inv) = _
    simp only [Category.assoc]
    rw [← i.map_comp_assoc, regular_one_augmentation TC.inclusion, i.map_id,
      Category.id_comp]
    exact (Functor.Monoidal.εIso i).hom_inv_id
  letI := InternalModule.freeFunctorFaithfulOfSplitUnit aug haug
  have hchi : (chi) ≠ Iso.refl (𝟭 (Mod_ N (i.obj TC.regularAlgebra))) :=
    B.moduleMonodromy_nontrivial (i.obj TC.regularAlgebra) (himage TC.regularAlgebra) hB
  have hw : ∃ W : Mod_ N (i.obj TC.regularAlgebra), (chi).hom.app W ≠ 𝟙 W := by
    by_contra h
    push_neg at h
    apply hchi
    ext W
    exact congrArg (fun f : W ⟶ W => f.hom) (h W)
  exact hw

include SA SD SN modRigid modUnit modFinite in
/-- Nondegeneracy of the original ambient extension supplies the actual
odd component internally. Thus every specified boundary pair has an
actual native odd comparison, with no nontrivial-grading witness input. -/
theorem tannakianOddBoundaryComparison_of_nondegenerate (hN : IsNondegenerate (C := N)) :
    letI := neutralModuleBraided i TC.regularAlgebra B himage s hfull hR
    Nonempty (G ≅ 𝟙_ (ModuleAlphaInduction.End Pos Odd)) := by
  obtain ⟨W, hW⟩ := tannakian_exists_negative_module TC i B himage SN hN
  exact tannakianOddBoundaryComparison SA TC i P B himage hfull e SD W hW

end AmbientFusion

end Paper18.Category.FixedBoundary
