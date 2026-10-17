import Paper18.Category.ModuleFunctorDualDimensionTransport
import Paper18.Category.ModuleFunctorDualDimension
import Paper18.Category.ModuleFunctorDualDimensionEquivalence

/-! # Actual module equivalence preserves intrinsic dual total dimension

The FP comparison is derived by applying the actual weight multiplier formula
on both sides of the genuine equivalence. No End dimension equality, tensor
comparison field, or prescribed numerical character is used.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators MonoidalLeftAction
universe v u vM uM vN uN w wM wN wA wB
namespace Paper18.Category.ModuleFunctor
open MonoidalLeftAction
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [RightRigidCategory C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {M : Type uM} [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [HasKernels M] [HasFiniteBiproducts M] [∀ X Y : M, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalLeftAction C M] [∀ c : C, (actionLeft M c).Additive]
  [∀ c : C, (actionLeft M c).Linear ℂ] [∀ X : M, (actionRight C X).Additive]
  {N : Type uN} [Category.{vN} N] [Preadditive N] [Linear ℂ N]
  [HasKernels N] [HasFiniteBiproducts N] [∀ X Y : N, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalLeftAction C N] [∀ c : C, (actionLeft N c).Additive]
  [∀ c : C, (actionLeft N c).Linear ℂ] [∀ X : N, (actionRight C X).Additive]
  {ι : Type w} [Fintype ι] (SC : FiniteSemisimpleSkeleton C ι)
  {κ : Type wM} [Fintype κ] (SM : FiniteSemisimpleSkeleton M κ) (j₀ : κ)
  {ν : Type wN} [Fintype ν] (SN : FiniteSemisimpleSkeleton N ν) (k₀ : ν)
  [HasKernels (ModuleAlphaInduction.End C M)]
  [∀ F G : ModuleAlphaInduction.End C M, FiniteDimensional ℂ (F ⟶ G)]
  [RightRigidCategory (ModuleAlphaInduction.End C M)] [Simple (𝟙_ (ModuleAlphaInduction.End C M))]
  [HasKernels (ModuleAlphaInduction.End C N)]
  [∀ F G : ModuleAlphaInduction.End C N, FiniteDimensional ℂ (F ⟶ G)]
  [RightRigidCategory (ModuleAlphaInduction.End C N)] [Simple (𝟙_ (ModuleAlphaInduction.End C N))]
  {α : Type wA} [Fintype α] (SA : FiniteSemisimpleSkeleton (ModuleAlphaInduction.End C M) α)
  {β : Type wB} [Fintype β] (SB : FiniteSemisimpleSkeleton (ModuleAlphaInduction.End C N) β)
  (I : Bundled C M N) [I.toFunctor.Full] [I.toFunctor.Faithful]
  (P : Bundled C N M) (adj : I.toFunctor ⊣ P.toFunctor)
  [IsModuleNatural C adj.unit] [IsModuleNatural C adj.counit] [IsIso adj.counit]
  (U : N ⥤ C) [U.Additive] [U.Faithful] [U.LeftLinear C]
  (hM : ∀ j k : κ, ∃ X : C, Nonempty (Retract (SM.simpleObject k) (X ⊙ₗ SM.simpleObject j)))
  (hN : ∀ j k : ν, ∃ X : C, Nonempty (Retract (SN.simpleObject k) (X ⊙ₗ SN.simpleObject j)))

include SC SM SN j₀ k₀ adj U hM hN in
/-- Genuine module conjugation preserves intrinsic End FP dimensions,
by comparing its actual underlying size on one actual simple. -/
theorem cornerExtension_fpdim (F : ModuleAlphaInduction.End C M) :
    SB.fpdim ((cornerExtension I P).obj F) = SA.fpdim F := by
  let X := SM.simpleObject j₀
  let V := I.toFunctor ⋙ U
  have hs := moduleFunctor_fpdim_underlying SC SM j₀ SA V hM F X
  have ht := moduleFunctor_fpdim_underlying SC SN k₀ SB U hN
    ((cornerExtension I P).obj F) (I.toFunctor.obj X)
  let e := I.toFunctor.mapIso (F.toFunctor.mapIso (asIso (adj.unit.app X)).symm)
  have hi := SC.fpdim_iso (U.mapIso e)
  have he : SB.fpdim ((cornerExtension I P).obj F) * SC.fpdim (U.obj (I.toFunctor.obj X)) =
      SA.fpdim F * SC.fpdim (U.obj (I.toFunctor.obj X)) := ht.symm.trans (hi.trans hs)
  have hp : 0 < SC.fpdim (U.obj (I.toFunctor.obj X)) :=
    moduleUnderlyingWeight_pos SC SM V j₀
  exact mul_right_cancel₀ hp.ne' he

include SC SM SN j₀ k₀ adj U hM hN in
/-- Reindexing the actual simple classes of genuine conjugation gives
actual equality of total dual FP dimensions. -/
theorem cornerEnd_totalFPdim : SA.fusionBasis.totalFPdim = SB.fusionBasis.totalFPdim := by
  letI := cornerExtension_full I P adj
  letI := cornerExtension_faithful I P adj
  letI := cornerExtensionEssSurj I P adj
  have h := weighted_simple_sum_equivalence SA SB (cornerExtension I P)
    (fun F => SB.fpdim F ^ 2) (fun e => congrArg (fun x : ℝ => x ^ 2) (SB.fpdim_iso e))
  simp only [cornerExtension_fpdim SC SM j₀ SN k₀ SA SB I P adj U hM hN,
    SA.fpdim_simple, SB.fpdim_simple] at h
  exact h

end Paper18.Category.ModuleFunctor
