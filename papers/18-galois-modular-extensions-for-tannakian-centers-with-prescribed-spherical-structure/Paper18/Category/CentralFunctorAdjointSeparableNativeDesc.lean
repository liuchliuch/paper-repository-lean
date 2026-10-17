import Paper18.Category.CentralFunctorAdjointSeparableNativeCap
import Paper18.Category.CentralFunctorAdjointSeparableOrdinaryCoend

/-! # Actual coend descent for the native diagonal action

The genuine native action preserves the cap coend. Its cap coordinates
therefore descend to an actual morphism from the action of the canonical
diagonal algebra, and their intertwining condition detects exactly the
actual original module-natural transformations.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonoidalLeftAction TensorProduct
universe v u vM uM vN uN w wM
namespace Paper18.Category.CentralFunctorAdjointSeparable
open MonoidalLeftAction ModuleFunctor.DiagonalAction
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {M : Type uM} [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [HasFiniteBiproducts M] [MonoidalLeftAction C M]
  {κ : Type wM} [Fintype κ] (T : FiniteSemisimpleSkeleton M κ)
  {N : Type uN} [Category.{vN} N] [Preadditive N] [Linear ℂ N]
  [HasFiniteBiproducts N] [MonoidalLeftAction C N]
  [∀ X Y : N, FiniteDimensional ℂ (X ⟶ Y)]
  [∀ X : C, (actionLeft M X).Additive] [∀ X : C, (actionLeft M X).Linear ℂ]
  [∀ X : C, (actionLeft N X).Additive] [∀ X : C, (actionLeft N X).Linear ℂ]
  [∀ m : M, (actionRight C m).Additive] [∀ m : M, (actionRight C m).Linear ℂ]
  [∀ n : N, (actionRight C n).Additive] [∀ n : N, (actionRight C n).Linear ℂ]

omit [RightRigidCategory C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  [HasFiniteBiproducts M] [∀ X Y : N, FiniteDimensional ℂ (X ⟶ Y)] in
/-- Actual external-pair maps have their actual post/precomposition coordinates. -/
@[reassoc]
lemma nativePairIso_map (F : Ordinary C M N) {X X' Y Y' : C}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    DiagonalAlgebra.capPairMap f g ⊵ₗ F ≫ (nativePairIso F X' Y').hom =
      (nativePairIso F X Y).hom ≫ (pairMapLeft f Y).app F ≫
        (pairMapRight X' g).app F := by
  simpa only [Category.assoc] using nativePairIso_covariance F f g

omit [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  [HasFiniteBiproducts M] [∀ X Y : N, FiniteDimensional ℂ (X ⟶ Y)] in
/-- The native cap coordinates satisfy actual dinaturality. -/
lemma nativeCap_dinaturality (F : Ordinary C M N) {X Y : C} (f : X ⟶ Y) :
    DiagonalAlgebra.capPairMap (dualMap C f) (𝟙 X) ⊵ₗ F ≫ nativeCap F X =
      DiagonalAlgebra.capPairMap (𝟙 Yᘁ) f ⊵ₗ F ≫ nativeCap F Y := by
  dsimp only [nativeCap]
  rw [nativePairIso_map_assoc, nativePairIso_map_assoc]
  have h₁ : (pairMapRight Xᘁ (𝟙 X)).app F = 𝟙 (pairObject Xᘁ X F) := by
    apply ordinary_hom_ext
    intro m
    change Xᘁ ⊴ₗ (toFunctor F).map ((𝟙 X) ⊵ₗ m) = 𝟙 _
    simp
  erw [h₁, Category.id_comp]
  have h₂ : (pairMapLeft (𝟙 Yᘁ) X).app F = 𝟙 (pairObject Yᘁ X F) := by
    apply ordinary_hom_ext
    intro m
    exact id_actionHomLeft _ _
  erw [h₂, Category.id_comp]
  rw [ordinaryCap_dinaturality]

/-- The genuine native algebra-action map, obtained by actual preserved
coend descent of the actual native cap coordinates. -/
def nativeActionMap (F : Ordinary C M N) :
    DiagonalAlgebra.canonicalAlgebra S ⊙ₗ F ⟶ F := by
  let A := actionRight (DeligneProduct C C) F
  letI := ordinaryFunctor_preservesCapCoend S T A
  exact DrinfeldCoendModules.capGeneratorDesc S A (nativeCap F) (nativeCap_dinaturality F)

/-- Exact cap-generator normalization of the actual native action map. -/
@[reassoc]
lemma capGenerator_nativeActionMap (F : Ordinary C M N) (X : C) :
    DiagonalAlgebra.capGenerator S X ⊵ₗ F ≫ nativeActionMap S T F = nativeCap F X := by
  let A := actionRight (DeligneProduct C C) F
  letI := ordinaryFunctor_preservesCapCoend S T A
  exact DrinfeldCoendModules.capGenerator_desc S A (nativeCap F) (nativeCap_dinaturality F) X

/-- Intertwining the genuine diagonal action maps is exactly actual
native module naturality for the original acting category. -/
theorem nativeActionMap_comm_iff {F G : Ordinary C M N} (τ : F ⟶ G) :
    nativeActionMap S T F ≫ τ =
        DiagonalAlgebra.canonicalAlgebra S ⊴ₗ τ ≫ nativeActionMap S T G ↔
      ModuleFunctor.IsModuleNatural C τ := by
  rw [← nativeCap_comm_iff]
  constructor
  · intro h X
    have hh := congrArg (fun k => DiagonalAlgebra.capGenerator S X ⊵ₗ F ≫ k) h
    dsimp only at hh
    rw [capGenerator_nativeActionMap_assoc, ← action_exchange_assoc,
      capGenerator_nativeActionMap] at hh
    exact hh
  · intro h
    let A := actionRight (DeligneProduct C C) F
    letI := ordinaryFunctor_preservesCapCoend S T A
    apply DrinfeldCoendModules.capGenerator_hom_ext S A
    intro X
    change DiagonalAlgebra.capGenerator S X ⊵ₗ F ≫ nativeActionMap S T F ≫ τ =
      DiagonalAlgebra.capGenerator S X ⊵ₗ F ≫
        DiagonalAlgebra.canonicalAlgebra S ⊴ₗ τ ≫ nativeActionMap S T G
    rw [capGenerator_nativeActionMap_assoc, ← action_exchange_assoc,
      capGenerator_nativeActionMap]
    exact h X

/-- Every actual original module map intertwines the genuine native
diagonal action maps. -/
@[reassoc]
lemma nativeActionMap_naturality {F G : Ordinary C M N} (τ : F ⟶ G)
    [ModuleFunctor.IsModuleNatural C τ] :
    nativeActionMap S T F ≫ τ =
      DiagonalAlgebra.canonicalAlgebra S ⊴ₗ τ ≫ nativeActionMap S T G :=
  (nativeActionMap_comm_iff S T τ).mpr inferInstance

end Paper18.Category.CentralFunctorAdjointSeparable
