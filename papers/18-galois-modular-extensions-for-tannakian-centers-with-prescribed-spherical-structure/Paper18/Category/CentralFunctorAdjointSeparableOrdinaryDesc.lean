import Paper18.Category.CentralFunctorAdjointSeparableOrdinaryCoend
import Paper18.Category.ModuleFunctorDiagonalActionLift

/-! # The actual cap-descended diagonal action map

The map out of the actual diagonal algebra is constructed by its actual
preserved coend universal property. Its generator formulas hold exactly.
The algebra action laws are proved after the actual monoidal pair action
is installed.
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

omit [RightRigidCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [Simple (𝟙_ C)] [HasFiniteBiproducts M]
  [∀ X Y : N, FiniteDimensional ℂ (X ⟶ Y)] in
/-- The actual singleton comparison transports actual external-pair maps
to the actual post/precomposition maps. -/
@[reassoc]
lemma delignePairIso_map (F : Ordinary C M N) {X X' Y Y' : C}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (deligneAt F).map (DiagonalAlgebra.capPairMap f g) ≫
        (deligneAtPairIso F X' Y').hom =
      (deligneAtPairIso F X Y).hom ≫ (pairMapLeft f Y).app F ≫
        (pairMapRight X' g).app F := by
  have h := (linearMatLiftEmbeddingIso (LinearTensor.lift (pairAt F))).hom.naturality
    (show (⟨X, Y⟩ : LinearTensor C C) ⟶ ⟨X', Y'⟩ from f ⊗ₜ[ℂ] g)
  change (deligneAt F).map (DiagonalAlgebra.capPairMap f g) ≫
      (deligneAtPairIso F X' Y').hom =
    (deligneAtPairIso F X Y).hom ≫
      (LinearTensor.lift (pairAt F)).map
        (show (⟨X, Y⟩ : LinearTensor C C) ⟶ ⟨X', Y'⟩ from f ⊗ₜ[ℂ] g) at h
  simpa only [LinearTensor.lift, LinearTensor.liftHom_tmul, pairAt,
    Category.assoc] using h

omit [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [Simple (𝟙_ C)] [HasFiniteBiproducts M]
  [∀ X Y : N, FiniteDimensional ℂ (X ⟶ Y)] in
/-- The true cap family is dinatural after the actual Deligne lift. -/
lemma deligneCap_dinaturality (F : Ordinary C M N) {X Y : C} (f : X ⟶ Y) :
    (deligneAt F).map (DiagonalAlgebra.capPairMap (dualMap C f) (𝟙 X)) ≫
        (deligneAtPairIso F Xᘁ X).hom ≫ ordinaryCap F X =
      (deligneAt F).map (DiagonalAlgebra.capPairMap (𝟙 Yᘁ) f) ≫
        (deligneAtPairIso F Yᘁ Y).hom ≫ ordinaryCap F Y := by
  rw [delignePairIso_map_assoc, delignePairIso_map_assoc]
  have h₁ : (pairMapRight Xᘁ (𝟙 X)).app F = 𝟙 (pairObject Xᘁ X F) := by
    apply ordinary_hom_ext
    intro m
    change Xᘁ ⊴ₗ (toFunctor F).map ((𝟙 X) ⊵ₗ m) = 𝟙 _
    simp
  erw [h₁, Category.id_comp]
  have h₂' : (pairMapLeft (𝟙 Yᘁ) X).app F = 𝟙 (pairObject Yᘁ X F) := by
    apply ordinary_hom_ext
    intro m
    exact id_actionHomLeft _ _
  erw [h₂', Category.id_comp]
  rw [ordinaryCap_dinaturality]

/-- The actual diagonal action map, constructed from the actual rigid
lineator cap coordinates and the actual coend. -/
def diagonalActionMap (F : Ordinary C M N) :
    (deligneAt F).obj (DiagonalAlgebra.canonicalAlgebra S) ⟶ F := by
  letI := ordinaryFunctor_preservesCapCoend S T (deligneAt F)
  exact DrinfeldCoendModules.capGeneratorDesc S (deligneAt F)
    (fun X => (deligneAtPairIso F Xᘁ X).hom ≫ ordinaryCap F X)
    (deligneCap_dinaturality F)

/-- The descended actual action has exactly its specified cap component
on every actual source object, not just on chosen simple labels. -/
@[reassoc]
lemma capGenerator_diagonalActionMap (F : Ordinary C M N) (X : C) :
    (deligneAt F).map (DiagonalAlgebra.capGenerator S X) ≫ diagonalActionMap S T F =
      (deligneAtPairIso F Xᘁ X).hom ≫ ordinaryCap F X := by
  letI := ordinaryFunctor_preservesCapCoend S T (deligneAt F)
  exact DrinfeldCoendModules.capGenerator_desc S (deligneAt F)
    (fun Y => (deligneAtPairIso F Yᘁ Y).hom ≫ ordinaryCap F Y)
    (deligneCap_dinaturality F) X

/-- Any actual natural map between the lifted pair functors which has
the specified pair components intertwines the actual diagonal maps
precisely when the original ordinary map is module natural. -/
theorem diagonalActionMap_comm_iff {F G : Ordinary C M N} (τ : F ⟶ G)
    (a : deligneAt F ⟶ deligneAt G)
    (ha : ∀ X : C,
      a.app (DeligneProduct.externalObject Xᘁ X) ≫ (deligneAtPairIso G Xᘁ X).hom =
        (deligneAtPairIso F Xᘁ X).hom ≫
          (pairEnd (M := M) (N := N) Xᘁ X).map τ) :
    diagonalActionMap S T F ≫ τ =
        a.app (DiagonalAlgebra.canonicalAlgebra S) ≫ diagonalActionMap S T G ↔
      ModuleFunctor.IsModuleNatural C τ := by
  rw [← ordinaryCap_comm_iff]
  constructor
  · intro h X
    have hh := congrArg (fun k =>
      (deligneAt F).map (DiagonalAlgebra.capGenerator S X) ≫ k) h
    dsimp only at hh
    rw [capGenerator_diagonalActionMap_assoc, a.naturality_assoc,
      capGenerator_diagonalActionMap] at hh
    have hax := congrArg (fun k => k ≫ ordinaryCap G X) (ha X)
    simp only [Category.assoc] at hax
    rw [hax] at hh
    exact (cancel_epi (deligneAtPairIso F Xᘁ X).hom).mp hh
  · intro h
    letI := ordinaryFunctor_preservesCapCoend S T (deligneAt F)
    apply DrinfeldCoendModules.capGenerator_hom_ext S (deligneAt F)
    intro X
    rw [capGenerator_diagonalActionMap_assoc, a.naturality_assoc,
      capGenerator_diagonalActionMap]
    have hax := congrArg (fun k => k ≫ ordinaryCap G X) (ha X)
    simp only [Category.assoc] at hax
    rw [hax, h X]

end Paper18.Category.CentralFunctorAdjointSeparable
