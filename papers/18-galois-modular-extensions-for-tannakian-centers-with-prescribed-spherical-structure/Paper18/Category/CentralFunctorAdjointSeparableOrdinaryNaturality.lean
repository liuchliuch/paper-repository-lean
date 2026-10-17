import Paper18.Category.CentralFunctorAdjointSeparableOrdinaryDesc

/-! # Actual naturality of the cap-descended diagonal map

Ordinary transformations induce actual transformations of the lifted
pair functors. Their cap-generator components characterize native module
naturality without a separately supplied transformation of the lifts.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonoidalLeftAction TensorProduct
universe v u vM uM vN uN w wM
namespace Paper18.Category.CentralFunctorAdjointSeparable
open MonoidalLeftAction ModuleFunctor.DiagonalAction
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C]
  {M : Type uM} [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction C M]
  {N : Type uN} [Category.{vN} N] [Preadditive N] [Linear ℂ N]
  [HasFiniteBiproducts N] [MonoidalLeftAction C N]
  [∀ X : C, (actionLeft M X).Additive] [∀ X : C, (actionLeft M X).Linear ℂ]
  [∀ X : C, (actionLeft N X).Additive] [∀ X : C, (actionLeft N X).Linear ℂ]
  [∀ m : M, (actionRight C m).Additive] [∀ m : M, (actionRight C m).Linear ℂ]
  [∀ n : N, (actionRight C n).Additive] [∀ n : N, (actionRight C n).Linear ℂ]

/-- The actual transformation on the linear tensor product of pair labels. -/
def linearPairMap {F G : Ordinary C M N} (τ : F ⟶ G) :
    LinearTensor.lift (pairAt F) ⟶ LinearTensor.lift (pairAt G) where
  app X := (pairEnd X.left X.right).map τ
  naturality {X Y} f := by
    change LinearTensor.liftHom (pairAt F) X Y f ≫ (pairEnd Y.left Y.right).map τ =
      (pairEnd X.left X.right).map τ ≫ LinearTensor.liftHom (pairAt G) X Y f
    induction f using TensorProduct.induction_on with
    | zero => simp
    | tmul f g =>
      change ((pairMapLeft f X.right).app F ≫ (pairMapRight Y.left g).app F) ≫
          (pairEnd Y.left Y.right).map τ =
        (pairEnd X.left X.right).map τ ≫
          ((pairMapLeft f X.right).app G ≫ (pairMapRight Y.left g).app G)
      rw [Category.assoc, ← (pairMapRight Y.left g).naturality,
        ← Category.assoc, ← (pairMapLeft f X.right).naturality, Category.assoc]
    | add f g hf hg =>
      simp only [map_add, Preadditive.add_comp, Preadditive.comp_add]
      rw [hf, hg]

/-- The actual transformation on finite direct sums of pair labels. -/
def deligneAtMap {F G : Ordinary C M N} (τ : F ⟶ G) : deligneAt F ⟶ deligneAt G where
  app X := biproduct.map (fun i => (linearPairMap τ).app (X.X i))
  naturality {X Y} f := by
    apply biproduct.hom_ext'
    intro i
    apply biproduct.hom_ext
    intro j
    simpa only [deligneAt, DeligneProduct.lift, linearMatLift,
      Category.assoc, biproduct.ι_matrix_assoc, biproduct.matrix_π,
      biproduct.ι_map_assoc, biproduct.map_π, biproduct.ι_desc,
      biproduct.lift_π, biproduct.lift_π_assoc] using (linearPairMap τ).naturality (f i j)

/-- The concrete lifted map preserves the actual identity transformation. -/
@[simp]
lemma deligneAtMap_id (F : Ordinary C M N) : deligneAtMap (𝟙 F) = 𝟙 (deligneAt F) := by
  apply NatTrans.ext
  funext X
  apply biproduct.hom_ext'
  intro i
  apply biproduct.hom_ext
  intro j
  simp [deligneAtMap, linearPairMap]
  erw [Category.id_comp, Category.id_comp]

/-- The concrete lifted map preserves actual composition. -/
@[simp]
lemma deligneAtMap_comp {F G H : Ordinary C M N} (τ : F ⟶ G) (σ : G ⟶ H) :
    deligneAtMap (τ ≫ σ) = deligneAtMap τ ≫ deligneAtMap σ := by
  apply NatTrans.ext
  funext X
  apply biproduct.hom_ext'
  intro i
  apply biproduct.hom_ext
  intro j
  simp [deligneAtMap, linearPairMap]

/-- The actual pair coordinate of the lifted ordinary transformation. -/
@[reassoc]
lemma deligneAtMap_pair {F G : Ordinary C M N} (τ : F ⟶ G) (X Y : C) :
    (deligneAtMap τ).app (DeligneProduct.externalObject X Y) ≫
        (deligneAtPairIso G X Y).hom =
      (deligneAtPairIso F X Y).hom ≫ (pairEnd X Y).map τ := by
  apply biproduct.hom_ext'
  intro i
  cases i
  simp [deligneAtMap, deligneAtPairIso, linearMatLiftSingletonIso,
    linearPairMap, biproductUniqueIso, limitBiconeOfUnique]
  change (pairEnd X Y).map τ ≫ 𝟙 _ = 𝟙 _ ≫ (pairEnd X Y).map τ
  simp only [Category.comp_id, Category.id_comp]

variable [RightRigidCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  [HasFiniteBiproducts M]
  {κ : Type wM} [Fintype κ] (T : FiniteSemisimpleSkeleton M κ)
  [∀ X Y : N, FiniteDimensional ℂ (X ⟶ Y)]

/-- Native module naturality is exactly compatibility with the actual
cap-descended diagonal map and the actual lifted ordinary map. -/
theorem diagonalActionMap_natural_iff {F G : Ordinary C M N} (τ : F ⟶ G) :
    diagonalActionMap S T F ≫ τ =
        (deligneAtMap τ).app (DiagonalAlgebra.canonicalAlgebra S) ≫
          diagonalActionMap S T G ↔ ModuleFunctor.IsModuleNatural C τ :=
  diagonalActionMap_comm_iff S T τ (deligneAtMap τ) (fun X => deligneAtMap_pair τ Xᘁ X)

/-- An actual module-natural transformation intertwines the actual
cap-descended action maps. -/
@[reassoc]
lemma diagonalActionMap_naturality {F G : Ordinary C M N} (τ : F ⟶ G)
    [ModuleFunctor.IsModuleNatural C τ] :
    diagonalActionMap S T F ≫ τ =
      (deligneAtMap τ).app (DiagonalAlgebra.canonicalAlgebra S) ≫
        diagonalActionMap S T G :=
  (diagonalActionMap_natural_iff S T τ).mpr inferInstance

end Paper18.Category.CentralFunctorAdjointSeparable
