import Paper18.Category.BalancedModuleCategory
import Paper18.Category.FixedBoundaryModuleEquivalence

/-! # The actual opposite algebra needed for categorical Picard products

A left internal module becomes a right module over the braided opposite
algebra.  The multiplication and the action are transported by the actual
strong monoidal mopping functor.  In particular no commutativity of the
underlying graph algebra is used in this change of orientation.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj
universe v u
namespace Paper18.Category.GraphPicard.MoritaProduct
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]

/-- Reversing tensor order exchanges the two unit laws and reverses the
associativity equation of an actual algebra object. -/
def unmopMonObj (A : Dᴹᵒᵖ) [MonObj A] : MonObj A.unmop where
  one := η[A].unmop
  mul := μ[A].unmop
  one_mul := congrArg Quiver.Hom.unmop (MonObj.mul_one A)
  mul_one := congrArg Quiver.Hom.unmop (MonObj.one_mul A)
  mul_assoc := by
    have h := congrArg Quiver.Hom.unmop (MonObj.mul_assoc A)
    change (A.unmop ◁ μ[A].unmop) ≫ μ[A].unmop =
      (α_ A.unmop A.unmop A.unmop).inv ≫
        μ[A].unmop ▷ A.unmop ≫ μ[A].unmop at h
    apply (cancel_epi (α_ A.unmop A.unmop A.unmop).inv).mp
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h.symm

variable [BraidedCategory D]

/-- The actual braided opposite algebra. Its multiplication is the
original multiplication after the actual self-braiding. -/
def oppositeAlgebra (B : Mon D) : Mon D := by
  exact { X := B.X, mon := (@unmopMonObj D _ _ (mop B.X)
      (Functor.monObjObj (F := mopFunctor D) B.X)) }

@[simp] theorem oppositeAlgebra_X (B : Mon D) : (oppositeAlgebra B).X = B.X := rfl

theorem oppositeAlgebra_one (B : Mon D) :
    (oppositeAlgebra B).mon.one = η[B.X] := by
  change 𝟙 (𝟙_ D) ≫ η[B.X] = η[B.X]
  exact Category.id_comp _

theorem oppositeAlgebra_mul (B : Mon D) :
    (oppositeAlgebra B).mon.mul = (β_ B.X B.X).hom ≫ μ[B.X] := rfl

/-- Right modules over the actual braided opposite algebra, expressed as
native left modules in the monoidal opposite. -/
abbrev OppositeRightModules (B : Mon D) :=
  letI := (oppositeAlgebra B).mon
  BalancedModuleCategory.RightModules (oppositeAlgebra B).X

/-- Actual transport of left modules to right modules over the braided
opposite algebra. Its underlying object and morphisms are unchanged. -/
def leftToRight (B : Mon D) : Mod_ D B.X ⥤ OppositeRightModules B := by
  letI := Functor.monObjObj (F := mopFunctor D) B.X
  exact InternalModule.mapModules (mopFunctor D) (A := B.X)

@[simp] theorem leftToRight_obj_X (B : Mon D) (M : Mod_ D B.X) :
    ((leftToRight B).obj M).X = mop M.X := rfl

@[simp] theorem leftToRight_map (B : Mon D) {M N : Mod_ D B.X} (f : M ⟶ N) :
    ((leftToRight B).map f).hom = f.hom.mop := rfl

/-- The transported right action is the genuine crossing followed by
the original left action, not the unchanged original module action. -/
theorem leftToRight_action (B : Mon D) (M : Mod_ D B.X) :
    (γ[mop (oppositeAlgebra B).X,((leftToRight B).obj M).X]).unmop =
      (β_ M.X B.X).hom ≫ γ[B.X,M.X] := rfl

instance leftToRight_full (B : Mon D) : (leftToRight B).Full := by
  letI := Functor.monObjObj (F := mopFunctor D) B.X
  exact InternalModule.mapModulesFull (mopFunctor D) (A := B.X)

instance leftToRight_faithful (B : Mon D) : (leftToRight B).Faithful := by
  letI := Functor.monObjObj (F := mopFunctor D) B.X
  exact InternalModule.mapModulesFaithful (mopFunctor D) (A := B.X)

variable [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]

/-- The actual separability section transports with the algebra. The
two bimodule-linearity equations exchange on unmopping. -/
def oppositeSeparable (B : Mon D) (S : SeparableAlgebra B.X) :
    letI := (oppositeAlgebra B).mon
    SeparableAlgebra (oppositeAlgebra B).X := by
  letI := Functor.monObjObj (F := mopFunctor D) B.X
  let T := S.map (mopFunctor D)
  exact
    { section_ := T.section_.unmop
      section_mul := congrArg Quiver.Hom.unmop T.section_mul
      left_linear := congrArg Quiver.Hom.unmop T.right_linear
      right_linear := congrArg Quiver.Hom.unmop T.left_linear }

instance leftToRight_additive (B : Mon D) : (leftToRight B).Additive := by
  letI := Functor.monObjObj (F := mopFunctor D) B.X
  exact InternalModule.mapModulesAdditive (mopFunctor D) (A := B.X)

instance leftToRight_linear (B : Mon D) : (leftToRight B).Linear ℂ := by
  letI := Functor.monObjObj (F := mopFunctor D) B.X
  exact InternalModule.mapModulesLinear (mopFunctor D) (A := B.X)

variable [HasKernels D]

/-- Separability and actual tensor equivalence derive essential
surjectivity of the left/right conversion on actual modules. -/
theorem leftToRight_essSurj (B : Mon D) (S : SeparableAlgebra B.X) :
    (leftToRight B).EssSurj := by
  letI := Functor.monObjObj (F := mopFunctor D) B.X
  exact InternalModule.mapModules_essSurj (mopFunctor D) S

/-- The actual complex-linear equivalence required to regard a second
left algebra-module category as the right factor of a balanced product. -/
def leftRightEquivalence (B : Mon D) (S : SeparableAlgebra B.X) :
    Mod_ D B.X ≌ OppositeRightModules B := by
  letI := leftToRight_essSurj B S
  letI : (leftToRight B).IsEquivalence := {}
  exact (leftToRight B).asEquivalence

instance leftRightEquivalence_functor_additive (B : Mon D) (S : SeparableAlgebra B.X) :
    (leftRightEquivalence B S).functor.Additive :=
  leftToRight_additive B

instance leftRightEquivalence_functor_linear (B : Mon D) (S : SeparableAlgebra B.X) :
    (leftRightEquivalence B S).functor.Linear ℂ :=
  leftToRight_linear B

instance leftRightEquivalence_inverse_additive (B : Mon D) (S : SeparableAlgebra B.X) :
    (leftRightEquivalence B S).inverse.Additive :=
  (leftRightEquivalence B S).inverse_additive

instance leftRightEquivalence_inverse_linear (B : Mon D) (S : SeparableAlgebra B.X) :
    (leftRightEquivalence B S).inverse.Linear ℂ :=
  Equivalence.inverseLinear ℂ (leftRightEquivalence B S)

end Paper18.Category.GraphPicard.MoritaProduct
