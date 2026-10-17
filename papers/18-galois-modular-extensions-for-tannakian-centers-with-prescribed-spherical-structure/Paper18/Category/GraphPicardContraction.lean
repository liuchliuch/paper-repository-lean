import Paper18.Category.ModuleFunctorFiniteContraction
import Paper18.Category.SemisimpleCoendBasic

/-! # Actual tensor cancellation by any nonzero object

An actual simple summand and its normalized rigid contraction recover
morphisms from tensoring by an arbitrary nonzero object. No graph-module
invertibility or alpha-induction conclusion is assumed.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category.GraphPicard
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [RightRigidCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D] [Simple (𝟙_ D)]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)

/-- A nonzero actual object has an actual chosen simple summand. -/
lemma length_pos_of_id_ne_zero (X : D) (hX : 𝟙 X ≠ 0) : 0 < S.length X := by
  by_contra hn
  have hz : S.length X = 0 := Nat.eq_zero_of_not_pos hn
  letI : IsEmpty (Fin (S.length X)) := by rw [hz]; infer_instance
  exact hX (by simpa only [Fintype.sum_empty] using (S.coendResolution X).symm)

/-- Actual inclusion and projection onto a genuine simple retract cancel
left tensoring back to that actual simple retract. -/
lemma restrict_leftTensor (X : D) (a : Fin (S.length X)) {A B : D} (f : A ⟶ B) :
    S.coendInclusion X a ▷ A ≫ X ◁ f ≫ S.coendProjection X a ▷ B =
      S.simpleObject (S.label X a) ◁ f := by
  rw [← whisker_exchange_assoc, ← comp_whiskerRight]
  have hp : S.coendInclusion X a ≫ S.coendProjection X a =
      𝟙 (S.simpleObject (S.label X a)) := by
    simp [FiniteSemisimpleSkeleton.coendInclusion,
      FiniteSemisimpleSkeleton.coendProjection, Category.assoc]
  rw [hp, id_whiskerRight, comp_id]

/-- Tensoring on the left by any actual nonzero object is genuinely
faithful, by the normalized cap/cup of one actual simple summand. -/
def tensorLeftFaithfulOfNonzero (X : D) (hX : 𝟙 X ≠ 0) : (tensorLeft X).Faithful where
  map_injective {A B} f g h := by
    change X ◁ f = X ◁ g at h
    let a : Fin (S.length X) := ⟨0, length_pos_of_id_ne_zero S X hX⟩
    have hs : S.simpleObject (S.label X a) ◁ f =
        S.simpleObject (S.label X a) ◁ g := by
      have hh := congrArg (fun z => S.coendInclusion X a ▷ A ≫ z ≫
        S.coendProjection X a ▷ B) h
      simpa only [restrict_leftTensor] using hh
    have hc := congrArg (ModuleFunctor.simpleLeftContraction S
      (S.simpleObject (S.label X a))) hs
    simpa only [ModuleFunctor.simpleLeftContraction_whiskerLeft] using hc

end Paper18.Category.GraphPicard
