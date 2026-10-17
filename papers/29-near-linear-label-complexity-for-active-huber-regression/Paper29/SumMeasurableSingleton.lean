import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Instances

open MeasureTheory
namespace Paper29.QueryModel

instance sumMeasurableSingleton {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] :
    MeasurableSingletonClass (A ⊕ B) := by
  constructor
  intro x
  cases x with
  | inl a => simpa only [Set.image_singleton] using (measurableSet_singleton a).inl_image (β:=B)
  | inr b => simpa only [Set.image_singleton] using (measurableSet_singleton b).inr_image (α:=A)



end Paper29.QueryModel
