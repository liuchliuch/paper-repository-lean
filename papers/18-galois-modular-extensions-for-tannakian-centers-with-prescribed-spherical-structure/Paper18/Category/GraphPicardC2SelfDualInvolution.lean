import Paper18.Category.GraphPicardNativeRealization

/-! # Actual inverse comparison for an involutive prescribed action

The specified tensor square comparison identifies the genuine inverse
functor with the forward functor, retaining its actual monoidal structure.
The resulting graph-input comparison includes the canonical double dual.
No graph-module self-duality is asserted by these functor comparisons.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u
namespace Paper18.Category.GraphPicard.C2SelfDual
section Monoidal
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  (β : D ≌ D) [β.functor.Monoidal]
  (r : β.functor ⋙ β.functor ≅ 𝟭 D) [NatTrans.IsMonoidal r.hom]

local instance inverseMonoidal : β.inverse.Monoidal := β.inverseMonoidal

/-- The specified actual square comparison, with the genuine equivalence
counit, identifies the forward functor with its actual monoidal inverse. -/
def forwardInverseIso : β.functor ≅ β.inverse :=
  Iso.isoCompInverse (H := β) r ≪≫ Functor.leftUnitor β.inverse

instance forwardInverseIsoMonoidal : NatTrans.IsMonoidal (forwardInverseIso β r).hom := by
  dsimp only [forwardInverseIso, Iso.isoCompInverse, Iso.compInverseIso, Iso.trans_hom,
    Iso.symm_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]
  infer_instance

/-- The inverse-to-forward comparison uses the specified tensor square. -/
def inverseForwardIso : β.inverse ≅ β.functor := (forwardInverseIso β r).symm

instance inverseForwardIsoMonoidal : NatTrans.IsMonoidal (inverseForwardIso β r).hom := by
  change NatTrans.IsMonoidal (forwardInverseIso β r).inv
  infer_instance

end Monoidal

section Graph
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [BraidedCategory D] [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasFiniteBiproducts D]
  (β : D ≌ D)
  [β.functor.Braided] [β.functor.Additive] [β.functor.Linear ℂ]
  (r : β.functor ⋙ β.functor ≅ 𝟭 D) [NatTrans.IsMonoidal r.hom]

local instance graphInverseMonoidal : β.inverse.Monoidal := β.inverseMonoidal

/-- The real native graph input `DD ⋙ β.inverse` is identified with
`DD ⋙ β.functor`. The canonical double dual is retained. -/
def correctedInputIso : graphInverseRealizationInput β ≅ graphRealizationInput β :=
  Functor.isoWhiskerLeft (doubleDualFunctor D) (inverseForwardIso β r)

instance correctedInputIsoMonoidal : NatTrans.IsMonoidal (correctedInputIso β r).hom := by
  change NatTrans.IsMonoidal (Functor.whiskerLeft (doubleDualFunctor D)
    (inverseForwardIso β r).hom)
  infer_instance

end Graph
end Paper18.Category.GraphPicard.C2SelfDual
