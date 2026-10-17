import Paper29.ChainingBounds
import Mathlib.Data.Setoid.Basic

noncomputable section
open scoped ENNReal
namespace Paper29.Chaining

private def quotientMap {T U : Type*} (f : T → U) (s : Setoid U) :
    Quotient (Setoid.comap f s) → Quotient s :=
  fun q => (Setoid.comapQuotientEquiv f s q).val

private theorem quotientMap_injective {T U : Type*} (f : T → U) (s : Setoid U) :
    Function.Injective (quotientMap f s) :=
  Subtype.val_injective.comp (Setoid.comapQuotientEquiv f s).injective

/-- Pull an admissible partition sequence back along any map. -/
def comap {T U : Type*} (f : T → U) (P : AdmissiblePartitions U) : AdmissiblePartitions T where
  cell := fun k => Setoid.comap f (P.cell k)
  initial := fun x y => P.initial (f x) (f y)
  nested := fun k x y h => P.nested k (f x) (f y) h
  finite := fun k => by
    letI := P.finite k
    exact Finite.of_injective (quotientMap f (P.cell k)) (quotientMap_injective f (P.cell k))
  cardinality := fun k => by
    letI := P.finite k
    exact (Nat.card_le_card_of_injective (quotientMap f (P.cell k))
      (quotientMap_injective f (P.cell k))).trans (P.cardinality k)

/-- Functional monotonicity under restriction and metric nonexpansion. -/
theorem gamma2_pullback {T U : Type*} (f : T → U)
    (d : T → T → ℝ≥0∞) (e : U → U → ℝ≥0∞)
    (hd : ∀ x y, d x y ≤ e (f x) (f y)) : gamma2 d ≤ gamma2 e := by
  unfold gamma2
  apply le_iInf
  intro P
  apply (iInf_le _ (comap f P)).trans
  apply iSup_le
  intro t
  apply le_iSup_of_le (f t)
  apply ENNReal.tsum_le_tsum
  intro k
  apply mul_le_mul_left'
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  apply iSup_le
  intro y
  apply iSup_le
  intro hy
  have hhx : (P.cell k).r (f t) (f x) := hx
  have hhy : (P.cell k).r (f t) (f y) := hy
  have hbound : e (f x) (f y) ≤ cellDiameter e P k (f t) := by
    apply le_iSup_of_le (f x)
    apply le_iSup_of_le hhx
    apply le_iSup_of_le (f y)
    exact le_iSup (fun _ : (P.cell k).r (f t) (f y) => e (f x) (f y)) hhy
  exact (hd x y).trans hbound

end Paper29.Chaining
