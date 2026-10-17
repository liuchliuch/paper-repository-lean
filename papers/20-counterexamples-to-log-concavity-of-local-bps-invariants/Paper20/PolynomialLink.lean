import Paper20.Polynomial
import Paper20.Partitions

/-! The §3 polynomial construction uses the same executable partitions,
hooks, contents and dimensions as the Hilbert computation. The old opaque
partial partition generator has been removed, not assumed equal. -/
namespace Paper20

@[simp] theorem partsHooks_eq_hooksOf (ps : List ℕ) : partsHooks ps = hooksOf ps := rfl
@[simp] theorem partsContent_eq_contentOf (ps : List ℕ) : partsContent ps = contentOf ps := rfl
@[simp] theorem partsDim_eq_dimOf (r : ℕ) (ps : List ℕ) : partsDim r ps = dimOf r ps := rfl

theorem partsEvenHooks_eq_evenHooksOf (ps : List ℕ) :
    partsEvenHooks ps = evenHooksOf ps := by
  unfold partsEvenHooks evenHooksOf
  rw [partsHooks_eq_hooksOf]
  apply List.countP_congr
  intro a ha
  simp

/-- The leading coefficient of the constructed `Q` with every summation
object explicitly linked to the Hilbert definitions. This theorem does not
claim the unproved character-theoretic interpretation as a walk count. -/
theorem Qcoeff_leading_partition_sum (r h : ℕ) :
    cget (Qcoeff r h) h =
      (((partitionsOf r).map (fun ps =>
        (dimOf r ps)^2 * (contentOf ps).natAbs^(2*h))).sum : ℚ) /
        ((r.factorial : ℚ) * ((2*h).factorial : ℚ)) := by
  rw [prop_3_2]
  unfold transpositionMoment transpositionMomentInt
  rw [foldl_add_eq_sum]
  simp only [zero_add, partsDim_eq_dimOf, partsContent_eq_contentOf]
  ring

end Paper20
