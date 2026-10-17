import Paper20.YoungDimensionNorm

namespace Paper20.YoungShapes
open Finset Paper20.YoungCorners
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- An actual saturated Young-lattice path from the empty diagram to the
specified shape. Each step remembers the preceding actual shape and its
proved single-box inclusion; the empty path is unique. -/
def Path : (n : ℕ) → Shape n → Type
  | 0,_ => PUnit
  | n+1,μ => Σ κ : {κ : Shape n // Covers κ.val μ.val}, Path n κ.val

instance pathFintype : ∀ n (μ : Shape n), Fintype (Path n μ)
  | 0,_ => inferInstanceAs (Fintype PUnit)
  | n+1,μ => by
    letI (κ : Shape n) : Fintype (Path n κ) := pathFintype n κ
    change Fintype (Σ κ : {κ : Shape n // Covers κ.val μ.val}, Path n κ.val)
    infer_instance

/-- The finite path recursion is exactly the actual one-box branching
recursion, so its cardinality is the original natural hook quotient. -/
theorem path_card (n : ℕ) : ∀ μ : Shape n, Fintype.card (Path n μ)=dimension μ.val := by
  induction n with
  | zero =>
    intro μ
    have he := vacuum_dimension 0 μ
    change (1:ℤ)=(dimension μ.val:ℤ) at he
    change 1=dimension μ.val
    exact_mod_cast he
  | succ n ih =>
    intro μ
    change Fintype.card (Σ κ : {κ : Shape n // Covers κ.val μ.val}, Path n κ.val)=_
    rw [Fintype.card_sigma]
    simp_rw [ih]
    calc
      _ = ∑ κ : {κ : YoungDiagram // Covers κ μ.val}, dimension κ.val :=
        Fintype.sum_equiv (lowerSingleLevelEquiv μ) _ _ (by intro κ; rfl)
      _ = _ := dimension_branching μ.val (by rw [μ.property]; omega)

/-- Pairs of actual paths with a common final diagram have total
cardinality n!. This is the actual path index set needed for matrix blocks,
proved from the hook/path equality rather than assumed from character theory. -/
theorem path_pairs_card (n : ℕ) :
    Fintype.card (Σ μ : Shape n, Path n μ × Path n μ)=n.factorial := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod,path_card]
  have hs := dimension_square_sum n
  apply Int.ofNat_inj.mp
  simpa only [Nat.cast_sum,Nat.cast_mul,pow_two] using hs

end
end Paper20.YoungShapes
