import Paper28.SplitPartitions
import Paper28.ShadowReindex

/-! The right cut differential is obtained by the actual block-swapping
coordinate isometry. No second independent Jacobian hypothesis is used. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open WithLp
open scoped InnerProductSpace
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

def splitSwap : α ⊕ (Unit ⊕ β) ≃ β ⊕ (Unit ⊕ α) where
  toFun := Sum.elim (fun a => .inr (.inr a))
    (Sum.elim (fun _ => .inr (.inl ())) Sum.inl)
  invFun := Sum.elim (fun b => .inr (.inr b))
    (Sum.elim (fun _ => .inr (.inl ())) Sum.inl)
  left_inv i := by
    rcases i with a | i
    · rfl
    · rcases i with z | b
      · cases z
        rfl
      · rfl
  right_inv i := by
    rcases i with b | i
    · rfl
    · rcases i with z | a
      · cases z
        rfl
      · rfl

theorem splitSwap_route (i : α ⊕ (Unit ⊕ β)) : splitRight i = splitLeft (splitSwap i) := by
  rcases i with a | i
  · rfl
  · rcases i with z | b <;> rfl

theorem splitSwap_coordinateTriple (u : EuclideanSpace ℝ (α ⊕ (Unit ⊕ β))) :
    coordinateTriple (Equiv.refl _) (reindexCoordinates splitSwap u) =
      reverseTriple (coordinateTriple (Equiv.refl _) u) := by
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext
  · ext b
    rfl
  · apply (WithLp.equiv 2 _).injective
    apply Prod.ext
    · rfl
    · ext a
      rfl

theorem splitRight_differential_swap
    (u h : EuclideanSpace ℝ (α ⊕ (Unit ⊕ β))) :
    shadowDifferential splitRight u h =
      shadowDifferential splitLeft (reindexCoordinates splitSwap u) (reindexCoordinates splitSwap h) := by
  ext b
  exact shadowDifferential_reindex splitSwap (Equiv.refl _) splitRight splitLeft
    splitSwap_route u h b

/-- Exact right-folding Gram identity, including zero coordinates. -/
theorem splitRight_differential_inner
    (u h k : EuclideanSpace ℝ (α ⊕ (Unit ⊕ β)))
    (hh : ∀ b, u (.inr (.inr b)) = 0 → h (.inr (.inr b)) = 0)
    (hk : ∀ b, u (.inr (.inr b)) = 0 → k (.inr (.inr b)) = 0) :
    ⟪shadowDifferential splitRight u h, shadowDifferential splitRight u k⟫_ℝ =
      ⟪rightFoldDerivative (coordinateTriple (Equiv.refl _) u) (coordinateTriple (Equiv.refl _) h),
        rightFoldDerivative (coordinateTriple (Equiv.refl _) u) (coordinateTriple (Equiv.refl _) k)⟫_ℝ := by
  rw [splitRight_differential_swap, splitRight_differential_swap]
  have hhu : ∀ a, reindexCoordinates splitSwap u (.inl a) = 0 →
      reindexCoordinates splitSwap h (.inl a) = 0 := hh
  have hku : ∀ a, reindexCoordinates splitSwap u (.inl a) = 0 →
      reindexCoordinates splitSwap k (.inl a) = 0 := hk
  rw [splitLeft_differential_inner _ _ _ hhu hku,
    splitSwap_coordinateTriple, splitSwap_coordinateTriple, splitSwap_coordinateTriple]
  rfl

end Paper28
