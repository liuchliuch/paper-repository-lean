import GeometricMedianCoresets.Paper

/-!
# Negative control: extra premise (type mismatch with the challenge)

The statement gains an extra `False` premise relative to the challenge, so the
official Comparator must reject this solution.
-/

noncomputable section

open scoped BigOperators RealInnerProductSpace
namespace GeometricMedianCoresets.Challenge

theorem lemma_2_2 {X : Type*} (S : SquaredMetric X)
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0)
    (P : Dataset X n) (Q : Dataset X m) (x y : X) :
    False →
      S.toDist.delta P Q x y = 2 * ⟪S.Φ x - S.Φ y, S.v Q - S.v P⟫ :=
  fun _ => S.delta_eq_inner hn hm P Q x y

end GeometricMedianCoresets.Challenge
