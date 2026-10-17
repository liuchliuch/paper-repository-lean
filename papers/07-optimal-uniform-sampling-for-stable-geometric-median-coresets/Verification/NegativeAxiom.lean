import GeometricMedianCoresets.Paper

/-!
# Negative control: unauthorized axiom

Uses an extra axiom, so the official Comparator must reject this solution.
-/

noncomputable section

open scoped BigOperators RealInnerProductSpace
namespace GeometricMedianCoresets.Challenge

axiom unauthorized_lemma_2_2 :
  ∀ {X : Type*} (S : SquaredMetric X) {n m : ℕ} (_hn : n ≠ 0) (_hm : m ≠ 0)
    (P : Dataset X n) (Q : Dataset X m) (x y : X),
    S.toDist.delta P Q x y = 2 * ⟪S.Φ x - S.Φ y, S.v Q - S.v P⟫

theorem lemma_2_2 {X : Type*} (S : SquaredMetric X)
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0)
    (P : Dataset X n) (Q : Dataset X m) (x y : X) :
    S.toDist.delta P Q x y = 2 * ⟪S.Φ x - S.Φ y, S.v Q - S.v P⟫ :=
  unauthorized_lemma_2_2 S hn hm P Q x y

end GeometricMedianCoresets.Challenge
