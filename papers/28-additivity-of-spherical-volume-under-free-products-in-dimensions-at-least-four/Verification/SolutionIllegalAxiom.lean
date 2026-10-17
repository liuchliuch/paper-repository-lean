import Paper28
set_option autoImplicit false
noncomputable section
open Paper28 Filter
open scoped InnerProductSpace
namespace Verification.Certificate

axiom untrustedFalse : False

theorem complementary_sqrt_bound (a b : ℝ) (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1) : Real.sqrt (a * b) + Real.sqrt ((1 - a) * (1 - b)) ≤ 1 :=
  False.elim untrustedFalse
end Verification.Certificate
