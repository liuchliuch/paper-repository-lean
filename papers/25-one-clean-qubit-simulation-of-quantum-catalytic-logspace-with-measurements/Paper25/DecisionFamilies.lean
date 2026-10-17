import Paper25.ResourceFamilies

/-! Common polynomial resource and bias constants over all binary inputs.
These lemmas assemble quantitative bounds; they assert no circuit compiler. -/
noncomputable section
namespace Paper25.OperationalModel

/-- A fixed-base overhead exponential in a logarithmic number of controls is
polynomial in the input length. The returned constants are uniform in x. -/
theorem control_overhead_polynomial {ell : Input → ℕ}
    (h : PolynomialBound (fun x => 2 ^ ell x)) (b : ℕ) :
    PolynomialBound (fun x => b ^ (ell x+1)) := by
  apply ((PolynomialBound.const b).mul (h.pow b)).mono
  intro x
  calc
    b^(ell x+1) = b*b^(ell x) := by rw [pow_succ, Nat.mul_comm]
    _ ≤ b*(2^b)^(ell x) := Nat.mul_le_mul_left b
      (Nat.pow_le_pow_left (Paper25.nat_le_two_pow b) _)
    _ = b*(2^ell x)^b := by simp only [← pow_mul, Nat.mul_comm]

/-- Turn the explicit source-independent accuracy and register bounds into
the signed-bias convention used in the paper's class statement. The family
here already consists of real local gate lists and true Born probabilities. -/
theorem effective_decides_of_resource_gap {G : EffectiveGateSet}
    (F : EffectiveTargetFamily G) (language : Input → Bool)
    (J K k : Input → ℕ)
    (hJ : PolynomialBound J) (hK : PolynomialBound K)
    (hk : PolynomialBound (fun x => 2^k x))
    (hJpos : ∀ x, 0 < J x) (hKpos : ∀ x, 0 < K x)
    (hgap : ∀ x, let gap := biasLam (J x) (K x) /
      ((2:ℝ)^(k x+4)*Real.sqrt (K x))
      if language x then 1/2+gap ≤ F.accept x
      else F.accept x ≤ 1/2-gap) :
    EffectiveDecidesWithInversePolynomialBias F language := by
  obtain ⟨C,d,hC,hbound⟩ := string_gap_inverse_polynomial hJ hK hk hJpos hKpos
  refine ⟨2*C,d,by positivity,?_⟩
  intro x
  have hb := hbound x
  have hg := hgap x
  simp only [EffectiveTargetFamily.signedBias]
  cases he : language x <;> simp only [he, Bool.false_eq_true, ↓reduceIte] at hg ⊢ <;>
    rw [mul_div_assoc] <;> linarith

end Paper25.OperationalModel
