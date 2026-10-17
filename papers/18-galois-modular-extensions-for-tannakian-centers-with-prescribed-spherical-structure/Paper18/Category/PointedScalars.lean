import Paper18.Category.PointedBasic

noncomputable section

namespace Paper18.Category.AppendixBPointed

/-- The standard fourth-root character of `ZMod 4`. -/
def fourthRoot : AddChar (ZMod 4) ℂ where
  toFun a := Paper18.chi (0, a)
  map_zero_eq_one' := Paper18.chi.map_zero_eq_one
  map_add_eq_mul' a b := by
    simpa using Paper18.chi.map_add_eq_mul (0, a) (0, b)

@[simp] lemma fourthRoot_apply (a : ZMod 4) :
    fourthRoot a = Complex.I ^ a.val := rfl

/-- The braiding coefficient `i^(a*d)`, independent of the associator. -/
def braidingScalar (p r : Paper18.PointedA) : ℂ := fourthRoot (p.1 * r.2)

lemma braidingScalar_eq (p r : Paper18.PointedA) :
    braidingScalar p r = Complex.I ^ (p.1.val * r.2.val) := by
  simp only [braidingScalar, fourthRoot_apply, ZMod.val_mul]
  exact (Complex.I_pow_eq_pow_mod _).symm

lemma braidingScalar_ne_zero (p r : Paper18.PointedA) : braidingScalar p r ≠ 0 := by
  rw [braidingScalar_eq]
  exact pow_ne_zero _ Complex.I_ne_zero

lemma braidingScalar_add_left (p r s : Paper18.PointedA) :
    braidingScalar (p + r) s = braidingScalar p s * braidingScalar r s := by
  change fourthRoot ((p.1 + r.1) * s.2) = _
  rw [add_mul, fourthRoot.map_add_eq_mul]
  rfl

lemma braidingScalar_add_right (p r s : Paper18.PointedA) :
    braidingScalar p (r + s) = braidingScalar p r * braidingScalar p s := by
  change fourthRoot (p.1 * (r.2 + s.2)) = _
  rw [mul_add, fourthRoot.map_add_eq_mul]
  rfl

lemma braidingScalar_self (p : Paper18.PointedA) : braidingScalar p p = Paper18.q p :=
  braidingScalar_eq p p

/-- The double braiding coefficient is exactly the pairing used in Appendix B. -/
lemma braidingScalar_monodromy (p r : Paper18.PointedA) :
    braidingScalar p r * braidingScalar r p = Paper18.monodromy p r := by
  rw [braidingScalar_eq, braidingScalar_eq, ← pow_add]
  simp only [Paper18.monodromy, Nat.mul_comm r.1.val p.2.val]

end Paper18.Category.AppendixBPointed
