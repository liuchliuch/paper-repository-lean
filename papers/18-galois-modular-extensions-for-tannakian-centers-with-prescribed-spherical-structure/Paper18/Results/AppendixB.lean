import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.AddChar
import Mathlib.Tactic

/-!
# Appendix B — a pointed obstruction in a fixed extension

Let `𝒯` be the pointed modular category of the quadratic form
`q(a,b) = i^{ab}` on `A = ℤ/4 × ℤ/4`, with monodromy
`m((a,b),(c,d)) = i^{ad+bc}`.  Take `f = (2,0)` and
`B = ⟨f⟩'_𝒯`, whose simples are `{(a,b) : b even}` and whose Müger centre is
`⟨f⟩ ≅ Rep(ℤ/2)`.

The positive spherical structure on `B` is modified by the sign character
`χ(a,b) = i^b ∈ {±1}`.  This character is `+1` on `f`, but it does **not** extend
to a spherical structure on `𝒯`: spherical structures on this pointed category
differ from the positive one by characters `A → {±1}`, and every such character
is trivial on `2A` — in particular on `(0,2)` — whereas `χ(0,2) = -1`.

The character `χ̃(a,b) = i^b` on all of `A` does give a pivotal extension whose
slope is `χ̃² = (-1)^b = m(f,(a,b))`, hence nonspherical.  The twist of `f`
remains `+1`.

This module proves the finite-group / `ℂ` computations behind that obstruction.
-/

noncomputable section

open Classical

namespace Paper18

/-! ## The group `A = ℤ/4 × ℤ/4` and the quadratic form -/

/-- The pointed modular group `A = ℤ/4 × ℤ/4`. -/
abbrev PointedA : Type := ZMod 4 × ZMod 4

/-- Quadratic form `q(a,b) = i^{ab}` on `A`. -/
def q (p : PointedA) : ℂ :=
  Complex.I ^ (p.1.val * p.2.val)

/-- Monodromy pairing `m((a,b),(c,d)) = i^{ad+bc}`. -/
def monodromy (p r : PointedA) : ℂ :=
  Complex.I ^ (p.1.val * r.2.val + p.2.val * r.1.val)

/-- The distinguished element `f = (2,0)`. -/
def f : PointedA := (((2 : ZMod 4)), (0 : ZMod 4))

/-! ## Powers of `Complex.I` -/

/-- `Complex.I ≠ 1`. -/
theorem Complex.I_ne_one : Complex.I ≠ (1 : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  simp [Complex.I_re] at hre

/-- `Complex.I ≠ -1`. -/
theorem Complex.I_ne_neg_one : Complex.I ≠ (-1 : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  simp [Complex.I_re] at hre

/-- `Complex.I ^ n = 1 ↔ 4 ∣ n`. -/
theorem Complex.I_pow_eq_one_iff (n : ℕ) : Complex.I ^ n = 1 ↔ 4 ∣ n := by
  have hmod : Complex.I ^ n = Complex.I ^ (n % 4) := Complex.I_pow_eq_pow_mod n
  rw [hmod, Nat.dvd_iff_mod_eq_zero]
  have hlt : n % 4 < 4 := Nat.mod_lt n (by decide)
  interval_cases h : n % 4
  · simp
  · rw [pow_one]
    exact ⟨fun he => absurd he Complex.I_ne_one, fun hd => absurd hd (by decide)⟩
  · rw [Complex.I_sq]
    exact ⟨fun he => absurd he (by norm_num : (-1 : ℂ) ≠ 1),
      fun hd => absurd hd (by decide)⟩
  · rw [Complex.I_pow_three]
    exact ⟨fun he => absurd he (by
      intro heq
      have hre := congrArg Complex.re heq
      simp [Complex.I_re] at hre),
      fun hd => absurd hd (by decide)⟩

/-! ## Nondegeneracy of the monodromy pairing -/

/-- `(1 : ZMod 4).val = 1`. -/
theorem ZMod.val_one_four : ((1 : ZMod 4)).val = 1 :=
  ZMod.val_one'' (by decide)

/-- `(2 : ZMod 4).val = 2`. -/
theorem ZMod.val_two_four : ((2 : ZMod 4)).val = 2 :=
  ZMod.val_cast_of_lt (by decide)

/-- The monodromy pairing is nondegenerate: if `m(p, r) = 1` for all `r`, then
`p = 0`. -/
theorem appendixB_monodromy_nondegenerate (p : PointedA)
    (h : ∀ r : PointedA, monodromy p r = 1) : p = 0 := by
  -- Evaluate at `r = (1,0)` and `r = (0,1)`.
  have h10 : monodromy p ((1 : ZMod 4), 0) = 1 := h ((1 : ZMod 4), 0)
  have h01 : monodromy p (0, (1 : ZMod 4)) = 1 := h (0, (1 : ZMod 4))
  have hval1 : ((1 : ZMod 4)).val = 1 := ZMod.val_one_four
  have hval0 : ((0 : ZMod 4)).val = 0 := ZMod.val_zero
  -- monodromy p (1,0) = I^{a·0 + b·1} = I^{b.val}
  have hb0 : Complex.I ^ p.2.val = 1 := by
    simpa [monodromy, hval1, hval0, mul_one, mul_zero, add_zero] using h10
  have ha0 : Complex.I ^ p.1.val = 1 := by
    simpa [monodromy, hval1, hval0, mul_one, mul_zero, zero_add] using h01
  have h4b : (4 : ℕ) ∣ p.2.val := Complex.I_pow_eq_one_iff _ |>.mp hb0
  have h4a : (4 : ℕ) ∣ p.1.val := Complex.I_pow_eq_one_iff _ |>.mp ha0
  have hblt : p.2.val < 4 := ZMod.val_lt _
  have halt : p.1.val < 4 := ZMod.val_lt _
  have hb : p.2.val = 0 := Nat.eq_zero_of_dvd_of_lt h4b hblt
  have ha : p.1.val = 0 := Nat.eq_zero_of_dvd_of_lt h4a halt
  have hpe : p.1 = 0 := ZMod.val_eq_zero _ |>.mp ha
  have hp2e : p.2 = 0 := ZMod.val_eq_zero _ |>.mp hb
  exact Prod.ext hpe hp2e

/-- In particular the Müger centre of the monodromy pairing on `A` is trivial
(the category `𝒯` is modular). -/
theorem appendixB_modular :
    ∀ p : PointedA, (∀ r : PointedA, monodromy p r = 1) → p = 0 :=
  appendixB_monodromy_nondegenerate

/-! ## The character `χ(a,b) = i^b` and the pointed obstruction -/

/-- The character `χ(a,b) = i^b` on `A = ℤ/4 × ℤ/4`.
On the subcategory `B` (where `b` is even) this is the sign character `{±1}`. -/
def chi : AddChar PointedA ℂ where
  toFun p := Complex.I ^ p.2.val
  map_zero_eq_one' := by
    show Complex.I ^ (Prod.snd (0 : PointedA)).val = 1
    rw [show Prod.snd (0 : PointedA) = (0 : ZMod 4) from rfl, ZMod.val_zero, pow_zero]
  map_add_eq_mul' := fun p q => by
    calc Complex.I ^ (p.2 + q.2).val
        = Complex.I ^ ((p.2.val + q.2.val) % 4) := by rw [ZMod.val_add]
      _ = Complex.I ^ (p.2.val + q.2.val) := (Complex.I_pow_eq_pow_mod _).symm
      _ = Complex.I ^ p.2.val * Complex.I ^ q.2.val := pow_add _ _ _

@[simp]
theorem chi_apply (p : PointedA) : chi p = Complex.I ^ p.2.val := rfl

/-- The specified character takes the value `-1` at `(0,2)`. -/
theorem appendixB_chi_at_zero_two : chi (((0 : ZMod 4), (2 : ZMod 4)) : PointedA) = -1 := by
  have hval : ((2 : ZMod 4)).val = 2 := ZMod.val_two_four
  simp [chi, hval, Complex.I_sq]

/-- **Appendix B obstruction.** Every character `ψ : A → ℂ` whose values square
to `1` (in particular every `{±1}`-valued character) is trivial on `(0,2)`.
Since `χ(0,2) = -1`, the prescribed `χ` does not extend to a spherical
structure on `𝒯`. -/
theorem appendixB_chi_0_2 (ψ : AddChar PointedA ℂ)
    (hsq : ∀ x : PointedA, ψ x ^ 2 = 1) : ψ (((0 : ZMod 4), (2 : ZMod 4)) : PointedA) = 1 := by
  have h : (((0 : ZMod 4), (2 : ZMod 4)) : PointedA)
      = ((0 : ZMod 4), (1 : ZMod 4)) + ((0 : ZMod 4), (1 : ZMod 4)) := by
    simp [Prod.ext_iff]
    norm_num
  rw [h, AddChar.map_add_eq_mul, ← pow_two, hsq]

/-- Same statement for `{±1}`-valued characters. -/
theorem appendixB_chi_0_2_of_sign (ψ : AddChar PointedA ℂ)
    (hsign : ∀ x : PointedA, ψ x = 1 ∨ ψ x = -1) :
    ψ (((0 : ZMod 4), (2 : ZMod 4)) : PointedA) = 1 :=
  appendixB_chi_0_2 ψ fun x => by
    rcases hsign x with h | h <;> simp [h, pow_two]

/-- Consequently, no `{±1}`-valued character on `A` restricts to the prescribed
`χ` on the subcategory, because such a character is `+1` at `(0,2)` while
`χ(0,2) = -1`. -/
theorem appendixB_chi_does_not_extend
    (ψ : AddChar PointedA ℂ)
    (hsign : ∀ x : PointedA, ψ x = 1 ∨ ψ x = -1)
    (hrestrict : ψ (((0 : ZMod 4), (2 : ZMod 4)) : PointedA) = chi (((0 : ZMod 4), (2 : ZMod 4)) : PointedA)) :
    False := by
  have h1 : ψ (((0 : ZMod 4), (2 : ZMod 4)) : PointedA) = 1 :=
    appendixB_chi_0_2_of_sign ψ hsign
  have h2 : chi (((0 : ZMod 4), (2 : ZMod 4)) : PointedA) = -1 :=
    appendixB_chi_at_zero_two
  rw [hrestrict] at h1
  rw [h2] at h1
  exact absurd h1 (by norm_num)

/-- **Appendix B obstruction** (paper name).  The sign character `χ(a,b) = i^b`
is `+1` on `f` but does not extend to a spherical structure on `𝒯`:
every `{±1}`-valued character on `A` is trivial on `(0,2)`, while `χ(0,2) = -1`. -/
theorem appendixB_obstruction :
    chi (((0 : ZMod 4), (2 : ZMod 4)) : PointedA) = -1 ∧
      (∀ ψ : AddChar PointedA ℂ,
        (∀ x : PointedA, ψ x = 1 ∨ ψ x = -1) →
          ψ (((0 : ZMod 4), (2 : ZMod 4)) : PointedA) = 1) ∧
      (∀ ψ : AddChar PointedA ℂ,
        (∀ x : PointedA, ψ x = 1 ∨ ψ x = -1) →
          ψ (((0 : ZMod 4), (2 : ZMod 4)) : PointedA) ≠ chi (((0 : ZMod 4), (2 : ZMod 4)) : PointedA)) := by
  refine ⟨appendixB_chi_at_zero_two, ?_, ?_⟩
  · intro ψ hsign
    exact appendixB_chi_0_2_of_sign ψ hsign
  · intro ψ hsign h
    exact appendixB_chi_does_not_extend ψ hsign h

/-! ## Slope of the pivotal extension `χ̃` -/

/-- The slope identity of Appendix B:
`χ̃(a,b)² = (-1)^b = m(f,(a,b))`.  The pivotal extension is therefore
nonspherical whenever `b` is odd. -/
theorem appendixB_slope (p : PointedA) :
    chi p ^ 2 = (-1 : ℂ) ^ p.2.val ∧
      (-1 : ℂ) ^ p.2.val = monodromy f p := by
  constructor
  · -- χ(p)² = (I^{b.val})² = (I²)^{b.val} = (-1)^{b.val}
    have h : (Complex.I ^ p.2.val) ^ 2 = (Complex.I ^ 2) ^ p.2.val := by
      calc (Complex.I ^ p.2.val) ^ 2
          = Complex.I ^ (p.2.val * 2) := (pow_mul ..).symm
        _ = Complex.I ^ (2 * p.2.val) := by rw [mul_comm]
        _ = (Complex.I ^ 2) ^ p.2.val := pow_mul ..
    rw [chi_apply, h, Complex.I_sq]
  · -- m(f,p) = I^{2·b.val + 0·a.val} = (I²)^{b.val} = (-1)^{b.val}
    have hval : ((2 : ZMod 4)).val = 2 := ZMod.val_two_four
    have hzero : ((0 : ZMod 4)).val = 0 := ZMod.val_zero
    simp only [monodromy, f, hval, hzero, zero_mul, add_zero]
    have h : Complex.I ^ (2 * p.2.val) = (Complex.I ^ 2) ^ p.2.val := pow_mul ..
    rw [h, Complex.I_sq]

/-- The twist of `f` remains `+1` (consistent with Lemma 2.1 of the paper):
`q(f) = i^{2·0} = 1`. -/
theorem appendixB_twist_f : q f = 1 := by
  have hval : ((2 : ZMod 4)).val = 2 := ZMod.val_two_four
  have hzero : ((0 : ZMod 4)).val = 0 := ZMod.val_zero
  simp [q, f, hval, hzero]

/-- The prescribed character is `+1` on `f = (2,0)`, as required for the
modification to fix the Tannakian centre. -/
theorem appendixB_chi_on_f : chi f = 1 := by
  have hzero : ((0 : ZMod 4)).val = 0 := ZMod.val_zero
  simp [chi, f, hzero]

end Paper18
