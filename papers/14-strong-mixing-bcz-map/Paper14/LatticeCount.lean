import Paper14.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Order.Floor.Ring
/-!
# Lattice points and primitive vectors

Paper anchors: Ex5 (`Λ_x`), S2.p1 (primitivity = coprimality), Ex32 (`Z_{n,α}`).
-/
open MeasureTheory Filter Topology Set
namespace Paper14

/-- Primitivity in the displayed basis is coprimality of coefficients. -/
def PrimitiveIffCoprimeStatement : Prop :=
  ∀ a b : ℝ, (a, b) ∈ Omega → ∀ p q : ℤ,
    IsPrimitiveVec (a, b)
      ((p : ℝ) * a + (q : ℝ) * b, (q : ℝ) / a) ↔ IsCoprime p q

/-- Change of coordinates: `c = 1/a ≥ 1` and `θ = b/a (mod 1)`. -/
def CoordinateChangeStatement : Prop :=
  ∀ x ∈ Omega, 1 ≤ cOf x ∧ 0 ≤ thetaOf x ∧ thetaOf x < 1

/-- On `Ω` one has `a > 0`, so `c = a⁻¹ ≥ 1` and `θ = fract(b/a)` lies in `[0,1)`. -/
theorem coordinateChange : CoordinateChangeStatement := by
  intro x hx
  have ha0 : 0 < x.1 := hx.1
  have ha1 : x.1 ≤ 1 := hx.2.1
  refine ⟨?_, Int.fract_nonneg _, Int.fract_lt_one _⟩
  show 1 ≤ cOf x
  rw [cOf]
  exact (one_le_inv₀ ha0).mpr ha1

/-- Helper: from `q / a = k * (q' / a)` with `a ≠ 0` get `q = k * q'` in `ℤ`. -/
private lemma cast_int_eq_of_div {a : ℝ} (ha : a ≠ 0) {q k q' : ℤ}
    (h : (q : ℝ) / a = (k : ℝ) * ((q' : ℝ) / a)) :
    q = k * q' := by
  have h2 : (q : ℝ) = (k : ℝ) * (q' : ℝ) := by
    calc (q : ℝ) = (q : ℝ) / a * a := (div_mul_cancel₀ _ ha).symm
      _ = ((k : ℝ) * ((q' : ℝ) / a)) * a := by rw [h]
      _ = (k : ℝ) * ((q' : ℝ) / a * a) := by ring
      _ = (k : ℝ) * (q' : ℝ) := by rw [div_mul_cancel₀ _ ha]
  exact_mod_cast h2

/-- Helper: from `p * a + q * b = k * (p' * a + q' * b)`, `q = k * q'`, `a ≠ 0`, get `p = k * p'`. -/
private lemma cast_fst_eq_of_cancel {a b : ℝ} (ha : a ≠ 0) {p q p' q' k : ℤ}
    (hfst : (p : ℝ) * a + (q : ℝ) * b = (k : ℝ) * ((p' : ℝ) * a + (q' : ℝ) * b))
    (hq : q = k * q') : p = k * p' := by
  have hqR : (q : ℝ) = (k : ℝ) * (q' : ℝ) := by exact_mod_cast hq
  have h2 : (p : ℝ) * a = (k : ℝ) * (p' : ℝ) * a := by
    calc (p : ℝ) * a
        = (p : ℝ) * a + (q : ℝ) * b - (q : ℝ) * b := by ring
      _ = (k : ℝ) * ((p' : ℝ) * a + (q' : ℝ) * b) - (q : ℝ) * b := by rw [hfst]
      _ = (k : ℝ) * (p' : ℝ) * a + ((k : ℝ) * (q' : ℝ) * b - (q : ℝ) * b) := by ring
      _ = (k : ℝ) * (p' : ℝ) * a := by
        rw [hqR]
        ring
  have h3 : (p : ℝ) = (k : ℝ) * (p' : ℝ) := by
    have h4 : (p : ℝ) * a * a⁻¹ = (k : ℝ) * (p' : ℝ) * a * a⁻¹ := by rw [h2]
    rwa [mul_assoc, mul_assoc, mul_inv_cancel₀ ha, mul_one, mul_one] at h4
  exact_mod_cast h3

/-- The vector with coefficients `(p,q)` is primitive in `Λ_{(a,b)}`
iff `gcd(p,q)=1`.  The basis `(a,0), (b,a⁻¹)` has `a ≠ 0`, so the
coefficients of a lattice vector are uniquely determined by the vector. -/
theorem primitiveIffCoprime : PrimitiveIffCoprimeStatement := by
  intro a b hab p q
  have ha0 : 0 < a := hab.1
  have ha : a ≠ 0 := ha0.ne'
  constructor
  · -- primitive ⇒ coprime
    intro hprim
    have hv0 : ((p : ℝ) * a + (q : ℝ) * b, (q : ℝ) / a) ≠ 0 := hprim.2.1
    by_contra hnc
    have hne : Int.gcd p q ≠ 1 := mt Int.isCoprime_iff_gcd_eq_one.mpr hnc
    rcases Nat.eq_zero_or_pos (Int.gcd p q) with hg0 | hgpos
    · -- gcd = 0 forces p = q = 0, hence v = 0
      obtain ⟨hp0, hq0⟩ := Int.gcd_eq_zero_iff.mp hg0
      apply hv0
      simp [hp0, hq0]
    · -- gcd = d ≥ 2, then v is a nontrivial multiple
      have hge2 : 2 ≤ Int.gcd p q := by
        rcases Nat.eq_or_lt_of_le hgpos with hg1 | hg1
        · exact absurd hg1.symm hne
        · omega
      obtain ⟨p', hp'⟩ : (Int.gcd p q : ℤ) ∣ p := Int.gcd_dvd_left p q
      obtain ⟨q', hq'⟩ : (Int.gcd p q : ℤ) ∣ q := Int.gcd_dvd_right p q
      have hp : p = (Int.gcd p q) * p' := by exact_mod_cast hp'
      have hq : q = (Int.gcd p q) * q' := by exact_mod_cast hq'
      have hwdef : ((p' : ℝ) * a + (q' : ℝ) * b, (q' : ℝ) / a) ∈ Lambda (a, b) :=
        mem_Lambda.mpr ⟨p', q', rfl, rfl⟩
      have hsmul :
          ((p : ℝ) * a + (q : ℝ) * b, (q : ℝ) / a)
            = ((Int.gcd p q : ℤ) : ℝ) • ((p' : ℝ) * a + (q' : ℝ) * b, (q' : ℝ) / a) := by
        apply Prod.ext
        · -- first coordinate
          simp only [Prod.smul_mk, smul_eq_mul]
          have hpR : (p : ℝ) = ((Int.gcd p q : ℤ) : ℝ) * (p' : ℝ) := by exact_mod_cast hp
          have hqR : (q : ℝ) = ((Int.gcd p q : ℤ) : ℝ) * (q' : ℝ) := by exact_mod_cast hq
          rw [hpR, hqR]
          ring
        · -- second coordinate
          simp only [Prod.smul_mk, smul_eq_mul]
          have hqR : (q : ℝ) = ((Int.gcd p q : ℤ) : ℝ) * (q' : ℝ) := by exact_mod_cast hq
          rw [hqR]
          field_simp
      have hw0 : ((p' : ℝ) * a + (q' : ℝ) * b, (q' : ℝ) / a) ≠ 0 := by
        intro h0
        have hq'a : (q' : ℝ) / a = 0 := congrArg Prod.snd h0
        have hq'0 : q' = 0 := by
          rcases div_eq_zero_iff.mp hq'a with h | h
          · exact_mod_cast h
          · exact absurd h ha
        have hp'a : (p' : ℝ) * a + (q' : ℝ) * b = 0 := congrArg Prod.fst h0
        have hp'0 : p' = 0 := by
          rw [hq'0] at hp'a
          simp only [Int.cast_zero, zero_mul, add_zero] at hp'a
          rcases mul_eq_zero.mp hp'a with h | h
          · exact_mod_cast h
          · exact absurd h ha
        have hp0 : p = 0 := by
          rw [hp, hp'0]
          ring
        have hq0 : q = 0 := by
          rw [hq, hq'0]
          ring
        have hg : Int.gcd p q = 0 := Int.gcd_eq_zero_iff.mpr ⟨hp0, hq0⟩
        omega
      have hkabs : |((Int.gcd p q : ℤ) : ℤ)| ≠ 1 := by
        have h : |((Int.gcd p q : ℤ) : ℤ)| = ((Int.gcd p q : ℤ) : ℤ) :=
          abs_of_nonneg (Int.natCast_nonneg _)
        rw [h]
        intro h1
        exact hne (by exact_mod_cast h1)
      have hthird := hprim.2.2 (Int.gcd p q)
        ((p' : ℝ) * a + (q' : ℝ) * b, (q' : ℝ) / a) hwdef hsmul
      cases hthird with
      | inl hk => exact hkabs hk
      | inr hw => exact hw0 hw
  · -- coprime ⇒ primitive
    intro hcop
    refine ⟨?_, ?_, ?_⟩
    · -- v ∈ Lambda
      exact mem_Lambda.mpr ⟨p, q, rfl, rfl⟩
    · -- v ≠ 0
      intro h0
      have hq0 : (q : ℝ) / a = 0 := congrArg Prod.snd h0
      have hq : (q : ℝ) = 0 := by
        rcases div_eq_zero_iff.mp hq0 with h | h
        · exact h
        · exact absurd h ha
      have hp0 : (p : ℝ) * a + (q : ℝ) * b = 0 := congrArg Prod.fst h0
      have hp : (p : ℝ) = 0 := by
        rw [show (q : ℝ) = 0 from hq] at hp0
        simp only [zero_mul, add_zero] at hp0
        rcases mul_eq_zero.mp hp0 with h | h
        · exact h
        · exact absurd h ha
      have hpz : p = 0 := by exact_mod_cast hp
      have hqz : q = 0 := by exact_mod_cast hq
      rw [Int.isCoprime_iff_gcd_eq_one, hqz, hpz] at hcop
      norm_num at hcop
    · -- no nontrivial integer multiple
      intro k w hw hsmul
      obtain ⟨p', q', hpw, hqw⟩ := mem_Lambda.mp hw
      have hsnd : (q : ℝ) / a = (k : ℝ) * ((q' : ℝ) / a) := by
        have h := congrArg Prod.snd hsmul
        simp only [Prod.smul_snd, smul_eq_mul] at h
        rw [hqw] at h
        exact h
      have hfst : (p : ℝ) * a + (q : ℝ) * b
          = (k : ℝ) * ((p' : ℝ) * a + (q' : ℝ) * b) := by
        have h := congrArg Prod.fst hsmul
        simp only [Prod.smul_fst, smul_eq_mul] at h
        rw [hpw] at h
        exact h
      have hq : q = k * q' := cast_int_eq_of_div ha hsnd
      have hp : p = k * p' := cast_fst_eq_of_cancel ha hfst hq
      have hk : (k : ℤ) ∣ p ∧ (k : ℤ) ∣ q :=
        ⟨⟨p', hp⟩, ⟨q', hq⟩⟩
      have hunit : IsUnit k := hcop.isUnit_of_dvd' hk.1 hk.2
      have : k = 1 ∨ k = -1 := Int.isUnit_iff.mp hunit
      cases this with
      | inl h => exact Or.inl (by rw [h]; simp)
      | inr h => exact Or.inl (by rw [h]; simp)

end Paper14
