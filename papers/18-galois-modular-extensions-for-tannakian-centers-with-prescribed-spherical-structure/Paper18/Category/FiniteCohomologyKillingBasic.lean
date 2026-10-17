import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! # Explicit fourth cocycles and their finite-group transfer primitive

The functions below are the usual multiplicative normalized inhomogeneous
cochains, with trivial coefficient action. All cochain equations are actual
pointwise equations; no cohomology-killing or categorical-existence theorem
is supplied as a field.
-/
noncomputable section
universe u v
namespace Paper18.Category.FiniteCohomologyKilling
open scoped BigOperators
open Classical
variable {G : Type u} [Group G] {M : Type v} [CommGroup M]

/-- The actual multiplicative inhomogeneous coboundary of a third cochain. -/
def dThree (a : G → G → G → M) (g h k l : G) : M :=
  a h k l * (a (g * h) k l)⁻¹ * a g (h * k) l * (a g h (k * l))⁻¹ * a g h k

/-- A normalized actual third cochain. -/
structure ThreeCochain (G : Type u) [Group G] (M : Type v) [CommGroup M] where
  val : G → G → G → M
  one₁ : ∀ h k, val 1 h k = 1
  one₂ : ∀ g k, val g 1 k = 1
  one₃ : ∀ g h, val g h 1 = 1

/-- A normalized fourth cocycle with trivial coefficient action. -/
structure FourCocycle (G : Type u) [Group G] (M : Type v) [CommGroup M] where
  val : G → G → G → G → M
  one₁ : ∀ h k l, val 1 h k l = 1
  one₂ : ∀ g k l, val g 1 k l = 1
  one₃ : ∀ g h l, val g h 1 l = 1
  one₄ : ∀ g h k, val g h k 1 = 1
  cocycle : ∀ a b c d e,
    val b c d e * val a (b * c) d e * val a b c (d * e) =
      val (a * b) c d e * val a b (c * d) e * val a b c d

attribute [simp] ThreeCochain.one₁ ThreeCochain.one₂ ThreeCochain.one₃
  FourCocycle.one₁ FourCocycle.one₂ FourCocycle.one₃ FourCocycle.one₄

lemma dThree_mul (a b : G → G → G → M) (g h k l : G) :
    dThree (fun x y z => a x y z * b x y z) g h k l =
      dThree a g h k l * dThree b g h k l := by
  apply Additive.ofMul.injective
  simp only [dThree, ofMul_mul, ofMul_inv]
  abel

lemma dThree_pow (a : G → G → G → M) (n : ℕ) (g h k l : G) :
    dThree (fun x y z => a x y z ^ n) g h k l = (dThree a g h k l) ^ n := by
  simp only [dThree, mul_pow, inv_pow]

/-- Third coboundaries satisfy the fourth cocycle equation, by cancellation. -/
lemma dThree_cocycle (a : G → G → G → M) (g h k l m : G) :
    dThree a h k l m * dThree a g (h * k) l m * dThree a g h k (l * m) =
      dThree a (g * h) k l m * dThree a g h (k * l) m * dThree a g h k l := by
  apply Additive.ofMul.injective
  simp only [dThree, mul_assoc, ofMul_mul, ofMul_inv]
  abel

namespace FourCocycle
variable (ω : FourCocycle G M)

/-- Actual cocycle pullback along an actual group homomorphism. -/
def pullback {H : Type*} [Group H] (p : H →* G) : FourCocycle H M where
  val a b c d := ω.val (p a) (p b) (p c) (p d)
  one₁ := by simp
  one₂ := by simp
  one₃ := by simp
  one₄ := by simp
  cocycle a b c d e := by simpa only [map_mul] using ω.cocycle (p a) (p b) (p c) (p d) (p e)

/-- A change by an actual normalized third coboundary. -/
def twist (a : ThreeCochain G M) : FourCocycle G M where
  val g h k l := ω.val g h k l / dThree a.val g h k l
  one₁ := by intros; simp [dThree]
  one₂ := by intros; simp [dThree]
  one₃ := by intros; simp [dThree]
  one₄ := by intros; simp [dThree]
  cocycle g h k l m := by
    simp only [div_mul_div_comm]
    rw [ω.cocycle, dThree_cocycle]

/-- Multiplying over the first coordinate is the explicit transfer cochain. -/
def transferPrimitive [Fintype G] (g h k : G) : M := ∏ t : G, ω.val t g h k

/-- The transfer cochain is normalized on all three coordinates. -/
def transferCochain [Fintype G] : ThreeCochain G M where
  val := ω.transferPrimitive
  one₁ := by intro h k; simp [transferPrimitive]
  one₂ := by intro g k; simp [transferPrimitive]
  one₃ := by intro g h; simp [transferPrimitive]

/-- The finite-group order annihilates every actual fourth cocycle class;
the proof supplies its actual third-cochain primitive. -/
lemma transferPrimitive_spec [Fintype G] (g h k l : G) :
    dThree ω.transferPrimitive g h k l = ω.val g h k l ^ Fintype.card G := by
  have hh := Finset.prod_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun t _ => ω.cocycle t g h k l)
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] at hh
  have hr : (∏ t : G, ω.val (t * g) h k l) = ω.transferPrimitive h k l :=
    Equiv.prod_comp (Equiv.mulRight g) (fun t => ω.val t h k l)
  rw [hr] at hh
  change ω.val g h k l ^ Fintype.card G * ω.transferPrimitive (g * h) k l *
      ω.transferPrimitive g h (k * l) =
    ω.transferPrimitive h k l * ω.transferPrimitive g (h * k) l *
      ω.transferPrimitive g h k at hh
  apply mul_right_cancel (b := ω.transferPrimitive (g * h) k l *
    ω.transferPrimitive g h (k * l))
  calc
    _ = ω.transferPrimitive h k l * ω.transferPrimitive g (h * k) l *
        ω.transferPrimitive g h k := by
      apply Additive.ofMul.injective
      simp only [dThree, ofMul_mul, ofMul_inv]
      abel
    _ = _ := by simpa only [mul_assoc] using hh.symm

end FourCocycle
end Paper18.Category.FiniteCohomologyKilling
