import Paper18.Fusion.Basic
import Paper18.Fusion.Pivotal
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Finite gradings and sign characters

ℤ/2-gradings of a fusion basis by monodromy with an order-two invertible
object, and sign characters `χ : ι → {±1}` arising as the ratio of two
spherical structures.
-/

noncomputable section

open Classical

universe u

open scoped BigOperators

namespace Paper18

/-- A `ℤ/2`-grading of a fusion basis: each simple is even or odd, the unit is
even, and duality preserves the degree. -/
structure Z2Grading {ι : Type u} [Fintype ι] (B : FusionBasis ι) where
  /-- Degree function: `false` = even, `true` = odd. -/
  degree : ι → Bool
  /-- The unit is even. -/
  degree_one : degree B.one = false
  /-- Duality preserves degree. -/
  degree_dual : ∀ x, degree (B.dual x) = degree x
  /-- Every constituent has the tensor-product degree. -/
  degree_tensor : ∀ x y z, 0 < B.N x y z →
    degree z = Bool.xor (degree x) (degree y)

namespace Z2Grading

variable {ι : Type u} [Fintype ι] {B : FusionBasis ι} (G : Z2Grading B)

/-- Even simple objects. -/
def even : Set ι := {x | G.degree x = false}

/-- Odd simple objects. -/
def odd : Set ι := {x | G.degree x = true}

lemma one_mem_even : B.one ∈ G.even := by
  simp [even, G.degree_one]

lemma even_union_odd : G.even ∪ G.odd = Set.univ := by
  ext x
  simp only [even, odd, Set.mem_setOf_eq, Set.mem_union, Set.mem_univ, iff_true]
  cases G.degree x <;> simp

/-- A grading is *faithful* when both parts are nonempty. -/
def Faithful : Prop := G.even.Nonempty ∧ G.odd.Nonempty

end Z2Grading

/-- A sign character on simples: values in `{1,-1}` and multiplicative along
tensor in the sense that the character of a tensor product is the product. -/
structure SignCharacter {ι : Type u} [Fintype ι] (B : FusionBasis ι) where
  /-- Values `χ(x) ∈ {1,-1} ⊂ ℂ`. -/
  val : ι → ℂ
  /-- Values are `±1`. -/
  val_mem : ∀ x, val x = 1 ∨ val x = -1
  /-- The unit has value `1`. -/
  val_one : val B.one = 1
  /-- Duality: `χ_{X*} = χ_X^{-1} = χ_X` since `χ_X = ±1`. -/
  val_dual : ∀ x, val (B.dual x) = (val x)⁻¹
  /-- Multiplicativity on every constituent of a tensor product. -/
  val_tensor : ∀ x y z, 0 < B.N x y z → val z = val x * val y

namespace SignCharacter

variable {ι : Type u} [Fintype ι] {B : FusionBasis ι} (χ : SignCharacter B)

lemma val_inv (x : ι) : (χ.val x)⁻¹ = χ.val x := by
  rcases χ.val_mem x with h | h <;> simp [h]

lemma val_dual_eq (x : ι) : χ.val (B.dual x) = χ.val x := by
  rw [χ.val_dual, χ.val_inv]

/-- Kernel of the sign character: simples with value `+1`. -/
def ker : Set ι := {x | χ.val x = 1}

/-- Values on a simple are roots of unity of order dividing two. -/
lemma val_sq (x : ι) : χ.val x ^ 2 = 1 := by
  rcases χ.val_mem x with h | h <;> simp [h]

/-- The character is real-valued. -/
lemma val_re (x : ι) : (χ.val x).re = χ.val x ∨ (χ.val x).re = -χ.val x := by
  rcases χ.val_mem x with h | h <;> simp [h]

end SignCharacter

/-- Ratio of two spherical/pivotal structures on the same fusion basis: the
slope of the second relative to the first.  If `j = j_+ χ` then `χ` is a sign
character and `χ_ε = -1` on the order-two lift `ε` of the unit. -/
def pivotalRatio {ι : Type u} [Fintype ι] {B : FusionBasis ι}
    (J Jpos : PivotalData B) (x : ι) : ℂ :=
  J.jdim x / Jpos.jdim x

lemma pivotalRatio_one {ι : Type u} [Fintype ι] {B : FusionBasis ι}
    (J Jpos : PivotalData B) :
    pivotalRatio J Jpos B.one = 1 := by
  simp [pivotalRatio, J.jdim_one, Jpos.jdim_one]

end Paper18
