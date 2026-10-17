import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! # The actual universal normalized two-cocycle module

The generators are nondegenerate ordered pairs of group elements. The
explicit group action makes the generator function an actual two-cocycle.
Over a finite ring and a finite group the underlying module is finite.
-/
noncomputable section
universe u v
namespace Paper18.Category.FiniteCohomologyKilling
open Classical
variable (G : Type u) [Group G] (R : Type v) [CommRing R]

def NondegeneratePair := {p : G × G // p.1 ≠ 1 ∧ p.2 ≠ 1}

def UniversalModule := NondegeneratePair G →₀ R

instance : AddCommGroup (UniversalModule G R) := inferInstanceAs (AddCommGroup (_ →₀ R))
instance : Module R (UniversalModule G R) := inferInstanceAs (Module R (_ →₀ R))
instance [Fintype G] : Fintype (NondegeneratePair G) :=
  inferInstanceAs (Fintype {p : G × G // p.1 ≠ 1 ∧ p.2 ≠ 1})
instance [Fintype G] [Fintype R] : Fintype (UniversalModule G R) :=
  inferInstanceAs (Fintype (_ →₀ R))

/-- The actual normalized universal pair generator. -/
def universalPair (g h : G) : UniversalModule G R :=
  if hg : g = 1 then 0 else if hh : h = 1 then 0 else
    Finsupp.single ⟨(g, h), hg, hh⟩ 1

@[simp] lemma universalPair_one_left (h : G) : universalPair G R 1 h = 0 := by
  simp [universalPair]

@[simp] lemma universalPair_one_right (g : G) : universalPair G R g 1 = 0 := by
  simp [universalPair]

lemma universalPair_of_ne (g h : G) (hg : g ≠ 1) (hh : h ≠ 1) :
    universalPair G R g h = Finsupp.single ⟨(g, h), hg, hh⟩ 1 := by
  simp only [universalPair, dif_neg hg, dif_neg hh]

/-- The explicit action on generators, extended by actual linearity. -/
def universalActionLinear (g : G) : UniversalModule G R →ₗ[R] UniversalModule G R :=
  Finsupp.linearCombination R (fun p : NondegeneratePair G =>
    universalPair G R (g * p.1.1) p.1.2 - universalPair G R g (p.1.1 * p.1.2) +
      universalPair G R g p.1.1)

lemma universalActionLinear_pair (g h k : G) :
    universalActionLinear G R g (universalPair G R h k) =
      universalPair G R (g * h) k - universalPair G R g (h * k) + universalPair G R g h := by
  by_cases hh : h = 1
  · subst h
    simp only [universalPair_one_left, map_zero, mul_one, one_mul,
      sub_self, add_zero, universalPair_one_right]
  · by_cases hk : k = 1
    · subst k
      simp only [universalPair_one_right, map_zero, mul_one, zero_sub, neg_add_cancel]
    · rw [universalPair_of_ne G R h k hh hk]
      change Finsupp.linearCombination R _
        (Finsupp.single (⟨(h, k), hh, hk⟩ : NondegeneratePair G) 1) = _
      simp only [Finsupp.linearCombination_single, one_smul]

lemma universalActionLinear_one : universalActionLinear G R 1 = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro p r
  have hs : (Finsupp.single p r : UniversalModule G R) =
      r • universalPair G R p.1.1 p.1.2 := by
    rw [universalPair_of_ne G R _ _ p.2.1 p.2.2]
    change Finsupp.single p r = r • Finsupp.single p (1 : R)
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hs]
  simp only [map_smul]
  change r • universalActionLinear G R 1 (universalPair G R p.1.1 p.1.2) =
    r • universalPair G R p.1.1 p.1.2
  congr 1
  simpa only [one_mul, universalPair_one_left, sub_zero, add_zero] using
    universalActionLinear_pair G R 1 p.1.1 p.1.2

lemma universalActionLinear_mul (g h : G) :
    universalActionLinear G R (g * h) =
      (universalActionLinear G R g).comp (universalActionLinear G R h) := by
  apply Finsupp.lhom_ext
  intro p r
  have hs : (Finsupp.single p r : UniversalModule G R) =
      r • universalPair G R p.1.1 p.1.2 := by
    rw [universalPair_of_ne G R _ _ p.2.1 p.2.2]
    change Finsupp.single p r = r • Finsupp.single p (1 : R)
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hs]
  simp only [LinearMap.comp_apply, map_smul]
  change r • universalActionLinear G R (g * h) (universalPair G R p.1.1 p.1.2) =
    r • universalActionLinear G R g (universalActionLinear G R h (universalPair G R p.1.1 p.1.2))
  congr 1
  rw [universalActionLinear_pair, universalActionLinear_pair]
  simp only [map_sub, map_add]
  rw [universalActionLinear_pair, universalActionLinear_pair, universalActionLinear_pair]
  simp only [mul_assoc]
  abel

/-- The generator function satisfies the actual normalized two-cocycle equation. -/
lemma universalPair_cocycle (g h k : G) :
    universalActionLinear G R g (universalPair G R h k) + universalPair G R g (h * k) =
      universalPair G R g h + universalPair G R (g * h) k := by
  rw [universalActionLinear_pair]
  abel

end Paper18.Category.FiniteCohomologyKilling
