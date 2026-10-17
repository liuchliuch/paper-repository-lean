import Paper18.Category.FiniteCohomologyKillingBasic
import Mathlib.RingTheory.RootsOfUnity.Basic

/-! # An actual torsion-valued representative of every complex fourth cocycle -/
noncomputable section
universe u
namespace Paper18.Category.FiniteCohomologyKilling
open Classical

lemma complexUnits_exists_pow (n : ℕ) (hn : 0 < n) (z : ℂˣ) :
    ∃ w : ℂˣ, w ^ n = z := by
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (z : ℂ) hn
  have hw₀ : w ≠ 0 := by
    intro he
    rw [he, zero_pow (Nat.ne_of_gt hn)] at hw
    exact Units.ne_zero z hw.symm
  refine ⟨Units.mk0 w hw₀, ?_⟩
  apply Units.ext
  simpa only [Units.val_pow_eq_pow_val, Units.val_mk0] using hw

/-- Choose actual roots, fixing the root of one to be one. -/
def complexUnitRoot (n : ℕ) (hn : 0 < n) (z : ℂˣ) : ℂˣ :=
  if z = 1 then 1 else Classical.choose (complexUnits_exists_pow n hn z)

@[simp] lemma complexUnitRoot_one (n : ℕ) (hn : 0 < n) :
    complexUnitRoot n hn 1 = 1 := by simp [complexUnitRoot]

@[simp] lemma complexUnitRoot_pow (n : ℕ) (hn : 0 < n) (z : ℂˣ) :
    complexUnitRoot n hn z ^ n = z := by
  by_cases hz : z = 1
  · simp [hz]
  · simp only [complexUnitRoot, if_neg hz]
    exact Classical.choose_spec (complexUnits_exists_pow n hn z)

variable {G : Type u} [Group G] [Fintype G]
namespace FourCocycle
variable (ω : FourCocycle G ℂˣ)

/-- The normalized root of the actual transfer primitive. -/
def rootTransferCochain : ThreeCochain G ℂˣ where
  val g h k := complexUnitRoot (Fintype.card G) Fintype.card_pos (ω.transferPrimitive g h k)
  one₁ := by intro h k; simp [transferPrimitive]
  one₂ := by intro g k; simp [transferPrimitive]
  one₃ := by intro g h; simp [transferPrimitive]

/-- An actual cohomologous fourth cocycle whose values have bounded finite order. -/
def torsionRepresentative : FourCocycle G ℂˣ := ω.twist ω.rootTransferCochain

/-- The constructed representative takes values in the roots of unity of
order dividing the actual order of the finite group. -/
lemma torsionRepresentative_pow (g h k l : G) :
    ω.torsionRepresentative.val g h k l ^ Fintype.card G = 1 := by
  change (ω.val g h k l / dThree ω.rootTransferCochain.val g h k l) ^ Fintype.card G = 1
  rw [div_pow, ← dThree_pow]
  have hc : (fun x y z => ω.rootTransferCochain.val x y z ^ Fintype.card G) =
      ω.transferPrimitive := by
    funext x y z
    exact complexUnitRoot_pow (Fintype.card G) Fintype.card_pos _
  rw [hc, ω.transferPrimitive_spec, div_self']

/-- The adjusted actual cocycle, now valued in an actual finite group of
complex roots of unity. -/
def torsionRepresentativeRoots : FourCocycle G (rootsOfUnity (Fintype.card G) ℂ) where
  val g h k l := ⟨ω.torsionRepresentative.val g h k l,
    (mem_rootsOfUnity _ _).mpr (ω.torsionRepresentative_pow g h k l)⟩
  one₁ h k l := by apply Subtype.ext; exact ω.torsionRepresentative.one₁ h k l
  one₂ g k l := by apply Subtype.ext; exact ω.torsionRepresentative.one₂ g k l
  one₃ g h l := by apply Subtype.ext; exact ω.torsionRepresentative.one₃ g h l
  one₄ g h k := by apply Subtype.ext; exact ω.torsionRepresentative.one₄ g h k
  cocycle a b c d e := by apply Subtype.ext; exact ω.torsionRepresentative.cocycle a b c d e

lemma rootsCoefficient_finite : Finite (rootsOfUnity (Fintype.card G) ℂ) := by
  letI : NeZero (Fintype.card G) := ⟨Fintype.card_ne_zero⟩
  infer_instance

/-- The original cocycle is recovered by the actual third coboundary,
so the finite-valued representative has not changed its cohomology class. -/
lemma torsionRepresentative_recover (g h k l : G) :
    ω.torsionRepresentative.val g h k l * dThree ω.rootTransferCochain.val g h k l =
      ω.val g h k l := by
  change (ω.val g h k l / dThree ω.rootTransferCochain.val g h k l) * _ = _
  exact div_mul_cancel _ _

end FourCocycle
end Paper18.Category.FiniteCohomologyKilling
