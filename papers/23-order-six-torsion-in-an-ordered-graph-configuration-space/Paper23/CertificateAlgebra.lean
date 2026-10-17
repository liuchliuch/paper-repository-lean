import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The algebraic consequence of the degree-two certificate in Paper 23

The chain groups remain arbitrary additive commutative groups.  The homology
object below is the actual quotient of the cycle subgroup by the boundary
subgroup.  In an integral cellular chain complex the groups are free abelian,
but no freeness hypothesis is needed for the certificate argument.
-/

namespace Paper23.CertificateAlgebra

universe u₃ u₂ u₁

/-- The part of an integral chain complex used by the degree-two certificate. -/
structure IntegralChainComplex₂
    (C3 : Type u₃) (C2 : Type u₂) (C1 : Type u₁)
    [AddCommGroup C3] [AddCommGroup C2] [AddCommGroup C1] where
  d3 : C3 →+ C2
  d2 : C2 →+ C1
  boundary_squared : ∀ c, d2 (d3 c) = 0

variable {C3 : Type u₃} {C2 : Type u₂} {C1 : Type u₁}
variable [AddCommGroup C3] [AddCommGroup C2] [AddCommGroup C1]

namespace IntegralChainComplex₂

variable (K : IntegralChainComplex₂ C3 C2 C1)

/-- Integral two-cycles. -/
abbrev Cycles₂ := K.d2.ker

/-- Boundaries regarded as a subgroup of the group of cycles. -/
def boundaries₂ : AddSubgroup K.Cycles₂ :=
  K.d3.range.comap K.d2.ker.subtype

/-- Degree-two integral homology, as cycles modulo boundaries. -/
abbrev Homology₂ := K.Cycles₂ ⧸ K.boundaries₂

/-- The usual quotient map from cycles to their homology classes. -/
def homologyClass : K.Cycles₂ →+ K.Homology₂ :=
  QuotientAddGroup.mk' K.boundaries₂

@[simp] theorem mem_boundaries₂ (c : K.Cycles₂) :
    c ∈ K.boundaries₂ ↔ (c : C2) ∈ K.d3.range := Iff.rfl

/-- Every boundary defines a cycle, using the chain-complex identity. -/
def boundaryCycle (c : C3) : K.Cycles₂ :=
  ⟨K.d3 c, K.boundary_squared c⟩

@[simp] theorem boundaryCycle_class (c : C3) :
    K.homologyClass (K.boundaryCycle c) = 0 := by
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  exact ⟨c, rfl⟩

end IntegralChainComplex₂

/-- The four identities of equation (5), in the original chain groups. -/
structure Certificate (K : IntegralChainComplex₂ C3 C2 C1) where
  z : C2
  b : C3
  phi : C2 →+ ZMod 6
  cycle : K.d2 z = 0
  bounding : K.d3 b = (6 : ℕ) • z
  cocycle : ∀ c, phi (K.d3 c) = 0
  evaluation : phi z = 1

/-- A mod-six detector and an annihilating multiple determine exact order six. -/
theorem exact_order_six_of_detector {A : Type*} [AddCommGroup A]
    (x : A) (f : A →+ ZMod 6) (annihilated : (6 : ℕ) • x = 0)
    (detected : f x = 1) : addOrderOf x = 6 := by
  apply Nat.dvd_antisymm (addOrderOf_dvd_of_nsmul_eq_zero annihilated)
  have h := addOrderOf_map_dvd f x
  simpa only [detected, ZMod.addOrderOf_one] using h

namespace Certificate

variable {K : IntegralChainComplex₂ C3 C2 C1} (cert : Certificate K)

/-- The certified chain, considered as a cycle. -/
def cycleElement : K.Cycles₂ := ⟨cert.z, cert.cycle⟩

/-- The class in the actual degree-two homology quotient. -/
def homologyElement : K.Homology₂ := K.homologyClass cert.cycleElement

/-- The cocycle vanishes on the boundary subgroup of the cycle group. -/
theorem boundaries_le_detector_ker :
    K.boundaries₂ ≤ (cert.phi.comp K.d2.ker.subtype).ker := by
  intro c hc
  obtain ⟨b, hb⟩ := hc
  change K.d3 b = (c : C2) at hb
  change cert.phi (c : C2) = 0
  rw [← hb]
  exact cert.cocycle b

/-- Evaluation by the cocycle descends to integral homology. -/
def homologyDetector : K.Homology₂ →+ ZMod 6 :=
  QuotientAddGroup.lift K.boundaries₂ (cert.phi.comp K.d2.ker.subtype)
    cert.boundaries_le_detector_ker

@[simp] theorem detector_on_class (c : K.Cycles₂) :
    cert.homologyDetector (K.homologyClass c) = cert.phi (c : C2) := rfl

@[simp] theorem detector_on_element :
    cert.homologyDetector cert.homologyElement = 1 := cert.evaluation

/-- The bounding chain gives six times the certified homology class equal to zero. -/
theorem six_smul_element : (6 : ℕ) • cert.homologyElement = 0 := by
  rw [homologyElement, ← map_nsmul]
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  exact ⟨cert.b, cert.bounding⟩

/-- The certified cycle has exact order six in degree-two integral homology. -/
theorem exact_order_six : addOrderOf cert.homologyElement = 6 :=
  exact_order_six_of_detector cert.homologyElement cert.homologyDetector
    cert.six_smul_element cert.detector_on_element

/-- The integral annihilator of the class consists precisely of multiples of six. -/
theorem zsmul_element_eq_zero_iff (k : ℤ) :
    k • cert.homologyElement = 0 ↔ (6 : ℤ) ∣ k := by
  rw [← addOrderOf_dvd_iff_zsmul_eq_zero, cert.exact_order_six]
  rfl

/-- Equivalently, a natural multiple bounds precisely when six divides it. -/
theorem nsmul_element_eq_zero_iff (k : ℕ) :
    k • cert.homologyElement = 0 ↔ 6 ∣ k := by
  rw [← addOrderOf_dvd_iff_nsmul_eq_zero, cert.exact_order_six]

/-- Twice the certified class has exact order three. -/
theorem twice_exact_order_three :
    addOrderOf ((2 : ℕ) • cert.homologyElement) = 3 := by
  rw [addOrderOf_nsmul' _ (by decide : (2 : ℕ) ≠ 0), cert.exact_order_six]
  decide

/-- Three times the certified class has exact order two. -/
theorem thrice_exact_order_two :
    addOrderOf ((3 : ℕ) • cert.homologyElement) = 2 := by
  rw [addOrderOf_nsmul' _ (by decide : (3 : ℕ) ≠ 0), cert.exact_order_six]
  decide

/-- The same integer divisibility test expressed directly in the chain group. -/
theorem zsmul_mem_range_iff (k : ℤ) :
    k • cert.z ∈ K.d3.range ↔ (6 : ℤ) ∣ k := by
  have h := QuotientAddGroup.eq_zero_iff (N := K.boundaries₂) (k • cert.cycleElement)
  change K.homologyClass (k • cert.cycleElement) = 0 ↔
    k • cert.z ∈ K.d3.range at h
  rw [map_zsmul] at h
  exact h.symm.trans (cert.zsmul_element_eq_zero_iff k)

/-- The detected homology class is nonzero. -/
theorem homologyElement_ne_zero : cert.homologyElement ≠ 0 := by
  intro h
  have hh := congrArg cert.homologyDetector h
  have h10 : (1 : ZMod 6) = 0 := by
    simpa only [cert.detector_on_element, map_zero] using hh
  exact (by decide : (1 : ZMod 6) ≠ 0) h10

include cert in
/-- The constructed homology quotient is not torsion-free. -/
theorem homology_not_torsion_free : ¬ IsAddTorsionFree K.Homology₂ := by
  intro h
  letI := h
  apply cert.homologyElement_ne_zero
  apply IsAddTorsionFree.nsmul_right_injective (by decide : (6 : ℕ) ≠ 0)
  simpa only [nsmul_zero] using cert.six_smul_element

/-- The certified integral cycle is not a boundary. -/
theorem not_boundary : cert.z ∉ K.d3.range := by
  rintro ⟨b, hb⟩
  have h : (1 : ZMod 6) = 0 := by
    rw [← cert.evaluation, ← hb]
    exact cert.cocycle b
  exact (by decide : (1 : ZMod 6) ≠ 0) h

/-- The explicit failure of saturation in the original chain group. -/
theorem failure_saturation :
    (6 : ℕ) • cert.z ∈ K.d3.range ∧
      cert.z ∈ K.d2.ker ∧ cert.z ∉ K.d3.range := by
  exact ⟨⟨cert.b, cert.bounding⟩, cert.cycle, cert.not_boundary⟩

include cert in
/-- Consequently the boundary subgroup is not saturated even within the cycles. -/
theorem boundaries_not_saturated :
    ¬ (∀ (c : K.Cycles₂) (n : ℕ), n ≠ 0 →
      n • c ∈ K.boundaries₂ → c ∈ K.boundaries₂) := by
  intro h
  have hz := h cert.cycleElement 6 (by decide) ⟨cert.b, cert.bounding⟩
  exact cert.not_boundary hz

include cert in
/-- In particular there is a nonzero torsion class, with an odd-order multiple. -/
theorem exists_exact_order_six_and_odd_torsion :
    ∃ x : K.Homology₂, addOrderOf x = 6 ∧ addOrderOf ((2 : ℕ) • x) = 3 := by
  exact ⟨cert.homologyElement, cert.exact_order_six, cert.twice_exact_order_three⟩

end Certificate
end Paper23.CertificateAlgebra
