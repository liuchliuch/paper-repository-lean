import Paper27.CyclicLaurent
import Paper27.Splitting
import Mathlib.Data.ZMod.Basic

/-!
# Global section construction for the two ramification obstructions

The novel averaging and cancellation step is proved here on a general complex
module of global meromorphic bundle maps. Local Laurent coefficients are linear
maps, so the global finite sum has precisely the local coefficients proved in
`CyclicLaurent`. The finite group is the actual cyclic group `ZMod n`.

The analytic and geometric inputs are deliberately separated: a removable-pole
extension theorem gives a regular global section; a regular splitting tangent
to the fixed compact curve gives a foliation with that curve as compact leaf;
Bott's normal connection then gives degree zero. These are explicit, universally
quantified interfaces, not axioms or assumptions of either obstruction itself.
A geometric application must instantiate the section spaces, their forgetful
map, the normal evaluations, the compact-leaf witness, and the actual degree.
-/

noncomputable section

open scoped BigOperators
open Finset

namespace Paper27.Geometry.Obstruction

abbrev CyclicGroup (n : ℕ) := Multiplicative (ZMod n)

def generator (n : ℕ) : CyclicGroup n := Multiplicative.ofAdd (1 : ZMod n)

theorem generator_pow (n j : ℕ) :
    generator n ^ j = Multiplicative.ofAdd (j : ZMod n) := by
  apply Multiplicative.toAdd.injective
  simp [generator, toAdd_pow, nsmul_eq_mul]

@[simp] theorem generator_pow_order (n : ℕ) : generator n ^ n = 1 := by
  rw [generator_pow, ZMod.natCast_self]
  rfl

section Sections

variable {M H : Type*} [AddCommGroup M] [Module ℂ M]
  [AddCommGroup H] [Module ℂ H]

/-- A global finite cyclic average of a section. The summands are actual global
sections obtained from the representation, rather than unrelated local arrays. -/
def sectionAverage (n : ℕ) (ρ : CyclicGroup n →* M ≃ₗ[ℂ] M) (s : M) : M :=
  (n : ℂ)⁻¹ • ∑ j ∈ range n, ρ (generator n ^ j) s

/-- The global meromorphic section in equation (6). -/
def affineSection (a : ℂ) (s₂ s₃ : M) : M :=
  (a - 1)⁻¹ • (a • s₃ - s₂)

/-- Projection of the global average is still the identity section. -/
theorem sectionAverage_projection {n : ℕ} (hn : 0 < n)
    (ρ : CyclicGroup n →* M ≃ₗ[ℂ] M) (π : M →ₗ[ℂ] H) (identity : H)
    (hπ : ∀ g s, π (ρ g s) = π s) (s : M) (hs : π s = identity) :
    π (sectionAverage n ρ s) = identity := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold sectionAverage
  rw [map_smul]
  simp only [map_sum, hπ, hs, Finset.sum_const, Finset.card_range]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hnC, one_smul]

/-- Equation (6) preserves the global splitting identity. -/
theorem affineSection_projection (π : M →ₗ[ℂ] H) (identity : H)
    (a : ℂ) (ha : a ≠ 1) (s₂ s₃ : M)
    (h₂ : π s₂ = identity) (h₃ : π s₃ = identity) :
    π (affineSection a s₂ s₃) = identity := by
  simp only [affineSection, map_smul, map_sub, h₂, h₃]
  have heq : a • identity - identity = (a - 1) • identity := by
    rw [sub_smul, one_smul]
  rw [heq, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr ha), one_smul]

/-- The actual global average is fixed by the cyclic generator. -/
theorem sectionAverage_invariant {n : ℕ}
    (ρ : CyclicGroup n →* M ≃ₗ[ℂ] M) (s : M) :
    ρ (generator n) (sectionAverage n ρ s) = sectionAverage n ρ s := by
  unfold sectionAverage
  rw [map_smul, map_sum]
  congr 1
  have hshift : ∀ j : ℕ,
      ρ (generator n) (ρ (generator n ^ j) s) = ρ (generator n ^ (j + 1)) s := by
    intro j
    rw [pow_succ', map_mul, LinearEquiv.mul_apply]
  simp_rw [hshift]
  have hsum :
      (∑ j ∈ range n, ρ (generator n ^ (j + 1)) s) + ρ (generator n ^ 0) s =
      (∑ j ∈ range n, ρ (generator n ^ j) s) + ρ (generator n ^ n) s := by
    exact (Finset.sum_range_succ' (fun j => ρ (generator n ^ j) s) n).symm.trans
      (Finset.sum_range_succ (fun j => ρ (generator n ^ j) s) n)
  have hend : ρ (generator n ^ n) s = ρ (generator n ^ 0) s := by
    simp only [generator_pow_order, pow_zero]
  rw [hend] at hsum
  exact add_right_cancel hsum

/-- A holomorphic section submodule remains holomorphic after averaging. -/
theorem sectionAverage_mem {n : ℕ} (ρ : CyclicGroup n →* M ≃ₗ[ℂ] M)
    (holomorphic : Submodule ℂ M)
    (hρ : ∀ g s, s ∈ holomorphic → ρ g s ∈ holomorphic)
    (s : M) (hs : s ∈ holomorphic) : sectionAverage n ρ s ∈ holomorphic := by
  apply holomorphic.smul_mem
  apply holomorphic.sum_mem
  intro j hj
  exact hρ (generator n ^ j) s hs

variable {I : Type*}

/-- Generator equivariance alone proves the coefficient formula for every
summand in the global average. -/
theorem coefficient_of_power {n : ℕ} {ζ : ℂ}
    (ρ : CyclicGroup n →* M ≃ₗ[ℂ] M)
    (coeff : I → M →ₗ[ℂ] CyclicLaurent.Coefficients)
    (hcoeff : ∀ i s k, coeff i (ρ (generator n) s) k =
      ζ ^ (1 - k) * coeff i s k)
    (i : I) (s : M) (j : ℕ) (k : ℤ) :
    coeff i (ρ (generator n ^ j) s) k =
      ζ ^ ((1 - k) * (j : ℤ)) * coeff i s k := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', map_mul, LinearEquiv.mul_apply, hcoeff, ih]
    simp only [zpow_mul, zpow_natCast, pow_succ', mul_assoc]

/-- Applying a local coefficient map to the global average gives exactly the
finite coefficient average proved in `CyclicLaurent`. -/
theorem coefficient_sectionAverage {n : ℕ} {ζ : ℂ}
    (ρ : CyclicGroup n →* M ≃ₗ[ℂ] M)
    (coeff : I → M →ₗ[ℂ] CyclicLaurent.Coefficients)
    (hcoeff : ∀ i s k, coeff i (ρ (generator n) s) k =
      ζ ^ (1 - k) * coeff i s k)
    (i : I) (s : M) :
    coeff i (sectionAverage n ρ s) = CyclicLaurent.average n ζ (coeff i s) := by
  funext k
  simp only [sectionAverage, map_smul, map_sum, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, CyclicLaurent.average, CyclicLaurent.pushforward,
    coefficient_of_power ρ coeff hcoeff]

/-- Local coefficients commute with the actual global affine combination. -/
theorem coefficient_affineSection (coeff : I → M →ₗ[ℂ] CyclicLaurent.Coefficients)
    (i : I) (a : ℂ) (s₂ s₃ : M) :
    coeff i (affineSection a s₂ s₃) =
      CyclicLaurent.affineCombination a (coeff i s₂) (coeff i s₃) := by
  funext k
  simp [affineSection, CyclicLaurent.affineCombination, smul_eq_mul,
    div_eq_mul_inv, mul_comm]

/-- The global equation (6) section has no negative or constant Laurent
coefficient in any chart and at any point indexed by `I`. -/
theorem affine_average_all_nonpositive {n : ℕ} {ζ a : ℂ} (hn : 0 < n)
    (hζ : IsPrimitiveRoot ζ n) (ha0 : a ≠ 0)
    (ρ : CyclicGroup n →* M ≃ₗ[ℂ] M)
    (coeff : I → M →ₗ[ℂ] CyclicLaurent.Coefficients)
    (hcoeff : ∀ i s k, coeff i (ρ (generator n) s) k =
      ζ ^ (1 - k) * coeff i s k)
    (s₂ s₃ : M)
    (h₂ : ∀ i k, k ≤ 0 → coeff i s₂ k =
      if k = 1 - (n : ℤ) then -(1 / (n : ℂ)) else 0)
    (hpole : ∀ i, CyclicLaurent.PoleBound n (coeff i s₃))
    (hleading : ∀ i, coeff i s₃ (1 - (n : ℤ)) = -(1 / (a * (n : ℂ)))) :
    ∀ i, CyclicLaurent.TangentRegular
      (coeff i (affineSection a s₂ (sectionAverage n ρ s₃))) := by
  intro i
  rw [coefficient_affineSection, coefficient_sectionAverage ρ coeff hcoeff]
  exact CyclicLaurent.affine_average_tangent hn hζ ha0
    (coeff i s₂) (coeff i s₃) (hpole i) (h₂ i) (hleading i)

end Sections

section StandardGeometricInputs

variable {M H R Leaf I : Type*} [AddCommGroup M] [Module ℂ M]
  [AddCommGroup H] [Module ℂ H]

/-- Two standard geometric facts, phrased on actual regular sections `R` and
actual witnesses `Leaf` of a regular foliation with the fixed curve as compact
leaf. `normal` evaluates the component normal to the curve. The exact splitting
identity ensures that its image is a regular line subbundle. -/
structure RegularLeafFacts (forget : R → M) (π : M →ₗ[ℂ] H) (identity : H)
    (normal : I → M → ℂ) (degree : ℤ) : Prop where
  tangent_leaf : ∀ r : R, π (forget r) = identity →
    (∀ i, normal i (forget r) = 0) → Nonempty Leaf
  bott_degree_zero : Nonempty Leaf → degree = 0

/-- The standard Laurent removable-singularity theorem for global meromorphic
bundle maps: when all negative Laurent coefficients vanish in the atlas,
there is a global regular section with that meromorphic image. -/
structure RemovablePoleFacts (forget : R → M)
    (coeff : I → M →ₗ[ℂ] CyclicLaurent.Coefficients) : Prop where
  regular_extension : ∀ s : M, (∀ i k, k < 0 → coeff i s k = 0) →
    ∃ r : R, forget r = s

/-- Removability, tangency/integrability, and the Bott degree theorem are
composed only after constructing a particular global section. -/
theorem degree_zero_of_laurent_splitting (forget : R → M) (π : M →ₗ[ℂ] H)
    (identity : H) (coeff : I → M →ₗ[ℂ] CyclicLaurent.Coefficients) (degree : ℤ)
    (removable : RemovablePoleFacts forget coeff)
    (leafFacts : RegularLeafFacts (Leaf := Leaf) forget π identity
      (fun i s => coeff i s 0) degree)
    (s : M) (hprojection : π s = identity)
    (htangent : ∀ i, CyclicLaurent.TangentRegular (coeff i s)) : degree = 0 := by
  obtain ⟨r, hr⟩ := removable.regular_extension s
    (fun i k hk => htangent i k (le_of_lt hk))
  apply leafFacts.bott_degree_zero
  apply leafFacts.tangent_leaf r
  · simpa [hr] using hprojection
  · intro i
    simpa [hr] using htangent i 0 (by omega)

/-- The common-component obstruction after the source produces its two actual
meromorphic splittings. The finite global sum and affine combination are
constructed in the proof; their extension and leaf give the degree-zero
contradiction. No impossibility of three fibrations is an input. -/
theorem common_tangency_obstruction {n : ℕ} {ζ a : ℂ} (hn : 0 < n)
    (hζ : IsPrimitiveRoot ζ n) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (ρ : CyclicGroup n →* M ≃ₗ[ℂ] M)
    (π : M →ₗ[ℂ] H) (identity : H)
    (hπ : ∀ g s, π (ρ g s) = π s)
    (coeff : I → M →ₗ[ℂ] CyclicLaurent.Coefficients)
    (hcoeff : ∀ i s k, coeff i (ρ (generator n) s) k =
      ζ ^ (1 - k) * coeff i s k)
    (forget : R → M) (degree : ℤ)
    (removable : RemovablePoleFacts forget coeff)
    (leafFacts : RegularLeafFacts (Leaf := Leaf) forget π identity
      (fun i s => coeff i s 0) degree)
    (hnegative : degree < 0) (s₂ s₃ : M)
    (h₂projection : π s₂ = identity) (h₃projection : π s₃ = identity)
    (h₂ : ∀ i k, k ≤ 0 → coeff i s₂ k =
      if k = 1 - (n : ℤ) then -(1 / (n : ℂ)) else 0)
    (hpole : ∀ i, CyclicLaurent.PoleBound n (coeff i s₃))
    (hleading : ∀ i, coeff i s₃ (1 - (n : ℤ)) = -(1 / (a * (n : ℂ)))) : False := by
  let s := affineSection a s₂ (sectionAverage n ρ s₃)
  have hsπ : π s = identity := affineSection_projection π identity a ha1 s₂
    (sectionAverage n ρ s₃) h₂projection
    (sectionAverage_projection hn ρ π identity hπ s₃ h₃projection)
  have hscoeff : ∀ i, CyclicLaurent.TangentRegular (coeff i s) :=
    affine_average_all_nonpositive hn hζ ha0 ρ coeff hcoeff s₂ s₃ h₂ hpole hleading
  have hd : degree = 0 := degree_zero_of_laurent_splitting forget π identity coeff degree
    removable leafFacts s hsπ hscoeff
  omega

/-- At points of the fixed curve, invariance of the actual global average and
the nontrivial normal eigenvalue force its normal component to vanish. -/
theorem average_normal_zero {n : ℕ} {ζ : ℂ} (hζ : ζ ≠ 1)
    (ρ : CyclicGroup n →* M ≃ₗ[ℂ] M)
    (value : I → M →ₗ[ℂ] (ℂ × ℂ))
    (hvalue : ∀ i s, value i (ρ (generator n) s) =
      ((value i s).1, ζ * (value i s).2)) (s : M) :
    ∀ i, (value i (sectionAverage n ρ s)).2 = 0 := by
  intro i
  apply Paper27.Splitting.fixed_normal_component_zero hζ
  rw [← hvalue, sectionAverage_invariant]

/-- The disjoint case: average an actual holomorphic splitting, use its fixed
normal component to obtain a tangent compact leaf, and contradict negativity. -/
theorem disjoint_obstruction {n : ℕ} {ζ : ℂ} (hn : 0 < n) (hζ : ζ ≠ 1)
    (ρ : CyclicGroup n →* M ≃ₗ[ℂ] M)
    (π : M →ₗ[ℂ] H) (identity : H)
    (hπ : ∀ g s, π (ρ g s) = π s)
    (holomorphic : Submodule ℂ M)
    (hρ : ∀ g s, s ∈ holomorphic → ρ g s ∈ holomorphic)
    (value : I → M →ₗ[ℂ] (ℂ × ℂ))
    (hvalue : ∀ i s, value i (ρ (generator n) s) =
      ((value i s).1, ζ * (value i s).2))
    (forget : R → M)
    (holomorphic_lift : ∀ s : M, s ∈ holomorphic → ∃ r : R, forget r = s)
    (degree : ℤ)
    (leafFacts : RegularLeafFacts (Leaf := Leaf) forget π identity
      (fun i s => (value i s).2) degree)
    (hnegative : degree < 0) (s : M) (hs : s ∈ holomorphic)
    (hsπ : π s = identity) : False := by
  obtain ⟨r, hr⟩ := holomorphic_lift (sectionAverage n ρ s)
    (sectionAverage_mem ρ holomorphic hρ s hs)
  have hproj : π (forget r) = identity := by
    rw [hr]
    exact sectionAverage_projection hn ρ π identity hπ s hsπ
  have hnormal : ∀ i, (value i (forget r)).2 = 0 := by
    rw [hr]
    exact average_normal_zero hζ ρ value hvalue s
  have hleaf : Nonempty Leaf := leafFacts.tangent_leaf r
    hproj hnormal
  have hd : degree = 0 := leafFacts.bott_degree_zero hleaf
  omega

end StandardGeometricInputs

end Paper27.Geometry.Obstruction
