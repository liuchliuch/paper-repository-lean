import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# The finite-index subgroup step in Lemma 3.4

The groups here are arbitrary, so this applies to the two fundamental groups
in the source. This file does not construct their covering curves or a
holomorphic lift of the resulting product covering.
-/
namespace Paper27.ProductCoverGroup

variable {G₁ G₂ : Type*} [Group G₁] [Group G₂]

/-- `H₁ = {g | (g,1) ∈ Γ}` in the notation of the paper. -/
def firstFactor (Γ : Subgroup (G₁ × G₂)) : Subgroup G₁ :=
  Γ.comap (MonoidHom.inl G₁ G₂)

/-- `H₂ = {g | (1,g) ∈ Γ}` in the notation of the paper. -/
def secondFactor (Γ : Subgroup (G₁ × G₂)) : Subgroup G₂ :=
  Γ.comap (MonoidHom.inr G₁ G₂)

/-- The product of the two axis subgroups really is contained in Γ. -/
theorem product_le (Γ : Subgroup (G₁ × G₂)) :
    (firstFactor Γ).prod (secondFactor Γ) ≤ Γ := by
  intro g hg
  have h₁ : (g.1, (1 : G₂)) ∈ Γ := hg.1
  have h₂ : ((1 : G₁), g.2) ∈ Γ := hg.2
  simpa using Γ.mul_mem h₁ h₂

/-- Pulling back a finite-index subgroup along any homomorphism preserves
finite index; no regularity/normality assumption is used. -/
theorem finite_index_comap {G K : Type*} [Group G] [Group K]
    (Γ : Subgroup G) [Γ.FiniteIndex] (f : K →* G) : (Γ.comap f).FiniteIndex := by
  constructor
  intro hz
  apply Subgroup.FiniteIndex.index_ne_zero (H := Γ)
  rw [Subgroup.index_comap] at hz
  exact Subgroup.index_eq_zero_of_relIndex_eq_zero hz

/-- Both `Hᵢ` in the proof have finite index, also for a nonnormal Γ. -/
theorem axis_subgroups_finite_index (Γ : Subgroup (G₁ × G₂)) [Γ.FiniteIndex] :
    (firstFactor Γ).FiniteIndex ∧ (secondFactor Γ).FiniteIndex :=
  ⟨finite_index_comap Γ _, finite_index_comap Γ _⟩

end Paper27.ProductCoverGroup
