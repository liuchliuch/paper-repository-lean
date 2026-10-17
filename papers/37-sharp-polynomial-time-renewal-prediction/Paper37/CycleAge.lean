import Paper37.EquilibriumCycle
import Paper37.KnownSupportLaw

/-! The exact generic age marginal of the one shared classical equilibrium
cycle interface, with no additional external dependency. -/
noncomputable section
namespace Paper37.CycleAge
open scoped BigOperators
open Paper37.Compression Paper37.Compression.Distribution
open Paper37.KnownSupportRisk Paper37.EquilibriumCycle Paper37.HazardChain

def toFinite {α : Type*} [Fintype α] (p : Distribution α) : Paper37.LowerBound.FiniteLaw α where
  mass := p.mass
  nonneg := p.nonneg
  total := p.total

abbrev CyclePhase (B : ℕ) := Phase (fun c : Fin B => c.val)

def phaseAge {B : ℕ} (z : CyclePhase B) : Fin B := ⟨z.2.val,by have h1 : z.2.val < z.1.val+1 := z.2.isLt;have h2 := z.1.isLt;omega⟩

lemma phase_mean {B : ℕ} (p : Distribution (Fin B)) :
    gapMean (toFinite p) (fun c : Fin B => c.val) = finiteMean p := rfl

lemma sum_phase_indicator (c a : ℕ) (w : ℝ) :
    (∑ t : Fin (c+1), if t.val=a then w else 0) = if a ≤ c then w else 0 := by
  by_cases ha : a ≤ c
  · let j : Fin (c+1) := ⟨a,by omega⟩
    have he : ∀ t : Fin (c+1), (t.val=a) ↔ t=j := by
      intro t
      exact ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
    simp_rw [he]
    simp [ha]
  · have he : ∀ t : Fin (c+1), t.val≠a := by intro t;have := t.isLt;omega
    simp [he,ha]

/-- Every finite positive-gap law has stationary age mass survival(a)/mean. -/
theorem phaseAge_mass {B : ℕ} (p : Distribution (Fin B)) (a : Fin B) :
    (∑ z : CyclePhase B, if phaseAge z=a then
      (phaseLaw (toFinite p) (fun c : Fin B => c.val)).mass z else 0) = ageLaw p a := by
  have he : ∀ z : CyclePhase B, (phaseAge z=a) ↔ z.2.val=a.val := by
    intro z
    exact Fin.ext_iff
  simp_rw [he]
  rw [Fintype.sum_sigma]
  change (∑ c : Fin B, ∑ t : Fin (c.val+1), if t.val=a.val then p c/finiteMean p else 0) = _
  simp_rw [sum_phase_indicator]
  change (∑ c : Fin B, if a.val ≤ c.val then p c/finiteMean p else 0) = survival p a.val/finiteMean p
  rw [survival_eq_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c hc
  split_ifs <;> simp

/-- Generic phase expectation reduces exactly to the actual equilibrium age
law. This is the age projection used by H.1, derived from the shared interface. -/
theorem phaseAge_expectation {B : ℕ} (p : Distribution (Fin B)) (f : Fin B → ℝ) :
    (∑ z : CyclePhase B, (phaseLaw (toFinite p) (fun c : Fin B => c.val)).mass z*f (phaseAge z)) =
      ∑ a, ageLaw p a*f a := by
  symm
  simp_rw [← phaseAge_mass,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  simp_rw [ite_mul,zero_mul]
  simp

lemma vector_realizes (μ : Paper37.Renewal.Law) (B : ℕ)
    (hS : ∀ d, B ≤ d → μ.mass d=0) (t : ℕ) :
    μ.mass t = ∑ j : Fin B, if j.val=t then (toFinite (Paper37.KnownSupportLaw.vector μ B hS)).mass j else 0 := by
  by_cases ht : t < B
  · let a : Fin B := ⟨t,ht⟩
    have he : ∀ j : Fin B, (j.val=t) ↔ j=a := by intro j; exact ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
    simp_rw [he]
    simp [toFinite,Paper37.KnownSupportLaw.vector,a]
  · have he : ∀ j : Fin B, j.val≠t := by intro j;have := j.isLt;omega
    simp [he,hS t (by omega)]

end Paper37.CycleAge
