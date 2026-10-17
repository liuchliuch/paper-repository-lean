import Paper08.FactorModel
import Paper08.Connected

/-! # The actual factor-intersection graph and its occurrence degree bound -/
noncomputable section
open scoped BigOperators
namespace Paper08.Interaction

def incident {n r m : ℕ} (E : FactorFamily n r m) (v : Fin n) : Finset (Fin m) :=
  Finset.univ.filter fun e => v ∈ (E e).scope

def graph {n r m : ℕ} (E : FactorFamily n r m) : SimpleGraph (Fin m) where
  Adj e f := e ≠ f ∧ ∃ v, v ∈ (E e).scope ∧ v ∈ (E f).scope
  symm := by
    rintro e f ⟨hne, v, he, hf⟩
    exact ⟨hne.symm, v, hf, he⟩
  loopless := by
    intro e h
    exact h.1 rfl

instance {n r m : ℕ} (E : FactorFamily n r m) : DecidableRel (graph E).Adj :=
  Classical.decRel _

theorem neighborFinset_eq {n r m : ℕ} (E : FactorFamily n r m) (e : Fin m) :
    (graph E).neighborFinset e =
      (E e).scope.biUnion (fun v => (incident E v).erase e) := by
  classical
  ext f
  simp only [SimpleGraph.mem_neighborFinset, graph, Finset.mem_biUnion,
    Finset.mem_erase, incident, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hne, v, he, hf⟩
    exact ⟨v, he, hne.symm, hf⟩
  · rintro ⟨v, he, hne, hf⟩
    exact ⟨hne.symm, v, he, hf⟩

/-- Equation (2.7) follows by charging every neighboring occurrence to one
variable of the current scope, and excluding the current occurrence itself. -/
theorem degree_le {n r m c : ℕ} (E : FactorFamily n r m)
    (hc : FamilyBoundedOccurrence E c) (e : Fin m) :
    (graph E).degree e ≤ r * (c - 1) := by
  classical
  rw [SimpleGraph.degree, neighborFinset_eq]
  calc
    ((E e).scope.biUnion (fun v => (incident E v).erase e)).card ≤
        ∑ v ∈ (E e).scope, ((incident E v).erase e).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ (E e).scope, (c - 1) := by
      apply Finset.sum_le_sum
      intro v hv
      have hm : e ∈ incident E v := by simp [incident, hv]
      have hcard := hc v
      change (incident E v).card ≤ c at hcard
      rw [Finset.card_erase_of_mem hm]
      omega
    _ = (E e).scope.card * (c - 1) := by simp
    _ ≤ r * (c - 1) := Nat.mul_le_mul_right _ (E e).card_le

/-- Connected supports in the actual factor model satisfy the paper's count. -/
theorem connected_support_count {n r m c : ℕ} (E : FactorFamily n r m)
    (hc : FamilyBoundedOccurrence E c) (a : ℕ) :
    (Enumeration.connectedSets (graph E) a).card ≤
      m * (4 * max 1 (r * (c - 1))) ^ (a - 1) := by
  simpa only [Fintype.card_fin] using
    Enumeration.card_connectedSets_le (graph E) (r * (c - 1)) a (degree_le E hc)

theorem local_coefficient_count {n r m c : ℕ} (E : FactorFamily n r m)
    (hc : FamilyBoundedOccurrence E c) (s : ℕ) :
    (Connected.localCoefficients (graph E) s).card ≤
      s * m * Connected.A₀ (r * (c - 1)) ^ s := by
  simpa only [Fintype.card_fin] using
    Connected.local_coeff_count (graph E) (r * (c - 1)) s (degree_le E hc)

end Paper08.Interaction
