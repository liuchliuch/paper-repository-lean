import Paper12.Incidence

noncomputable section
namespace Paper12
open Classical
variable {X Q : Type*} [Fintype X] [Fintype Q]

theorem cnot_map (γ : X ≃ X) (τ : Q ≃ Q) (q : Q) (x : X) :
    (cnotThreshold q x).map (γ.sumCongr τ) = cnotThreshold (τ q) (γ x) := by
  apply Threshold.ext_data
  · rfl
  · simp [Threshold.map, cnotThreshold]
  · rfl

theorem incidenceLayer_map (w : Q → PWord X) (s : PSym)
    (γ : X ≃ X) (τ : Q ≃ Q) (hw : ∀ q x, w (τ q) (γ x) = w q x) :
    Layer.map (γ.sumCongr τ) (incidenceLayer w s) = incidenceLayer w s := by
  apply Layer.ext
  ext g
  constructor
  · intro hg
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hg
    obtain ⟨⟨q, x⟩, hqx, rfl⟩ := Finset.mem_map.mp ha
    change Gate.thr ((cnotThreshold q x).map (γ.sumCongr τ)) ∈ _
    rw [cnot_map]
    refine Finset.mem_map.mpr ⟨(τ q, γ x), ?_, rfl⟩
    simpa only [incidenceSet, Finset.mem_filter, Finset.mem_univ, true_and, hw] using hqx
  · intro hg
    obtain ⟨⟨q, x⟩, hqx, rfl⟩ := Finset.mem_map.mp hg
    refine Finset.mem_map.mpr ⟨Gate.thr (cnotThreshold (τ.symm q) (γ.symm x)), ?_, ?_⟩
    · refine Finset.mem_map.mpr ⟨(τ.symm q, γ.symm x), ?_, rfl⟩
      have hh := hw (τ.symm q) (γ.symm x)
      simp only [Equiv.apply_symm_apply] at hh
      simpa only [incidenceSet, Finset.mem_filter, Finset.mem_univ, true_and, ← hh] using hqx
    · change Gate.thr ((cnotThreshold (τ.symm q) (γ.symm x)).map (γ.sumCongr τ)) = _
      rw [cnot_map, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      rfl

theorem incidenceCircuit_preserved (w : Q → PWord X) (s : PSym)
    (γ : X ≃ X) (τ : Q ≃ Q) (hw : ∀ q x, w (τ q) (γ x) = w q x) :
    (incidenceCircuit w s).Preserved (γ.sumCongr τ) := by
  intro L hL
  simp only [incidenceCircuit, List.mem_singleton] at hL
  subst L
  exact incidenceLayer_map w s γ τ hw
end Paper12
