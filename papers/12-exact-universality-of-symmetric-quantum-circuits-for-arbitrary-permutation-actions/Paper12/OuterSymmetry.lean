import Paper12.OuterCircuit
import Paper12.OneHotSymmetry

noncomputable section
namespace Paper12
open Matrix Classical
variable {X W : Type*} [Fintype X] [Fintype W]

def outerDataLift (e : (X ⊕ W) ≃ (X ⊕ W)) :
    (X ⊕ (W ⊕ Fin 1)) ≃ (X ⊕ (W ⊕ Fin 1)) :=
  (Equiv.sumAssoc X W (Fin 1)).symm.trans
    ((e.sumCongr (Equiv.refl (Fin 1))).trans (Equiv.sumAssoc X W (Fin 1)))

def outerFinalLift (e : (X ⊕ W) ≃ (X ⊕ W)) :
    (X ⊕ (W ⊕ Fin 2)) ≃ (X ⊕ (W ⊕ Fin 2)) :=
  (Equiv.sumAssoc X W (Fin 2)).symm.trans
    ((e.sumCongr (Equiv.refl (Fin 2))).trans (Equiv.sumAssoc X W (Fin 2)))

theorem workspaceControls_map {J K : Type*} [Fintype J] [Fintype K]
    (e : (J ⊕ K) ≃ (J ⊕ K)) (γ : J ≃ J)
    (he : ∀ x, e (Sum.inl x) = Sum.inl (γ x)) :
    (workspaceControls J K).map e.toEmbedding = workspaceControls J K := by
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz, hzy⟩ := Finset.mem_map.mp hy
    obtain ⟨w, _, rfl⟩ := Finset.mem_map.mp hz
    obtain ⟨w', hw'⟩ := lift_inr_map e he w
    exact Finset.mem_map.mpr ⟨w', Finset.mem_univ _, hw'.symm.trans hzy⟩
  · intro hy
    obtain ⟨w, _, rfl⟩ := Finset.mem_map.mp hy
    obtain ⟨w', hw'⟩ := lift_inr_surj e he w
    exact Finset.mem_map.mpr ⟨Sum.inr w', Finset.mem_map.mpr ⟨w', Finset.mem_univ _, rfl⟩, hw'⟩

theorem outerDataLift_restrict (e : (X ⊕ W) ≃ (X ⊕ W)) (γ : X ≃ X)
    (he : ∀ x, e (Sum.inl x) = Sum.inl (γ x)) (x : X) :
    outerDataLift e (Sum.inl x) = Sum.inl (γ x) := by
  simp [outerDataLift, he]

theorem outerFinalLift_restrict (e : (X ⊕ W) ≃ (X ⊕ W)) (γ : X ≃ X)
    (he : ∀ x, e (Sum.inl x) = Sum.inl (γ x)) (x : X) :
    outerFinalLift e (Sum.inl x) = Sum.inl (γ x) := by
  simp [outerFinalLift, he]

theorem outerWire_intertwines (e : (X ⊕ W) ≃ (X ⊕ W))
    (x : (X ⊕ (W ⊕ Fin 1)) ⊕ Fin 1) :
    outerFinalLift e (outerWireEquiv x) =
      outerWireEquiv ((outerDataLift e).sumCongr (Equiv.refl (Fin 1)) x) := by
  cases x with
  | inl x =>
    cases x with
    | inl a => cases he : e (Sum.inl a) <;> simp [outerFinalLift, outerDataLift, outerWireEquiv, he]
    | inr w =>
      cases w with
      | inl w => cases he : e (Sum.inr w) <;> simp [outerFinalLift, outerDataLift, outerWireEquiv, he]
      | inr r => rfl
  | inr z => rfl

theorem obliviousCircuit_preserved (A : Circuit (X ⊕ W)) (p : ℝ)
    (γ : X ≃ X) (e : (X ⊕ W) ≃ (X ⊕ W))
    (he : ∀ x, e (Sum.inl x) = Sum.inl (γ x)) (hA : A.Preserved e) :
    (obliviousCircuit A p).Preserved (outerFinalLift e) := by
  let d := outerDataLift e
  have hT : (outerT A p).Preserved d := by
    apply Circuit.preserved_rewire (Equiv.sumAssoc X W (Fin 1))
      (Circuit.preserved_mul (Circuit.preserved_onLeft (Equiv.refl (Fin 1)) hA)
        (Circuit.preserved_onRight e (singleCircuit_preserved (Equiv.refl (Fin 1)) _ rfl)))
    intro x
    simp [d, outerDataLift]
  have hTF := Circuit.preserved_onLeft (Equiv.refl (Fin 1)) hT
  have hd : ∀ x, d (Sum.inl x) = Sum.inl (γ x) := outerDataLift_restrict e γ he
  have hF : (outerF (X := X) (W := W) p).Preserved (d.sumCongr (Equiv.refl (Fin 1))) :=
    equalityCircuit_preserved _ _ (flagEquality_map d _ _ (workspaceControls_map d γ hd))
  have hI : (outerIteration A p).Preserved (d.sumCongr (Equiv.refl (Fin 1))) :=
    Circuit.preserved_mul hTF (Circuit.preserved_mul hF
      (Circuit.preserved_mul (Circuit.preserved_adjoint hTF) hF))
  have hZ (θ : ℝ) :
      ((singleCircuit (ryGate (0 : Fin 1) θ)).onRight (J := X ⊕ (W ⊕ Fin 1))).Preserved
        (d.sumCongr (Equiv.refl (Fin 1))) :=
    Circuit.preserved_onRight d (singleCircuit_preserved (Equiv.refl (Fin 1)) _ rfl)
  have hphase : (singleCircuit (phaseGate (Sum.inl (Sum.inr (Sum.inr (0 : Fin 1))))
      ((-1 : ℂ) ^ ampK p) (sign_phase_unitary _))).Preserved
      (d.sumCongr (Equiv.refl (Fin 1))) := by
    apply singleCircuit_preserved
    rfl
  have hRaw : (outerRaw A p).Preserved (d.sumCongr (Equiv.refl (Fin 1))) :=
    Circuit.preserved_mul hphase (Circuit.preserved_mul (hZ (Real.pi / 2))
      (Circuit.preserved_mul (Circuit.preserved_power hI (ampK p))
        (Circuit.preserved_mul hTF (hZ (-Real.pi / 2)))))
  exact Circuit.preserved_rewire outerWireEquiv hRaw (outerWire_intertwines e)

theorem obliviousCircuit_symmetric {Γ : Subgroup (X ≃ X)} {A : Circuit (X ⊕ W)}
    (hsym : Symmetric Γ A) (p : ℝ) : Nonempty (Symmetric Γ (obliviousCircuit A p)) := by
  refine ⟨⟨fun γ => outerFinalLift (hsym.lift γ), ?_, ?_⟩⟩
  · intro γ x
    exact outerFinalLift_restrict _ γ.val (hsym.restrict γ) x
  · intro γ L hL
    exact obliviousCircuit_preserved A p γ.val (hsym.lift γ) (hsym.restrict γ)
      (hsym.preserves γ) L hL
end Paper12
