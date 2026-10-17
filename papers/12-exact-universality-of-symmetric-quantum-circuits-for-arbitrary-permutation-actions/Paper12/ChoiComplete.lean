import Paper12.ChoiCircuit

noncomputable section
namespace Paper12
open Matrix Classical
variable {X T : Type*} [Fintype X] [Fintype T]

theorem choiBell_preserved (γ : X ≃ X) (τ : T ≃ T) :
    (choiBell (X := X) (T := T)).Preserved
      (γ.sumCongr ((γ.sumCongr γ).sumCongr τ)) := by
  apply Circuit.preserved_rewire bellWires
    (Circuit.preserved_onLeft (γ.sumCongr τ) (bellPreparation_preserved γ))
  intro z
  rcases z with (d|a)|(b|t) <;> rfl

theorem choiSwap_preserved (γ : X ≃ X) (τ : T ≃ T) :
    (choiSwap (X := X) (T := T)).Preserved
      (γ.sumCongr ((γ.sumCongr γ).sumCongr τ)) := by
  apply Circuit.preserved_rewire swapWires
    (Circuit.preserved_onLeft (γ.sumCongr τ) (pairSwap_preserved γ))
  intro z
  rcases z with (d|b)|(a|t) <;> rfl

theorem choiBlock_preserved (CJ : Circuit ((X ⊕ X) ⊕ T)) (γ : X ≃ X)
    (e : ((X ⊕ X) ⊕ T) ≃ ((X ⊕ X) ⊕ T))
    (hr : ∀ x, e (Sum.inl x) = Sum.inl ((γ.sumCongr γ) x)) (hCJ : CJ.Preserved e) :
    (choiBlock CJ).Preserved (γ.sumCongr e) := by
  have he := lift_decompose (γ.sumCongr γ) e hr
  rw [he] at hCJ ⊢
  exact Circuit.preserved_mul (choiSwap_preserved γ _)
    (Circuit.preserved_mul (Circuit.preserved_adjoint (choiBell_preserved γ _))
      (Circuit.preserved_onRight γ hCJ))

theorem choiBlock_symmetric {Γ : Subgroup (X ≃ X)} (CJ : Circuit ((X ⊕ X) ⊕ T))
    (hs : ∀ γ : Γ, ∃ e : ((X ⊕ X) ⊕ T) ≃ ((X ⊕ X) ⊕ T),
      (∀ x, e (Sum.inl x) = Sum.inl ((γ.val.sumCongr γ.val) x)) ∧ CJ.Preserved e) :
    Nonempty (Symmetric Γ (choiBlock CJ)) := by
  choose e hr hp using hs
  refine ⟨⟨fun γ => γ.val.sumCongr (e γ), (fun _ _ => rfl), ?_⟩⟩
  intro γ
  exact choiBlock_preserved CJ γ.val (e γ) (hr γ) (hp γ)

theorem choiProbability_pos : 0 < choiProbability X := by
  unfold choiProbability
  positivity

theorem choiBlock_blockEncodes (CJ : Circuit ((X ⊕ X) ⊕ T)) (U : Op X)
    (hprep : applyOp CJ.unitary (zeroKet _) = embedZero (W := T) (choiVec U)) :
    BlockEncodes (choiBlock CJ).unitary (choiProbability X) U := by
  unfold BlockEncodes
  rw [choiBlock_encoding CJ U hprep]
  have hr : Real.sqrt (choiProbability X) = ((2 : ℝ) ^ Fintype.card X)⁻¹ :=
    Real.sqrt_sq (by positivity)
  rw [hr]
  simp only [_root_.Complex.ofReal_inv, _root_.Complex.ofReal_pow, _root_.Complex.ofReal_ofNat]

/-- Appendix A: the actual SWAP·Bell†·CJ circuit, followed by the same
exact elementary amplifier. The existing Choi lift is retained on all of A,B,T. -/
theorem appendix_choi_construction {Γ : Subgroup (X ≃ X)}
    (CJ : Circuit ((X ⊕ X) ⊕ T)) (U : Op X) (hU : Uᴴ * U = 1)
    (hprep : applyOp CJ.unitary (zeroKet _) = embedZero (W := T) (choiVec U))
    (hs : ∀ γ : Γ, ∃ e : ((X ⊕ X) ⊕ T) ≃ ((X ⊕ X) ⊕ T),
      (∀ x, e (Sum.inl x) = Sum.inl ((γ.val.sumCongr γ.val) x)) ∧ CJ.Preserved e) :
    zeroBlock (choiBlock CJ).unitary = ((2 : ℂ) ^ Fintype.card X)⁻¹ • U ∧
    Nonempty (Symmetric Γ (choiBlock CJ)) ∧
    ∃ C : Circuit (X ⊕ (((X ⊕ X) ⊕ T) ⊕ Fin 2)),
      CleanImplements C U ∧ Nonempty (Symmetric Γ C) ∧
      Fintype.card (((X ⊕ X) ⊕ T) ⊕ Fin 2) = 2 * Fintype.card X + Fintype.card T + 2 ∧
      C.size ≤ 32 * (CJ.size + 5 * Fintype.card X + 1) * (ampK (choiProbability X) + 1) ∧
      ∀ (γ : X ≃ X) (e : ((X ⊕ X) ⊕ T) ≃ ((X ⊕ X) ⊕ T)),
        (∀ x, e (Sum.inl x) = Sum.inl ((γ.sumCongr γ) x)) → CJ.Preserved e →
        C.Preserved (outerFinalLift (γ.sumCongr e)) := by
  have hb := choiBlock_blockEncodes CJ U hprep
  obtain ⟨hA⟩ := choiBlock_symmetric CJ hs
  refine ⟨choiBlock_encoding CJ U hprep, ⟨hA⟩,
    obliviousCircuit (choiBlock CJ) (choiProbability X),
    obliviousCircuit_clean _ U _ hU choiProbability_pos hb,
    obliviousCircuit_symmetric hA _, ?_, ?_, ?_⟩
  · simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  · simpa only [choiBlock_size] using obliviousCircuit_size (choiBlock CJ) (choiProbability X)
  · intro γ e hr hCJ
    apply obliviousCircuit_preserved
    · intro x; rfl
    · exact choiBlock_preserved CJ γ e hr hCJ
end Paper12
