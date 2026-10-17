import Paper13
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Paper13Contracts
open Paper13 Matrix
open scoped Kronecker BigOperators

theorem paper_lemma_3 : IsOrthProj localP ∧
    Module.finrank ℂ (LinearMap.range (Matrix.toLin' localP)) = 2 ∧
    comm localP (Xv (0 : Fin 7) + Xv 1 + Xv 2 + Xv 3 + Xv 4 + Xv 5 + Xv 6) = 0 ∧
    Hzz_H * localP = 0 ∧ localP * Hzz_H = 0 ∧ comm localP Hz_H = 0 ∧
    Matrix.reindexAlgEquiv ℂ ℂ portBasis.symm localP = (1 : Op1) ⊗ₖ localP0 :=
  ⟨localP_isOrthProj, localP_finrank_two, lemma3_commutator.1, Hzz_H_mul_localP,
    localP_mul_Hzz_H, lemma3_commutator.2.2.2, localP_tensor_factor⟩

theorem paper_lemma_4 (k : ℕ) (hk : 7 ≤ k) : (Gk k).Connected ∧
    Fintype.card (GkVert k) = 7*k ∧ (Gk k).edgeFinset.card = 9*k-1 ∧
    (Gk k).maxDegree = 5 ∧ (∀ φ : Gk k ≃g Gk k, φ = 1) ∧
    ¬ Nonempty ((Gk k).Coloring (Fin 2)) ∧ ¬ (Gk k).IsRegularOfDegree 2 := lemma4 k hk

theorem port_coupling {α : Type*} [Fintype α] [DecidableEq α] (B : Matrix α α ℂ) :
    (localP ⊗ₖ (1 : Matrix α α ℂ)) * (Zv (4 : Fin 7) ⊗ₖ B) =
      (Zv (4 : Fin 7) ⊗ₖ B) * (localP ⊗ₖ (1 : Matrix α α ℂ)) := localP_comm_Z_port B

theorem appendix_identity : (64 : ℂ) • localP =
    1 + printedCertificate + piSwap 1 6 * piSwap 3 5 := corrected_certificate_identity

theorem appendix_counterexample :
    (comm printedCertificate Hzz_H).mulVec (basisKet certX) = (8 : ℂ) • basisKet certY ∧
    comm printedCertificate Hzz_H ≠ 0 :=
  ⟨printedCertificate_commutator_on_x, printedCertificate_not_commute⟩

theorem parity_split {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R F : Matrix ι ι ℂ) (hR : R*R=R) (hF : F*F=1)
    (hcomm : R*F=F*R) (htrace : Matrix.trace (R*F)=0) :
    2 * Module.finrank ℂ (LinearMap.range (Matrix.toLin' (parityRefinement R F 1))) =
      Module.finrank ℂ (LinearMap.range (Matrix.toLin' R)) ∧
    2 * Module.finrank ℂ (LinearMap.range (Matrix.toLin' (parityRefinement R F (-1)))) =
      Module.finrank ℂ (LinearMap.range (Matrix.toLin' R)) := parity_half_rank R F hR hF hcomm htrace

theorem irreducible_block_bound {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]
    (L : Set (Matrix ι ι ℂ)) (W : Submodule ℂ (ι → ℂ)) (hW : IrreducibleOn L W)
    (R : β → Matrix ι ι ℂ) (hcomm : ∀ b A, A ∈ L → R b*A=A*R b) (hsum : ∑ b, R b = 1) :
    ∃ b, Module.finrank ℂ W ≤ Module.finrank ℂ (LinearMap.range (Matrix.toLin' (R b))) :=
  irreducible_le_one_block L W hW R hcomm hsum

theorem skew_dimension (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Module.finrank ℝ (skewAdjoint (Matrix ι ι ℂ)) = (Fintype.card ι)^2 := skewAdjoint_finrank ι

theorem block_dimension_bound {ι β : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] [Fintype β] (L : Submodule ℝ (Matrix ι ι ℂ)) (R : β → Matrix ι ι ℂ)
    (hsum : ∑ b, R b = 1) (hskew : ∀ A ∈ L, Aᴴ = -A)
    (hcomm : ∀ A ∈ L, ∀ b, A*R b=R b*A) (htrace : ∀ A ∈ L, Matrix.trace A=0) :
    Module.finrank ℝ L ≤ (∑ b, (Module.finrank ℂ (LinearMap.range (Matrix.toLin' (R b))))^2)-1 :=
  traceless_skew_block_bound L R hsum hskew hcomm htrace

theorem local_initial_state : localP.mulVec (fun _ => (1 : ℂ)) = 0 := localP_uniform

theorem general_ratio_divergence (r d : ℕ) (hr : 0 < r) (hrd : r < d) :
    ∀ M : ℚ, ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      M ≤ ((d^2 : ℚ)/((r^2+(d-r)^2 : ℕ) : ℚ))^k - 4/((r^2+(d-r)^2 : ℕ) : ℚ)^k :=
  amplification_ratio_diverges r d hr hrd

theorem tensor_projector_rank {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] (P : κ → Matrix ι ι ℂ) (hP : ∀ v, P v*P v=P v) :
    Module.finrank ℂ (LinearMap.range (Matrix.toLin' (tensorMatrix P))) =
      ∏ v, Module.finrank ℂ (LinearMap.range (Matrix.toLin' (P v))) := tensorMatrix_finrank P hP

theorem gadget_joint_blocks (k : ℕ) :
    (∑ s, gadgetBlock k s) = 1 ∧
    (∀ s t, s ≠ t → gadgetBlock k s * gadgetBlock k t = 0) ∧
    (∑ s, (Module.finrank ℂ (LinearMap.range (Matrix.toLin' (gadgetBlock k s))))^2) = 15880^k ∧
    (∀ s, Module.finrank ℂ (LinearMap.range (Matrix.toLin' (gadgetBlock k s))) ≤ 126^k) :=
  ⟨gadgetBlock_complete k, gadgetBlock_orthogonal k, gadgetBlock_sum_rank_sq k, gadgetBlock_rank_le k⟩

theorem paper_theorem_1 (k : ℕ) (hk : 7 ≤ k) :
    (Gk k).Connected ∧ Fintype.card (GkVert k) = 7*k ∧
    (Gk k).edgeFinset.card = 9*k-1 ∧ (Gk k).maxDegree = 5 ∧
    (∀ φ : Gk k ≃g Gk k, φ = 1) ∧ Theorem1AlgebraClaim k ∧
    ((Module.finrank ℝ (graphNat (GkOrdinal k)) : ℚ) /
      Module.finrank ℝ (graphStd (GkOrdinal k))) ≥
      (2048/1985 : ℚ)^k - 4/(15880 : ℚ)^k := theorem1_actual k hk

theorem paper_theorem_1_divergence : Filter.Tendsto
    (fun k : ℕ => (Module.finrank ℝ (graphNat (GkOrdinal k)) : ℚ) /
      Module.finrank ℝ (graphStd (GkOrdinal k))) Filter.atTop Filter.atTop := theorem1_actual_divergence

theorem paper_corollary_2 (k : ℕ) (hk : 7 ≤ k) : Corollary2Claim k := corollary2_actual k hk

theorem paper_corollary_2_limit : Filter.Tendsto
    (fun k : ℕ => (invariantDeficit (GkOrdinal k) : ℝ) / (2 : ℝ)^(7*k-1))
      Filter.atTop (nhds 1) := corollary2_actual_limit

theorem paper_prop_5 {h k : ℕ} (hk : 1 ≤ k) (K : PortedGadget h)
    (B : SimpleGraph (Fin k)) : Proposition5Claim K B := proposition5_actual hk K B

theorem paper_prop_5_divergence {h : ℕ} (K : PortedGadget h) (B : (k : ℕ) → SimpleGraph (Fin k))
    (hgraphs : ∀ᶠ k : ℕ in Filter.atTop,
      let Γ := portedAssemblyOrdinal K (B k)
      Γ.Connected ∧ ¬Nonempty (Γ.Coloring (Fin 2)) ∧
        (∀ φ : Γ ≃g Γ, φ=SimpleGraph.Iso.refl) ∧ ¬Γ.IsRegularOfDegree 2) :
    Filter.Tendsto (fun k : ℕ =>
      (Module.finrank ℝ (graphNat (portedAssemblyOrdinal K (B k))) : ℚ) /
        Module.finrank ℝ (graphStd (portedAssemblyOrdinal K (B k)))) Filter.atTop Filter.atTop := proposition5_actual_divergence K B hgraphs

theorem natural_classification {n : ℕ} (hn : 2 ≤ n) (G : SimpleGraph (Fin n))
    (hc : G.Connected) (hnb : ¬Nonempty (G.Coloring (Fin 2))) (hncy : ¬G.IsRegularOfDegree 2) :
    graphMa G=scSpace n ∧ Module.finrank ℝ (graphMa G)=2^(2*n-1)-2 := ⟨graphMa_eq_scSpace_of_nonbip hn G hc hnb hncy,graphMa_dimension_of_nonbip hn G hc hnb hncy⟩

theorem natural_inclusion {n : ℕ} (G : SimpleGraph (Fin n)) : graphStd G ≤ graphNat G := graphStd_le_nat G

theorem positive_parity_dimension (n : ℕ) (hn : 0 < n) : Module.finrank ℂ (plusSpace n)=2^(n-1) := plusSpace_finrank n hn

theorem assembly_initial_state (k : ℕ) (hk : 1 ≤ k) :
    (initialSectorProjector k).mulVec (fun _ => (1 : ℂ))=(fun _ => 1) ∧
    InvariantUnder (graphStd (GkOrdinal k) : Set (Op (k*7)))
      (LinearMap.range (Matrix.toLin' (initialSectorProjector k))) ∧
    Module.finrank ℂ (LinearMap.range (Matrix.toLin' (initialSectorProjector k)))=126^k/2 := ⟨initialSector_fixes_uniform k,initialSector_invariant k,initialSector_rank k hk⟩

theorem local_controls_nonpreservation :
    (∀ v : Fin 7, v≠4 → ¬InvariantUnder {iMul (Xv v)} (LinearMap.range (Matrix.toLin' localP))) ∧
    (∀ u v : Fin 7, H.Adj u v → ¬InvariantUnder {iMul (ZZ u v)} (LinearMap.range (Matrix.toLin' localP))) := ⟨local_sector_not_invariant_X,local_sector_not_invariant_ZZ⟩
end Paper13Contracts


