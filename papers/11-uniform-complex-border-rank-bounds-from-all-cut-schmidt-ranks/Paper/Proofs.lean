import Paper.Statements
import UniformBorderRank

/-! # Proofs of the paper statements

Each public statement is discharged by its concrete implementation.
-/

namespace UniformBorderRank.Paper

theorem lemma_3_1 : PaperStatements.lemma_3_1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    exact Fsum_eq_F q hq
  · intro a b ha hb
    exact F_add_le a b ha hb
  · intro q hq
    exact F_lt_succ hq

theorem lemma_2_3 : PaperStatements.lemma_2_3 := by
  intro r hr q b hcomm hnc
  exact centralizer_bound hr q b hcomm hnc

theorem product_rank_le_one : PaperStatements.product_rank_le_one := by
  intro N d T h
  exact cpRankLe_one_of_isProduct h

theorem border_of_cp : PaperStatements.border_of_cp := by
  intro N d T b h
  exact borderRankLe_of_cpRankLe h

theorem finite_difference_eval_count : PaperStatements.finite_difference_eval_count := by
  intro k
  exact ⟨evalPoints_eq k, coeffRankBound_eq k⟩

theorem all_cut_hypothesis : PaperStatements.all_cut_hypothesis := by
  intro N d T D
  rfl

theorem lemma_2_1 : PaperStatements.lemma_2_1 := by
  intro N d E r hr hpos
  exact faithful_product_contraction_proved E r ⟨hr, hpos⟩

theorem lemma_2_3_full : PaperStatements.lemma_2_3_full := by
  intro ι _ r hr A hcomm
  exact centralizer_algebras hr A hcomm

theorem product_curve_coefficient : PaperStatements.product_curve_coefficient := by
  intro N hN d v w k
  exact borderRankLe_prodCurveCoeff d hN v w k

theorem theorem_1_1_rank_one : PaperStatements.theorem_1_1_rank_one := by
  intro N hN d T hT hr
  exact isProduct_of_maxSchmidtRank_one hN T hT hr

theorem proposition_3_2 : PaperStatements.proposition_3_2 := by
  intro N hN d A _ _ _ hA phi ell
  haveI : Nontrivial A := Module.nontrivial_of_finrank_pos hA
  exact borderRankLe_algebra_product hN (fun i x => phi i (Pi.single x 1)) ell

theorem theorem_1_1 : PaperStatements.theorem_1_1 := by
  intro N hN d T hT
  exact uniform_border_rank_bound d hN T hT

theorem all_cut_uniform_bound : PaperStatements.all_cut_uniform_bound := by
  intro N D hN hD d T hT hcut
  exact borderRankLe_of_allCutLe d hN hD T hT hcut

theorem corollary_1_2 : PaperStatements.corollary_1_2 := by
  intro N D hN hD d T hT hcut
  exact allCut_mem_projectiveSecant d hN hD T hT hcut

theorem proposition_2_2 : PaperStatements.proposition_2_2 := by
  intro N hN d T hT hr
  exact exists_original_anchored_presentation d hN T hT hr

theorem fixed_weight_examples : PaperStatements.fixed_weight_examples := by
  intro N hN d e₀ e₁
  refine ⟨isProduct_fixedWeightTensor_zero d e₀ e₁, ?_⟩
  intro k
  exact ⟨borderRankLe_fixedWeightTensor d hN e₀ e₁ k,
    schmidtRank_fixedWeightTensor_le d hN e₀ e₁ k⟩

theorem disjoint_block_examples : PaperStatements.disjoint_block_examples := by
  intro N B _ _ d block T
  refine ⟨schmidtRank_blockProduct d block T, ?_⟩
  intro hN hT E C hC
  exact ⟨two_pow_entangled_blocks_le_maxSchmidtRank d block T hN hT E C hC,
    entangled_blocks_card_le_log2 d block T hN hT E C hC⟩

theorem full_derivative_dimension : PaperStatements.full_derivative_dimension := by
  refine ⟨?_, ?_, ?_⟩
  · intro N d T
    exact finrank_fullDerivativeSpace_tensorPolynomial d T
  · intro N hN d T hT
    exact finrank_fullDerivativeSpace_le d hN T hT
  · intro N d T hT hprod
    exact finrank_fullDerivativeSpace_of_isProduct d T hT hprod

theorem numerical_growth : PaperStatements.numerical_growth := by
  refine ⟨fun _ hq => F_le_mul_four_pow hq,
    fun _ hD => Bhat_le_exp hD, fun D => Real.log (Bhat D : ℝ), log_Bhat_isBigO, ?_⟩
  intro D
  exact (Real.exp_log (by exact_mod_cast Bhat_pos D)).symm

end UniformBorderRank.Paper
