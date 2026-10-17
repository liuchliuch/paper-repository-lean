import Paper.Statements
import UniformBorderRank

/-! # Negative control module: same names, extra `False` premise

Theorem names match `Paper.Challenge` so the comparator will compare types.
Each type is `False → <paper statement>`, which is strictly stronger as a
hypothesis (requires proving from `False`).  The comparator must reject the
type mismatch with the challenge (which has no extra premise).
-/

namespace UniformBorderRank.Paper

theorem lemma_3_1 : False → PaperStatements.lemma_3_1 := by
  intro h; exact (h.elim)

theorem lemma_2_3 : False → PaperStatements.lemma_2_3 := by
  intro h; exact (h.elim)

theorem product_rank_le_one : False → PaperStatements.product_rank_le_one := by
  intro h; exact (h.elim)

theorem border_of_cp : False → PaperStatements.border_of_cp := by
  intro h; exact (h.elim)

theorem finite_difference_eval_count : False → PaperStatements.finite_difference_eval_count := by
  intro h; exact (h.elim)

theorem all_cut_hypothesis : False → PaperStatements.all_cut_hypothesis := by
  intro h; exact (h.elim)

theorem lemma_2_1 : False → PaperStatements.lemma_2_1 := by
  intro h; exact h.elim

theorem lemma_2_3_full : False → PaperStatements.lemma_2_3_full := by
  intro h; exact h.elim

theorem product_curve_coefficient : False → PaperStatements.product_curve_coefficient := by
  intro h; exact h.elim

theorem theorem_1_1_rank_one : False → PaperStatements.theorem_1_1_rank_one := by
  intro h; exact h.elim

theorem proposition_3_2 : False → PaperStatements.proposition_3_2 := by
  intro h; exact h.elim

theorem theorem_1_1 : False → PaperStatements.theorem_1_1 := by
  intro h; exact h.elim

theorem all_cut_uniform_bound : False → PaperStatements.all_cut_uniform_bound := by
  intro h; exact h.elim

theorem corollary_1_2 : False → PaperStatements.corollary_1_2 := by
  intro h; exact h.elim

theorem proposition_2_2 : False → PaperStatements.proposition_2_2 := by
  intro h; exact h.elim

theorem fixed_weight_examples : False → PaperStatements.fixed_weight_examples := by
  intro h; exact h.elim

theorem disjoint_block_examples : False → PaperStatements.disjoint_block_examples := by
  intro h; exact h.elim

theorem full_derivative_dimension : False → PaperStatements.full_derivative_dimension := by
  intro h; exact h.elim

theorem numerical_growth : False → PaperStatements.numerical_growth := by
  intro h; exact h.elim

end UniformBorderRank.Paper
