import UniformBorderRank.RetainedAnchors
import Mathlib.Data.Nat.Log

/-! Actual products across disjoint site blocks and multiplicativity of their
flattening ranks, as used in Section 5.2.  A site labelling partitions the
original `Fin N` sites into its disjoint fibers. -/
noncomputable section
namespace UniformBorderRank
open Finset Module

/-- The coefficient matrix of a product of a finite family of matrices. -/
def blockMatrix {B : Type*} [Fintype B] {I J : B → Type*}
    (M : ∀ b, Matrix (I b) (J b) ℂ) : Matrix (∀ b, I b) (∀ b, J b) ℂ :=
  fun u v => ∏ b, M b (u b) (v b)

lemma blockMatrix_mul {B : Type*} [Fintype B] [DecidableEq B]
    {I J K : B → Type*} [∀ b, Fintype (J b)]
    (M : ∀ b, Matrix (I b) (J b) ℂ) (P : ∀ b, Matrix (J b) (K b) ℂ) :
    (blockMatrix M : Matrix (∀ b, I b) (∀ b, J b) ℂ) * blockMatrix P =
      blockMatrix (fun b => M b * P b) := by
  classical
  ext u v
  simp only [Matrix.mul_apply, blockMatrix]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun b j => M b (u b) j * P b j (v b))).symm

lemma blockMatrix_one {B : Type*} [Fintype B] {I : B → Type*}
    [∀ b, DecidableEq (I b)] :
    blockMatrix (fun b => (1 : Matrix (I b) (I b) ℂ)) =
      (1 : Matrix (∀ b, I b) (∀ b, I b) ℂ) := by
  classical
  ext u v
  by_cases huv : u = v
  · subst v
    simp [blockMatrix]
  · obtain ⟨b, hb⟩ : ∃ b, u b ≠ v b := by simpa only [funext_iff, not_forall] using huv
    simp only [blockMatrix, Matrix.one_apply, if_neg huv]
    exact Finset.prod_eq_zero (Finset.mem_univ b) (if_neg hb)

/-- Matrix rank of a finite coefficient product is the product of the ranks.
The proof tensors actual rank factorizations and their two normalizers. -/
theorem rank_blockMatrix {B : Type*} [Fintype B] [DecidableEq B]
    {I J : B → Type*} [∀ b, Fintype (I b)] [∀ b, Fintype (J b)]
    (M : ∀ b, Matrix (I b) (J b) ℂ) :
    (blockMatrix M : Matrix (∀ b, I b) (∀ b, J b) ℂ).rank = ∏ b, (M b).rank := by
  classical
  let r (b : B) := (M b).rank
  have hf (b : B) := exists_normalized_rank_factorization (M b) (r b)
    (Matrix.rank_eq_finrank_span_row (M b)).symm
  choose X Y L R hXY hLM hYR using hf
  have hXY' (b : B) : Matrix.of (X b) * Matrix.of (Y b) = M b := by ext i j; exact (hXY b i j).symm
  have hLM' (b : B) : Matrix.of (L b) * M b = Matrix.of (Y b) := by ext a j; exact hLM b a j
  have hYR' (b : B) : Matrix.of (Y b) * Matrix.of (R b) = 1 := by ext a a'; exact hYR b a a'
  have hprodXY : (blockMatrix X : Matrix (∀ b, I b) (∀ b, Fin (r b)) ℂ) *
      blockMatrix Y = blockMatrix M := by
    rw [blockMatrix_mul]
    exact congrArg blockMatrix (funext hXY')
  have hprodLM : (blockMatrix L : Matrix (∀ b, Fin (r b)) (∀ b, I b) ℂ) *
      blockMatrix M = blockMatrix Y := by
    rw [blockMatrix_mul]
    exact congrArg blockMatrix (funext hLM')
  have hprodYR : (blockMatrix Y : Matrix (∀ b, Fin (r b)) (∀ b, J b) ℂ) *
      blockMatrix R = 1 := by
    rw [blockMatrix_mul]
    calc
      _ = blockMatrix (fun b => (1 : Matrix (Fin (r b)) (Fin (r b)) ℂ)) :=
        congrArg blockMatrix (funext hYR')
      _ = 1 := blockMatrix_one
  have hc : Fintype.card (∀ b, Fin (r b)) = ∏ b, r b := by simp [Fintype.card_pi]
  apply le_antisymm
  · rw [← hprodXY]
    exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans_eq hc)
  · have h₁ := Matrix.rank_mul_le_left (blockMatrix Y) (blockMatrix R)
    rw [hprodYR, Matrix.rank_one, hc] at h₁
    have h₂ := Matrix.rank_mul_le_right (blockMatrix L) (blockMatrix M)
    rw [hprodLM] at h₂
    exact h₁.trans h₂

abbrev BlockSite {N : ℕ} {B : Type*} (block : Fin N → B) (b : B) :=
  {i : Fin N // block i = b}
abbrev BlockCoeffs {N : ℕ} {B : Type*} (d : Fin N → ℕ) (block : Fin N → B) (b : B) :=
  (∀ i : BlockSite block b, Fin (d i)) → ℂ

/-- Tensor product across the disjoint fibers of a site labelling, on the
original coefficient tensor space. -/
def blockProduct {N : ℕ} {B : Type*} [Fintype B]
    (d : Fin N → ℕ) (block : Fin N → B) (T : ∀ b, BlockCoeffs d block b) : Coeffs d :=
  fun u => ∏ b, T b (fun i => u i)

/-- The genuine flattening of one block across the restriction of `S`. -/
def blockFlatCoeff {N : ℕ} {B : Type*} {d : Fin N → ℕ} {block : Fin N → B}
    (T : ∀ b, BlockCoeffs d block b) (S : Finset (Fin N)) (b : B)
    (u : ∀ i : BlockSite block b, i.val ∈ S → Fin (d i))
    (v : ∀ i : BlockSite block b, i.val ∈ Sᶜ → Fin (d i)) : ℂ :=
  T b (fun i => if hi : i.val ∈ S then u i hi else v i (Finset.mem_compl.mpr hi))

def blockSchmidtRank {N : ℕ} {B : Type*} {d : Fin N → ℕ} {block : Fin N → B}
    (T : ∀ b, BlockCoeffs d block b) (S : Finset (Fin N)) (b : B) : ℕ :=
  Module.finrank ℂ (Submodule.span ℂ (Set.range (blockFlatCoeff T S b)))

private def groupCutRow {N : ℕ} {B : Type*} {d : Fin N → ℕ} (block : Fin N → B)
    (S : Finset (Fin N)) (u : ∀ i ∈ S, Fin (d i)) :
    ∀ b, ∀ i : BlockSite block b, i.val ∈ S → Fin (d i) :=
  fun _ i hi => u i hi

private lemma groupCutRow_surjective {N : ℕ} {B : Type*} {d : Fin N → ℕ}
    (block : Fin N → B) (S : Finset (Fin N)) :
    Function.Surjective (groupCutRow (d := d) block S) := by
  intro u
  refine ⟨fun i hi => u (block i) ⟨i, rfl⟩ hi, ?_⟩
  funext b i hi
  rcases i with ⟨i, hbi⟩
  subst b
  rfl

/-- The original global flattening of a disjoint block product has precisely
the product of the restricted block flattening ranks. -/
theorem schmidtRank_blockProduct {N : ℕ} {B : Type*} [Fintype B] [DecidableEq B]
    (d : Fin N → ℕ) (block : Fin N → B) (T : ∀ b, BlockCoeffs d block b)
    (S : Finset (Fin N)) :
    schmidtRank d (blockProduct d block T) S = ∏ b, blockSchmidtRank T S b := by
  classical
  have he : flatCoeff d (blockProduct d block T) S =
      fun u v => blockMatrix (blockFlatCoeff T S) (groupCutRow block S u)
        (groupCutRow block Sᶜ v) := by
    funext u v
    rfl
  unfold schmidtRank
  rw [he, rowSpan_finrank_surjective_reindex _ _ _
    (groupCutRow_surjective block S) (groupCutRow_surjective block Sᶜ)]
  change Module.finrank ℂ (Submodule.span ℂ (Set.range (Matrix.row (blockMatrix (blockFlatCoeff T S)))) ) = _
  rw [← Matrix.rank_eq_finrank_span_row, rank_blockMatrix]
  apply Finset.prod_congr rfl
  intro b hb
  exact Matrix.rank_eq_finrank_span_row _

lemma blockSchmidtRank_congr_cut {N : ℕ} {B : Type*} [DecidableEq B]
    {d : Fin N → ℕ} {block : Fin N → B} (T : ∀ b, BlockCoeffs d block b)
    {S U : Finset (Fin N)} (b : B)
    (hcut : ∀ i : BlockSite block b, i.val ∈ S ↔ i.val ∈ U) :
    blockSchmidtRank T S b = blockSchmidtRank T U b := by
  classical
  let f : (∀ i : BlockSite block b, i.val ∈ U → Fin (d i)) →
      (∀ i : BlockSite block b, i.val ∈ S → Fin (d i)) :=
    fun u i hi => u i ((hcut i).mp hi)
  let g : (∀ i : BlockSite block b, i.val ∈ Uᶜ → Fin (d i)) →
      (∀ i : BlockSite block b, i.val ∈ Sᶜ → Fin (d i)) :=
    fun v i hi => v i (Finset.mem_compl.mpr (fun h =>
      (Finset.mem_compl.mp hi) ((hcut i).mpr h)))
  have hf : Function.Surjective f := by
    intro u
    exact ⟨fun i hi => u i ((hcut i).mpr hi), rfl⟩
  have hg : Function.Surjective g := by
    intro v
    exact ⟨fun i hi => v i (Finset.mem_compl.mpr (fun h =>
      (Finset.mem_compl.mp hi) ((hcut i).mp h))), rfl⟩
  have he : (fun u v => blockFlatCoeff T S b (f u) (g v)) = blockFlatCoeff T U b := by
    funext u v
    apply congrArg (T b)
    funext i
    by_cases hiS : i.val ∈ S
    · have hiU := (hcut i).mp hiS
      simp only [dif_pos hiS, dif_pos hiU, f]
    · have hiU : i.val ∉ U := fun h => hiS ((hcut i).mpr h)
      simp only [dif_neg hiS, dif_neg hiU, g]
  have hr := rowSpan_finrank_surjective_reindex (blockFlatCoeff T S b) f g hf hg
  rw [he] at hr
  exact hr.symm

/-- Combine independently chosen internal block cuts into a cut of the original sites. -/
def combinedBlockCut {N : ℕ} {B : Type*} (block : Fin N → B)
    (C : B → Finset (Fin N)) : Finset (Fin N) :=
  Finset.univ.filter (fun i => i ∈ C (block i))

lemma blockSchmidtRank_combined {N : ℕ} {B : Type*} [DecidableEq B]
    {d : Fin N → ℕ} (block : Fin N → B) (T : ∀ b, BlockCoeffs d block b)
    (C : B → Finset (Fin N)) (b : B) :
    blockSchmidtRank T (combinedBlockCut block C) b = blockSchmidtRank T (C b) b := by
  apply blockSchmidtRank_congr_cut
  intro i
  simp only [combinedBlockCut, Finset.mem_filter, Finset.mem_univ, true_and, i.property]

lemma blockSchmidtRank_pos_of_product_ne_zero {N : ℕ} {B : Type*}
    [Fintype B] [DecidableEq B] {d : Fin N → ℕ} (block : Fin N → B)
    (T : ∀ b, BlockCoeffs d block b) (hT : blockProduct d block T ≠ 0)
    (S : Finset (Fin N)) (b : B) : 1 ≤ blockSchmidtRank T S b := by
  classical
  obtain ⟨u, hu⟩ : ∃ u, blockProduct d block T u ≠ 0 := by
    by_contra! h
    exact hT (funext h)
  have hb : T b (fun i => u i) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hu) b (Finset.mem_univ _)
  let row : ∀ i : BlockSite block b, i.val ∈ S → Fin (d i) := fun i _ => u i
  let col : ∀ i : BlockSite block b, i.val ∈ Sᶜ → Fin (d i) := fun i _ => u i
  have he : blockFlatCoeff T S b row col = T b (fun i => u i) := by
    apply congrArg (T b)
    funext i
    simp only [row, col]
    split_ifs <;> rfl
  have hn : blockFlatCoeff T S b row ≠ 0 := by
    intro h
    exact hb (he.symm.trans (congrFun h col))
  apply Submodule.one_le_finrank_iff.mpr
  intro hbot
  have hr := Submodule.subset_span (R := ℂ) (Set.mem_range_self (f := blockFlatCoeff T S b) row)
  rw [hbot] at hr
  exact hn hr

lemma schmidtRank_empty_le_one {N : ℕ} (d : Fin N → ℕ) (T : Coeffs d) :
    schmidtRank d T ∅ ≤ 1 := by
  classical
  have h := Matrix.rank_le_card_height (Matrix.of (flatCoeff d T ∅))
  have hc : Fintype.card (∀ i ∈ (∅ : Finset (Fin N)), Fin (d i)) = 1 := by simp
  rw [hc] at h
  exact (Matrix.rank_eq_finrank_span_row _).symm.trans_le h

lemma schmidtRank_univ_le_one {N : ℕ} (d : Fin N → ℕ) (T : Coeffs d) :
    schmidtRank d T Finset.univ ≤ 1 := by
  classical
  have h := Matrix.rank_le_card_width (Matrix.of (flatCoeff d T Finset.univ))
  have hc : Fintype.card (∀ i ∈ (Finset.univ : Finset (Fin N))ᶜ, Fin (d i)) = 1 := by simp
  rw [hc] at h
  exact (Matrix.rank_eq_finrank_span_row _).symm.trans_le h

/-- Every cut rank is at most the largest nontrivial cut rank of a nonzero
tensor with at least two sites, including the two trivial cuts. -/
lemma schmidtRank_le_maxSchmidtRank {N : ℕ} (d : Fin N → ℕ) (T : Coeffs d)
    (hN : 2 ≤ N) (hT : T ≠ 0) (S : Finset (Fin N)) :
    schmidtRank d T S ≤ maxSchmidtRank d T := by
  by_cases hS : S = ∅
  · subst S
    exact (schmidtRank_empty_le_one d T).trans (maxSchmidtRank_pos hN T hT)
  by_cases hU : S = Finset.univ
  · subst S
    exact (schmidtRank_univ_le_one d T).trans (maxSchmidtRank_pos hN T hT)
  exact allCutLe_of_maxSchmidtRank_le T _ le_rfl S hS hU

/-- The Section 5.2 block obstruction: independently entangled disjoint
blocks give an exponential lower bound on the maximal original cut rank. -/
theorem two_pow_entangled_blocks_le_maxSchmidtRank {N : ℕ} {B : Type*}
    [Fintype B] [DecidableEq B] (d : Fin N → ℕ) (block : Fin N → B)
    (T : ∀ b, BlockCoeffs d block b) (hN : 2 ≤ N)
    (hT : blockProduct d block T ≠ 0) (E : Finset B)
    (C : B → Finset (Fin N)) (hC : ∀ b ∈ E, 2 ≤ blockSchmidtRank T (C b) b) :
    2 ^ E.card ≤ maxSchmidtRank d (blockProduct d block T) := by
  classical
  let S := combinedBlockCut block C
  have hbound : ∀ b, (if b ∈ E then 2 else 1) ≤ blockSchmidtRank T S b := by
    intro b
    by_cases hb : b ∈ E
    · simpa only [if_pos hb, S, blockSchmidtRank_combined] using hC b hb
    · simpa only [if_neg hb] using blockSchmidtRank_pos_of_product_ne_zero block T hT S b
  have hprod := Finset.prod_le_prod (fun b (_ : b ∈ Finset.univ) => Nat.zero_le
    (if b ∈ E then 2 else 1)) (fun b _ => hbound b)
  have hpow : (∏ b, if b ∈ E then 2 else 1) = 2 ^ E.card := by simp
  rw [hpow, ← schmidtRank_blockProduct d block T S] at hprod
  exact hprod.trans (schmidtRank_le_maxSchmidtRank d _ hN hT S)

/-- At most `floor(log₂ r)` independently entangled blocks can occur. -/
theorem entangled_blocks_card_le_log2 {N : ℕ} {B : Type*}
    [Fintype B] [DecidableEq B] (d : Fin N → ℕ) (block : Fin N → B)
    (T : ∀ b, BlockCoeffs d block b) (hN : 2 ≤ N)
    (hT : blockProduct d block T ≠ 0) (E : Finset B)
    (C : B → Finset (Fin N)) (hC : ∀ b ∈ E, 2 ≤ blockSchmidtRank T (C b) b) :
    E.card ≤ Nat.log2 (maxSchmidtRank d (blockProduct d block T)) := by
  rw [Nat.log2_eq_log_two]
  exact Nat.le_log_of_pow_le (by decide)
    (two_pow_entangled_blocks_le_maxSchmidtRank d block T hN hT E C hC)

end UniformBorderRank
