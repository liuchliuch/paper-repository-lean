import K44K35Free.Amplification
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Finset.Lattice.Fold

/-!
# The actual generalized extremal function

The extremal function below is the maximum number of copies among the finite
collection of all `K_{3,5}`-free graphs on `Fin n`. Relabelling proves its
universality for arbitrary finite vertex sets. The final theorem derives the
paper's two-sided cubic bounds from its actual graph-existence lower bound.
-/

namespace K44K35Free
open Finset

/-- All forbidden-subgraph-free graphs on the labelled `n`-vertex set. -/
noncomputable def k35FreeGraphs (n : ℕ) : Finset (SimpleGraph (Fin n)) := by
  classical
  exact Finset.univ.filter IsK35Free

/-- The actual generalized Turán number `ex(n,K₄,₄,K₃,₅)`. -/
noncomputable def exK44K35 (n : ℕ) : ℕ :=
  (k35FreeGraphs n).sup numK44

@[simp] theorem mem_k35FreeGraphs {n : ℕ} (G : SimpleGraph (Fin n)) :
    G ∈ k35FreeGraphs n ↔ IsK35Free G := by
  classical
  simp [k35FreeGraphs]

/-- The edgeless graph belongs to the admissible family at every vertex count. -/
theorem isK35Free_bot {V : Type} [Fintype V] :
    IsK35Free (⊥ : SimpleGraph V) := by
  classical
  intro X hX
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < X.card)
  have hempty : commonNeighbors (⊥ : SimpleGraph V) X = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hAdj := mem_commonNeighbors.mp hv x hx
    exact hAdj
  rw [hempty]
  simp

/-- The extremal number is attained by an admissible graph, so it is an actual maximum. -/
theorem exK44K35_attained (n : ℕ) :
    ∃ G : SimpleGraph (Fin n), IsK35Free G ∧ numK44 G = exK44K35 n := by
  classical
  have hn : (k35FreeGraphs n).Nonempty :=
    ⟨⊥, (mem_k35FreeGraphs _).mpr isK35Free_bot⟩
  obtain ⟨G, hG, hmax⟩ := Finset.exists_mem_eq_sup (k35FreeGraphs n) hn numK44
  exact ⟨G, (mem_k35FreeGraphs _).mp hG, hmax.symm⟩

/-- Every admissible labelled graph is bounded by the extremal number. -/
theorem numK44_le_exK44K35_fin {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : IsK35Free G) : numK44 G ≤ exK44K35 n :=
  Finset.le_sup ((mem_k35FreeGraphs G).mpr hG)

/-- Relabelling makes the finite maximum universal for every finite `n`-vertex graph. -/
theorem numK44_le_exK44K35 {V : Type} [Fintype V] (G : SimpleGraph V)
    (hG : IsK35Free G) {n : ℕ} (hn : Fintype.card V = n) :
    numK44 G ≤ exK44K35 n := by
  let e := Fintype.equivFinOfCardEq hn
  have h := numK44_le_exK44K35_fin (G.map e.toEmbedding) (isK35Free_map G e.toEmbedding hG)
  rwa [numK44_map] at h

/-- Lemma 2 bounds the maximum over all graphs, with the paper's exact constant. -/
theorem exK44K35_le_choose (n : ℕ) : exK44K35 n ≤ n.choose 3 / 8 := by
  classical
  apply Finset.sup_le
  intro G hG
  simpa only [Fintype.card_fin] using
    lemma_2_paper_form G ((mem_k35FreeGraphs G).mp hG)

/-- A coarse cubic upper bound sufficient for the `Theta(n³)` consequence. -/
theorem exK44K35_le_cube (n : ℕ) : exK44K35 n ≤ n ^ 3 :=
  (exK44K35_le_choose n).trans ((Nat.div_le_self _ _).trans (Nat.choose_le_pow n 3))

/-- The lower graph-existence statement entails genuine two-sided bounds for the
actual extremal function. The premise is discharged by the paper's construction. -/
theorem extremal_cubic_bounds_of_graph_lower_bound
    (hlower : ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
        Fintype.card V = n ∧ IsK35Free G ∧ G.IsBipartite ∧
          c * (n : ℝ) ^ 3 ≤ numK44 G) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      c * (n : ℝ) ^ 3 ≤ exK44K35 n ∧ (exK44K35 n : ℝ) ≤ C * (n : ℝ) ^ 3 := by
  obtain ⟨c, hc, n₀, hlower⟩ := hlower
  refine ⟨c, 1, hc, by norm_num, n₀, ?_⟩
  intro n hn
  obtain ⟨V, instV, G, hcard, hfree, _, hcopies⟩ := hlower n hn
  constructor
  · exact hcopies.trans (by exact_mod_cast numK44_le_exK44K35 G hfree hcard)
  · simpa only [one_mul, Nat.cast_pow] using (Nat.cast_le (α := ℝ)).mpr (exK44K35_le_cube n)

end K44K35Free
