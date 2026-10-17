import K44K35Free.Survival
import K44K35Free.PruningGeometry
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-! Proposition 10 for the concrete graph, original indexed exceptional blocks,
and designated pairs of the quartic cap construction. -/

noncomputable section
namespace K44K35Free.Construction

open Geometry Finset

attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F]

local instance survivalGeometryLocalInstance1 : Fintype (Plane F) := Fintype.ofFinite _
local instance survivalGeometryLocalInstance2 (α : F) (c : Quartic F) : Fintype (BlockIndex α c) := Fintype.ofFinite _

/-- The final graph has the construction's two vertex classes as a genuine
    two-coloring, for every realization of the local choices. -/
theorem finalGraph_isBipartite (α : F) (c : Quartic F)
    (T : V F ≃ₗ[F] V F) (L : ℕ) (R : Choices α c) :
    (finalGraph α c T L R).IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk
    (fun v => if v.isLeft then (0 : Fin 2) else 1) ?_⟩
  intro u v huv
  cases u <;> cases v <;> simp_all [finalGraph, Pruning.bipartiteGraph]

/-- Every designated pair has exactly sixteen distinct bipartite edges. -/
theorem copyEdges_card_of_designated (α : F) (c : Quartic F)
    (T : V F ≃ₗ[F] V F) {D : Plane F × Plane F}
    (hD : D ∈ designatedPairs α c T) : (copyEdges α c D).card = 16 := by
  obtain ⟨hA, hC, _⟩ := (mem_designatedPairs α c T D).mp hD
  simp only [copyEdges, card_product, hA.2, hC.2]

/-- Every edge remaining after the preliminary alteration has load at most L
    in the original nonmutual indexed blocks. -/
theorem preliminary_actual_load_le (α : F) (c : Quartic F)
    (T : V F ≃ₗ[F] V F) (L : ℕ) {e : Param F × Param F}
    (he : e ∈ preliminary α c T L) :
    (univ.filter fun i : BlockIndex α c => ¬ actualMutual α c T i ∧
      e ∈ (actualBlocks α c T i).edges).card ≤ L := by
  classical
  have h := PreliminaryAlteration.preliminaryEdges_load_le (initialEdges α c T)
    (fun i => (actualBlocks α c T i).edges) (actualMutual α c T) L he
  simpa only [PreliminaryAlteration.blockLoad] using h

/-- **Proposition 10.** Independent uniform two-subset choices in the actual
    original blocks have a realization retaining at least the fraction
    `6^(-16L)` of the preliminary designated copies. -/
theorem proposition10_survival (α : F) (c : Quartic F)
    (hα : K44K35Free.IsNonsquare α) (T : V F ≃ₗ[F] V F) (L : ℕ) :
    ∃ R : Choices α c, ValidChoices α c T R ∧
      ((preDesignated α c T L).card : ℝ) / 6 ^ (16 * L) ≤
        (survivingPairs α c T L R).card := by
  classical
  have hpre : ∀ D ∈ preDesignated α c T L,
      copyEdges α c D ⊆ preliminary α c T L := by
    intro D hD
    exact (mem_filter.mp hD).2
  have hsize : ∀ D ∈ preDesignated α c T L, (copyEdges α c D).card ≤ 16 := by
    intro D hD
    exact (copyEdges_card_of_designated α c T (mem_filter.mp hD).1).le
  have hrequirements : ∀ D ∈ preDesignated α c T L, ∀ i,
      ¬ actualMutual α c T i → Pruning.Active (actualBlocks α c T i) →
      ∀ y ∈ (actualBlocks α c T i).exceptional,
      (Pruning.requirements (copyEdges α c D) (actualBlocks α c T i) y).card ≤ 2 := by
    intro D hD i _ _ y _
    exact actual_requirements_card_le_two α c hα T D (mem_filter.mp hD).1 i y
  obtain ⟨R, hR, hcount⟩ := Pruning.exists_pruning_retaining_fraction_real
    (preDesignated α c T L) (copyEdges α c) (preliminary α c T L)
    (actualBlocks α c T) (actualMutual α c T) L hpre hsize
    (actualBlocks_controlled_card_le_four α c hα T) hrequirements
    (fun _ he => preliminary_actual_load_le α c T L he)
  refine ⟨R, ?_, ?_⟩
  · intro i hi ha y hy
    exact mem_powersetCard.mp (hR i hi ha y hy)
  · have heq : ((preDesignated α c T L).filter
        (fun D => copyEdges α c D ⊆ Pruning.prunedEdges (preliminary α c T L)
          (actualBlocks α c T) (actualMutual α c T) R)) = survivingPairs α c T L R := by
      ext D
      simp only [survivingPairs, prune, mem_filter]
    rwa [heq] at hcount

/-- The numerical form (35), using the preliminary lower bound (25). -/
theorem proposition10_paper_bound (α : F) (c : Quartic F)
    (hα : K44K35Free.IsNonsquare α) (T : V F ≃ₗ[F] V F) (L : ℕ)
    (c₂ : ℝ) (hpre : c₂ * (Fintype.card F : ℝ) ^ 9 ≤
      (preDesignated α c T L).card) :
    ∃ R : Choices α c, ValidChoices α c T R ∧
      1 / 6 ^ (16 * L) * c₂ * (Fintype.card F : ℝ) ^ 9 ≤
        (survivingPairs α c T L R).card := by
  obtain ⟨R, hR, hcount⟩ := proposition10_survival α c hα T L
  refine ⟨R, hR, ?_⟩
  have hpos : (0 : ℝ) < 6 ^ (16 * L) := by positivity
  calc
    1 / 6 ^ (16 * L) * c₂ * (Fintype.card F : ℝ) ^ 9 =
        (c₂ * (Fintype.card F : ℝ) ^ 9) / 6 ^ (16 * L) := by ring
    _ ≤ ((preDesignated α c T L).card : ℝ) / 6 ^ (16 * L) :=
      div_le_div_of_nonneg_right hpre hpos.le
    _ ≤ _ := hcount

end K44K35Free.Construction
