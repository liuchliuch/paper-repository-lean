import K44K35Free.QuarticSections
import K44K35Free.Construction

/-! The quartic averaging bound for the entire concrete family of rich planes. -/
noncomputable section
namespace K44K35Free.Construction

open Geometry

variable {F : Type*} [Field F] [Fintype F]

theorem graphRichPlanes_subset_richPlanes (α : F) (c : Quartic F) :
    Geometry.richPlanes α c ⊆ richPlanes α c := by
  classical
  intro E hE
  exact (mem_richPlanes α c E).mpr (Geometry.richPlanes_spec α c hE)

/-- Lemma 6 in terms of all actual nonexceptional four-point planes. -/
theorem lemma_6_many_richPlanes (α : F) (hα : IsNonsquare α)
    (hF : ringChar F ≠ 2) (hq : 8 ≤ Fintype.card F) :
    ∃ c : Quartic F, Fintype.card F ^ 9 ≤ 768 * (richPlanes α c).card := by
  classical
  obtain ⟨c, hc, _⟩ := Geometry.lemma_6_many_four_point_sections α hα hF hq
  exact ⟨c, hc.trans (Nat.mul_le_mul_left 768
    (Finset.card_le_card (graphRichPlanes_subset_richPlanes α c)))⟩

/-- The paper's absolute-constant and sufficiently-large quantifiers,
with `c₀ = 1/768` and threshold `q₀ = 8`. -/
theorem lemma_6_uniform :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ q₀ : ℕ,
      ∀ (K : Type*) [Field K] [Fintype K] (α : K),
        IsNonsquare α → ringChar K ≠ 2 → q₀ ≤ Fintype.card K →
          ∃ c : Quartic K,
            c₀ * (Fintype.card K : ℝ) ^ 9 ≤ (richPlanes α c).card := by
  refine ⟨1 / 768, by norm_num, 8, ?_⟩
  intro K _ _ α hα hK hq
  obtain ⟨c, hc⟩ := lemma_6_many_richPlanes α hα hK hq
  refine ⟨c, ?_⟩
  have hr : (Fintype.card K : ℝ) ^ 9 ≤ 768 * (richPlanes α c).card := by
    exact_mod_cast hc
  nlinarith

end K44K35Free.Construction
