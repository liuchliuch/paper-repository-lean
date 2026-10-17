import Paper29.SeedNonempty
import Paper29.LongLower
import Paper29.ShortLower

noncomputable section
open MeasureTheory
open scoped ENNReal Classical
namespace Paper29.QueryModel

/-- Theorem 2.2 with the original arbitrary-matrix-size, exact-rank and
arbitrary measurable randomized adaptive-policy quantifiers. No external
concentration, posterior channel or transcript input is assumed. -/
theorem theorem2_2 : LowerBoundStatement := by
  refine ⟨1/1280000,by norm_num,?_⟩
  intro n d r hr hrdn ε hε hεhi
  have hrn : r ≤ n := (le_min_iff.mp hrdn).1
  have hrd : r ≤ d := (le_min_iff.mp hrdn).2
  refine ⟨HardDistribution.fixedDesign n d r,HardDistribution.fixedDesign_rank n d r hr hrn hrd,?_⟩
  intro Ω mΩ μ hμ p hp
  letI := mΩ
  letI := hμ
  haveI : Nonempty Ω := seed_nonempty μ
  by_cases hN : n/r < 160
  · have hA : HardDistribution.fixedDesign n d r=HardDistribution.shortDesign n d r := by
      simp only [HardDistribution.fixedDesign,if_pos hN]
    rw [hA] at hp
    exact HardDistribution.short_lower_bound μ hr hrn hrd hN ε p hp
  · have hA : HardDistribution.fixedDesign n d r=HardDistribution.longDesign n d r (n/r) := by
      simp only [HardDistribution.fixedDesign,if_neg hN]
    rw [hA] at hp
    exact HardDistribution.long_lower_bound μ hr hrd (by omega) ε hε hεhi p hp

end Paper29.QueryModel
