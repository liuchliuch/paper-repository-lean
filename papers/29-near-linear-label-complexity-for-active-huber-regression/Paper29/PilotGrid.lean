import Paper29.UniformExpectation
import Paper29.EventTools
import Paper29.SampleWeights
import Paper29.AllScale

noncomputable section
open scoped BigOperators Classical
namespace Paper29.ProcessTools

theorem expectation_finset_sum {n m : ℕ} {ι : Type*} (π : Fin n → ℝ)
    (s : Finset ι) (f : ι → (Fin m → Fin n) → ℝ) :
    Sampling.expectation π (fun ν => ∑ i ∈ s, f i ν) =
      ∑ i ∈ s, Sampling.expectation π (f i) := by
  unfold Sampling.expectation
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

/-- One nonnegative random variable accounts for all finite-scale bad events.
Its threshold one implies error at most `S/32` at each grid radius. -/
def pilotTest {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (π : Fin n → ℝ)
    (grid : Finset ℝ) (ν : Fin m → Fin n) : ℝ :=
  ∑ S ∈ grid, (32 / S) * unshiftedError A π S ν

theorem pilotTest_nonneg {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (π : Fin n → ℝ) (hπ : ∀ i, 0 ≤ π i) (grid : Finset ℝ)
    (hgrid : ∀ S ∈ grid, 0 < S) (ν : Fin m → Fin n) : 0 ≤ pilotTest A π grid ν := by
  apply Finset.sum_nonneg
  intro S hS
  exact mul_nonneg (div_nonneg (by norm_num) (hgrid S hS).le)
    (unshiftedError_nonneg A π hπ (hgrid S hS).le ν)

/-- Finite union bound expressed through a single true expectation. -/
theorem pilotTest_expectation {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (τ π : Fin n → ℝ) (T C G : ℝ) (hT : 0 < T) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (external : ExternalProcess.AnchoredChaining C)
    (hτ : ∀ i, 0 < τ i) (hπ : ∀ i, 0 < π i) (hsum : ∑ i, π i = 1)
    (hm : 0 < m) (hrel : ∀ i, τ i = T * π i) (cover : ScoreGeometry A τ G)
    (ha : alpha C G T m ≤ 1) (grid : Finset ℝ) (hgrid : ∀ S ∈ grid, 0 < S) :
    Sampling.expectation π (pilotTest (m := m) A π grid) ≤
      64 * alpha C G T m * grid.card := by
  unfold pilotTest
  rw [expectation_finset_sum]
  have hs : ∑ S ∈ grid, Sampling.expectation π
      (fun ν : Fin m → Fin n => (32 / S) * unshiftedError A π S ν) ≤
      ∑ _S ∈ grid, 64 * alpha C G T m := by
    apply Finset.sum_le_sum
    intro S hS
    rw [expectation_mul_const]
    have hpos := hgrid S hS
    have he := (unshifted_expectation_bound A τ π T C G hT hC hG external
      hτ hπ hsum hm hrel cover ha (hgrid S hS)).1
    calc
      _ ≤ (32 / S) * (2 * alpha C G T m * S) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = _ := by field_simp [ne_of_gt hpos]; ring
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm] using hs

/-- The grid's only deterministic property: it covers the finite Huber range
within a factor two. It is verified for an explicit dyadic grid separately. -/
def PilotGridCovers {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (grid : Finset ℝ) : Prop :=
  ∀ h, 1 / 2 ≤ unshifted A h → unshifted A h ≤ 8 * (n : ℝ)^3 →
    ∃ S ∈ grid, unshifted A h ≤ S ∧ S ≤ 2 * unshifted A h

theorem pilotTest_finite_range {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (π : Fin n → ℝ) (hπ : ∀ i, 0 ≤ π i) (grid : Finset ℝ)
    (hgrid : ∀ S ∈ grid, 0 < S) (hcover : PilotGridCovers A grid)
    (ν : Fin m → Fin n) (hν : pilotTest A π grid ν ≤ 1) :
    ∀ h, 1 / 2 ≤ unshifted A h → unshifted A h ≤ 8 * (n : ℝ)^3 →
      |Sampling.sampledUnshifted π ν A h - unshifted A h| ≤
        (1 / 16) * unshifted A h := by
  intro h hlo hhi
  obtain ⟨S, hS, hle, htwo⟩ := hcover h hlo hhi
  have hpos := hgrid S hS
  have hb : BddAbove (Set.range (fun k : Ball A S =>
      |Sampling.sampledUnshifted π ν A k - unshifted A k|)) :=
    unshiftedError_bdd A π hπ S ν
  have he : |Sampling.sampledUnshifted π ν A h - unshifted A h| ≤
      unshiftedError A π S ν := le_supremum _ hb ⟨h, hle⟩
  have hsingle : (32 / S) * unshiftedError A π S ν ≤ pilotTest A π grid ν := by
    apply Finset.single_le_sum (fun R hR => ?_) hS
    exact mul_nonneg (div_nonneg (by norm_num) (hgrid R hR).le)
      (unshiftedError_nonneg A π hπ (hgrid R hR).le ν)
  have hx : 32 * unshiftedError A π S ν ≤ S := by
    have hh := (div_le_iff₀ hpos).mp (show
      32 * unshiftedError A π S ν / S ≤ 1 by
        convert hsingle.trans hν using 1 <;> ring)
    linarith
  linarith

/-- The actual all-scale pilot embedding event, obtained from finite-scale
expectation control and the already proved Huber all-scale extension. -/
theorem pilot_embedding_probability {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (τ π : Fin n → ℝ) (T C G δ : ℝ) (hn : 16 < n)
    (hT : 0 < T) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (external : ExternalProcess.AnchoredChaining C)
    (hτ : ∀ i, 0 < τ i) (hπ : ∀ i, 0 < π i) (hsum : ∑ i, π i = 1)
    (hlower : ∀ i, 1 / (2 * (n : ℝ)) ≤ π i)
    (hm : 0 < m) (hrel : ∀ i, τ i = T * π i) (cover : ScoreGeometry A τ G)
    (ha : alpha C G T m ≤ 1) (grid : Finset ℝ) (hgrid : ∀ S ∈ grid, 0 < S)
    (hcover : PilotGridCovers A grid) (hbudget : 64 * alpha C G T m * grid.card ≤ δ) :
    1 - δ ≤ Sampling.eventMass (Sampling.iidMass π)
      (Finset.univ.filter (fun ν : Fin m → Fin n => ∀ h,
        |Sampling.sampledUnshifted π ν A h - unshifted A h| ≤
          (1 / 8) * unshifted A h)) := by
  have hp := fun i => (hπ i).le
  have hgood := good_event_of_expectation (Sampling.iidMass π)
    (pilotTest (m := m) A π grid) (Sampling.iidMass_nonneg π hp)
    (Sampling.iidMass_sum π hsum) (pilotTest_nonneg A π hp grid hgrid)
    (a := 1) (δ := δ) (by norm_num) (by
      simpa using (pilotTest_expectation A τ π T C G hT hC hG external hτ hπ hsum
        hm hrel cover ha grid hgrid).trans hbudget)
  apply hgood.trans
  apply eventMass_mono _ (Sampling.iidMass_nonneg π hp)
  intro ν hν
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hν ⊢
  have hf := pilotTest_finite_range A π hp grid hgrid hcover ν hν
  have hall := AllScale.huber_all_scale_extension A (Sampling.importanceWeights π ν)
    hn (Sampling.importanceWeights_nonneg π hp ν)
    (Sampling.importanceWeights_sum_le (by omega) hm π hπ hlower ν) (by
      intro h hlo hhi
      simpa only [Sampling.weightedHuber_importanceWeights, Sampling.sampledUnshifted]
        using hf h hlo hhi)
  simpa only [Sampling.weightedHuber_importanceWeights, Sampling.sampledUnshifted] using hall

end Paper29.ProcessTools
