import Paper09.UpperScale
import Paper09.BlockDynamics
import Paper09.PercolationLabels

open Real Filter Finset BigOperators
open Paper09.LatticeGeometry Paper09.BlockCovering Paper09.BlockColoring
open scoped Topology
noncomputable section
namespace Paper09.UpperParameters

/-- The coarse half-mesh selected in (3.10), with `C₁=32`. -/
def sourceS (κ : ℝ) (n : ℕ) : ℕ := Nat.ceil (4*log (UpperScale.clusterCutoff κ n))

/-- The actual percolation influence constant supplied by the good-root
coupling, before comparison with the asymptotic `H_R` expression. -/
def rootInfluence (ρ : ℝ) (R s M : ℕ) : ℝ :=
  (Percolation.initialRadius R:ℝ)+2/ρ+(M:ℝ)/ρ*exp (-(s:ℝ))

@[simp] lemma source_radius (κ : ℝ) (n : ℕ) :
    8*sourceS κ n = UpperScale.roundedRadius (UpperScale.clusterCutoff κ n) := rfl

/-- Dimension-only constant in the actual incidence relation `J_y R ≤ A I_y`. -/
def overlapConstant (d : ℕ) : ℝ := 4*(d:ℝ)*(4:ℝ)^d

lemma overlapConstant_pos {d : ℕ} (hd : 1 ≤ d) : 0 < overlapConstant d := by
  unfold overlapConstant
  have : (0:ℝ)<d := by exact_mod_cast (by omega : 0<d)
  positivity

/-- Actual covering geometry, without an assumed incidence certificate. -/
lemma incidence_geometry {d n s L : ℕ} {good : Point d → Prop}
    (hd : 1 ≤ d) (hs : 0 < s) (hevent : SmallClusters good n s L)
    {y : Point d} (hy : y ∈ volume n) :
    0 < I good n s y ∧
      (J good n s y:ℝ)*(8*s:ℕ) ≤ overlapConstant d*(I good n s y:ℝ) := by
  have hcov := covering_scaled hs hevent hy
  have hlow := covering_lower hs hevent hy
  have hIpos : 0 < I good n s y :=
    lt_of_lt_of_le (pow_pos (show 0<2*s+1 by omega) _) hlow
  refine ⟨hIpos, ?_⟩
  have hi : ((8*s:ℕ):ℝ)^d ≤ (4:ℝ)^d*(I good n s y:ℝ) := by exact_mod_cast hcov.1
  have hj : (J good n s y:ℝ) ≤ 4*(d:ℝ)*((8*s:ℕ):ℝ)^(d-1) := by exact_mod_cast hcov.2.2
  have hm := mul_le_mul_of_nonneg_right hj (show (0:ℝ)≤(8*s:ℕ) by positivity)
  have heq : ((8*s:ℕ):ℝ)^(d-1)*((8*s:ℕ):ℝ) = ((8*s:ℕ):ℝ)^d := by
    rw [← pow_succ, show d-1+1=d by omega]
  have hhi := mul_le_mul_of_nonneg_left hi (show 0≤4*(d:ℝ) by positivity)
  unfold overlapConstant
  nlinarith only [hm, hhi, heq]

/-- The maximal block really contains a site and has the proved volume bound. -/
lemma maxBlockSize_range {d n s L : ℕ} {good : Point d → Prop}
    (hs : 0 < s) (hL : 1 ≤ L) (hevent : SmallClusters good n s L) :
    1 ≤ maxBlockSize good n s ∧ maxBlockSize good n s ≤ L*(8*s)^d := by
  have hQ := colorCount_pos hs hevent
  have hM : 0 < maxBlockSize good n s := by
    by_contra h
    have hz : maxBlockSize good n s=0 := by omega
    simp [colorCount, hz] at hQ
  exact ⟨by omega, maxBlockSize_bound hs hL hevent⟩

/-- A fixed explicit coefficient dominates the good-root coupling's actual
`r₀+2/ρ+(M/ρ)e^{-s}` constant. -/
lemma rootInfluence_le {ρ : ℝ} (hρ : 0 < ρ) {s M : ℕ}
    (hR : 1 ≤ log (8*s:ℕ)) :
    rootInfluence ρ (8*s) s M ≤
      (4+4/ρ)*(log (8*s:ℕ))^2 +
        (4+4/ρ)*(M:ℝ)*exp (-((8*s:ℕ):ℝ)/8) := by
  have hceil := (Nat.ceil_lt_add_one (sq_nonneg (log (8*s:ℕ)))).le
  have hsquare : 1 ≤ (log (8*s:ℕ))^2 := by nlinarith
  have hρi : 0 ≤ 1/ρ := by positivity
  have hcoeff : 1/ρ ≤ 4+4/ρ := by
    simp only [div_eq_mul_inv] at hρi ⊢
    nlinarith
  have hexp : exp (-((8*s:ℕ):ℝ)/8) = exp (-(s:ℝ)) := by
    congr 1
    push_cast
    ring
  unfold rootInfluence Percolation.initialRadius
  rw [hexp]
  have hmain := mul_le_mul_of_nonneg_right hcoeff
    (mul_nonneg (Nat.cast_nonneg M : (0:ℝ)≤M) (exp_pos (-(s:ℝ))).le)
  have hbase := mul_le_mul_of_nonneg_left hsquare (show 0≤3+4/ρ by positivity)
  simp only [div_eq_mul_inv] at hρi hmain hbase ⊢
  nlinarith

/-- The actual integer `r₀=ceil((log R)^2)` is positive and fits below `s` for
the source's rounded scales. -/
theorem initialRadius_fits {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ n : ℕ in atTop,
      0 < sourceS κ n ∧
      0 < Percolation.initialRadius (8*sourceS κ n) ∧
      Percolation.initialRadius (8*sourceS κ n) ≤ sourceS κ n ∧
      1 ≤ log (8*sourceS κ n:ℕ) := by
  have hRtop := UpperScale.roundedRadius_tendsto.comp (UpperScale.clusterCutoff_tendsto hκ)
  have hlog := Real.tendsto_log_atTop.comp hRtop
  have hratio : Tendsto (fun R : ℝ => (log R)^2/R) atTop (𝓝 0) := by
    simpa only [Real.rpow_one, Real.rpow_ofNat] using
      (isLittleO_log_rpow_rpow_atTop (2:ℝ) (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero
  have hs := (hratio.comp hRtop).eventually (gt_mem_nhds (show (0:ℝ)<1/16 by norm_num))
  filter_upwards [hRtop.eventually (eventually_ge_atTop 16),
    hlog.eventually (eventually_ge_atTop 1), hs] with n hR hlog hs
  change (16:ℝ) ≤ (8*sourceS κ n:ℕ) at hR
  change 1 ≤ log (8*sourceS κ n:ℕ) at hlog
  change (log (8*sourceS κ n:ℕ))^2/((8*sourceS κ n:ℕ):ℝ)<1/16 at hs
  have hRp : (0:ℝ)<(8*sourceS κ n:ℕ) := by linarith
  have hspos : 0 < sourceS κ n := by
    have hh : 0 < 8*sourceS κ n := by exact_mod_cast hRp
    omega
  have hceilLo := Nat.le_ceil ((log (8*sourceS κ n:ℕ))^2)
  have hceilHi := (Nat.ceil_lt_add_one (sq_nonneg (log (8*sourceS κ n:ℕ)))).le
  have hr0pos : 0 < Percolation.initialRadius (8*sourceS κ n) := by
    have hh : (0:ℝ)<(Nat.ceil ((log (8*sourceS κ n:ℕ))^2):ℝ) := by nlinarith
    exact_mod_cast hh
  refine ⟨hspos, hr0pos, ?_, hlog⟩
  have hsq := (div_lt_iff₀ hRp).mp hs
  have hh : (Percolation.initialRadius (8*sourceS κ n):ℝ) ≤ sourceS κ n := by
    unfold Percolation.initialRadius
    push_cast at hR hsq hceilHi ⊢
    nlinarith
  exact_mod_cast hh

/-- Final parameter connection for the actual indexed covering. On the
small-cluster event, neither the influence/overlap absorption nor the `I+J`
comparison is an extra premise. The final incidence rate comes from the
actual closure coloring. -/
theorem covering_parameters (d : ℕ) (hd : 2 ≤ d) (κ ρ : ℝ)
    (hκ : 1 ≤ κ) (hρ : 0 < ρ) :
    ∀ᶠ n : ℕ in atTop, ∀ good : Point d → Prop,
      SmallClusters good n (sourceS κ n) (UpperScale.clusterCutoff κ n) →
      0 < Percolation.initialRadius (8*sourceS κ n) ∧
      Percolation.initialRadius (8*sourceS κ n) ≤ sourceS κ n ∧
      1 ≤ maxBlockSize good n (sourceS κ n) ∧
      maxBlockSize good n (sourceS κ n) ≤
        UpperScale.clusterCutoff κ n*(8*sourceS κ n)^d ∧
      ∀ y ∈ volume n,
        rootInfluence ρ (8*sourceS κ n) (sourceS κ n) (maxBlockSize good n (sourceS κ n)) *
          (J good n (sourceS κ n) y:ℝ) ≤ (I good n (sourceS κ n) y:ℝ)/2 ∧
        I good n (sourceS κ n) y+J good n (sourceS κ n) y ≤ 4*I good n (sourceS κ n) y ∧
        BlockDynamics.coveringRate d / maxBlockSize good n (sourceS κ n) ≤
          (I good n (sourceS κ n) y:ℝ)/(4*colorCount good n (sourceS κ n)) := by
  have hκp : 0 < κ := by linarith
  have hd1 : 1 ≤ d := by omega
  have hA := overlapConstant_pos hd1
  have hCH : 0 ≤ 4+4/ρ := by positivity
  have habs := (UpperScale.clusterCutoff_tendsto hκp).eventually
    (UpperScale.overlap_absorption d hd1 (4+4/ρ) (overlapConstant d) hCH hA)
  have hL := (UpperScale.clusterCutoff_tendsto hκp).eventually (eventually_ge_atTop 1)
  have hR := (UpperScale.roundedRadius_tendsto.comp (UpperScale.clusterCutoff_tendsto hκp)).eventually
    (eventually_ge_atTop (overlapConstant d))
  filter_upwards [initialRadius_fits hκp, habs, hL, hR] with n hinit habs hL hR
  intro good hevent
  have hLn : 1 ≤ UpperScale.clusterCutoff κ n := by exact_mod_cast hL
  obtain ⟨hMlo,hMhi⟩ := maxBlockSize_range hinit.1 hLn hevent
  refine ⟨hinit.2.1, hinit.2.2.1, hMlo, hMhi, ?_⟩
  intro y hy
  obtain ⟨hIpos,hJI⟩ := incidence_geometry hd1 hinit.1 hevent hy
  have hI : (0:ℝ)<I good n (sourceS κ n) y := by exact_mod_cast hIpos
  have hM : (0:ℝ)≤maxBlockSize good n (sourceS κ n) := by positivity
  have hMb : (maxBlockSize good n (sourceS κ n):ℝ) ≤
      (UpperScale.clusterCutoff κ n:ℝ)*(8*sourceS κ n:ℕ)^d := by exact_mod_cast hMhi
  have habs' := habs (maxBlockSize good n (sourceS κ n)) (I good n (sourceS κ n) y)
    (J good n (sourceS κ n) y) hM hMb hI (by positivity) hJI
  have hHJ := mul_le_mul_of_nonneg_right (rootInfluence_le (M := maxBlockSize good n (sourceS κ n)) hρ hinit.2.2.2)
    (Nat.cast_nonneg (J good n (sourceS κ n) y) : (0:ℝ)≤_)
  refine ⟨hHJ.trans habs', ?_, ?_⟩
  · change overlapConstant d ≤ ((8*sourceS κ n:ℕ):ℝ) at hR
    have hh := mul_le_mul_of_nonneg_left hR
      (Nat.cast_nonneg (J good n (sourceS κ n) y) : (0:ℝ)≤_)
    have hJ : (J good n (sourceS κ n) y:ℝ) ≤ I good n (sourceS κ n) y := by nlinarith
    have hh' : J good n (sourceS κ n) y ≤ I good n (sourceS κ n) y := by exact_mod_cast hJ
    omega
  · let yp : ↥(volume (d := d) n) := ⟨y,hy⟩
    exact BlockDynamics.covering_incidence_ratio hinit.1 hevent yp

end Paper09.UpperParameters
