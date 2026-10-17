import Paper09
import Paper09.Main
import Paper09.SoftShell
import Paper09.Defects
import Paper09.Spectral

/-!
# Solution side of the official Comparator.

Each declaration matches `Verification.Challenge` in type and is witnessed
by a closed proof from the `Paper09` library.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
local instance (priority := 2000) verificationSumDecidableEq {I O : Type*} : DecidableEq (I ⊕ O) :=
  Classical.decEq _

open Finset BigOperators Classical Real Filter MeasureTheory Paper09 Paper09.Gaussian Paper09.LatticeGeometry
open scoped Topology

namespace Verification.Challenge

/-- Lemma 2.2 engine (soft-shell Rayleigh comparison). -/
theorem lemma_2_2_engine {α : Type*} [Fintype α]
    {G : Paper09.UpdateGraph α} {ν μ : Paper09.FinProb α} {D gapν : ℝ}
    (f : α → ℝ)
    (hgap : G.dirichlet ν f ≤ gapν * Paper09.FinProb.variance ν f)
    (hlo : ∀ y, exp (-D) * ν.w y ≤ μ.w y)
    (hhi : ∀ y, μ.w y ≤ exp D * ν.w y) :
    G.dirichlet μ f * Paper09.FinProb.variance ν f
      ≤ exp (2 * D) * (gapν * Paper09.FinProb.variance ν f * Paper09.FinProb.variance μ f) :=
  Paper09.lemma_2_2_engine f hgap hlo hhi

/-- Lemma 2.2 with `D = 2A + b k`. -/
theorem lemma_2_2_fixed_shell {α : Type*} [Fintype α]
    {G : Paper09.UpdateGraph α} {ν μ : Paper09.FinProb α} {A b k gapν : ℝ}
    (f : α → ℝ)
    (hgap : G.dirichlet ν f ≤ gapν * Paper09.FinProb.variance ν f)
    (hA : 0 ≤ A) (hb : 0 ≤ b) (hk : 0 ≤ k)
    (hlo : ∀ y, exp (- (2 * A + b * k)) * ν.w y ≤ μ.w y)
    (hhi : ∀ y, μ.w y ≤ exp (2 * A + b * k) * ν.w y) :
    G.dirichlet μ f * Paper09.FinProb.variance ν f
      ≤ exp (4 * A + 2 * b * k) * (gapν * Paper09.FinProb.variance ν f * Paper09.FinProb.variance μ f) :=
  Paper09.lemma_2_2_fixed_shell f hgap hA hb hk hlo hhi

/-- Lemma 2.3 defect moments (2.5). -/
theorem lemma_2_3_moments (n : ℕ) (q b : ℝ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hb : 0 ≤ b) :
    (∑ k ∈ Finset.range (n + 1),
        ((n.choose k : ℝ) * q ^ k * (1 - q) ^ (n - k)) * exp (b * k))
        ≤ exp ((n : ℝ) * q * (exp b - 1)) ∧
    exp (-b * (n : ℝ) * q)
        ≤ (∑ k ∈ Finset.range (n + 1),
        ((n.choose k : ℝ) * q ^ k * (1 - q) ^ (n - k)) * exp (-b * k)) :=
  Paper09.lemma_2_3_moments n q b hq hq1 hb

/-- Lemma 2.3 gap bound (2.6). -/
theorem lemma_2_3_gap (n : ℕ) (q b A gapπ gapν : ℝ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hb : 0 ≤ b) (hA : 0 ≤ A) (hgapν : 0 ≤ gapν)
    (hsoft : gapπ ≤ gapν * exp (4 * A)
      * ((∑ k ∈ Finset.range (n + 1),
          ((n.choose k : ℝ) * q ^ k * (1 - q) ^ (n - k)) * exp (b * k))
      / (∑ k ∈ Finset.range (n + 1),
          ((n.choose k : ℝ) * q ^ k * (1 - q) ^ (n - k)) * exp (-b * k)))) :
    gapπ ≤ gapν * exp (4 * A + (n : ℝ) * q * (exp b - 1 + b)) :=
  Paper09.lemma_2_3_gap n q b A gapπ gapν hq hq1 hb hA hgapν hsoft

/-- Scalar exponential inequalities used in Appendix A.1; no semigroup claim. -/
theorem lemma_A_1_full {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2) :
    (∀ t gap : ℝ, 0 ≤ t → 0 < gap → exp (-t * gap) / 2 > 1 / 4 →
        t < log 2 / gap) ∧
    (∀ t gap πmin : ℝ, 0 < πmin → 0 < gap →
        log (1 / (ε * πmin)) / gap ≤ t →
        exp (- t * gap) * (1 / πmin) ≤ 1 / ε) :=
  Paper09.lemma_A_1_full hε hε'

/-- Auxiliary first-log bounds, conditional on the exponential endpoints. -/
theorem theorem_1_3_two_sided {d c C : ℝ}
    (hd : 2 ≤ d) (hc : 0 < c) (hC : 0 < C) :
    let a := Paper09.aExp d
    0 < a ∧ a < 1 ∧
    ∀ n Y, 3 ≤ n → 0 < Y →
      exp (c * (log n / log (log n)) ^ a) ≤ Y →
      Y ≤ exp (C * (log n) ^ a * (log (log n)) ^ (d - 1)) →
      c * (log n / log (log n)) ^ a ≤ log Y ∧
      log Y ≤ C * (log n) ^ a * (log (log n)) ^ (d - 1) :=
  Paper09.theorem_1_3_two_sided hd hc hC

/-- Corollary 1.4 exponent. -/
theorem corollary_1_4 : Paper09.aExp 2 = 1 / 2 :=
  Paper09.corollary_1_4

/-- Prop 2.1 island gap cost (2.9). -/
theorem gap_bound_on_island (c0 ε0 m d qH0 b0 : ℝ)
    (hm : 0 < m) (hd : 0 < d) (hq : 0 ≤ qH0) (hb0 : 0 ≤ b0)
    (hε : ε0 = c0 / 16)
    (hH : 2 * d * qH0 * (exp b0 - 1 + b0) ≤ c0 / 4) :
    -c0 * m ^ (d - 1) + 4 * ε0 * m ^ (d - 1)
        + 2 * d * m ^ (d - 1) * qH0 * (exp b0 - 1 + b0)
      ≤ -(c0 / 2) * m ^ (d - 1) :=
  Paper09.gap_bound_on_island c0 ε0 m d qH0 b0 hm hd hq hb0 hε hH

/-- Lem 3.2 binomial tail. -/
theorem binomial_tail_estimate (d p r : ℝ)
    (hd : 1 ≤ d) (hp : 0 ≤ p) (hp' : p < 1 / (20 * d)) (hr : 1 ≤ r) :
    (2 * d * exp 1 * p) ^ r ≤ (exp 1 / 10) ^ r :=
  Paper09.binomial_tail_estimate d p r hd hp hp' hr

/-- Lem 3.5 ideal-step algebra (3.15). -/
theorem ideal_step_one_site (Iy Jy Q HR : ℝ)
    (hI : 0 < Iy) (hQ : 0 < Q) (hJ : 0 ≤ Jy) (hHR : 0 ≤ HR)
    (hHRJ : HR * Jy ≤ Iy / 2) :
    1 - Iy / Q + HR * Jy / Q ≤ 1 - Iy / (2 * Q) :=
  Paper09.ideal_step_one_site Iy Jy Q HR hI hQ hJ hHR hHRJ

/-- Lem 3.6 simulated-step error absorption. -/
theorem simulated_error_absorbed (M Iy Jy Q cstar : ℝ)
    (hM : 1 ≤ M) (hI : 0 < Iy) (hQ : 0 < Q) (hJ : 0 ≤ Jy)
    (hc : 0 < cstar) (hc' : cstar ≤ 1 / 32)
    (hIJ : Iy + Jy ≤ 4 * Iy) :
    2 * M * (cstar / M ^ 2) * (Iy + Jy) / Q ≤ Iy / (4 * Q) :=
  Paper09.simulated_error_absorbed M Iy Jy Q cstar hM hI hQ hJ hc hc' hIJ



theorem gibbs_soft_shell_sum {I O : Type*} [Fintype I] [Fintype O] [Nonempty I]
    (Λ : Paper09.Lattice (I ⊕ O)) (h : I ⊕ O → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset O) (hS : ∀ i o, Λ.adj (Sum.inl i) (Sum.inr o) → o ∈ S)
    (ζ : O → Spin) :
    let p := gibbs Λ h β univ ∅ (fun _ => 0)
    let ν := sumInteriorGibbs Λ (fun _ => 0) β ζ
    let b := 4 * β * (shellDegree Λ Lattice.leftSites (Lattice.rightShell S) : ℝ)
    spectralGap (V := I ⊕ O) p ≤ spectralGap (V := I) ν *
      exp (4 * fieldMass h Lattice.leftSites) *
        (p.expect (fun η => exp (b * (defectCount S ζ (fun o => η (Sum.inr o)) : ℝ))) /
          p.expect (fun η => exp (-b * (defectCount S ζ (fun o => η (Sum.inr o)) : ℝ)))) :=
  Paper09.gibbs_soft_shell_sum Λ h β hβ S hS ζ

theorem gibbs_soft_shell_defect_gap {I O : Type*} [Fintype I] [Fintype O] [Nonempty I]
    (Λ : Paper09.Lattice (I ⊕ O)) (h : I ⊕ O → ℝ) (β H d : ℝ) (hβ : 0 ≤ β)
    (hdeg : (Λ.maxDegree : ℝ) ≤ 2 * d)
    (S : Finset O) (hS : ∀ i o, Λ.adj (Sum.inl i) (Sum.inr o) → o ∈ S)
    (ζ : O → Spin) (hh : ∀ o ∈ S, H ≤ spinVal (ζ o) * h (Sum.inr o)) :
    let p := gibbs Λ h β univ ∅ (fun _ => 0)
    let ν := sumInteriorGibbs Λ (fun _ => 0) β ζ
    let b := 4 * β * (shellDegree Λ Lattice.leftSites (Lattice.rightShell S) : ℝ)
    spectralGap (V := I ⊕ O) p ≤ spectralGap (V := I) ν *
      exp (4 * fieldMass h Lattice.leftSites + (S.card : ℝ) * qH H d β *
        (exp b - 1 + b)) :=
  Paper09.gibbs_soft_shell_defect_gap Λ h β H d hβ hdeg S hS ζ hh

theorem lemma_2_3_gibbs {V : Type*} [Fintype V]
    (Λ : Paper09.Lattice V) (h : V → ℝ) (β H d b : ℝ) (B T S : Finset V)
    (hBT : Disjoint B T) (hSB : S ⊆ B) (φ ζ : V → Spin)
    (hβ : 0 ≤ β) (hb : 0 ≤ b) (hdeg : (Λ.maxDegree : ℝ) ≤ 2 * d)
    (hh : ∀ x ∈ S, H ≤ spinVal (ζ x) * h x) :
    (gibbs Λ h β B T φ).expect (fun η => exp (b * (defectCount S ζ η : ℝ)))
      ≤ exp ((S.card : ℝ) * qH H d β * (exp b - 1)) ∧
    exp (-b * (S.card : ℝ) * qH H d β) ≤
      (gibbs Λ h β B T φ).expect (fun η => exp (-b * (defectCount S ζ η : ℝ))) :=
  Paper09.lemma_2_3_gibbs Λ h β H d b B T S hBT hSB φ ζ hβ hb hdeg hh

theorem lemma_A_2_local_gap (d : ℕ) (β : ℝ) (hd : 2 ≤ d) (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset (LatticeGeometry.Point d)), A.Nonempty →
      ∀ (Λ : Paper09.Lattice ↥A),
      (∀ x y : ↥A, Λ.adj x y ↔ LatticeGeometry.Adj x.val y.val) →
      ∀ (h : ↥A → ℝ) (S : Finset ↥A) (φ : ↥A → Spin),
      C⁻¹ * exp (-C * (A.card : ℝ) ^ exponentA d) ≤
        spectralGap (gibbs Λ h β univ S φ) :=
  Paper09.lemma_A_2_local_gap d β hd hβ

theorem griffithsStatistic_tendstoInMeasure_of_bounds
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Y : ℕ → Ω → ℝ)
    {c C a b : ℝ} (hc : 0 < c) (hC : 0 < C) (ha : 0 < a)
    (hgood : Tendsto (fun n : ℕ => μ {ω | ¬
      (exp (c * (log (n : ℝ) / log (log (n : ℝ))) ^ a) ≤ Y n ω ∧
        Y n ω ≤ exp (C * (log (n : ℝ)) ^ a * (log (log (n : ℝ))) ^ b))})
      atTop (𝓝 0)) :
    TendstoInMeasure μ (fun (n : ℕ) ω => griffithsStatistic (n : ℝ) (Y n ω)) atTop (fun _ => a) :=
  Paper09.griffithsStatistic_tendstoInMeasure_of_bounds μ Y hc hC ha hgood

theorem strong_disorder (d β σ : ℝ) (hd : 1 ≤ d) (hβ : 0 < β)
    (hσ : sigma0 d β ≤ σ) :
    ∃ K > 0, rho K d β < 1 / (40 * d) ∧
      (law σ).real {x | |x| ≤ K} < 1 / (40 * d) :=
  Paper09.Gaussian.strong_disorder d β σ hd hβ hσ

theorem island_log_cost_geometric (σ ε H : ℝ) (hσ : 0 < σ) (hε : 0 < ε)
    (d : ℕ) :
    ∃ C₂ > 0, ∀ (B S : Type*) [Fintype B] [Fintype S] (ζ : S → Bool)
      (m : ℕ), 2 ≤ m → Fintype.card B = m ^ d →
      Fintype.card S = 2 * d * m ^ (d - 1) →
      -Real.log ((Measure.pi (fun _ : B ⊕ S => law σ)).real
        (islandEvent B S ζ (ε / m) H)) ≤ C₂ * (m : ℝ) ^ d * Real.log m :=
  Paper09.Gaussian.island_log_cost_geometric σ ε H hσ hε d

theorem exists_ordering_cutwidth {d : ℕ} (hd : 2 ≤ d) (A : Finset (Paper09.LatticeGeometry.Point d))
    (Λ : Paper09.Lattice ↥A)
    (hΛ : ∀ x y : ↥A, Λ.adj x y ↔ Adj x.val y.val) :
    ∃ order : Fin A.card ≃ ↥A, ∀ j ≤ A.card,
      ((Paper09.CanonicalPath.cutEdges Λ
        (Paper09.CanonicalPath.initialSegment order j)).card : ℝ) ≤
          cutwidthConstant d * (A.card : ℝ) ^ Paper09.exponentA d :=
  Paper09.LatticeGeometry.exists_ordering_cutwidth hd A Λ hΛ

open Paper09.Percolation Paper09.BlockCovering Paper09.BlockColoring Paper09.BlockDynamics
theorem proposition_2_1_actual (d : ℕ) (β σ : ℝ) (hd : 2 ≤ d) (hβ : 0 < β)
    (hσ : 0 < σ) (hslow : Paper09.RFIM.SurfaceSlowPureBoxes d β) :
    ∃ c > 0, Tendsto (fun n : ℕ => (Paper09.RFIM.environmentLaw d σ)
      {h | ¬ exp (c * (log (n:ℝ) / log (log (n:ℝ))) ^ Paper09.exponentA d) ≤
        min (Paper09.RFIM.relaxationTime d n β h) (Paper09.RFIM.mixingTime d n β h)})
      atTop (𝓝 0) :=
  Paper09.RFIM.proposition_2_1 d β σ hd hβ hσ hslow

theorem lemma_A_1_reversible_actual {α : Type*} [Fintype α] [Nontrivial α]
    (C : Paper09.ReversibleMixing.Chain α) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1 / 2) :
    Real.log 2 * Paper09.ReversibleMixing.relaxationTime C ≤
      Paper09.ReversibleMixing.mixingTime C (1 / 4) ∧
    Paper09.ReversibleMixing.mixingTime C ε ≤
      Paper09.ReversibleMixing.relaxationTime C * Real.log
        (1 / (ε * Paper09.ReversibleMixing.minimumWeight C)) :=
  Paper09.ReversibleMixing.lemma_A_1 C ε hε hε1

theorem lemma_3_2_real {d : ℕ} (hd : 0 < d) (σ K ρ : ℝ)
    (hρ : 0 ≤ ρ) (hρsmall : ρ < 1 / (40 * (d : ℝ)))
    (hweak : (Gaussian.law σ).real {x | |x| ≤ K} < 1 / (40 * (d : ℝ))) :
    ∃ R0 : ℕ, ∃ κ : ℝ, 0 < κ ∧ ∀ R n : ℕ, ∀ L : ℝ,
      R0 ≤ R → R ≤ n → 8 ∣ R → κ * Real.log (n : ℝ) ≤ L →
        1 - Real.exp (-L) ≤ (RFIM.environmentLaw d σ).real
          {h | SmallClustersReal
            (goodLabel K ρ R (initialRadius R) (R / 8) h) n R L} :=
  Paper09.Percolation.lemma_3_2_real hd σ K ρ hρ hρsmall hweak

theorem lemma_3_3 {d : ℕ} {good : Paper09.LatticeGeometry.Point d → Prop} {n s L : ℕ}
    (hs : 0 < s) (hL : 1 ≤ L) (hevent : SmallClusters good n s L) :
    maxBlockSize good n s ≤ L*(8*s)^d ∧
    (∀ y ∈ volume n,
      (8*s)^d ≤ 4^d * I good n s y ∧
        I good n s y ≤ 2*(8*s)^d ∧ J good n s y ≤ 4*d*(8*s)^(d-1)) ∧
    ∀ (i : BlockIndex good n s) y,
      y ∈ boundary (volume n) (block i) → ∃ k, good k ∧ Near (8*s) y (center s k) :=
  Paper09.BlockCovering.lemma_3_3 hs hL hevent

theorem gibbs_boundary_influence_paper36 {V : Type*} [Fintype V] {d : ℕ} (Λ : Paper09.Lattice V)
    (h : LatticeGeometry.Point d → ℝ) (β K : ℝ)
    (f : V → LatticeGeometry.Point d) (hf : Function.Injective f)
    (hadj : ∀ ⦃x z⦄, Λ.adj x z → LatticeGeometry.Adj (f x) (f z))
    (B T : Finset V) (hBT : Disjoint B T) (φ φ' : Config V) (y : V) (hyB : y ∉ B)
    (hβ : 0 ≤ β) (hdeg : (Λ.maxDegree : ℝ) ≤ 2 * (d : ℝ))
    (hboundary : ∀ r ∈ T, φ r ≠ φ' r → r = y)
    (R : ℕ) (v : LatticeGeometry.Point d) (hdiv : 8 ∣ R)
    (hlog : 1 ≤ (Real.log (R : ℝ)) ^ 2) (hcut : Percolation.initialRadius R ≤ R / 8)
    (hgood : Percolation.goodLabel K (rho K (d : ℝ) β) R
      (Percolation.initialRadius R) (R / 8) h v)
    (hy : f y ∈ Percolation.latticeCube (Percolation.coarseCenter R v) R) :
    hammingWasserstein
      (gibbs Λ (fun z => h (f z)) β B T φ)
      (gibbs Λ (fun z => h (f z)) β B T φ') ≤
      (2 + 2 / rho K (d : ℝ) β) * (Real.log (R : ℝ)) ^ 2 +
        (2 + 2 / rho K (d : ℝ) β) * (B.card : ℝ) * Real.exp (-(R : ℝ) / 8) :=
  Paper09.DisagreementGoodRoot.gibbs_boundary_influence_paper36 Λ h β K f hf hadj B T hBT φ φ' y hyB hβ hdeg hboundary R v hdiv hlog hcut hgood hy

theorem lemma_3_5 {d : ℕ} (hd : 2 ≤ d) (K β κ : ℝ)
    (hβ : 0 ≤ β) (hκ : 1 ≤ κ) :
    ∀ᶠ n : ℕ in atTop,
      ∃ hs : 0 < UpperParameters.sourceS κ n,
        ∀ h : Paper09.LatticeGeometry.Point d → ℝ,
          ∀ hevent : SmallClusters (Paper09.IdealContraction.sourceGood K β (UpperParameters.sourceS κ n) h)
            n (UpperParameters.sourceS κ n) (UpperScale.clusterCutoff κ n),
          ∀ η ξ : Config ↥(volume (d := d) n),
            hammingWasserstein (Paper09.IdealContraction.canonicalKernel K β h hs hevent η)
                (Paper09.IdealContraction.canonicalKernel K β h hs hevent ξ) ≤
              (1 - coveringRate d /
                maxBlockSize (Paper09.IdealContraction.sourceGood K β (UpperParameters.sourceS κ n) h)
                  n (UpperParameters.sourceS κ n)) * hammingR η ξ :=
  Paper09.IdealContraction.lemma_3_5 hd K β κ hβ hκ

open Paper09.RFIM
local instance (priority := 2000) verificationVolumeDecidableEq {d n : ℕ} :
    DecidableEq ↥(Paper09.BlockCovering.volume (d := d) n) := Classical.decEq _
set_option maxHeartbeats 1500000
set_option maxRecDepth 4000
theorem lemma_3_6 (d : ℕ) (K β σ κ : ℝ) (hd : 2 ≤ d) (hβ : 0 < β)
    (hσ : 0 ≤ σ) (hκ : 1 ≤ κ) :
    ∃ C : ℝ, 1 ≤ C ∧ 1 ≤ C*coveringRate d ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ hs : 0 < UpperParameters.sourceS κ n,
          ∀ (h : Paper09.LatticeGeometry.Point d → ℝ)
            (hevent : SmallClusters (Paper09.IdealContraction.sourceGood K β (UpperParameters.sourceS κ n) h)
              n (UpperParameters.sourceS κ n) (UpperScale.clusterCutoff κ n)),
            (∀ x ∈ volume n, |h x| ≤ σ*sqrt (8*log (((2*n+1)^d:ℕ):ℝ))) →
            let s := UpperParameters.sourceS κ n
            let M := maxBlockSize (Paper09.IdealContraction.sourceGood K β s h) n s
            let T := UpperScale.stepTime d C (8*s) (UpperScale.clusterCutoff κ n) M (((2*n+1)^d:ℕ):ℝ)
            0 ≤ T ∧ ∀ η ξ : Config ↥(volume (d := d) n),
              hammingWasserstein (Paper09.SimulatedContraction.canonicalKernel K β h hs hevent T η)
                  (Paper09.SimulatedContraction.canonicalKernel K β h hs hevent T ξ) ≤
                (1-coveringRate d/M)*hammingR η ξ :=
  Paper09.SimulatedContraction.lemma_3_6 d K β σ κ hd hβ hσ hκ

theorem theorem_1_3_bounds_actual (d : ℕ) (β σ : ℝ) (hd : 2 ≤ d) (hβ : 0 < β)
    (hσ : 0 < σ) (hslow : SurfaceSlowPureBoxes d β)
    (hstrong : StrongGaussianDisorder d β σ) :
    ∃ c > 0, ∃ C > 0, Tendsto (fun n : ℕ => (environmentLaw d σ)
      {h | ¬(exp (c*(log (n:ℝ)/log (log (n:ℝ)))^exponentA d) ≤
          min (relaxationTime d n β h) (mixingTime d n β h) ∧
        max (relaxationTime d n β h) (mixingTime d n β h) ≤
          exp (C*(log (n:ℝ))^exponentA d*(log (log (n:ℝ)))^((d:ℝ)-1)))}) atTop (𝓝 0) :=
  Paper09.RFIM.theorem_1_3_bounds d β σ hd hβ hσ hslow hstrong

theorem theorem_1_3_actual (d : ℕ) (β σ : ℝ) (hd : 2 ≤ d) (hβ : 0 < β)
    (hσ : 0 < σ) (hslow : SurfaceSlowPureBoxes d β)
    (hstrong : StrongGaussianDisorder d β σ) :
    (∃ c > 0, ∃ C > 0, Tendsto (fun n : ℕ => (environmentLaw d σ)
      {h | ¬(exp (c*(log (n:ℝ)/log (log (n:ℝ)))^exponentA d) ≤
          min (relaxationTime d n β h) (mixingTime d n β h) ∧
        max (relaxationTime d n β h) (mixingTime d n β h) ≤
          exp (C*(log (n:ℝ))^exponentA d*(log (log (n:ℝ)))^((d:ℝ)-1)))}) atTop (𝓝 0)) ∧
    TendstoInMeasure (environmentLaw d σ)
      (fun (n : ℕ) h => log (log (max (exp 1) (relaxationTime d n β h))) / log (log (n:ℝ)))
      atTop (fun _ => exponentA d) ∧
    TendstoInMeasure (environmentLaw d σ)
      (fun (n : ℕ) h => log (log (max (exp 1) (mixingTime d n β h))) / log (log (n:ℝ)))
      atTop (fun _ => exponentA d) :=
  Paper09.RFIM.theorem_1_3 d β σ hd hβ hσ hslow hstrong

open Paper09.RFIM
theorem proposition_3_1_actual (d : ℕ) (β σ : ℝ) (hd : 2 ≤ d) (hβ : 0 < β)
    (hσ : 0 < σ) (hstrong : StrongGaussianDisorder d β σ) :
    ∃ C > 0, Tendsto (fun n : ℕ => (environmentLaw d σ)
      {h | ¬ max (relaxationTime d n β h) (mixingTime d n β h) ≤
        exp (C*(log (n:ℝ))^exponentA d*(log (log (n:ℝ)))^(d-1))}) atTop (𝓝 0) :=
  Paper09.RFIM.proposition_3_1 d β σ hd hβ hσ hstrong

/-- Source S2.p14, with its real polynomial exponent and eventual small-ball cutoff. -/
theorem iid_island_log_cost_geometric (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (d : ℕ) (ε H : ℝ) (hε : 0 < ε) (hsmall : (∃ (c : ℝ), 0 < c ∧ ∃ (α : ℝ), 0 < α ∧ ∃ (u₀ : ℝ), 0 < u₀ ∧
      ∀ u : ℝ, 0 < u → u ≤ u₀ → c*u^α ≤ ν.real {x : ℝ | |x| ≤ u}))
    (htailPos : 0 < ν.real (Set.Ici H)) (htailNeg : 0 < ν.real (Set.Iic (-H))) :
    ∃ C > 0, ∃ m₀ : ℕ, ∀ (B S : Type*) [Fintype B] [Fintype S] (ζ : S → Bool)
      (m : ℕ), 2 ≤ m → m₀ ≤ m → Fintype.card B = m^d →
      Fintype.card S ≤ 2*d*m^(d-1) →
      0 < (Measure.pi (fun _ : B ⊕ S => ν)).real (Gaussian.islandEvent B S ζ (ε/m) H) ∧
      -log ((Measure.pi (fun _ : B ⊕ S => ν)).real (Gaussian.islandEvent B S ζ (ε/m) H)) ≤
        C*(m:ℝ)^d*log m :=
  Paper09.RFIM.iid_island_log_cost_geometric ν d ε H hε hsmall htailPos htailNeg

theorem proposition_2_1_iid_actual (d : ℕ) (β : ℝ) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hd : 2 ≤ d) (hβ : 0 < β)
    (hsmall : (∃ (c : ℝ), 0 < c ∧ ∃ (α : ℝ), 0 < α ∧ ∃ (u₀ : ℝ), 0 < u₀ ∧
      ∀ u : ℝ, 0 < u → u ≤ u₀ → c*u^α ≤ ν.real {x : ℝ | |x| ≤ u}))
    (hsource : ∃ (c₀ : ℝ) (seq : ℕ → ℕ) (H : ℝ),
      0 < c₀ ∧ StrictMono seq ∧
      Tendsto (fun k => (seq (k+1):ℝ)/(seq k:ℝ)) atTop (𝓝 1) ∧
      (∀ᶠ k in atTop, ∃ ζ : Paper09.RFIM.Point d → Spin,
        pureBoxGap d (seq k) β ζ ≤ exp (-c₀*(seq k:ℝ)^(d-1))) ∧
      0 < H ∧
      2*(d:ℝ)*qH H d β*(exp (8*(d:ℝ)*β)-1+8*(d:ℝ)*β) ≤ c₀/4 ∧
      0 < ν.real (Set.Ici H) ∧ 0 < ν.real (Set.Iic (-H))) :
    ∃ c > 0, Tendsto (fun n : ℕ => (iidEnvironmentLaw d ν)
      {h | ¬ exp (c*(log (n:ℝ)/log (log (n:ℝ)))^exponentA d) ≤
        min (relaxationTime d n β h) (mixingTime d n β h)}) atTop (𝓝 0) :=
  Paper09.RFIM.proposition_2_1_iid d β ν hd hβ hsmall hsource

end Verification.Challenge
