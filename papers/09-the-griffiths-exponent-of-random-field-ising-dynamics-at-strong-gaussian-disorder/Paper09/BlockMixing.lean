import Paper09.RFIM
import Paper09.MixingTimes
import Paper09.GibbsShell

open Finset BigOperators Classical Real
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 800000
namespace Paper09.RFIM

local instance (priority := 2000) blockMixPointDecEq (d : ℕ) : DecidableEq (Point d) := Classical.decEq _
local instance (priority := 2000) blockMixSiteDecEq {d : ℕ} (A : Finset (Point d)) : DecidableEq ↥A := Classical.decEq _

private theorem interaction_abs_le {V : Type*} [Fintype V]
    (Λ : Lattice V) (β : ℝ) (hβ : 0 ≤ β) (η : Config V) :
    |Λ.interaction β univ η| ≤ β/2 * Fintype.card V * Λ.maxDegree := by
  unfold Lattice.interaction
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ β/2)]
  apply (mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (by positivity : 0 ≤ β/2)).trans
  have hrow (x : V) : |∑ y : V, if Λ.adj x y then spinVal (η x)*spinVal (η y) else 0| ≤ Λ.maxDegree := by
    calc _ ≤ ∑ y : V, |if Λ.adj x y then spinVal (η x)*spinVal (η y) else 0| := abs_sum_le_sum_abs _ _
      _ = ((univ.filter (Λ.adj x)).card : ℝ) := by
        simp only [abs_ite, abs_mul, abs_spinVal, one_mul, abs_zero]
        rw [← Finset.sum_boole]
      _ ≤ Λ.maxDegree := by exact_mod_cast Λ.degree_le x
  have hs : (∑ x : V, |∑ y : V, if Λ.adj x y then spinVal (η x)*spinVal (η y) else 0|) ≤
      (Fintype.card V : ℝ)*Λ.maxDegree := by
    calc _ ≤ ∑ _x : V, (Λ.maxDegree : ℝ) := sum_le_sum (fun x _ => hrow x)
      _ = _ := by simp
  nlinarith

private theorem effectiveField_abs_le {d : ℕ} (A : Finset (Point d)) (h : Point d → ℝ)
    (β hmax : ℝ) (hβ : 0 ≤ β) (hh : ∀ x ∈ A, |h x| ≤ hmax)
    (ζ : Point d → Spin) (x : ↥A) :
    |effectiveField A h β ζ x| ≤ hmax + 2*(d:ℝ)*β := by
  have hs : |∑ y ∈ externalBoundary A,
      if LatticeGeometry.Adj x.val y then spinVal (ζ y) else 0| ≤ 2*(d:ℝ) := by
    calc _ ≤ ∑ y ∈ externalBoundary A,
          |if LatticeGeometry.Adj x.val y then spinVal (ζ y) else 0| := abs_sum_le_sum_abs _ _
      _ = (((externalBoundary A).filter (LatticeGeometry.Adj x.val)).card : ℝ) := by
        simp only [abs_ite, abs_spinVal, abs_zero]
        rw [← Finset.sum_boole]
      _ ≤ ((LatticeGeometry.neighbors x.val).card : ℝ) := by
        apply Nat.cast_le.mpr
        apply card_le_card
        intro y hy
        exact LatticeGeometry.mem_neighbors.mpr (mem_filter.mp hy).2
      _ ≤ 2*(d:ℝ) := by exact_mod_cast LatticeGeometry.card_neighbors_le x.val
  unfold effectiveField
  have ha := abs_add_le (h x.val) (β * ∑ y ∈ externalBoundary A,
    if LatticeGeometry.Adj x.val y then spinVal (ζ y) else 0)
  rw [abs_mul, abs_of_nonneg hβ] at ha
  have hb := mul_le_mul_of_nonneg_left hs hβ
  linarith [hh x.val x.property]

/-- The actual pinned Hamiltonian has a field-uniform linear volume bound. -/
theorem pinned_energy_abs_le {d : ℕ} (A : Finset (Point d)) (h : Point d → ℝ)
    (β hmax : ℝ) (hβ : 0 ≤ β) (hh : ∀ x ∈ A, |h x| ≤ hmax)
    (ζ : Point d → Spin) (η : Config ↥A) :
    |(domainLattice A).interaction β univ η +
      Lattice.fieldEnergy (effectiveField A h β ζ) univ η| ≤
        (A.card : ℝ)*(hmax+3*(d:ℝ)*β) := by
  have hi := interaction_abs_le (domainLattice A) β hβ η
  have hf := fieldEnergy_abs_le (effectiveField A h β ζ) univ η
  have hm : fieldMass (effectiveField A h β ζ) univ ≤
      (A.card : ℝ)*(hmax+2*(d:ℝ)*β) := by
    unfold fieldMass
    calc _ ≤ ∑ _x : ↥A, (hmax+2*(d:ℝ)*β) :=
        sum_le_sum (fun x _ => effectiveField_abs_le A h β hmax hβ hh ζ x)
      _ = _ := by simp; ring
  have ha := abs_add_le ((domainLattice A).interaction β univ η)
    (Lattice.fieldEnergy (effectiveField A h β ζ) univ η)
  have hdeg : ((domainLattice A).maxDegree:ℝ) = 2*(d:ℝ) := by norm_num [domainLattice]
  rw [Fintype.card_coe, hdeg] at hi
  nlinarith

/-- Equation (3.17), proved from the genuine Hamiltonian, actual partition
function, and exactly `2^|A|` configurations. -/
theorem minimumWeight_pinned_lower {d : ℕ} (A : Finset (Point d)) (h : Point d → ℝ)
    (β hmax : ℝ) (hβ : 0 ≤ β) (hhmax : 0 ≤ hmax)
    (hh : ∀ x ∈ A, |h x| ≤ hmax) (ζ : Point d → Spin) :
    exp (-((2+6*(d:ℝ)*β)*(A.card:ℝ)*(1+hmax))) ≤ minimumWeight (pinnedGibbs A h β ζ) := by
  let K := (A.card:ℝ)*(hmax+3*(d:ℝ)*β)
  let E := fun η : Config ↥A => (domainLattice A).interaction β univ η +
    Lattice.fieldEnergy (effectiveField A h β ζ) univ η
  have hE : ∀ η, |E η| ≤ K := fun η => pinned_energy_abs_le A h β hmax hβ hh ζ η
  have hZ : isingZ (domainLattice A) (effectiveField A h β ζ) β univ ∅ (fun _ => 0) ≤
      (2:ℝ)^A.card * exp K := by
    unfold isingZ
    calc
      _ ≤ ∑ _η : Config ↥A, exp K := by
        apply sum_le_sum; intro η hη
        simp only [isingWeight, Lattice.boundEnergy, sum_empty, sum_const_zero, mul_zero, add_zero]
        exact exp_le_exp.mpr ((le_abs_self (E η)).trans (hE η))
      _ = _ := by simp [Fintype.card_fun, Spin]
  have hw (η : Config ↥A) : exp (-K) ≤
      isingWeight (domainLattice A) (effectiveField A h β ζ) β univ ∅ (fun _ => 0) η := by
    simp only [isingWeight, Lattice.boundEnergy, sum_empty, sum_const_zero, mul_zero, add_zero]
    exact exp_le_exp.mpr (abs_le.mp (hE η)).1
  have hp (η : Config ↥A) : exp (-(A.card:ℝ)*log 2 - 2*K) ≤ (pinnedGibbs A h β ζ).w η := by
    have hden : 0 < (2:ℝ)^A.card * exp K := by positivity
    have hfrac : exp (-K) / ((2:ℝ)^A.card*exp K) ≤ (pinnedGibbs A h β ζ).w η := by
      exact div_le_div₀ (exp_nonneg _) (hw η) (isingZ_pos _ _ _ _ _ _) hZ
    have he : exp (-K) / ((2:ℝ)^A.card*exp K) = exp (-(A.card:ℝ)*log 2 - 2*K) := by
      have ht : (2:ℝ)^A.card = exp ((A.card:ℝ)*log 2) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<2)]
      rw [ht, ← exp_add, ← exp_sub]
      congr 1
      ring
    rwa [he] at hfrac
  apply le_trans _ (hp (minimumWeightState (pinnedGibbs A h β ζ)))
  apply exp_le_exp.mpr
  have hl : log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hq : 0 ≤ (A.card:ℝ) := Nat.cast_nonneg _
  have hdβ : 0 ≤ 6*(d:ℝ)*β := by positivity
  have hh1 := mul_le_mul_of_nonneg_left hl hq
  have hh2 := mul_nonneg hdβ hhmax
  dsimp [K]
  nlinarith

/-- Running the actual local chain longer cannot increase its TV error. -/
theorem heatBath_tv_later {V : Type*} [Fintype V] (p : FinProb (Config V))
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (η : Config V) :
    tvDist (heatBathTransition p t η) p ≤ tvDist (heatBathTransition p s η) p := by
  have he (ξ : Config V) : (heatBathTransition p t η).w ξ =
      (MarkovKernel.push (heatBathTransition p (t-s)) (heatBathTransition p s η)).w ξ := by
    have hh := heatBathTransition_add p s (t-s) hs (sub_nonneg.mpr hst) η ξ
    simpa only [add_sub_cancel] using hh
  have htveq : tvDist (heatBathTransition p t η) p =
      tvDist (MarkovKernel.push (heatBathTransition p (t-s)) (heatBathTransition p s η)) p := by
    unfold tvDist
    simp only [he]
  rw [htveq]
  exact MarkovKernel.tvDist_to_stationary_le _ _ _ (heatBathTransition_stationary p (t-s))

/-- A concrete time above the actual comparison time is a good time for
all initial configurations, not merely an upper bound on a mixing infimum. -/
theorem heatBath_good_later {V : Type*} [Fintype V] (p : FinProb (Config V))
    (hp : ∀ η, 0 < p.w η) (x : V) (δ T : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hT : mixingUpperTime p δ ≤ T) :
    0 ≤ T ∧ ∀ η, tvDist (heatBathTransition p T η) p ≤ δ := by
  obtain ⟨h0, hh⟩ := heatBath_good_upper_time p hp x δ hδ hδ1
  exact ⟨h0.trans hT, fun η => (heatBath_tv_later p _ _ h0 hT η).trans (hh η)⟩

theorem log_minimumWeight_pinned_le {d : ℕ} (A : Finset (Point d)) (h : Point d → ℝ)
    (β hmax : ℝ) (hβ : 0 ≤ β) (hhmax : 0 ≤ hmax)
    (hh : ∀ x ∈ A, |h x| ≤ hmax) (ζ : Point d → Spin) :
    log (1/minimumWeight (pinnedGibbs A h β ζ)) ≤
      (2+6*(d:ℝ)*β)*(A.card:ℝ)*(1+hmax) := by
  have hm : 0 < minimumWeight (pinnedGibbs A h β ζ) :=
    minimumWeight_pos _ (fun _ => div_pos (isingWeight_pos _ _ _ _ _ _ _) (isingZ_pos _ _ _ _ _ _))
  have hl := minimumWeight_pinned_lower A h β hmax hβ hhmax hh ζ
  apply (Real.log_le_iff_le_exp (one_div_pos.mpr hm)).mpr
  have hi := one_div_le_one_div_of_le (exp_pos _) hl
  simpa only [neg_mul, Real.exp_neg, one_div, inv_inv] using hi

/-- Equation (3.17) on the physical Gaussian maximum-field event, with an
explicit constant depending only on dimension, inverse temperature and sigma. -/
theorem log_minimumWeight_on_field_event {d : ℕ} (A : Finset (Point d))
    (h : Point d → ℝ) (β σ M N : ℝ) (hβ : 0 ≤ β) (hσ : 0 ≤ σ)
    (hM : 0 ≤ M) (hqM : (A.card:ℝ) ≤ M)
    (hh : ∀ x ∈ A, |h x| ≤ σ*sqrt (8*log N)) (ζ : Point d → Spin) :
    log (1/minimumWeight (pinnedGibbs A h β ζ)) ≤
      ((2+6*(d:ℝ)*β)*(1+σ*sqrt 8))*M*(1+sqrt (log N)) := by
  have h0 : 0 ≤ σ*sqrt (8*log N) := by positivity
  have hb : 0 ≤ 2+6*(d:ℝ)*β := by positivity
  have hsqrt : sqrt (8*log N) = sqrt 8*sqrt (log N) := sqrt_mul (by norm_num : (0:ℝ)≤8) _
  have hf : 1+σ*sqrt (8*log N) ≤ (1+σ*sqrt 8)*(1+sqrt (log N)) := by
    rw [hsqrt]
    nlinarith [sqrt_nonneg (log N), mul_nonneg hσ (sqrt_nonneg 8)]
  calc log (1/minimumWeight (pinnedGibbs A h β ζ)) ≤
      (2+6*(d:ℝ)*β)*(A.card:ℝ)*(1+σ*sqrt (8*log N)) :=
        log_minimumWeight_pinned_le A h β _ hβ h0 hh ζ
    _ ≤ (2+6*(d:ℝ)*β)*M*(1+σ*sqrt (8*log N)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqM hb) (by positivity)
    _ ≤ (2+6*(d:ℝ)*β)*M*((1+σ*sqrt 8)*(1+sqrt (log N))) :=
      mul_le_mul_of_nonneg_left hf (mul_nonneg hb hM)
    _ = _ := by ring

/-- Actual local mixing comparison, uniform over the physical fields and
all fixed exterior pinnings. The only field premise bounds `|h_x|` on `A`. -/
theorem pinned_mixingUpperTime_bound (d : ℕ) (β : ℝ) (hd : 2 ≤ d) (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset (Point d)), A.Nonempty →
      ∀ (h : Point d → ℝ) (ζ : Point d → Spin) (hmax : ℝ),
      0 ≤ hmax → (∀ x ∈ A, |h x| ≤ hmax) →
      ∀ δ : ℝ, 0 < δ → δ < 1 →
      mixingUpperTime (pinnedGibbs A h β ζ) δ ≤
        C*exp (C*(A.card:ℝ)^exponentA d)*
          ((A.card:ℝ)*(1+hmax)+log (1/δ)) := by
  obtain ⟨Cg, hCg, hgap⟩ := pinned_local_gap d β hd hβ
  let B := 2+6*(d:ℝ)*β
  let K := B+1
  let C := Cg*(K+1)+1
  have hB : 0 < B := by dsimp [B]; positivity
  have hK : 1 ≤ K := by dsimp [K]; linarith
  have hC : 0 < C := by dsimp [C]; positivity
  have hCgC : Cg ≤ C := by dsimp [C]; nlinarith
  have hprodC : Cg*K ≤ C := by dsimp [C]; nlinarith
  refine ⟨C, hC, ?_⟩
  intro A hA h ζ hmax hhmax hh δ hδ hδ1
  let p := pinnedGibbs A h β ζ
  let Q := (A.card:ℝ)^exponentA d
  let J := (A.card:ℝ)*(1+hmax)+log (1/δ)
  have hp : ∀ η, 0 < p.w η := fun _ => div_pos (isingWeight_pos _ _ _ _ _ _ _) (isingZ_pos _ _ _ _ _ _)
  have hmin := minimumWeight_pos p hp
  have hgap0 : 0 < spectralGap p := heatBath_gap_pos p hp ⟨hA.choose, hA.choose_spec⟩
  have hbase : 0 < Cg⁻¹*exp (-Cg*Q) := by positivity
  have hg := hgap A hA h ζ
  change Cg⁻¹*exp (-Cg*Q) ≤ spectralGap p at hg
  have hi : (spectralGap p)⁻¹ ≤ Cg*exp (Cg*Q) := by
    have hi := one_div_le_one_div_of_le hbase hg
    simpa only [one_div, mul_inv_rev, inv_inv, ← Real.exp_neg, neg_mul, neg_neg, mul_comm] using hi
  have hlogδ : 0 ≤ log (1/δ) := Real.log_nonneg ((one_le_div hδ).mpr hδ1.le)
  have hlog : log (1/(δ*minimumWeight p)) ≤ B*(A.card:ℝ)*(1+hmax)+log (1/δ) := by
    have hl := log_minimumWeight_pinned_le A h β hmax hβ.le hhmax hh ζ
    have he : log (1/(δ*minimumWeight p)) = log (1/δ)+log (1/minimumWeight p) := by
      rw [log_div (by norm_num) (mul_pos hδ hmin).ne', log_one,
        log_mul hδ.ne' hmin.ne', log_div (by norm_num) hδ.ne',
        log_div (by norm_num) hmin.ne', log_one]
      ring
    rw [he]
    dsimp [B] at *
    linarith
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hlogK : log (1/(δ*minimumWeight p)) ≤ K*J := by
    have hh0 : 0 ≤ (A.card:ℝ)*(1+hmax) := by positivity
    have hmult := mul_nonneg (sub_nonneg.mpr hK) hlogδ
    dsimp [J, K] at *
    nlinarith
  have he : Cg*exp (Cg*Q)*K ≤ C*exp (C*Q) := by
    have hQ : 0 ≤ Q := by dsimp [Q]; positivity
    have hexp : exp (Cg*Q) ≤ exp (C*Q) := exp_le_exp.mpr (mul_le_mul_of_nonneg_right hCgC hQ)
    have hh := mul_le_mul hprodC hexp (exp_nonneg _) hC.le
    nlinarith
  unfold mixingUpperTime
  rw [div_eq_mul_inv]
  calc log (1/(δ*minimumWeight p)) * (spectralGap p)⁻¹ ≤
      (K*J)*(Cg*exp (Cg*Q)) := mul_le_mul hlogK hi (inv_nonneg.mpr (spectralGap_nonneg p)) (by positivity)
    _ ≤ C*exp (C*Q)*J := by nlinarith [mul_le_mul_of_nonneg_right he hJ]

private theorem volume_surface_identity (d : ℕ) (hd : 1 ≤ d) (L R : ℝ)
    (hL : 0 ≤ L) (hR : 0 ≤ R) :
    (L*R^d)^exponentA d = R^(d-1)*L^exponentA d := by
  rw [Real.mul_rpow hL (pow_nonneg hR d), ← Real.rpow_natCast_mul hR]
  have he : (d:ℝ)*exponentA d = ((d-1:ℕ):ℝ) := by
    unfold exponentA
    rw [Nat.cast_sub hd, Nat.cast_one]
    have hd0 : (d:ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    field_simp
  rw [he, Real.rpow_natCast, mul_comm]

/-- Equations (3.17)--(3.18): one physical time works for every actual pinned
block, boundary condition and starting spin configuration on the field event. -/
theorem pinned_block_mixing (d : ℕ) (β σ cstar : ℝ) (hd : 2 ≤ d) (hβ : 0 < β)
    (hσ : 0 ≤ σ) (hcstar : 0 < cstar) (hcstar1 : cstar < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset (Point d)), A.Nonempty →
      ∀ (h : Point d → ℝ) (ζ : Point d → Spin) (L R M N : ℝ),
      1 ≤ L → 1 ≤ R → 1 ≤ M → 2 ≤ N →
      (A.card:ℝ) ≤ M → (A.card:ℝ) ≤ L*R^d →
      (∀ x ∈ A, |h x| ≤ σ*sqrt (8*log N)) →
      let T := C*exp (C*(R^(d-1)*L^exponentA d)) *
        (M*(1+sqrt (log N))+2*log M+1)
      0 ≤ T ∧ ∀ η, tvDist (heatBathTransition (pinnedGibbs A h β ζ) T η)
        (pinnedGibbs A h β ζ) ≤ cstar/M^2 := by
  obtain ⟨C₀, hC₀, hbound⟩ := pinned_mixingUpperTime_bound d β hd hβ
  let F := 1+σ*sqrt 8
  let K := F+log (1/cstar)+2
  let C := C₀*(K+1)+1
  have hclog : 0 ≤ log (1/cstar) := Real.log_nonneg ((one_le_div hcstar).mpr hcstar1.le)
  have hF : 1 ≤ F := by dsimp [F]; nlinarith [mul_nonneg hσ (sqrt_nonneg 8)]
  have hK : 1 ≤ K := by dsimp [K]; linarith
  have hFK : F ≤ K := by dsimp [K]; linarith
  have hlogK : log (1/cstar) ≤ K := by dsimp [K]; linarith
  have hC : 0 < C := by dsimp [C]; positivity
  have hC₀C : C₀ ≤ C := by dsimp [C]; nlinarith
  have hprodC : C₀*K ≤ C := by dsimp [C]; nlinarith
  refine ⟨C, hC, ?_⟩
  intro A hA h ζ L R M N hL hR hM hN hqM hqvol hh
  let p := pinnedGibbs A h β ζ
  let hmax := σ*sqrt (8*log N)
  let S := R^(d-1)*L^exponentA d
  let J := M*(1+sqrt (log N))+2*log M+1
  let δ := cstar/M^2
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hL0 : 0 ≤ L := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hmax0 : 0 ≤ hmax := by dsimp [hmax]; positivity
  have hδ : 0 < δ := div_pos hcstar (sq_pos_of_pos hM0)
  have hδ1 : δ < 1 := (div_lt_one (sq_pos_of_pos hM0)).mpr
    (hcstar1.trans_le (one_le_pow₀ (n := 2) hM))
  have hlogM : 0 ≤ log M := log_nonneg hM
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hpower : (A.card:ℝ)^exponentA d ≤ S := by
    have hh := Real.rpow_le_rpow (Nat.cast_nonneg A.card) hqvol (exponentA_pos hd).le
    rwa [volume_surface_identity d (by omega) L R hL0 hR0] at hh
  have hlogδ : log (1/δ) = 2*log M+log (1/cstar) := by
    have he : 1/δ = M^2/cstar := by dsimp [δ]; field_simp
    rw [he, log_div (pow_ne_zero 2 hM0.ne') hcstar.ne', log_pow,
      log_div (by norm_num) hcstar.ne', log_one]
    ring
  have hfield : 1+hmax ≤ F*(1+sqrt (log N)) := by
    have hsqrt : sqrt (8*log N) = sqrt 8 * sqrt (log N) := sqrt_mul (by norm_num : (0:ℝ)≤8) _
    dsimp [hmax, F]
    rw [hsqrt]
    nlinarith [sqrt_nonneg (log N), mul_nonneg hσ (sqrt_nonneg 8)]
  have hbracket : (A.card:ℝ)*(1+hmax)+log (1/δ) ≤ K*J := by
    have hq := mul_le_mul_of_nonneg_right hqM (by positivity : 0 ≤ 1+hmax)
    have hf := mul_le_mul_of_nonneg_left hfield hM0.le
    have h1 := mul_le_mul_of_nonneg_right hFK
      (mul_nonneg hM0.le (by positivity : 0 ≤ 1+sqrt (log N)))
    have h2 := mul_le_mul_of_nonneg_right hK (by positivity : 0 ≤ 2*log M)
    rw [hlogδ]
    dsimp [J]
    nlinarith
  have he : C₀*exp (C₀*(A.card:ℝ)^exponentA d)*K ≤ C*exp (C*S) := by
    have harg : C₀*(A.card:ℝ)^exponentA d ≤ C*S :=
      (mul_le_mul_of_nonneg_left hpower hC₀.le).trans (mul_le_mul_of_nonneg_right hC₀C hS)
    have hx := mul_le_mul hprodC (exp_le_exp.mpr harg) (exp_nonneg _) hC.le
    nlinarith
  have htime : mixingUpperTime p δ ≤ C*exp (C*S)*J := by
    apply (hbound A hA h ζ hmax hmax0 hh δ hδ hδ1).trans
    calc C₀*exp (C₀*(A.card:ℝ)^exponentA d)*
        ((A.card:ℝ)*(1+hmax)+log (1/δ)) ≤
        C₀*exp (C₀*(A.card:ℝ)^exponentA d)*(K*J) :=
          mul_le_mul_of_nonneg_left hbracket (by positivity)
      _ ≤ C*exp (C*S)*J := by nlinarith [mul_le_mul_of_nonneg_right he hJ]
  exact heatBath_good_later p (fun _ => div_pos (isingWeight_pos _ _ _ _ _ _ _) (isingZ_pos _ _ _ _ _ _))
    ⟨hA.choose, hA.choose_spec⟩ δ (C*exp (C*S)*J) hδ hδ1 htime

/-- An explicit physical field cancelling the arbitrary all-minus exterior.
This represents any finite-domain one-site field without introducing missing
interactions beyond an ambient free-boundary volume. -/
def boundaryCancelField {d : ℕ} (A : Finset (Point d)) (f : ↥A → ℝ) (β : ℝ) : Point d → ℝ :=
  fun x => if hx : x ∈ A then f ⟨x,hx⟩ - β*∑ y ∈ externalBoundary A,
    if LatticeGeometry.Adj x y then spinVal 0 else 0 else 0

theorem boundaryCancelField_effective {d : ℕ} (A : Finset (Point d)) (f : ↥A → ℝ) (β : ℝ) :
    effectiveField A (boundaryCancelField A f β) β (fun _ => 0) = f := by
  funext x
  unfold effectiveField boundaryCancelField
  rw [dif_pos x.property]
  ring

theorem boundaryCancelField_abs_le {d : ℕ} (A : Finset (Point d)) (f : ↥A → ℝ)
    (β hmax : ℝ) (hβ : 0 ≤ β) (hf : ∀ x, |f x| ≤ hmax) :
    ∀ x ∈ A, |boundaryCancelField A f β x| ≤ hmax+2*(d:ℝ)*β := by
  intro x hx
  have hh := effectiveField_abs_le A (fun _ => 0) β 0 hβ (by intro y hy; simp)
    (fun _ => 0) ⟨x,hx⟩
  change |0+β*∑ y ∈ externalBoundary A, if LatticeGeometry.Adj x y then spinVal 0 else 0| ≤ _ at hh
  unfold boundaryCancelField
  rw [dif_pos hx]
  have ha : |f ⟨x,hx⟩ - β*∑ y ∈ externalBoundary A, if LatticeGeometry.Adj x y then spinVal 0 else 0| ≤
      |f ⟨x,hx⟩| + |β*∑ y ∈ externalBoundary A, if LatticeGeometry.Adj x y then spinVal 0 else 0| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (f ⟨x,hx⟩)
      (-(β*∑ y ∈ externalBoundary A, if LatticeGeometry.Adj x y then spinVal 0 else 0))
  simp only [zero_add] at hh
  exact ha.trans (add_le_add (hf ⟨x,hx⟩) hh)

theorem boundaryCancelField_gibbs {d : ℕ} (A : Finset (Point d)) (f : ↥A → ℝ) (β : ℝ) :
    pinnedGibbs A (boundaryCancelField A f β) β (fun _ => 0) =
      gibbs (domainLattice A) f β univ ∅ (fun _ => 0) := by
  unfold pinnedGibbs
  rw [boundaryCancelField_effective]

/-- The local comparison time also applies directly to a field on the
actual domain subtype, as used by conditioning a free-boundary ambient law. -/
theorem domain_field_mixingUpperTime_bound (d : ℕ) (β : ℝ) (hd : 2 ≤ d) (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset (Point d)), A.Nonempty →
      ∀ (f : ↥A → ℝ) (hmax : ℝ), 0 ≤ hmax → (∀ x, |f x| ≤ hmax) →
      ∀ δ : ℝ, 0 < δ → δ < 1 →
      mixingUpperTime (gibbs (domainLattice A) f β univ ∅ (fun _ => 0)) δ ≤
        C*exp (C*(A.card:ℝ)^exponentA d)*
          ((A.card:ℝ)*(1+hmax+2*(d:ℝ)*β)+log (1/δ)) := by
  obtain ⟨C,hC,hbound⟩ := pinned_mixingUpperTime_bound d β hd hβ
  refine ⟨C,hC,?_⟩
  intro A hA f hmax hhmax hf δ hδ hδ1
  have hh := hbound A hA (boundaryCancelField A f β) (fun _ => 0)
    (hmax+2*(d:ℝ)*β) (by positivity)
    (boundaryCancelField_abs_le A f β hmax hβ.le hf) δ hδ hδ1
  rw [boundaryCancelField_gibbs] at hh
  convert hh using 1 <;> ring

/-- Source-time (3.18) for the exact finite-domain Gibbs law with its actual
conditional field. The `2dβ` allowance includes all frozen ambient neighbors,
without requiring interactions with sites outside the ambient volume. -/
theorem domain_field_block_mixing (d : ℕ) (β σ cstar : ℝ) (hd : 2 ≤ d) (hβ : 0 < β)
    (hσ : 0 ≤ σ) (hcstar : 0 < cstar) (hcstar1 : cstar < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset (Point d)), A.Nonempty →
      ∀ (f : ↥A → ℝ) (L R M N : ℝ),
      1 ≤ L → 1 ≤ R → 1 ≤ M → 2 ≤ N →
      (A.card:ℝ) ≤ M → (A.card:ℝ) ≤ L*R^d →
      (∀ x, |f x| ≤ σ*sqrt (8*log N)+2*(d:ℝ)*β) →
      let p := gibbs (domainLattice A) f β univ ∅ (fun _ => 0)
      let T := C*exp (C*(R^(d-1)*L^exponentA d)) *
        (M*(1+sqrt (log N))+2*log M+1)
      0 ≤ T ∧ ∀ η, tvDist (heatBathTransition p T η) p ≤ cstar/M^2 := by
  obtain ⟨C,hC,hbound⟩ := pinned_block_mixing d β (σ+4*(d:ℝ)*β) cstar hd hβ
    (by positivity) hcstar hcstar1
  refine ⟨C,hC,?_⟩
  intro A hA f L R M N hL hR hM hN hqM hqvol hf
  have hlogN : log 2 ≤ log N := Real.log_le_log (by norm_num) hN
  have hsqrt : 1 ≤ sqrt (8*log N) := by
    have hlow := Real.log_two_gt_d9
    have hs := Real.sq_sqrt (by linarith : 0 ≤ 8*log N)
    have hs0 := Real.sqrt_nonneg (8*log N)
    nlinarith
  have hh := boundaryCancelField_abs_le A f β (σ*sqrt (8*log N)+2*(d:ℝ)*β) hβ.le hf
  have hphys : ∀ x ∈ A, |boundaryCancelField A f β x| ≤
      (σ+4*(d:ℝ)*β)*sqrt (8*log N) := by
    intro x hx
    have hβ0 : 0 ≤ 4*(d:ℝ)*β := by positivity
    have hmult := mul_le_mul_of_nonneg_left hsqrt hβ0
    have hhere := hh x hx
    nlinarith
  have hmix := hbound A hA (boundaryCancelField A f β) (fun _ => 0)
    L R M N hL hR hM hN hqM hqvol hphys
  rwa [boundaryCancelField_gibbs] at hmix

end Paper09.RFIM
