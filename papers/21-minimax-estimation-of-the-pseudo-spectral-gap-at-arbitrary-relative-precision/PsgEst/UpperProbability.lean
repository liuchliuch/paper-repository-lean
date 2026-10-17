import PsgEst.UpperDeterministic
import PsgEst.ProbabilityThinning
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The uniform probability bound from the relative Laplacian proposition

The input below is exactly Proposition 1, with its actual finite path law and
singular-deficit event. The lag distribution, union bound, sample-size arithmetic,
and deterministic estimator step are proved in this module.
-/

open Matrix BigOperators Real Finset Classical
namespace PsgEst
namespace UpperProbability

/-- The complete relative Laplacian concentration statement (Proposition 1). -/
def Proposition1Bound (d : ℕ) [NeZero d] : Prop :=
  ∀ (m : ℕ) (Q : Stoch d) (st : Stationary Q) (τ η : ℝ) (mu0 : Fin d → ℝ),
    0 < τ → 0 < η → η ≤ 1/4 → 1 ≤ (m:ℝ)*gammaPS Q st →
    (∀ i, 0 ≤ mu0 i) → (∑ i, mu0 i = 1) →
    pathMeasure Q.P mu0 (univ.filter fun Y : Fin (m+1) → Fin d =>
      ¬ (degPos Y ∧ |(1-sigma2 (lHat Y))-(1-sigma2 (simil st.mu Q.P))| ≤
        η*(3*(1-sigma2 (simil st.mu Q.P))+τ)/(1-η))) ≤
      4*(d:ℝ)/Stationary.star st * exp (-((m:ℝ)*Stationary.star st*gammaPS Q st*η^2)/36) +
      4*(d:ℝ)*exp (-(3*(m:ℝ)*Stationary.star st*τ*η^2)/16)

lemma pathMeasure_mono {d n : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) (mu : Fin d → ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hmu : ∀ i, 0 ≤ mu i)
    {A B : Finset (Fin (n+1) → Fin d)} (hAB : A ⊆ B) :
    pathMeasure P mu A ≤ pathMeasure P mu B := by
  unfold pathMeasure
  exact sum_le_sum_of_subset_of_nonneg hAB (fun X _ _ => pathProb_nonneg P mu hP hmu X)

lemma pathMeasure_exists_le {d n : ℕ} {ι : Type*} [Fintype ι]
    (P : Matrix (Fin d) (Fin d) ℝ) (mu : Fin d → ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hmu : ∀ i, 0 ≤ mu i)
    (F : ι → (Fin (n+1) → Fin d) → Prop) :
    pathMeasure P mu (univ.filter fun X => ∃ i, F i X) ≤
      ∑ i, pathMeasure P mu (univ.filter (F i)) := by
  unfold pathMeasure
  simp only [sum_filter]
  rw [sum_comm]
  apply sum_le_sum
  intro X _
  by_cases h : ∃ i, F i X
  · obtain ⟨i, hi⟩ := h
    rw [if_pos ⟨i,hi⟩]
    have hs := single_le_sum (f := fun j => if F j X then pathProb P mu X else 0)
      (fun j _ => by dsimp only; split_ifs; exact pathProb_nonneg P mu hP hmu X; exact le_rfl)
      (mem_univ i)
    simpa only [if_pos hi] using hs
  · rw [if_neg h]
    exact sum_nonneg (fun i _ => by split_ifs; exact pathProb_nonneg P mu hP hmu X; exact le_rfl)

/-- The floor in the number of observed lagged transitions loses at most a
factor two once there are at least two full blocks. -/
lemma div_cast_lower (n k : ℕ) (hk : 0 < k) (h2k : 2*k ≤ n) :
    (n:ℝ)/(2*(k:ℝ)) ≤ (n/k:ℕ) := by
  have hm : 1 ≤ n/k := (Nat.le_div_iff_mul_le hk).mpr (by omega)
  have hmul := Nat.mul_le_mul_left k hm
  have hdiv := Nat.lt_mul_div_succ n hk
  have hnat : n ≤ 2*(n/k)*k := by nlinarith
  rw [div_le_iff₀ (by positivity : (0:ℝ)<2*k)]
  have hr : (n:ℝ) ≤ 2*(n/k:ℕ)*(k:ℝ) := by exact_mod_cast hnat
  nlinarith

/-- Numerical bounds (preceding (20)) for every lag in `1..floor(1/γ)`. -/
lemma lag_sample_bounds (n k : ℕ) (γ Γ : ℝ) (hγ : 0 < γ)
    (hk : 0 < k) (hkK : k ≤ ⌊1/γ⌋₊) (hn : 8/γ ≤ (n:ℝ))
    (hΓ : (k:ℝ)*γ/4 ≤ Γ) :
    1 ≤ (n/k:ℕ)*Γ ∧ (n:ℝ)*γ/8 ≤ (n/k:ℕ)*Γ ∧
      (n:ℝ)*γ/2 ≤ (n/k:ℕ)*((k:ℝ)*γ) := by
  have hkR : (0:ℝ)<k := Nat.cast_pos.mpr hk
  have hk1 : (k:ℝ) ≤ 1/γ :=
    (Nat.cast_le.mpr hkK).trans (Nat.floor_le (by positivity))
  have hkg : (k:ℝ)*γ ≤ 1 := (le_div_iff₀ hγ).mp hk1
  have hng : 8 ≤ (n:ℝ)*γ := (div_le_iff₀ hγ).mp hn
  have hn2 : 2*(k:ℝ) ≤ n := by nlinarith
  have h2k : 2*k ≤ n := by exact_mod_cast hn2
  have hm := div_cast_lower n k hk h2k
  have hmnonneg : (0:ℝ) ≤ (n/k:ℕ) := Nat.cast_nonneg _
  have hmk : (n:ℝ)/2 ≤ (n/k:ℕ)*(k:ℝ) := by
    have h := (div_le_iff₀ (by positivity : (0:ℝ)<2*k)).mp hm
    nlinarith
  have hmg : (n:ℝ)*γ/2 ≤ (n/k:ℕ)*((k:ℝ)*γ) := by
    nlinarith [mul_le_mul_of_nonneg_right hmk hγ.le]
  have hmΓ : (n:ℝ)*γ/8 ≤ (n/k:ℕ)*Γ := by
    have h := mul_le_mul_of_nonneg_left hΓ hmnonneg
    nlinarith
  exact ⟨by linarith, hmΓ, hmg⟩

/-- The sample condition both dominates `8/γ` and makes the union tail at most δ. -/
lemma sample_condition (d n : ℕ) (p γ ε δ : ℝ)
    (hd : 1 ≤ d) (hp : 0 < p) (hp1 : p ≤ 1) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hε : 0 < ε) (hε' : ε < 1/2) (hδ : 0 < δ) (hδ' : δ < 1)
    (hn : 73728/(p*γ*ε^2)*log (8*(d:ℝ)/(δ*p*γ)) ≤ (n:ℝ)) :
    8/γ ≤ (n:ℝ) ∧
      (8*(d:ℝ)/(p*γ))*exp (-((n:ℝ)*p*γ*ε^2)/73728) ≤ δ := by
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hprod : 0 < δ*p*γ := by positivity
  have hprod1 : δ*p*γ ≤ 1 := by
    calc
      δ*p*γ ≤ 1*1*1 := mul_le_mul (mul_le_mul hδ'.le hp1 hp.le (by norm_num))
        hγ1 hγ.le (by norm_num)
      _ = 1 := by norm_num
  have hApos : 0 < 8*(d:ℝ)/(δ*p*γ) := by positivity
  have hA2 : (2:ℝ) ≤ 8*(d:ℝ)/(δ*p*γ) := by
    rw [le_div_iff₀ hprod]
    nlinarith
  have hloghalf : (1/2:ℝ) ≤ log (8*(d:ℝ)/(δ*p*γ)) := by
    have hl := Real.one_sub_inv_le_log_of_pos (show (0:ℝ)<2 by norm_num)
    have hmono := Real.log_le_log (show (0:ℝ)<2 by norm_num) hA2
    norm_num at hl
    linarith
  have he2 : 0 < ε^2 := sq_pos_of_pos hε
  have hden : 0 < p*γ*ε^2 := by positivity
  have hreq : 73728*log (8*(d:ℝ)/(δ*p*γ)) ≤ (n:ℝ)*(p*γ*ε^2) := by
    have hm := (div_le_iff₀ hden).mp (show
      73728*log (8*(d:ℝ)/(δ*p*γ))/(p*γ*ε^2) ≤ (n:ℝ) by
        simpa only [div_mul_eq_mul_div] using hn)
    exact hm
  have hpe : p*ε^2 ≤ 1 := by
    have he1 : ε^2 ≤ 1 := by nlinarith
    exact (mul_le_mul hp1 he1 (sq_nonneg ε) (by norm_num)).trans_eq (by ring)
  have hng : 8 ≤ (n:ℝ)*γ := by
    have h := mul_le_mul_of_nonneg_left hpe (show 0 ≤ (n:ℝ)*γ by positivity)
    nlinarith
  refine ⟨(div_le_iff₀ hγ).mpr hng, ?_⟩
  have hexp : exp (-((n:ℝ)*p*γ*ε^2)/73728) ≤ 1/(8*(d:ℝ)/(δ*p*γ)) := by
    calc
      _ ≤ exp (-log (8*(d:ℝ)/(δ*p*γ))) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      _ = _ := by rw [Real.exp_neg, Real.exp_log hApos, one_div]
  calc
    _ ≤ (8*(d:ℝ)/(p*γ))*(1/(8*(d:ℝ)/(δ*p*γ))) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = δ := by field_simp

/-- The actual Proposition 1 good event, at the observed `k`th subsample. -/
def lagGood {d n : ℕ} (S : Stoch d) (st : Stationary S) (ε : ℝ)
    (k : ℕ) (X : Fin (n+1) → Fin d) : Prop :=
  degPos (skipPath X k) ∧
    |(1-sigma2 (lHat (skipPath X k)))-(1-sigma2 (Lk S st k))| ≤
      (ε/16)*(3*(1-sigma2 (Lk S st k))+(k:ℝ)*gammaPS S st)/(1-ε/16)

/-- Proposition 1 and the exact subsampling law give a common bound for every
small lag, with the constants appearing in (20). -/
theorem lag_failure_bound {d : ℕ} [NeZero d] (hprop : Proposition1Bound d)
    (E : Ergodic d) (n k : ℕ) (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1/2)
    (hk : 0 < k) (hkK : k ≤ ⌊1/gammaPS E.S E.st⌋₊)
    (hn : 8/gammaPS E.S E.st ≤ (n:ℝ))
    (mu0 : Fin d → ℝ) (hmu : ∀ i, 0 ≤ mu0 i) (hsum : ∑ i, mu0 i = 1) :
    pathMeasure E.S.P mu0 (univ.filter fun X : Fin (n+1) → Fin d =>
      ¬ lagGood E.S E.st ε k X) ≤
      (4*(d:ℝ)/Stationary.star E.st+4*(d:ℝ))*
        exp (-((n:ℝ)*Stationary.star E.st*gammaPS E.S E.st*ε^2)/73728) := by
  let γ := gammaPS E.S E.st
  let p := Stationary.star E.st
  let Γ := gammaPS (E.S.pow k) (stationaryPow E.S E.st k)
  have hp : 0 < p := Stationary.star_pos E.st
  have hγ : 0 < γ := E.gap_pos
  have hkR : (0:ℝ)<k := Nat.cast_pos.mpr hk
  have hkg : (k:ℝ)*γ ≤ 1 := by
    apply (le_div_iff₀ hγ).mp
    exact (Nat.cast_le.mpr hkK).trans (Nat.floor_le (by positivity))
  have hΓ : (k:ℝ)*γ/4 ≤ Γ := by
    have h := ((lemma_1 E.S E.st E.gap_pos).1 k hk).1
    rw [min_eq_left hkg] at h
    linarith
  have hb := lag_sample_bounds n k γ Γ hγ hk hkK hn hΓ
  let F : Finset (Fin (n/k+1) → Fin d) := univ.filter fun Y =>
    ¬ (degPos Y ∧ |(1-sigma2 (lHat Y))-(1-sigma2 (Lk E.S E.st k))| ≤
      (ε/16)*(3*(1-sigma2 (Lk E.S E.st k))+(k:ℝ)*γ)/(1-ε/16))
  have hpush : pathMeasure E.S.P mu0 (univ.filter fun X : Fin (n+1) → Fin d =>
      ¬ lagGood E.S E.st ε k X) = pathMeasure (E.S.P^k) mu0 F := by
    have hevent : (univ.filter fun X : Fin (n+1) → Fin d => ¬ lagGood E.S E.st ε k X) =
        univ.filter fun X => skipPath X k ∈ F := by
      ext X
      simp only [mem_filter, mem_univ, true_and, F, lagGood]
      rfl
    rw [hevent, skipPath_measure E.S.P mu0 E.S.row_stoch k F]
  have hpr := hprop (n/k) (E.S.pow k) (stationaryPow E.S E.st k)
    ((k:ℝ)*γ) (ε/16) mu0 (mul_pos hkR hγ) (by positivity) (by linarith)
    hb.1 hmu hsum
  change pathMeasure (E.S.P^k) mu0 F ≤
      4*(d:ℝ)/p*exp (-((n/k:ℕ)*p*Γ*(ε/16)^2)/36) +
      4*(d:ℝ)*exp (-(3*(n/k:ℕ)*p*((k:ℝ)*γ)*(ε/16)^2)/16) at hpr
  rw [hpush]
  have hs1 := mul_le_mul_of_nonneg_right hb.2.1
    (show 0 ≤ p*(ε/16)^2 by positivity)
  have hs2 := mul_le_mul_of_nonneg_right hb.2.2
    (show 0 ≤ p*(ε/16)^2 by positivity)
  have hnonneg : 0 ≤ (n:ℝ)*p*γ*ε^2 := by positivity
  have he1 : -((n/k:ℕ)*p*Γ*(ε/16)^2)/36 ≤ -((n:ℝ)*p*γ*ε^2)/73728 := by
    nlinarith
  have he2 : -(3*(n/k:ℕ)*p*((k:ℝ)*γ)*(ε/16)^2)/16 ≤
      -((n:ℝ)*p*γ*ε^2)/73728 := by nlinarith
  calc
    _ ≤ 4*(d:ℝ)/p*exp (-((n/k:ℕ)*p*Γ*(ε/16)^2)/36) +
        4*(d:ℝ)*exp (-(3*(n/k:ℕ)*p*((k:ℝ)*γ)*(ε/16)^2)/16) := hpr
    _ ≤ 4*(d:ℝ)/p*exp (-((n:ℝ)*p*γ*ε^2)/73728) +
        4*(d:ℝ)*exp (-((n:ℝ)*p*γ*ε^2)/73728) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he1) (by positivity))
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he2) (by positivity))
    _ = _ := by ring

/-- Theorem 1 from Proposition 1.  All lag selection, finite probability,
floor arithmetic and the numerical sample requirement are discharged here. -/
theorem uniform_upper_of_proposition1 {d : ℕ} [NeZero d]
    (hprop : Proposition1Bound d) (E : Ergodic d) (n : ℕ) (ε δ : ℝ)
    (hε : 0 < ε) (hε' : ε < 1/2) (hδ : 0 < δ) (hδ' : δ < 1)
    (mu0 : Fin d → ℝ) (hmu : ∀ i, 0 ≤ mu0 i) (hsum : ∑ i, mu0 i = 1)
    (hn : 73728/(Stationary.star E.st*gammaPS E.S E.st*ε^2)*
      log (8*(d:ℝ)/(δ*Stationary.star E.st*gammaPS E.S E.st)) ≤ (n:ℝ)) :
    pathMeasure E.S.P mu0 (univ.filter fun X : Fin (n+1) → Fin d =>
      ε*gammaPS E.S E.st < |gammaHat X-gammaPS E.S E.st|) ≤ δ := by
  let γ := gammaPS E.S E.st
  let p := Stationary.star E.st
  let K := ⌊1/γ⌋₊
  let B := (4*(d:ℝ)/p+4*(d:ℝ))*exp (-((n:ℝ)*p*γ*ε^2)/73728)
  have hp : 0 < p := Stationary.star_pos E.st
  have hp1 : p ≤ 1 := by
    let i : Fin d := ⟨0, Nat.pos_of_neZero d⟩
    have hi : E.st.mu i ≤ ∑ j, E.st.mu j :=
      single_le_sum (fun j _ => (E.st.pos j).le) (mem_univ i)
    exact (Stationary.star_le E.st i).trans (by simpa only [E.st.sum_one] using hi)
  have hγ : 0 < γ := E.gap_pos
  have hs := sample_condition d n p γ ε δ (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))
    hp hp1 hγ E.gap_le_one hε hε' hδ hδ' hn
  have hKcast : (K:ℝ) ≤ 1/γ := Nat.floor_le (by positivity)
  have hKn : K ≤ n := by
    have hinv : 1/γ ≤ 8/γ :=
      div_le_div_of_nonneg_right (by norm_num : (1:ℝ) ≤ 8) hγ.le
    have hle : (K:ℝ) ≤ n := hKcast.trans (hinv.trans hs.1)
    exact_mod_cast hle
  let bad : Fin K → (Fin (n+1) → Fin d) → Prop :=
    fun j X => ¬ lagGood E.S E.st ε (j.val+1) X
  have hcovered : (univ.filter fun X : Fin (n+1) → Fin d =>
      ε*γ < |gammaHat X-γ|) ⊆ univ.filter fun X => ∃ j : Fin K, bad j X := by
    intro X hX
    simp only [mem_filter, mem_univ, true_and] at *
    by_contra hnone
    have hgood : ∀ k : ℕ, 0 < k → k ≤ K → lagGood E.S E.st ε k X := by
      intro k hk hkK
      have hj : k-1 < K := by omega
      have hnot := not_exists.mp hnone (⟨k-1,hj⟩ : Fin K)
      have hkval : k-1+1=k := by omega
      simpa only [bad, hkval, not_not] using hnot
    have he := gammaHat_error_of_prop1_bounds X E.S E.st E.gap_pos ε hε hε' hKn hgood
    exact (not_le_of_gt hX) he
  have hbad : ∀ j : Fin K,
      pathMeasure E.S.P mu0 (univ.filter (bad j)) ≤ B := by
    intro j
    exact lag_failure_bound hprop E n (j.val+1) ε hε hε' (by omega) (by
      change j.val+1 ≤ K
      omega) hs.1 mu0 hmu hsum
  have hcoef : 4*(d:ℝ)/p+4*(d:ℝ) ≤ 8*(d:ℝ)/p := by
    have hsingle : 4*(d:ℝ) ≤ 4*(d:ℝ)/p :=
      (le_div_iff₀ hp).mpr (mul_le_of_le_one_right (by positivity) hp1)
    have htwice : 8*(d:ℝ)/p = 2*(4*(d:ℝ)/p) := by ring
    rw [htwice]
    linarith
  have hcoefficient : (K:ℝ)*(4*(d:ℝ)/p+4*(d:ℝ)) ≤ (1/γ)*(8*(d:ℝ)/p) :=
    mul_le_mul hKcast hcoef (by positivity) (by positivity)
  calc
    _ ≤ pathMeasure E.S.P mu0 (univ.filter fun X => ∃ j : Fin K, bad j X) :=
      pathMeasure_mono E.S.P mu0 E.S.nonneg hmu hcovered
    _ ≤ ∑ j : Fin K, pathMeasure E.S.P mu0 (univ.filter (bad j)) :=
      by
        convert (pathMeasure_exists_le (ι := Fin K) E.S.P mu0 E.S.nonneg hmu bad) using 1 <;> congr
        funext j
        congr
    _ ≤ ∑ _j : Fin K, B := sum_le_sum (fun j _ => hbad j)
    _ = (K:ℝ)*B := by simp
    _ ≤ (8*(d:ℝ)/(p*γ))*exp (-((n:ℝ)*p*γ*ε^2)/73728) := by
      dsimp [B]
      calc
        _ = ((K:ℝ)*(4*(d:ℝ)/p+4*(d:ℝ)))*exp (-((n:ℝ)*p*γ*ε^2)/73728) := by ring
        _ ≤ ((1/γ)*(8*(d:ℝ)/p))*exp (-((n:ℝ)*p*γ*ε^2)/73728) :=
          mul_le_mul_of_nonneg_right hcoefficient (Real.exp_nonneg _)
        _ = _ := by ring
    _ ≤ δ := hs.2

end UpperProbability
end PsgEst
