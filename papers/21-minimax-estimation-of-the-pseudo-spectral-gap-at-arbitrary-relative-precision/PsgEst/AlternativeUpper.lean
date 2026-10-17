import PsgEst.AppendixVisitClosed
import PsgEst.RelativeConcentration
import PsgEst.UpperProbability
import PsgEst.MatrixFreedmanTheorem

/-!
# Appendix A's alternative finite-sample estimator bound

The proved occupation lemma replaces Paulin's inequality in the relative
Laplacian argument. The extra logarithm is displayed in a finite sample
condition for the original estimator and the actual lagged path laws.
-/

open Matrix BigOperators Real Finset
namespace PsgEst.AlternativeUpper

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The logarithmic numerator in the appendix mixing lag. -/
def logBudget (p η : ℝ) : ℝ := 1+2*log (4/(η*p))

lemma logBudget_ge_one (p η : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hη : 0 < η) (hη1 : η ≤ 1) : 1 ≤ logBudget p η := by
  have hprod : η*p ≤ 1 := by nlinarith
  have harg : 1 ≤ 4/(η*p) := (le_div_iff₀ (mul_pos hη hp)).mpr (by linarith)
  have hh := Real.log_nonneg harg
  dsimp [logBudget]
  linarith

lemma star_pow {d : ℕ} [NeZero d] (S : Stoch d) (st : Stationary S) (k : ℕ) :
    Stationary.star (stationaryPow S st k) = Stationary.star st := rfl

/-- The appendix lag for a small estimator lag is at most `5 B/(k γ)`. -/
lemma mixingLag_le {d : ℕ} [NeZero d] (S : Stoch d) (st : Stationary S)
    (γ η B : ℝ) (hγ : 0 < γ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hB : B = logBudget (Stationary.star st) η) (k : ℕ) (hk : 0 < k)
    (hkg : (k:ℝ)*γ ≤ 1)
    (hΓ : (k:ℝ)*γ/4 ≤ gammaPS (S.pow k) (stationaryPow S st k)) :
    (mixingLag (S.pow k) (stationaryPow S st k) η:ℝ) ≤ 5*B/((k:ℝ)*γ) := by
  have hp := Stationary.star_pos st
  let i : Fin d := ⟨0,Nat.pos_of_neZero d⟩
  have hp1 : Stationary.star st ≤ 1 := (Stationary.star_le st i).trans
    (probability_coordinate_le_one st.mu st.nonneg st.sum_one i)
  have hB1 : 1 ≤ B := by rw [hB]; exact logBudget_ge_one _ _ hp hp1 hη hη1
  have hkγ : 0 < (k:ℝ)*γ := mul_pos (Nat.cast_pos.mpr hk) hγ
  have hΓpos : 0 < gammaPS (S.pow k) (stationaryPow S st k) := by linarith
  have hceil : (mixingLag (S.pow k) (stationaryPow S st k) η:ℝ) ≤
      B/gammaPS (S.pow k) (stationaryPow S st k)+1 := by
    change (⌈(1+2*log (4/(η*Stationary.star (stationaryPow S st k))))/
      gammaPS (S.pow k) (stationaryPow S st k)⌉₊:ℝ) ≤ _
    rw [star_pow]
    change (⌈logBudget (Stationary.star st) η/
      gammaPS (S.pow k) (stationaryPow S st k)⌉₊:ℝ) ≤ _
    rw [← hB]
    exact (Nat.ceil_lt_add_one (by positivity)).le
  have hratio : B/gammaPS (S.pow k) (stationaryPow S st k) ≤ 4*B/((k:ℝ)*γ) := by
    apply (div_le_div_iff₀ hΓpos hkγ).mpr
    have hh := mul_le_mul_of_nonneg_left hΓ (show 0 ≤ 4*B by linarith)
    nlinarith
  have hone : 1 ≤ B/((k:ℝ)*γ) := (le_div_iff₀ hkγ).mpr (by linarith)
  calc _ ≤ B/gammaPS (S.pow k) (stationaryPow S st k)+1 := hceil
    _ ≤ 4*B/((k:ℝ)*γ)+B/((k:ℝ)*γ) := add_le_add hratio hone
    _ = _ := by ring

/-- Replacing the degree concentration in Proposition 1 by the closed
appendix lemma preserves the matrix martingale and normalization arguments. -/
theorem relative_failure {d m : ℕ} [NeZero d] (Q : Stoch d) (st : Stationary Q)
    (τ η : ℝ) (mu : Fin d → ℝ) (hτ : 0 < τ) (hη : 0 < η) (hη4 : η ≤ 1/4)
    (hgap : 0 < gammaPS Q st) (hmu : ∀ i, 0 ≤ mu i) (hsum : ∑ i, mu i = 1)
    (hm2 : 2*mixingLag Q st η ≤ m)
    (hsize : 2/η ≤ (m:ℝ)*Stationary.star st/(2*(mixingLag Q st η:ℝ)))
    (hFreedman : MatrixFreedmanInput Q mu) :
    pathMeasure Q.P mu (univ.filter fun Y : Fin (m+1) → Fin d =>
      ¬ RelativeConcentration.good Q st τ η Y) ≤
      4*(d:ℝ)*(mixingLag Q st η:ℝ)*
        exp (-((m:ℝ)*Stationary.star st*η^2/(72*(mixingLag Q st η:ℝ)))) +
      4*(d:ℝ)*exp (-(3*(m:ℝ)*Stationary.star st*τ*η^2)/16) := by
  have hb := mixingLag_pos Q st hgap η hη hη4
  have hm : 0 < m := by omega
  have hdeg := (lemma_2_closed m Q st η (1/2) mu hη hη4 (by norm_num) (by norm_num)
    hmu hsum hgap).2 ⟨hm2,hsize⟩
  have heq : pathMeasure Q.P mu (univ.filter fun Y : Fin (m+1) → Fin d =>
      ¬ degreeEvent st.mu η Y) = eventProb Q.P mu (fun Y : Fin (m+1) → Fin d => ¬ degreeEvent st.mu η Y) := by
    unfold eventProb
    congr
  change pathMeasure Q.P mu (univ.filter fun Y : Fin (m+1) → Fin d =>
    ¬ degreeEvent st.mu η Y) ≤ _ at hdeg
  rw [heq] at hdeg
  have hmart := edgeProcess_tail Q st mu hmu hsum τ η hτ hη hη4 hm hFreedman
  have hpEq : pathMeasure Q.P mu (univ.filter fun Y : Fin (m+1) → Fin d =>
      ¬ RelativeConcentration.good Q st τ η Y) =
      eventProb Q.P mu (fun Y : Fin (m+1) → Fin d => ¬ RelativeConcentration.good Q st τ η Y) := by
    unfold eventProb
    congr
  rw [hpEq]
  by_cases hd : 1 < d
  · calc
      _ ≤ eventProb Q.P mu (fun Y : Fin (m+1) → Fin d =>
          (¬ degreeEvent st.mu η Y) ∨ (degreeEvent st.mu η Y ∧
            η*(m:ℝ) < martingaleSumNorm (edgeProcessZ Q st τ) Y)) := by
        apply eventProb_mono Q.P mu Q.nonneg hmu
        intro Y hfail
        by_cases hE : degreeEvent st.mu η Y
        · right
          refine ⟨hE, ?_⟩
          by_contra hnorm
          exact hfail (RelativeConcentration.good_of_degree_and_norm hd Q st Y hm τ η
            hτ hη hη4 hE (le_of_not_gt hnorm))
        · exact Or.inl hE
      _ ≤ eventProb Q.P mu (fun Y : Fin (m+1) → Fin d => ¬ degreeEvent st.mu η Y) +
          eventProb Q.P mu (fun Y : Fin (m+1) → Fin d => degreeEvent st.mu η Y ∧
            η*(m:ℝ) < martingaleSumNorm (edgeProcessZ Q st τ) Y) :=
        eventProb_or_le Q.P mu Q.nonneg hmu _ _
      _ ≤ _ := by simpa only [mixingLag, logBudget, neg_div] using add_le_add hdeg hmart
  · have hd1 : d = 1 := by have := NeZero.ne d; omega
    subst d
    have hz := eventProb_mono Q.P mu Q.nonneg hmu
      (E:=fun Y : Fin (m+1) → Fin 1 => ¬ RelativeConcentration.good Q st τ η Y)
      (F:=fun _ => False) (fun Y hY => hY
        (RelativeConcentration.good_one_state Q st Y hm τ η hτ hη hη4))
    have hf : eventProb Q.P mu (fun _ : Fin (m+1) → Fin 1 => False) = 0 := by
      simp [eventProb, pathMeasure]
    rw [hf] at hz
    exact hz.trans (by have hp := Stationary.star_pos st; positivity)


/-- Uniform small-lag arithmetic: occupation side conditions and cancellation
of the polynomial dependence on the estimator lag. -/
lemma occupation_arithmetic (n m k b : ℕ) (p γ η B : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) (hγ : 0 < γ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hB : 1 ≤ B) (hk : 0 < k) (hb : 0 < b)
    (hm : (n:ℝ)/(2*(k:ℝ)) ≤ m)
    (hblag : (b:ℝ) ≤ 5*B/((k:ℝ)*γ))
    (hlarge : 360*B ≤ (n:ℝ)*p*γ*η^2) :
    2*b ≤ m ∧ 2/η ≤ (m:ℝ)*p/(2*(b:ℝ)) ∧
      (n:ℝ)*p*γ*η^2/(720*B) ≤ (m:ℝ)*p*η^2/(72*(b:ℝ)) := by
  have hkR : (0:ℝ) < k := Nat.cast_pos.mpr hk
  have hkγ : 0 < (k:ℝ)*γ := mul_pos hkR hγ
  have hbR : (0:ℝ) < b := Nat.cast_pos.mpr hb
  have hBpos : 0 < B := by linarith
  have hmk : (n:ℝ) ≤ 2*(m:ℝ)*(k:ℝ) := by
    have hh := (div_le_iff₀ (by positivity : (0:ℝ) < 2*(k:ℝ))).mp hm
    nlinarith
  have hbk : (b:ℝ)*(k:ℝ)*γ ≤ 5*B := by
    have hh := (le_div_iff₀ hkγ).mp hblag
    nlinarith
  have hηsq : η^2 ≤ 1 := by nlinarith
  have hpη : p*η^2 ≤ 1 := by
    exact (mul_le_mul hp1 hηsq (sq_nonneg η) (by norm_num)).trans_eq (by ring)
  have hng : 360*B ≤ (n:ℝ)*γ := by
    have hh := mul_le_mul_of_nonneg_left hpη (show 0 ≤ (n:ℝ)*γ by positivity)
    nlinarith
  have hηsqη : η^2 ≤ η := by nlinarith
  have hnpgη : 360*B ≤ (n:ℝ)*p*γ*η := by
    have hh := mul_le_mul_of_nonneg_left hηsqη (show 0 ≤ (n:ℝ)*p*γ by positivity)
    linarith
  have hmb : 2*(b:ℝ) ≤ m := by
    apply (mul_le_mul_iff_left₀ hkγ).mp
    have hh := mul_le_mul_of_nonneg_right hmk hγ.le
    nlinarith
  have hmpη : 4*(b:ℝ) ≤ (m:ℝ)*p*η := by
    apply (mul_le_mul_iff_left₀ hkγ).mp
    have hh := mul_le_mul_of_nonneg_right hmk (show 0 ≤ p*γ*η by positivity)
    nlinarith
  have hsize : 2/η ≤ (m:ℝ)*p/(2*(b:ℝ)) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*(b:ℝ))).mpr
    rw [show 2/η*(2*(b:ℝ)) = (4*(b:ℝ))/η by ring]
    exact (div_le_iff₀ hη).mpr hmpη
  have hnb : (n:ℝ)*(b:ℝ)*γ ≤ 10*(m:ℝ)*B := by
    apply (mul_le_mul_iff_left₀ hkR).mp
    have h1 := mul_le_mul_of_nonneg_left hbk (show 0 ≤ 2*(m:ℝ) by positivity)
    have h2 := mul_le_mul_of_nonneg_right hmk (show 0 ≤ (b:ℝ)*γ by positivity)
    nlinarith
  refine ⟨by exact_mod_cast hmb, hsize, ?_⟩
  apply (div_le_div_iff₀ (by positivity : 0 < 720*B)
    (by positivity : 0 < 72*(b:ℝ))).mpr
  have hh := mul_le_mul_of_nonneg_right hnb (show 0 ≤ 72*p*η^2 by positivity)
  nlinarith

/-- The explicit extra-log sample condition supplies every algebraic and
exponential estimate needed in the final finite union. -/
lemma sample_condition (d n : ℕ) (p γ ε δ : ℝ)
    (hd : 1 ≤ d) (hp : 0 < p) (hp1 : p ≤ 1) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hε : 0 < ε) (hε2 : ε < 1/2) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hn : 184320*logBudget p (ε/16)/(p*γ*ε^2)*
      log (40*(d:ℝ)*logBudget p (ε/16)/(δ*γ^2)) ≤ (n:ℝ)) :
    8/γ ≤ (n:ℝ) ∧ 360*logBudget p (ε/16) ≤ (n:ℝ)*p*γ*(ε/16)^2 ∧
      (24*(d:ℝ)*logBudget p (ε/16)/γ^2)*
        exp (-((n:ℝ)*p*γ*ε^2)/(184320*logBudget p (ε/16))) ≤ δ := by
  let B := logBudget p (ε/16)
  have hB : 1 ≤ B := logBudget_ge_one p (ε/16) hp hp1 (by positivity) (by linarith)
  have hBpos : 0 < B := by linarith
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hg2 : γ^2 ≤ 1 := by nlinarith
  have hδγ : δ*γ^2 ≤ 1 := by nlinarith [sq_nonneg γ]
  have hApos : 0 < 40*(d:ℝ)*B/(δ*γ^2) := by positivity
  have hA2 : (2:ℝ) ≤ 40*(d:ℝ)*B/(δ*γ^2) := by
    apply (le_div_iff₀ (by positivity : 0 < δ*γ^2)).mpr
    have hdB : 1 ≤ (d:ℝ)*B := by nlinarith
    nlinarith
  have hloghalf : (1/2:ℝ) ≤ log (40*(d:ℝ)*B/(δ*γ^2)) := by
    have hl := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 2 by norm_num)
    have hm := Real.log_le_log (show (0:ℝ) < 2 by norm_num) hA2
    norm_num at hl
    linarith
  have hden : 0 < p*γ*ε^2 := by positivity
  have hreq : 184320*B*log (40*(d:ℝ)*B/(δ*γ^2)) ≤ (n:ℝ)*(p*γ*ε^2) := by
    apply (div_le_iff₀ hden).mp
    simpa only [div_mul_eq_mul_div] using hn
  have hstrong : 92160*B ≤ (n:ℝ)*p*γ*ε^2 := by
    have hh := mul_le_mul_of_nonneg_left hloghalf (show 0 ≤ 184320*B by positivity)
    nlinarith
  have hpε : p*ε^2 ≤ 1 := by
    have he : ε^2 ≤ 1 := by nlinarith
    exact (mul_le_mul hp1 he (sq_nonneg ε) (by norm_num)).trans_eq (by ring)
  have hng : 8 ≤ (n:ℝ)*γ := by
    have hh := mul_le_mul_of_nonneg_left hpε (show 0 ≤ (n:ℝ)*γ by positivity)
    nlinarith
  refine ⟨(div_le_iff₀ hγ).mpr hng, by nlinarith, ?_⟩
  have hexp : exp (-((n:ℝ)*p*γ*ε^2)/(184320*B)) ≤
      exp (-log (40*(d:ℝ)*B/(δ*γ^2))) := by
    apply Real.exp_le_exp.mpr
    have hh : log (40*(d:ℝ)*B/(δ*γ^2)) ≤ (n:ℝ)*p*γ*ε^2/(184320*B) := by
      apply (le_div_iff₀ (by positivity : 0 < 184320*B)).mpr
      nlinarith
    simpa only [neg_div] using neg_le_neg hh
  calc _ ≤ (24*(d:ℝ)*B/γ^2)*exp (-log (40*(d:ℝ)*B/(δ*γ^2))) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = (3/5:ℝ)*δ := by
      rw [Real.exp_neg, Real.exp_log hApos, inv_div]
      field_simp
      <;> ring
    _ ≤ δ := by linarith

/-- Each lag in the deterministic estimator argument has the appendix
failure bound, including its actual initial distribution. -/
theorem lag_failure_bound {d : ℕ} [NeZero d] (E : Ergodic d) (n k : ℕ)
    (ε : ℝ) (hε : 0 < ε) (hε2 : ε < 1/2) (hk : 0 < k)
    (hkK : k ≤ ⌊1/gammaPS E.S E.st⌋₊)
    (hn : 8/gammaPS E.S E.st ≤ (n:ℝ))
    (hlarge : 360*logBudget (Stationary.star E.st) (ε/16) ≤
      (n:ℝ)*Stationary.star E.st*gammaPS E.S E.st*(ε/16)^2)
    (mu : Fin d → ℝ) (hmu : ∀ i, 0 ≤ mu i) (hsum : ∑ i, mu i = 1)
    (hFreedman : MatrixFreedmanInput (E.S.pow k) mu) :
    pathMeasure E.S.P mu (univ.filter fun X : Fin (n+1) → Fin d =>
      ¬ UpperProbability.lagGood E.S E.st ε k X) ≤
      (24*(d:ℝ)*logBudget (Stationary.star E.st) (ε/16)/((k:ℝ)*gammaPS E.S E.st))*
        exp (-((n:ℝ)*Stationary.star E.st*gammaPS E.S E.st*ε^2)/
          (184320*logBudget (Stationary.star E.st) (ε/16))) := by
  let γ := gammaPS E.S E.st
  let p := Stationary.star E.st
  let η := ε/16
  let B := logBudget p η
  let Γ := gammaPS (E.S.pow k) (stationaryPow E.S E.st k)
  let b := mixingLag (E.S.pow k) (stationaryPow E.S E.st k) η
  let m := n/k
  have hp : 0 < p := Stationary.star_pos E.st
  let i : Fin d := ⟨0,Nat.pos_of_neZero d⟩
  have hp1 : p ≤ 1 := (Stationary.star_le E.st i).trans
    (probability_coordinate_le_one E.st.mu E.st.nonneg E.st.sum_one i)
  have hγ : 0 < γ := E.gap_pos
  have hkR : (0:ℝ) < k := Nat.cast_pos.mpr hk
  have hkγ : 0 < (k:ℝ)*γ := mul_pos hkR hγ
  have hη : 0 < η := by dsimp [η]; positivity
  have hη4 : η ≤ 1/4 := by dsimp [η]; linarith
  have hB1 : 1 ≤ B := logBudget_ge_one p η hp hp1 hη (by linarith)
  have hkg : (k:ℝ)*γ ≤ 1 := by
    apply (le_div_iff₀ hγ).mp
    exact (Nat.cast_le.mpr hkK).trans (Nat.floor_le (by positivity))
  have hΓ : (k:ℝ)*γ/4 ≤ Γ := by
    have hh := ((lemma_1 E.S E.st E.gap_pos).1 k hk).1
    rw [min_eq_left hkg] at hh
    linarith
  have hΓpos : 0 < Γ := lt_of_lt_of_le (div_pos hkγ (by norm_num)) hΓ
  have hb : 0 < b := mixingLag_pos _ _ hΓpos η hη hη4
  have hbnd : (b:ℝ) ≤ 5*B/((k:ℝ)*γ) :=
    mixingLag_le E.S E.st γ η B hγ hη (by linarith) rfl k hk hkg hΓ
  have hng : 8 ≤ (n:ℝ)*γ := (div_le_iff₀ hγ).mp hn
  have h2k : 2*k ≤ n := by
    have hh : 2*(k:ℝ) ≤ n := by nlinarith
    exact_mod_cast hh
  have hm : (n:ℝ)/(2*(k:ℝ)) ≤ m := UpperProbability.div_cast_lower n k hk h2k
  have hocc := occupation_arithmetic n m k b p γ η B hp hp1 hγ hη (by linarith)
    hB1 hk hb hm hbnd hlarge
  let F : Finset (Fin (m+1) → Fin d) := univ.filter fun Y =>
    ¬ RelativeConcentration.good (E.S.pow k) (stationaryPow E.S E.st k) ((k:ℝ)*γ) η Y
  have hpush : pathMeasure E.S.P mu (univ.filter fun X : Fin (n+1) → Fin d =>
      ¬ UpperProbability.lagGood E.S E.st ε k X) = pathMeasure (E.S.P^k) mu F := by
    have hevent : (univ.filter fun X : Fin (n+1) → Fin d =>
        ¬ UpperProbability.lagGood E.S E.st ε k X) =
        univ.filter fun X => skipPath X k ∈ F := by
      ext X
      simp only [mem_filter, mem_univ, true_and, F, UpperProbability.lagGood,
        RelativeConcentration.good]
      rfl
    rw [hevent, skipPath_measure E.S.P mu E.S.row_stoch k F]
  have hpr := relative_failure (m:=m) (E.S.pow k) (stationaryPow E.S E.st k)
    ((k:ℝ)*γ) η mu hkγ hη hη4 hΓpos hmu hsum hocc.1 hocc.2.1 hFreedman
  change pathMeasure (E.S.P^k) mu F ≤
    4*(d:ℝ)*(b:ℝ)*exp (-((m:ℝ)*p*η^2/(72*(b:ℝ)))) +
      4*(d:ℝ)*exp (-(3*(m:ℝ)*p*((k:ℝ)*γ)*η^2)/16) at hpr
  have he1 : -((m:ℝ)*p*η^2/(72*(b:ℝ))) ≤
      -((n:ℝ)*p*γ*ε^2)/(184320*B) := by
    have hh := neg_le_neg hocc.2.2
    dsimp [η] at hh
    convert hh using 1 <;> ring
  have hmg := (UpperProbability.lag_sample_bounds n k γ Γ hγ hk hkK hn hΓ).2.2
  have he2 : -(3*(m:ℝ)*p*((k:ℝ)*γ)*η^2)/16 ≤
      -((n:ℝ)*p*γ*ε^2)/(184320*B) := by
    have hmul := mul_le_mul_of_nonneg_right hmg (show 0 ≤ p*η^2 by positivity)
    have hn0 : 0 ≤ (n:ℝ)*p*γ*η^2 := by positivity
    have hdiv : (n:ℝ)*p*γ*η^2/(720*B) ≤ (n:ℝ)*p*γ*η^2/720 :=
      div_le_div_of_nonneg_left hn0 (by norm_num) (by nlinarith only [hB1])
    have hh : (n:ℝ)*p*γ*η^2/(720*B) ≤ 3*(m:ℝ)*p*((k:ℝ)*γ)*η^2/16 := by
      nlinarith only [hmul, hdiv, hn0]
    dsimp [η] at hh
    convert neg_le_neg hh using 1 <;> ring
  have hcoef : 4*(d:ℝ)*(b:ℝ)+4*(d:ℝ) ≤ 24*(d:ℝ)*B/((k:ℝ)*γ) := by
    have hterm := mul_le_mul_of_nonneg_left hbnd (show 0 ≤ 4*(d:ℝ) by positivity)
    have hone : 1 ≤ B/((k:ℝ)*γ) := (le_div_iff₀ hkγ).mpr (by linarith)
    have hterm2 : 4*(d:ℝ) ≤ 4*(d:ℝ)*(B/((k:ℝ)*γ)) := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hone (show 0 ≤ 4*(d:ℝ) by positivity)
    calc _ ≤ 4*(d:ℝ)*(5*B/((k:ℝ)*γ))+4*(d:ℝ)*(B/((k:ℝ)*γ)) :=
        add_le_add hterm hterm2
      _ = _ := by ring
  rw [hpush]
  calc _ ≤ _ := hpr
    _ ≤ (4*(d:ℝ)*(b:ℝ)+4*(d:ℝ))*
        exp (-((n:ℝ)*p*γ*ε^2)/(184320*B)) := by
      calc _ ≤ 4*(d:ℝ)*(b:ℝ)*exp (-((n:ℝ)*p*γ*ε^2)/(184320*B)) +
          4*(d:ℝ)*exp (-((n:ℝ)*p*γ*ε^2)/(184320*B)) :=
            add_le_add (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he1) (by positivity))
              (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he2) (by positivity))
        _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (exp_nonneg _)

/-- Appendix A, paragraph 6, as an explicit finite-sample bound for the
original estimator, parametrized by the explicit matrix Freedman statement
for each actual thinned chain. The final theorem supplies its proved instance.
-/
theorem uniform_upper_of_freedman {d : ℕ} [NeZero d] (E : Ergodic d)
    (n : ℕ) (ε δ : ℝ) (hε : 0 < ε) (hε2 : ε < 1/2) (hδ : 0 < δ) (hδ1 : δ < 1)
    (mu : Fin d → ℝ) (hmu : ∀ i, 0 ≤ mu i) (hsum : ∑ i, mu i = 1)
    (hFreedman : ∀ k : ℕ, MatrixFreedmanInput (E.S.pow k) mu)
    (hn : 184320*logBudget (Stationary.star E.st) (ε/16)/
      (Stationary.star E.st*gammaPS E.S E.st*ε^2)*
      log (40*(d:ℝ)*logBudget (Stationary.star E.st) (ε/16)/
        (δ*(gammaPS E.S E.st)^2)) ≤ (n:ℝ)) :
    pathMeasure E.S.P mu (univ.filter fun X : Fin (n+1) → Fin d =>
      ε*gammaPS E.S E.st < |gammaHat X-gammaPS E.S E.st|) ≤ δ := by
  let γ := gammaPS E.S E.st
  let p := Stationary.star E.st
  let K := ⌊1/γ⌋₊
  let B := logBudget p (ε/16)
  let T := exp (-((n:ℝ)*p*γ*ε^2)/(184320*B))
  have hp : 0 < p := Stationary.star_pos E.st
  let i : Fin d := ⟨0,Nat.pos_of_neZero d⟩
  have hp1 : p ≤ 1 := (Stationary.star_le E.st i).trans
    (probability_coordinate_le_one E.st.mu E.st.nonneg E.st.sum_one i)
  have hγ : 0 < γ := E.gap_pos
  have hB1 : 1 ≤ B := logBudget_ge_one p (ε/16) hp hp1 (by positivity) (by linarith)
  have hs := sample_condition d n p γ ε δ (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))
    hp hp1 hγ E.gap_le_one hε hε2 hδ hδ1 hn
  have hKcast : (K:ℝ) ≤ 1/γ := Nat.floor_le (by positivity)
  have hKn : K ≤ n := by
    have hinv : 1/γ ≤ 8/γ := div_le_div_of_nonneg_right (by norm_num) hγ.le
    have hh : (K:ℝ) ≤ n := hKcast.trans (hinv.trans hs.1)
    exact_mod_cast hh
  let bad : Fin K → (Fin (n+1) → Fin d) → Prop :=
    fun j X => ¬ UpperProbability.lagGood E.S E.st ε (j.val+1) X
  have hcovered : (univ.filter fun X : Fin (n+1) → Fin d =>
      ε*γ < |gammaHat X-γ|) ⊆ univ.filter fun X => ∃ j : Fin K, bad j X := by
    intro X hX
    simp only [mem_filter, mem_univ, true_and] at *
    by_contra hnone
    have hgood : ∀ k : ℕ, 0 < k → k ≤ K → UpperProbability.lagGood E.S E.st ε k X := by
      intro k hk hkK
      have hj : k-1 < K := by omega
      have hnot := not_exists.mp hnone (⟨k-1,hj⟩ : Fin K)
      have hkval : k-1+1 = k := by omega
      simpa only [bad, hkval, not_not] using hnot
    have he := gammaHat_error_of_prop1_bounds X E.S E.st E.gap_pos ε hε hε2 hKn hgood
    exact (not_le_of_gt hX) he
  have hbad (j : Fin K) : pathMeasure E.S.P mu (univ.filter (bad j)) ≤
      (24*(d:ℝ)*B/γ)*T := by
    have hjpos : 0 < j.val+1 := by omega
    have hjK : j.val+1 ≤ ⌊1/γ⌋₊ := by change j.val+1 ≤ K; omega
    have hh := lag_failure_bound E n (j.val+1) ε hε hε2 hjpos hjK hs.1 hs.2.1
      mu hmu hsum (hFreedman (j.val+1))
    have hden : γ ≤ ((j.val+1:ℕ):ℝ)*γ := by
      have hjR : (1:ℝ) ≤ ((j.val+1:ℕ):ℝ) := by exact_mod_cast hjpos
      nlinarith only [mul_le_mul_of_nonneg_right hjR hγ.le]
    exact hh.trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left (by positivity) hγ hden) (exp_nonneg _))
  calc _ ≤ pathMeasure E.S.P mu (univ.filter fun X => ∃ j : Fin K, bad j X) :=
      UpperProbability.pathMeasure_mono E.S.P mu E.S.nonneg hmu hcovered
    _ ≤ ∑ j : Fin K, pathMeasure E.S.P mu (univ.filter (bad j)) := by
      convert (UpperProbability.pathMeasure_exists_le (ι:=Fin K)
        E.S.P mu E.S.nonneg hmu bad) using 1 <;> congr
      funext j
      congr
    _ ≤ ∑ _j : Fin K, (24*(d:ℝ)*B/γ)*T := sum_le_sum (fun j _ => hbad j)
    _ = (K:ℝ)*(24*(d:ℝ)*B/γ)*T := by simp; ring
    _ ≤ (24*(d:ℝ)*B/γ^2)*T := by
      have hh := mul_le_mul_of_nonneg_right hKcast
        (show 0 ≤ 24*(d:ℝ)*B/γ by positivity)
      apply mul_le_mul_of_nonneg_right _ (exp_nonneg _)
      convert hh using 1 <;> ring
    _ ≤ δ := hs.2.2

lemma logBudget_sixteenth (p ε : ℝ) :
    logBudget p (ε/16) = 1+2*log (64/(ε*p)) := by
  have harg : 4/((ε/16)*p) = 64/(ε*p) := by ring
  simp only [logBudget, harg]

/-- Explicit finite-sample threshold witnessing the appendix's additional
logarithm, with the same inverse `p γ ε²` polynomial dependence. -/
def sampleSize (d : ℕ) (p γ ε δ : ℝ) : ℝ :=
  let B := 1+2*log (64/(ε*p))
  184320*B/(p*γ*ε^2)*log (40*(d:ℝ)*B/(δ*γ^2))

/-- The appendix guarantee, using a named explicit sample-size expression. -/
theorem uniform_upper_sampleSize_of_freedman {d : ℕ} [NeZero d] (E : Ergodic d)
    (n : ℕ) (ε δ : ℝ) (hε : 0 < ε) (hε2 : ε < 1/2) (hδ : 0 < δ) (hδ1 : δ < 1)
    (mu : Fin d → ℝ) (hmu : ∀ i, 0 ≤ mu i) (hsum : ∑ i, mu i = 1)
    (hFreedman : ∀ k : ℕ, MatrixFreedmanInput (E.S.pow k) mu)
    (hn : sampleSize d (Stationary.star E.st) (gammaPS E.S E.st) ε δ ≤ (n:ℝ)) :
    pathMeasure E.S.P mu (univ.filter fun X : Fin (n+1) → Fin d =>
      ε*gammaPS E.S E.st < |gammaHat X-gammaPS E.S E.st|) ≤ δ := by
  apply uniform_upper_of_freedman E n ε δ hε hε2 hδ hδ1 mu hmu hsum hFreedman
  simpa only [logBudget_sixteenth] using hn

/-- The complete appendix alternative: an explicit extra-log sample condition
for the original estimator, with no external concentration premise. -/
theorem uniform_upper_sampleSize {d : ℕ} [NeZero d] (E : Ergodic d)
    (n : ℕ) (ε δ : ℝ) (hε : 0 < ε) (hε2 : ε < 1/2) (hδ : 0 < δ) (hδ1 : δ < 1)
    (mu : Fin d → ℝ) (hmu : ∀ i, 0 ≤ mu i) (hsum : ∑ i, mu i = 1)
    (hn : sampleSize d (Stationary.star E.st) (gammaPS E.S E.st) ε δ ≤ (n:ℝ)) :
    pathMeasure E.S.P mu (univ.filter fun X : Fin (n+1) → Fin d =>
      ε*gammaPS E.S E.st < |gammaHat X-gammaPS E.S E.st|) ≤ δ := by
  exact uniform_upper_sampleSize_of_freedman E n ε δ hε hε2 hδ hδ1 mu hmu hsum
    (fun k => matrixFreedman_proved (E.S.pow k) mu) hn

/-- The same conclusion with all logarithms and the numerical constant
visible in the sufficient sample-size condition. -/
theorem uniform_upper {d : ℕ} [NeZero d] (E : Ergodic d)
    (n : ℕ) (ε δ : ℝ) (hε : 0 < ε) (hε2 : ε < 1/2) (hδ : 0 < δ) (hδ1 : δ < 1)
    (mu : Fin d → ℝ) (hmu : ∀ i, 0 ≤ mu i) (hsum : ∑ i, mu i = 1)
    (hn : let p := Stationary.star E.st
      let γ := gammaPS E.S E.st
      let B := 1+2*log (64/(ε*p))
      184320*B/(p*γ*ε^2)*log (40*(d:ℝ)*B/(δ*γ^2)) ≤ (n:ℝ)) :
    pathMeasure E.S.P mu (univ.filter fun X : Fin (n+1) → Fin d =>
      ε*gammaPS E.S E.st < |gammaHat X-gammaPS E.S E.st|) ≤ δ := by
  exact uniform_upper_sampleSize E n ε δ hε hε2 hδ hδ1 mu hmu hsum hn

end
end PsgEst.AlternativeUpper
