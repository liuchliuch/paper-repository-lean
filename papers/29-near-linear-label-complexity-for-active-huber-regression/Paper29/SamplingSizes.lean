import Paper29.AccuracyConstants
import Paper29.FiniteScoreConstruction
import Mathlib.Tactic.GCongr

noncomputable section
open scoped BigOperators
namespace Paper29.ProcessTools

def pilotRawSize {n : ℕ} (C G : ℝ) (τ : Fin n → ℝ) : ℝ :=
  (128*C*G)^2*(2*∑ i,τ i)*Real.log (2*(n:ℝ))^3*((pilotGrid n).card:ℝ)^2/failureProbability^2

def mainRawSize {n : ℕ} (C G : ℝ) (τ : Fin n → ℝ) (ε : ℝ) : ℝ :=
  transferConstant C G 16*(∑ i,τ i)*Real.log (2*(n:ℝ))^3/
    ((mainAccuracy ε)^2*failureProbability^2)

def pilotSizeConstant (C G K : ℝ) : ℝ :=
  (128*C*G)^2*2*K*(6/Real.log 2)^2/failureProbability^2

def mainSizeConstant (C G K : ℝ) : ℝ :=
  transferConstant C G 16*K*pilotC₀^2/failureProbability^2

theorem raw_sizes_rank_bound {n r : ℕ} (hn : 1 ≤ n) (C G K : ℝ)
    (hK : 0 ≤ K) (τ : Fin n → ℝ) (hτ : ∀ i, 0 ≤ τ i)
    (hT : (∑ i,τ i) ≤ K*r*Real.log (2*(n:ℝ)))
    {ε : ℝ} (hε : 0 < ε) (hεhi : ε < 1/2) :
    pilotRawSize C G τ ≤ pilotSizeConstant C G K*r*Real.log (2*(n:ℝ))^6 ∧
      mainRawSize C G τ ε ≤ mainSizeConstant C G K*r*Real.log (2*(n:ℝ))^4/ε^2 := by
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (2*(n:ℝ)) := (Real.log_pos (by linarith : (1:ℝ)<2*n)).le
  have hgrid := pilotGrid_card_le hn
  have hcoef : 0 ≤ 6/Real.log 2 := by positivity
  have hmass : 0 ≤ ∑ i,τ i := Finset.sum_nonneg (fun i _ => hτ i)
  have hfail : 0 < failureProbability^2 := by norm_num [failureProbability]
  have hη := mainAccuracy_spec hε hεhi
  constructor
  · unfold pilotRawSize
    calc
      _ ≤ (128*C*G)^2*(2*(K*r*Real.log (2*(n:ℝ))))*Real.log (2*(n:ℝ))^3*
          ((6/Real.log 2)*Real.log (2*(n:ℝ)))^2/failureProbability^2 := by
        gcongr
      _ = _ := by unfold pilotSizeConstant; ring
  · have htransfer : 0 ≤ transferConstant C G 16 := by unfold transferConstant; positivity
    unfold mainRawSize
    calc
      _ = (transferConstant C G 16*(∑ i,τ i)*Real.log (2*(n:ℝ))^3/failureProbability^2) *
          (1/(mainAccuracy ε)^2) := by ring
      _ ≤ (transferConstant C G 16*(K*r*Real.log (2*(n:ℝ)))*Real.log (2*(n:ℝ))^3/failureProbability^2) *
          (1/(mainAccuracy ε)^2) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        gcongr
      _ ≤ (transferConstant C G 16*(K*r*Real.log (2*(n:ℝ)))*Real.log (2*(n:ℝ))^3/failureProbability^2) *
          (pilotC₀^2/ε^2) := mul_le_mul_of_nonneg_left hη.2.2.2 (by positivity)
      _ = _ := by unfold mainSizeConstant; ring

/-- Ceiling costs are absorbed by a universal log-six term. -/
theorem rounded_size_bound {n r : ℕ} (hn : 1 ≤ n) (hr : 1 ≤ r)
    {a b P M ε : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hP : 0 ≤ P) (hM : 0 ≤ M)
    (hε : 0 < ε)
    (hpilot : a ≤ P*r*Real.log (2*(n:ℝ))^6)
    (hmain : b ≤ M*r*Real.log (2*(n:ℝ))^4/ε^2) :
    ((⌈a⌉₊+⌈b⌉₊:ℕ):ℝ) ≤
      (P+M+2/(Real.log 2)^6)*r*(Real.log (2*(n:ℝ))^6+Real.log (2*(n:ℝ))^4/ε^2) := by
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hrR : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hln : Real.log 2 ≤ Real.log (2*(n:ℝ)) := Real.log_le_log (by norm_num) (by linarith)
  have hlog : 0 ≤ Real.log (2*(n:ℝ)) := hl2.le.trans hln
  have hpw : (Real.log 2)^6 ≤ Real.log (2*(n:ℝ))^6 := pow_le_pow_left₀ hl2.le hln 6
  have hcost : 2 ≤ (2/(Real.log 2)^6)*r*Real.log (2*(n:ℝ))^6 := by
    have hp : 0 < (Real.log 2)^6 := pow_pos hl2 6
    have hscaled : (Real.log 2)^6 ≤ (r:ℝ)*Real.log (2*(n:ℝ))^6 := by
      exact hpw.trans (le_mul_of_one_le_left (pow_nonneg hlog 6) hrR)
    have hh : 2 ≤ 2*((r:ℝ)*Real.log (2*(n:ℝ))^6)/(Real.log 2)^6 :=
      (le_div_iff₀ hp).2 (by linarith)
    convert hh using 1 <;> ring
  have hceil₀ := Nat.ceil_lt_add_one ha
  have hceil := Nat.ceil_lt_add_one hb
  have hbase : ((⌈a⌉₊+⌈b⌉₊:ℕ):ℝ) ≤
      (P+2/(Real.log 2)^6)*r*Real.log (2*(n:ℝ))^6+M*r*Real.log (2*(n:ℝ))^4/ε^2 := by
    push_cast
    nlinarith only [hceil₀,hceil,hpilot,hmain,hcost]
  apply hbase.trans
  have h₁ := mul_nonneg (mul_nonneg hM (Nat.cast_nonneg r)) (pow_nonneg hlog 6)
  have h₂ := div_nonneg (mul_nonneg (mul_nonneg
    (add_nonneg hP (by positivity : (0:ℝ)≤2/(Real.log 2)^6)) (Nat.cast_nonneg r))
    (pow_nonneg hlog 4)) (sq_nonneg ε)
  calc
    _ ≤ ((P+2/(Real.log 2)^6)*r*Real.log (2*(n:ℝ))^6+M*r*Real.log (2*(n:ℝ))^4/ε^2) +
        M*r*Real.log (2*(n:ℝ))^6 +
        (P+2/(Real.log 2)^6)*r*Real.log (2*(n:ℝ))^4/ε^2 := by linarith only [h₁,h₂]
    _ = _ := by ring

end Paper29.ProcessTools
