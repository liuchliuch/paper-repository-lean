import PsgEst.ProbabilityResidues
import PsgEst.Mixing

/-! Appendix A's occupation bound for the actual outgoing and incoming
counts. Residue laws, residue cardinalities, finite unions and the scalar
martingale estimate are all proved before this final composition. -/

open Matrix BigOperators Real Finset Classical
namespace PsgEst

/-- If a sum exceeds the sum of prescribed absolute bounds, one component
exceeds its own bound. No independence is used. -/
lemma appendix_abs_sum_bad_exists {α : Type*} [Fintype α] (x w : α → ℝ)
    (hbad : ∑ a, w a < |∑ a, x a|) : ∃ a, w a < |x a| := by
  by_contra h
  push_neg at h
  have hs : |∑ a, x a| ≤ ∑ a, w a :=
    (Finset.abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun a _ => h a))
  exact (not_lt_of_ge hs) hbad

/-- A deviation in the full window implies a deviation in an actual residue. -/
theorem appendix_window_bad_residue {d m b : ℕ} (hb : 0 < b) (hm : b ≤ m)
    (η p : ℝ) (i : Fin d) (Y : Fin m → Fin d)
    (hbad : η*(m:ℝ)*p < |observationVisitCount i Y - (m:ℝ)*p|) :
    ∃ r : Fin b, η*(residueLength m b r : ℝ)*p <
      |appendixVisitCount i (residuePath hb r (residueLength_pos hb hm r) Y) -
        (residueLength m b r : ℝ)*p| := by
  have hlength : (∑ r : Fin b, (residueLength m b r : ℝ)) = (m:ℝ) := by
    exact_mod_cast sum_residueLength (m := m) hb
  have hsum : observationVisitCount i Y - (m:ℝ)*p =
      ∑ r : Fin b, (appendixVisitCount i (residuePath hb r (residueLength_pos hb hm r) Y) -
        (residueLength m b r : ℝ)*p) := by
    rw [sum_sub_distrib, ← sum_mul, hlength, observationVisitCount_eq_sum_appendix hb hm]
  have hweights : (∑ r : Fin b, η*(residueLength m b r : ℝ)*p) = η*(m:ℝ)*p := by
    rw [← sum_mul, ← mul_sum, hlength]
  apply appendix_abs_sum_bad_exists
    (fun r : Fin b => appendixVisitCount i (residuePath hb r (residueLength_pos hb hm r) Y) -
      (residueLength m b r : ℝ)*p)
    (fun r : Fin b => η*(residueLength m b r : ℝ)*p)
  rwa [hweights, ← hsum]

/-- The smaller-residue exponent dominates the uniform window exponent. -/
theorem appendix_residue_exponent {m b : ℕ} (hb : 0 < b) (hm : 2*b ≤ m)
    (η p : ℝ) (hp : 0 ≤ p) (r : Fin b) :
    (m:ℝ)*p*η^2/(72*(b:ℝ)) ≤ η^2*(residueLength m b r : ℝ)*p/36 := by
  have hlen := residueLength_ge_half_ratio hb hm r
  have hc : 0 ≤ η^2*p/36 := by positivity
  calc
    _ = (η^2*p/36)*((m:ℝ)/(2*(b:ℝ))) := by field_simp; ring
    _ ≤ (η^2*p/36)*(residueLength m b r : ℝ) := mul_le_mul_of_nonneg_left hlen hc
    _ = _ := by ring

/-- A single residue in a genuine observation window has the scalar tail
under its actual shifted initial distribution and thinned transition. -/
theorem appendix_residue_tail {d m b n : ℕ} (S : Stoch d) (st : Stationary S)
    (mu : Fin d → ℝ) (hmu : ∀ a, 0 ≤ mu a) (hsum : ∑ a, mu a = 1)
    (η : ℝ) (hη : 0 < η) (hη4 : η ≤ 1/4) (hb : 0 < b) (hm : 2*b ≤ m)
    (hentry : ∀ a j, |(S.pow b).P a j / st.mu j - 1| ≤ η/4)
    (i : Fin d) (hsize : 2/η ≤ (m:ℝ)*st.mu i/(2*(b:ℝ)))
    (hinput : ∀ r : ℕ, MatrixFreedmanInput (S.pow b) (shiftedLaw S.P mu r))
    (s : ℕ) (hwindow : s+m ≤ n+1) (r : Fin b) :
    eventProb S.P mu (fun X : Fin (n+1) → Fin d =>
      η*(residueLength m b r : ℝ)*st.mu i <
        |appendixVisitCount i (residuePath hb r (residueLength_pos hb (by omega) r)
          (trajectoryWindow s m hwindow X)) - (residueLength m b r : ℝ)*st.mu i|) ≤
      2*exp (-((m:ℝ)*st.mu i*η^2/(72*(b:ℝ)))) := by
  let ell := residueLength m b r
  have hpos : 0 < ell := residueLength_pos hb (by omega) r
  have heq : ell-1+1 = ell := by omega
  have hsizer : 2/η ≤ (ell:ℝ)*st.mu i := by
    calc
      _ ≤ (m:ℝ)*st.mu i/(2*(b:ℝ)) := hsize
      _ = ((m:ℝ)/(2*(b:ℝ)))*st.mu i := by ring
      _ ≤ (ell:ℝ)*st.mu i :=
        mul_le_mul_of_nonneg_right (residueLength_ge_half_ratio hb hm r) (st.nonneg i)
  have htail := appendix_visit_count_tail (m := ell-1) (S.pow b) (stationaryPow S st b)
    (shiftedLaw S.P mu (s+r.val)) (shiftedLaw_nonneg S mu hmu _) (shiftedLaw_sum S mu hsum _)
    η hη hη4 hentry i (by simpa only [heq] using hsizer) (hinput (s+r.val))
  let E : (Fin (ell-1+1) → Fin d) → Prop := fun Y =>
    η*(ell:ℝ)*st.mu i < |appendixVisitCount i Y - (ell:ℝ)*st.mu i|
  have hlaw := residuePath_eventProb S.P mu S.row_stoch hb r hpos s hwindow E
  change eventProb S.P mu (fun X : Fin (n+1) → Fin d =>
    E (residuePath hb r hpos (trajectoryWindow s m hwindow X))) ≤ _
  rw [hlaw]
  calc
    _ ≤ 2*exp (-(η^2*(ell:ℝ)*st.mu i/36)) := by simpa only [E, heq] using htail
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.exp_le_exp.mpr (neg_le_neg (appendix_residue_exponent hb hm η (st.mu i) (st.nonneg i) r))

/-- Finite union over residue classes gives the count bound in any actual
window. The residue sequences are not asserted to be independent. -/
theorem appendix_window_tail {d m b n : ℕ} (S : Stoch d) (st : Stationary S)
    (mu : Fin d → ℝ) (hmu : ∀ a, 0 ≤ mu a) (hsum : ∑ a, mu a = 1)
    (η : ℝ) (hη : 0 < η) (hη4 : η ≤ 1/4) (hb : 0 < b) (hm : 2*b ≤ m)
    (hentry : ∀ a j, |(S.pow b).P a j / st.mu j - 1| ≤ η/4)
    (i : Fin d) (hsize : 2/η ≤ (m:ℝ)*st.mu i/(2*(b:ℝ)))
    (hinput : ∀ r : ℕ, MatrixFreedmanInput (S.pow b) (shiftedLaw S.P mu r))
    (s : ℕ) (hwindow : s+m ≤ n+1) :
    eventProb S.P mu (fun X : Fin (n+1) → Fin d =>
      η*(m:ℝ)*st.mu i < |observationVisitCount i (trajectoryWindow s m hwindow X) - (m:ℝ)*st.mu i|) ≤
      2*(b:ℝ)*exp (-((m:ℝ)*st.mu i*η^2/(72*(b:ℝ)))) := by
  let E : Fin b → (Fin (n+1) → Fin d) → Prop := fun r X =>
    η*(residueLength m b r : ℝ)*st.mu i <
      |appendixVisitCount i (residuePath hb r (residueLength_pos hb (by omega) r)
        (trajectoryWindow s m hwindow X)) - (residueLength m b r : ℝ)*st.mu i|
  calc
    _ ≤ eventProb S.P mu (fun X : Fin (n+1) → Fin d => ∃ r : Fin b, E r X) :=
      eventProb_mono S.P mu S.nonneg hmu (fun X hX =>
        appendix_window_bad_residue hb (by omega) η (st.mu i) i _ hX)
    _ ≤ ∑ r : Fin b, eventProb S.P mu (E r) := eventProb_exists_le S.P mu S.nonneg hmu E
    _ ≤ ∑ _ : Fin b, 2*exp (-((m:ℝ)*st.mu i*η^2/(72*(b:ℝ)))) :=
      sum_le_sum (fun r _ => appendix_residue_tail S st mu hmu hsum η hη hη4 hb hm
        hentry i hsize hinput s hwindow r)
    _ = _ := by simp; ring

/-- The departure observation window counts exactly the outgoing degrees. -/
lemma appendix_departure_window {d m : ℕ} (i : Fin d) (Y : Fin (m+1) → Fin d) :
    observationVisitCount i (trajectoryWindow 0 m (by omega) Y) = stateSum (stateIndicator i) false Y := by
  unfold observationVisitCount stateSum
  apply sum_congr rfl
  intro t _
  apply congrArg (stateIndicator i)
  apply congrArg Y
  apply Fin.ext
  simp [observationIndex]

/-- The arrival observation window counts exactly the incoming degrees. -/
lemma appendix_arrival_window {d m : ℕ} (i : Fin d) (Y : Fin (m+1) → Fin d) :
    observationVisitCount i (trajectoryWindow 1 m (by omega) Y) = stateSum (stateIndicator i) true Y := by
  unfold observationVisitCount stateSum
  apply sum_congr rfl
  intro t _
  apply congrArg (stateIndicator i)
  apply congrArg Y
  apply Fin.ext
  simp [observationIndex]
  omega

/-- State-sum version of the window tail for both true observation offsets. -/
theorem appendix_stateSum_tail {d m b : ℕ} (S : Stoch d) (st : Stationary S)
    (mu : Fin d → ℝ) (hmu : ∀ a, 0 ≤ mu a) (hsum : ∑ a, mu a = 1)
    (η : ℝ) (hη : 0 < η) (hη4 : η ≤ 1/4) (hb : 0 < b) (hm : 2*b ≤ m)
    (hentry : ∀ a j, |(S.pow b).P a j / st.mu j - 1| ≤ η/4)
    (i : Fin d) (hsize : 2/η ≤ (m:ℝ)*st.mu i/(2*(b:ℝ)))
    (hinput : ∀ r : ℕ, MatrixFreedmanInput (S.pow b) (shiftedLaw S.P mu r)) (a : Bool) :
    eventProb S.P mu (fun Y : Fin (m+1) → Fin d =>
      η*(m:ℝ)*st.mu i < |stateSum (stateIndicator i) a Y - (m:ℝ)*st.mu i|) ≤
      2*(b:ℝ)*exp (-((m:ℝ)*st.mu i*η^2/(72*(b:ℝ)))) := by
  cases a
  · simpa only [appendix_departure_window] using
      appendix_window_tail (n := m) S st mu hmu hsum η hη hη4 hb hm hentry i hsize hinput 0 (by omega)
  · simpa only [appendix_arrival_window] using
      appendix_window_tail (n := m) S st mu hmu hsum η hη hη4 hb hm hentry i hsize hinput 1 (by omega)

/-- The joint outgoing/incoming degree tail in Appendix A. The minimum mass
is the actual `Stationary.star` of the given chain. -/
theorem appendix_degree_tail {d m b : ℕ} [NeZero d] (S : Stoch d) (st : Stationary S)
    (mu : Fin d → ℝ) (hmu : ∀ a, 0 ≤ mu a) (hsum : ∑ a, mu a = 1)
    (η : ℝ) (hη : 0 < η) (hη4 : η ≤ 1/4) (hb : 0 < b) (hm : 2*b ≤ m)
    (hentry : ∀ a j, |(S.pow b).P a j / st.mu j - 1| ≤ η/4)
    (hsize : 2/η ≤ (m:ℝ)*Stationary.star st/(2*(b:ℝ)))
    (hinput : ∀ r : ℕ, MatrixFreedmanInput (S.pow b) (shiftedLaw S.P mu r)) :
    eventProb S.P mu (fun Y : Fin (m+1) → Fin d => ¬ degreeEvent st.mu η Y) ≤
      4*(d:ℝ)*(b:ℝ)*exp (-((m:ℝ)*Stationary.star st*η^2/(72*(b:ℝ)))) := by
  let C := 2*(b:ℝ)*exp (-((m:ℝ)*Stationary.star st*η^2/(72*(b:ℝ))))
  let E : Bool × Fin d → (Fin (m+1) → Fin d) → Prop := fun ai Y =>
    η*(m:ℝ)*st.mu ai.2 < |stateSum (stateIndicator ai.2) ai.1 Y - (m:ℝ)*st.mu ai.2|
  have hstate (a : Bool) (i : Fin d) : eventProb S.P mu (E (a,i)) ≤ C := by
    have hsizei : 2/η ≤ (m:ℝ)*st.mu i/(2*(b:ℝ)) :=
      hsize.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Stationary.star_le st i) (Nat.cast_nonneg m)) (by positivity))
    have hexp : exp (-((m:ℝ)*st.mu i*η^2/(72*(b:ℝ)))) ≤
        exp (-((m:ℝ)*Stationary.star st*η^2/(72*(b:ℝ)))) := by
      apply Real.exp_le_exp.mpr
      apply neg_le_neg
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Stationary.star_le st i) (Nat.cast_nonneg m)) (sq_nonneg η)
    have htail : eventProb S.P mu (E (a,i)) ≤
        2*(b:ℝ)*exp (-((m:ℝ)*st.mu i*η^2/(72*(b:ℝ)))) :=
      appendix_stateSum_tail S st mu hmu hsum η hη hη4 hb hm hentry i hsizei hinput a
    exact htail.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
  calc
    _ ≤ eventProb S.P mu (fun Y : Fin (m+1) → Fin d => ∃ ai, E ai Y) := by
      apply eventProb_mono S.P mu S.nonneg hmu
      intro Y hY
      change ¬ ∀ a i, _ at hY
      push_neg at hY
      obtain ⟨a,i,hi⟩ := hY
      exact ⟨(a,i),hi⟩
    _ ≤ ∑ ai : Bool × Fin d, eventProb S.P mu (E ai) := eventProb_exists_le S.P mu S.nonneg hmu E
    _ ≤ ∑ _ : Bool × Fin d, C := sum_le_sum (fun ai _ => hstate ai.1 ai.2)
    _ = _ := by simp [C]; ring

/-- The same bound stated directly for the actual incoming and outgoing
transition counts. -/
theorem appendix_degree_counts_tail {d m b : ℕ} [NeZero d] (S : Stoch d) (st : Stationary S)
    (mu : Fin d → ℝ) (hmu : ∀ a, 0 ≤ mu a) (hsum : ∑ a, mu a = 1)
    (η : ℝ) (hη : 0 < η) (hη4 : η ≤ 1/4) (hb : 0 < b) (hm : 2*b ≤ m)
    (hentry : ∀ a j, |(S.pow b).P a j / st.mu j - 1| ≤ η/4)
    (hsize : 2/η ≤ (m:ℝ)*Stationary.star st/(2*(b:ℝ)))
    (hinput : ∀ r : ℕ, MatrixFreedmanInput (S.pow b) (shiftedLaw S.P mu r)) :
    eventProb S.P mu (fun Y : Fin (m+1) → Fin d => ∃ i,
      η*(m:ℝ)*st.mu i < |(outDeg Y i:ℝ)-(m:ℝ)*st.mu i| ∨
      η*(m:ℝ)*st.mu i < |(inDeg Y i:ℝ)-(m:ℝ)*st.mu i|) ≤
      4*(d:ℝ)*(b:ℝ)*exp (-((m:ℝ)*Stationary.star st*η^2/(72*(b:ℝ)))) := by
  apply le_trans (eventProb_mono S.P mu S.nonneg hmu ?_)
    (appendix_degree_tail S st mu hmu hsum η hη hη4 hb hm hentry hsize hinput)
  intro Y hY hE
  obtain ⟨i,hi⟩ := hY
  rcases hi with ho | hi
  · have he := hE false i
    rw [← outDeg_eq_stateSum] at he
    exact not_lt_of_ge he ho
  · have he := hE true i
    rw [← inDeg_eq_stateSum] at he
    exact not_lt_of_ge he hi

/-- Appendix A with the actual explicit lag selected from the proved
exponential contraction and entrywise mixing estimates. -/
theorem appendix_degree_tail_mixingLag {d m : ℕ} [NeZero d] (S : Stoch d) (st : Stationary S)
    (hgap : 0 < gammaPS S st)
    (mu : Fin d → ℝ) (hmu : ∀ a, 0 ≤ mu a) (hsum : ∑ a, mu a = 1)
    (η : ℝ) (hη : 0 < η) (hη4 : η ≤ 1/4)
    (hm : 2*mixingLag S st η ≤ m)
    (hsize : 2/η ≤ (m:ℝ)*Stationary.star st/(2*(mixingLag S st η:ℝ)))
    (hinput : ∀ r : ℕ, MatrixFreedmanInput (S.pow (mixingLag S st η)) (shiftedLaw S.P mu r)) :
    eventProb S.P mu (fun Y : Fin (m+1) → Fin d => ¬ degreeEvent st.mu η Y) ≤
      4*(d:ℝ)*(mixingLag S st η:ℝ)*
        exp (-((m:ℝ)*Stationary.star st*η^2/(72*(mixingLag S st η:ℝ)))) := by
  apply appendix_degree_tail S st mu hmu hsum η hη hη4
    (mixingLag_pos S st hgap η hη hη4) hm ?_ hsize hinput
  intro a j
  exact (relative_entry_abs_le_exp S st hgap (mixingLag S st η) a j).trans
    (mixingLag_exp_bound S st hgap η hη)

/-- The explicit mixing-lag specialization, directly in terms of the actual
incoming and outgoing transition counts. -/
theorem appendix_degree_counts_tail_mixingLag {d m : ℕ} [NeZero d]
    (S : Stoch d) (st : Stationary S) (hgap : 0 < gammaPS S st)
    (mu : Fin d → ℝ) (hmu : ∀ a, 0 ≤ mu a) (hsum : ∑ a, mu a = 1)
    (η : ℝ) (hη : 0 < η) (hη4 : η ≤ 1/4)
    (hm : 2*mixingLag S st η ≤ m)
    (hsize : 2/η ≤ (m:ℝ)*Stationary.star st/(2*(mixingLag S st η:ℝ)))
    (hinput : ∀ r : ℕ, MatrixFreedmanInput (S.pow (mixingLag S st η)) (shiftedLaw S.P mu r)) :
    eventProb S.P mu (fun Y : Fin (m+1) → Fin d => ∃ i,
      η*(m:ℝ)*st.mu i < |(outDeg Y i:ℝ)-(m:ℝ)*st.mu i| ∨
      η*(m:ℝ)*st.mu i < |(inDeg Y i:ℝ)-(m:ℝ)*st.mu i|) ≤
      4*(d:ℝ)*(mixingLag S st η:ℝ)*
        exp (-((m:ℝ)*Stationary.star st*η^2/(72*(mixingLag S st η:ℝ)))) := by
  apply appendix_degree_counts_tail S st mu hmu hsum η hη hη4
    (mixingLag_pos S st hgap η hη hη4) hm ?_ hsize hinput
  intro a j
  exact (relative_entry_abs_le_exp S st hgap (mixingLag S st η) a j).trans
    (mixingLag_exp_bound S st hgap η hη)

/-- The original sample threshold (26) supplies both residue-size conditions
and reduces the explicit joint tail to `δ`. -/
theorem appendix_sample_condition (d m b : ℕ) (p η δ : ℝ)
    (hd : 1 ≤ d) (hb : 0 < b) (hp : 0 < p) (hp1 : p ≤ 1)
    (hη : 0 < η) (hη4 : η ≤ 1/4) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hm : 72*(b:ℝ)/(p*η^2)*log (4*(d:ℝ)*(b:ℝ)/δ) ≤ (m:ℝ)) :
    2*b ≤ m ∧ 2/η ≤ (m:ℝ)*p/(2*(b:ℝ)) ∧
      4*(d:ℝ)*(b:ℝ)*exp (-((m:ℝ)*p*η^2/(72*(b:ℝ)))) ≤ δ := by
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hbR : (1:ℝ) ≤ b := by exact_mod_cast (Nat.one_le_of_lt hb)
  have hdb : (1:ℝ) ≤ (d:ℝ)*(b:ℝ) := by
    have h := mul_le_mul hdR hbR (by norm_num : (0:ℝ) ≤ 1) (by linarith : (0:ℝ) ≤ d)
    simpa only [one_mul] using h
  have hApos : 0 < 4*(d:ℝ)*(b:ℝ)/δ := by positivity
  have hA2 : (2:ℝ) ≤ 4*(d:ℝ)*(b:ℝ)/δ := by
    apply (le_div_iff₀ hδ).mpr
    nlinarith
  have hloghalf : (1/2:ℝ) ≤ log (4*(d:ℝ)*(b:ℝ)/δ) := by
    have hl := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 2 by norm_num)
    have hmono := Real.log_le_log (show (0:ℝ) < 2 by norm_num) hA2
    norm_num at hl
    linarith
  have hden : 0 < p*η^2 := mul_pos hp (sq_pos_of_pos hη)
  have hreq : 72*(b:ℝ)*log (4*(d:ℝ)*(b:ℝ)/δ) ≤ (m:ℝ)*(p*η^2) := by
    apply (div_le_iff₀ hden).mp
    simpa only [div_mul_eq_mul_div] using hm
  have hstrong : 36*(b:ℝ) ≤ (m:ℝ)*(p*η^2) := by
    have hmul := mul_le_mul_of_nonneg_left hloghalf (show 0 ≤ 72*(b:ℝ) by positivity)
    nlinarith
  have hηsq : η^2 ≤ 1 := by nlinarith
  have hprod1 : p*η^2 ≤ 1 := by
    have h := mul_le_mul hp1 hηsq (sq_nonneg η) (by norm_num : (0:ℝ) ≤ 1)
    simpa only [one_mul] using h
  have hT : (m:ℝ)*(p*η^2) ≤ (m:ℝ) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hprod1 (Nat.cast_nonneg m)
  have hmreal : 2*(b:ℝ) ≤ (m:ℝ) := by nlinarith
  have hmNat : 2*b ≤ m := by exact_mod_cast hmreal
  have hηsqle : η^2 ≤ η := by
    nlinarith [mul_nonneg hη.le (show 0 ≤ 1-η by linarith)]
  have hmpη : 4*(b:ℝ) ≤ (m:ℝ)*p*η := by
    have hh := mul_le_mul_of_nonneg_left hηsqle
      (show 0 ≤ (m:ℝ)*p by positivity)
    nlinarith
  have hsize : 2/η ≤ (m:ℝ)*p/(2*(b:ℝ)) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*(b:ℝ))).mpr
    have hh : 4*(b:ℝ)/η ≤ (m:ℝ)*p := (div_le_iff₀ hη).mpr hmpη
    convert hh using 1
    ring
  refine ⟨hmNat,hsize,?_⟩
  have hexp : exp (-((m:ℝ)*p*η^2/(72*(b:ℝ)))) ≤
      exp (-log (4*(d:ℝ)*(b:ℝ)/δ)) := by
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    apply (le_div_iff₀ (by positivity : 0 < 72*(b:ℝ))).mpr
    nlinarith
  calc
    _ ≤ (4*(d:ℝ)*(b:ℝ))*exp (-log (4*(d:ℝ)*(b:ℝ)/δ)) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = δ := by
      rw [Real.exp_neg, Real.exp_log hApos, inv_div]
      field_simp

/-- Complete Lemma 2, with the source's explicit ceiling lag and both of its
conclusions. Only the original matrix Freedman theorem for the actual shifted
thinned laws is external; all Appendix A arguments have been proved. -/
theorem lemma_2_paper_of_freedman {d : ℕ} [NeZero d] (m : ℕ)
    (Q : Stoch d) (st : Stationary Q) (η δ : ℝ) (mu0 : Fin d → ℝ)
    (hη : 0 < η) (hη4 : η ≤ 1/4) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hmu : ∀ i, 0 ≤ mu0 i) (hsum : ∑ i, mu0 i = 1) (hgap : 0 < gammaPS Q st)
    (hinput : ∀ r : ℕ, MatrixFreedmanInput (Q.pow (mixingLag Q st η)) (shiftedLaw Q.P mu0 r)) :
    let p := Stationary.star st
    let Γ := gammaPS Q st
    let b : ℕ := Nat.ceil ((1 + 2*log (4/(η*p)))/Γ)
    let fail : Finset (Fin (m+1) → Fin d) := univ.filter fun Y => ¬ degreeEvent st.mu η Y
    ((72*b/(p*η^2)*log (4*(d:ℝ)*b/δ) ≤ (m:ℝ)) → pathMeasure Q.P mu0 fail ≤ δ) ∧
      ((2*b ≤ m ∧ 2/η ≤ (m:ℝ)*p/(2*b)) → pathMeasure Q.P mu0 fail ≤
        4*(d:ℝ)*b*exp (-((m:ℝ)*p*η^2/(72*b)))) := by
  dsimp only
  have hevent : pathMeasure Q.P mu0 (univ.filter fun Y : Fin (m+1) → Fin d =>
      ¬ degreeEvent st.mu η Y) = eventProb Q.P mu0
      (fun Y : Fin (m+1) → Fin d => ¬ degreeEvent st.mu η Y) := by
    unfold eventProb
    apply congrArg (pathMeasure Q.P mu0)
    ext Y
    simp only [mem_filter, mem_univ, true_and]
  simp only [hevent]
  change ((72*(mixingLag Q st η:ℝ)/(Stationary.star st*η^2)*
      log (4*(d:ℝ)*(mixingLag Q st η:ℝ)/δ) ≤ (m:ℝ)) →
      eventProb Q.P mu0 (fun Y : Fin (m+1) → Fin d => ¬ degreeEvent st.mu η Y) ≤ δ) ∧
    ((2*mixingLag Q st η ≤ m ∧ 2/η ≤ (m:ℝ)*Stationary.star st/(2*(mixingLag Q st η:ℝ))) →
      eventProb Q.P mu0 (fun Y : Fin (m+1) → Fin d => ¬ degreeEvent st.mu η Y) ≤
        4*(d:ℝ)*(mixingLag Q st η:ℝ)*exp (-((m:ℝ)*Stationary.star st*η^2/(72*(mixingLag Q st η:ℝ)))))
  have hb := mixingLag_pos Q st hgap η hη hη4
  constructor
  · intro hm
    have hp := Stationary.star_pos st
    let i : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
    have hp1 : Stationary.star st ≤ 1 := (Stationary.star_le st i).trans
      (probability_coordinate_le_one st.mu st.nonneg st.sum_one i)
    have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
    obtain ⟨hm2,hsize,hdelta⟩ := appendix_sample_condition d m (mixingLag Q st η)
      (Stationary.star st) η δ hd hb hp hp1 hη hη4 hδ hδ1 hm
    exact (appendix_degree_tail_mixingLag Q st hgap mu0 hmu hsum η hη hη4 hm2 hsize hinput).trans hdelta
  · rintro ⟨hm,hsize⟩
    exact appendix_degree_tail_mixingLag Q st hgap mu0 hmu hsum η hη hη4 hm hsize hinput

end PsgEst
