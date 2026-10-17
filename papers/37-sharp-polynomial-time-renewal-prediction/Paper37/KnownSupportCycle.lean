import Paper37.CycleAge
import Paper37.IIDTuple
import Paper37.CycleGoodEvent
import Paper37.RenewalCompression

/-! Appendix H.1 for the actual observation-word law, using the single explicit
classical equilibrium-cycle construction shared with Appendix F. All parsing,
sample selection, statistical bounds and endpoint compatibility are proved. -/
noncomputable section
namespace Paper37.KnownSupportCycle
open scoped BigOperators ENNReal
open Paper37.Renewal Paper37.Compression Paper37.Compression.Distribution
open Paper37.KnownSupportLaw Paper37.KnownSupportRisk Paper37.KnownSupportWord
open Paper37.BackwardRender Paper37.CycleAge Paper37.IIDTuple

lemma wordHazard_full_render {n B : ℕ} [Nonempty (Fin B)]
    (hB : 1 ≤ B) (hBn : 2*B ≤ n) (a : Fin B) (ds : Fin n → Fin B) :
    wordHazard B (n/B-1) (render n a.val (List.ofFn (fun i => (ds i).val))) =
      estimatedHazard (n/B-1) (takeSample (n/B-1) n
        (by have := Nat.div_le_self n B; omega) (fromFn n ds)) a := by
  let k := n/B-1
  have hk : k ≤ n := by dsimp [k];have := Nat.div_le_self n B;omega
  have hg : ∀ d ∈ List.ofFn (fun i => (ds i).val), d < B := by
    intro d hd
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hd
    exact (ds i).isLt
  have hex := render_extract_bounded hB hBn (by simp) a.isLt hg
  have hi := indices_of_toFn n (fromFn n ds)
  rw [toFn_fromFn] at hi
  have hpre := prefix_indices k n hk (fromFn n ds)
  rw [← hi] at hpre
  rw [← hpre] at hex
  have ha : a.val < n := by have := a.isLt;omega
  unfold wordHazard
  rw [render_age ha,if_pos a.isLt,hex,estimatedHazard_formula]
  simp_rw [sampleIndices_count]
  rfl

lemma source_word_mass (cycle : EquilibriumCycle.EquilibriumCyclePrinciple)
    (μ : Law) (B : ℕ) (hS : ∀ d, B ≤ d → μ.mass d=0)
    (n : ℕ) (w : List Bool) (hw : w.length=n) :
    (EquilibriumCycle.sampleLaw (toFinite (vector μ B hS)) (fun c : Fin B => c.val) n).eventMass
      (fun z => EquilibriumCycle.sampleWord (fun c : Fin B => c.val) n z=w) = blockMass μ w :=
  cycle (Fin B) (toFinite (vector μ B hS)) (fun c : Fin B => c.val) μ
    (vector_realizes μ B hS) n w hw

lemma positive_sample_word (cycle : EquilibriumCycle.EquilibriumCyclePrinciple)
    (μ : Law) (B : ℕ) (hS : ∀ d, B ≤ d → μ.mass d=0) (n : ℕ)
    (z : CyclePhase B × (Fin n → Fin B))
    (hz : 0 < (EquilibriumCycle.sampleLaw (toFinite (vector μ B hS))
      (fun c : Fin B => c.val) n).mass z) :
    0 < blockMass μ (EquilibriumCycle.sampleWord (fun c : Fin B => c.val) n z) := by
  rw [← source_word_mass cycle μ B hS n _ (EquilibriumCycle.sampleWord_length _ _ _)]
  apply hz.trans_le
  unfold Paper37.LowerBound.FiniteLaw.eventMass
  exact le_trans (by simp) (Finset.single_le_sum
    (fun i _ => by split_ifs;exact (EquilibriumCycle.sampleLaw _ _ _).nonneg i;rfl)
    (Finset.mem_univ z))

lemma rendered_conditional (μ : Law) {n B : ℕ} (hBn : 2*B ≤ n)
    (z : CyclePhase B × (Fin n → Fin B))
    (hp : 0 < blockMass μ (EquilibriumCycle.sampleWord (fun c : Fin B => c.val) n z)) :
    conditional μ (EquilibriumCycle.sampleWord (fun c : Fin B => c.val) n z) =
      μ.mass (phaseAge z.1).val / tail μ (phaseAge z.1).val := by
  have ha : z.1.2.val < n := by have := (phaseAge z.1).isLt; change z.1.2.val < B at this;omega
  have hseen : true ∈ EquilibriumCycle.sampleWord (fun c : Fin B => c.val) n z := by
    obtain ⟨j,x,hx,_,_⟩ := render_parse (ds:=List.ofFn (fun i => (z.2 i).val)) ha
    change true ∈ render n z.1.2.val _
    rw [hx]
    simp
  rw [conditional_visible_renewal μ _ hseen hp]
  change μ.mass (ageFrom 0 (render n z.1.2.val _)) / tail μ (ageFrom 0 (render n z.1.2.val _)) = _
  rw [render_age ha]
  rfl

/-- Exact source risk transport: the history-based predictor uses the latest
floor(n/B)-1 fully observed gaps, whose iid law is derived from the shared
classical cycle representation and the proved deterministic parser. -/
theorem realRisk_eq_product (cycle : EquilibriumCycle.EquilibriumCyclePrinciple)
    (μ : Law) {n B : ℕ} [Nonempty (Fin B)]
    (hS : ∀ d, B ≤ d → μ.mass d=0) (hB : 1 ≤ B) (hBn : 2*B ≤ n) :
    (∑ x ∈ (words n).toFinset, blockMass μ x *
      Boundary.klReal (conditional μ x) (wordHazard B (n/B-1) x)) =
    ∑ s, Paper37.IIDAddOne.iidLaw (vector μ B hS) (n/B-1) s *
      ∑ a : Fin B, (tail μ a.val/mean μ) * Boundary.klReal
        (μ.mass a.val/tail μ a.val) (estimatedHazard (n/B-1) s a) := by
  let p := vector μ B hS
  let P := EquilibriumCycle.sampleLaw (toFinite p) (fun c : Fin B => c.val) n
  let f := EquilibriumCycle.sampleWord (fun c : Fin B => c.val) n
  let k := n/B-1
  have hk : k ≤ n := by dsimp [k]; have := Nat.div_le_self n B;omega
  have hpush := Paper37.CycleGoodEvent.expectation_pushforward P f n
    (EquilibriumCycle.sampleWord_length _ _) (fun x => Boundary.klReal (conditional μ x) (wordHazard B k x))
  have hpush' : P.expectation (fun x => Boundary.klReal (conditional μ (f x)) (wordHazard B k (f x))) =
      ∑ w ∈ (words n).toFinset, blockMass μ w * Boundary.klReal (conditional μ w) (wordHazard B k w) := by
    rw [hpush]
    apply Finset.sum_congr rfl
    intro w hw
    have hwlen := (mem_words n w).mp (List.mem_toFinset.mp hw)
    change (EquilibriumCycle.sampleLaw (toFinite (vector μ B hS)) (fun c : Fin B => c.val) n).eventMass
      (fun z => EquilibriumCycle.sampleWord (fun c : Fin B => c.val) n z=w) * _ = _
    rw [source_word_mass cycle μ B hS n w hwlen]
  rw [← hpush',EquilibriumCycle.sampleLaw_expectation]
  change (∑ z : CyclePhase B, (EquilibriumCycle.phaseLaw (toFinite p) (fun c : Fin B => c.val)).mass z *
    ∑ ds : Fin n → Fin B, (∏ i, p (ds i)) * Boundary.klReal (conditional μ (f (z,ds))) (wordHazard B k (f (z,ds)))) = _
  have hpoint : ∀ z : CyclePhase B, ∀ ds : Fin n → Fin B,
    (EquilibriumCycle.phaseLaw (toFinite p) (fun c : Fin B => c.val)).mass z *
      ((∏ i, p (ds i)) * Boundary.klReal (conditional μ (f (z,ds))) (wordHazard B k (f (z,ds)))) =
    (EquilibriumCycle.phaseLaw (toFinite p) (fun c : Fin B => c.val)).mass z *
      ((∏ i, p (ds i)) * Boundary.klReal (μ.mass (phaseAge z).val/tail μ (phaseAge z).val)
        (estimatedHazard k (takeSample k n hk (fromFn n ds)) (phaseAge z))) := by
    intro z ds
    by_cases hz : P.mass (z,ds)=0
    · change (EquilibriumCycle.phaseLaw _ _).mass z * (∏ i,p (ds i))=0 at hz
      simp only [← mul_assoc,hz,zero_mul]
    · have hzpos : 0 < P.mass (z,ds) := lt_of_le_of_ne (P.nonneg _) (Ne.symm hz)
      have hp := positive_sample_word cycle μ B hS n (z,ds) hzpos
      rw [rendered_conditional μ hBn (z,ds) hp]
      change _ * (_ * Boundary.klReal _ (wordHazard B k (render n (phaseAge z).val _))) = _
      rw [wordHazard_full_render hB hBn]
  simp_rw [Finset.mul_sum,hpoint]
  simp_rw [← Finset.mul_sum]
  have hpre : ∀ z : CyclePhase B,
    (∑ ds : Fin n → Fin B, (∏ i,p (ds i)) * Boundary.klReal
      (μ.mass (phaseAge z).val/tail μ (phaseAge z).val)
      (estimatedHazard k (takeSample k n hk (fromFn n ds)) (phaseAge z))) =
    ∑ s, Paper37.IIDAddOne.iidLaw p k s * Boundary.klReal
      (μ.mass (phaseAge z).val/tail μ (phaseAge z).val) (estimatedHazard k s (phaseAge z)) := by
    intro z
    exact iidFn_prefix_expectation p k n hk (fun s : Paper37.IIDAddOne.Sample (Fin B) k =>
      Boundary.klReal (μ.mass (phaseAge z).val/tail μ (phaseAge z).val) (estimatedHazard k s (phaseAge z)))
  simp_rw [hpre]
  rw [phaseAge_expectation p (fun a => ∑ s, Paper37.IIDAddOne.iidLaw p k s *
    Boundary.klReal (μ.mass a.val/tail μ a.val) (estimatedHazard k s a))]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro a ha
  change (Paper37.HazardChain.survival p a.val/finiteMean p) *
    (Paper37.IIDAddOne.iidLaw p k s * _) = _
  rw [vector_survival,vector_mean]
  ring

/-- The complete H.2 inequalities for the actual word-based add-one predictor,
with the original renewal mean m and known positive gap bound B≤n/2. -/
theorem realRisk_bounds (cycle : EquilibriumCycle.EquilibriumCyclePrinciple)
    (μ : Law) {n B : ℕ} [Nonempty (Fin B)]
    (hS : ∀ d, B ≤ d → μ.mass d=0) (hB : 1 ≤ B) (hBn : 2*B ≤ n) :
    let R := ∑ x ∈ (words n).toFinset, blockMass μ x *
      Boundary.klReal (conditional μ x) (wordHazard B (n/B-1) x)
    R ≤ ((B:ℝ)-1)/(mean μ*(n/B:ℕ)) ∧
      R ≤ (B:ℝ)*((B:ℝ)-1)/(mean μ*((n:ℝ)-B)) ∧
      R ≤ 2*(B:ℝ)^2/(mean μ*n) ∧ R ≤ 2*(B:ℝ)^2/n := by
  dsimp only
  rw [realRisk_eq_product cycle μ hS hB hBn]
  exact product_risk_bounds μ hS hB hBn

lemma positive_word_render (cycle : EquilibriumCycle.EquilibriumCyclePrinciple)
    (μ : Law) (B : ℕ) (hS : ∀ d, B ≤ d → μ.mass d=0) (n : ℕ)
    (x : List Bool) (hx : x.length=n) (hp : 0 < blockMass μ x) :
    ∃ z : CyclePhase B × (Fin n → Fin B),
      0 < (EquilibriumCycle.sampleLaw (toFinite (vector μ B hS)) (fun c : Fin B => c.val) n).mass z ∧
      EquilibriumCycle.sampleWord (fun c : Fin B => c.val) n z=x := by
  classical
  rw [← source_word_mass cycle μ B hS n x hx] at hp
  unfold Paper37.LowerBound.FiniteLaw.eventMass at hp
  obtain ⟨z,_,hz⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun z _ => by split_ifs;exact (EquilibriumCycle.sampleLaw _ _ _).nonneg z;rfl)).mp hp
  split_ifs at hz with hzx
  · exact ⟨z,hz,hzx⟩
  · exact False.elim (lt_irrefl 0 hz)

lemma wordHazard_pos (B k : ℕ) (x : List Bool) : 0 < wordHazard B k x := by
  unfold wordHazard
  dsimp only
  split_ifs with ha
  · let a : Fin B := ⟨ageFrom 0 x,ha⟩
    have hn : 0 < (((extract k x).count (ageFrom 0 x):ℝ)+1) := by positivity
    apply div_pos hn
    apply hn.trans_le
    have h := Finset.single_le_sum (s:=Finset.univ)
      (f:=fun j : Fin B => if ageFrom 0 x ≤ j.val then (((extract k x).count j.val:ℝ)+1) else 0)
      (fun j _ => by dsimp;split_ifs <;> positivity) (Finset.mem_univ a)
    simpa only [a,le_refl,if_true] using h
  · norm_num

lemma wordHazard_lt_one {B k : ℕ} (x : List Bool)
    (ha : ageFrom 0 x+1 < B) : wordHazard B k x < 1 := by
  let a : Fin B := ⟨ageFrom 0 x,by omega⟩
  let b : Fin B := ⟨ageFrom 0 x+1,ha⟩
  let f := fun j : Fin B => if ageFrom 0 x ≤ j.val then (((extract k x).count j.val:ℝ)+1) else 0
  have hab : b ≠ a := by intro h;have hv := congrArg Fin.val h;dsimp [a,b] at hv;omega
  have hstrict : f a < ∑ j, f j := Finset.single_lt_sum hab (Finset.mem_univ a)
    (Finset.mem_univ b) (by dsimp [f,b];rw [if_pos (by omega)];positivity)
    (fun j _ _ => by dsimp [f];split_ifs <;> positivity)
  have hn : 0 < f a := by dsimp [f,a];rw [if_pos (le_refl _)];positivity
  have hd : 0 < ∑ j, f j := hn.trans hstrict
  unfold wordHazard
  rw [if_pos (show ageFrom 0 x < B by omega)]
  apply (div_lt_one hd).mpr
  simpa only [f,a,le_refl,if_true] using hstrict

lemma rendered_tail_pos (μ : Law) {n B : ℕ} (hBn : 2*B ≤ n)
    (z : CyclePhase B × (Fin n → Fin B))
    (hp : 0 < blockMass μ (EquilibriumCycle.sampleWord (fun c : Fin B => c.val) n z)) :
    0 < tail μ (phaseAge z.1).val := by
  have ha : z.1.2.val < n := by have := (phaseAge z.1).isLt;change z.1.2.val < B at this;omega
  have hseen : true ∈ EquilibriumCycle.sampleWord (fun c : Fin B => c.val) n z := by
    obtain ⟨j,x,hx,_,_⟩ := render_parse (ds:=List.ofFn (fun i => (z.2 i).val)) ha
    change true ∈ render n z.1.2.val _
    rw [hx]
    simp
  have hn : 0 < stationaryNumerator μ 0 (EquilibriumCycle.sampleWord (fun c : Fin B => c.val) n z) :=
    (div_pos_iff_of_pos_right (mean_pos μ)).mp hp
  have ht := stationary_positive_terminal_tail μ 0 _ hseen hn
  change 0 < tail μ (ageFrom 0 (render n z.1.2.val _)) at ht
  rw [render_age ha] at ht
  exact ht

/-- No positive-probability history receives an incompatible endpoint: the
only possible prediction 1 is the maximal age, where the true hazard is 1. -/
theorem endpoint_compatible (cycle : EquilibriumCycle.EquilibriumCyclePrinciple)
    (μ : Law) {n B : ℕ} (hS : ∀ d, B ≤ d → μ.mass d=0) (hBn : 2*B ≤ n)
    (x : List Bool) (hx : x.length=n) (hp : 0 < blockMass μ x)
    (hq : wordHazard B (n/B-1) x=1) : conditional μ x=1 := by
  obtain ⟨z,hz,hzx⟩ := positive_word_render cycle μ B hS n x hx hp
  have hpz : 0 < blockMass μ (EquilibriumCycle.sampleWord (fun c : Fin B => c.val) n z) := by rwa [hzx]
  have ha : z.1.2.val < n := by have := (phaseAge z.1).isLt;change z.1.2.val < B at this;omega
  have hage : ageFrom 0 x=(phaseAge z.1).val := by
    rw [← hzx]
    exact render_age ha
  have hlast : (phaseAge z.1).val+1=B := by
    have hlt := (phaseAge z.1).isLt
    by_contra hh
    have hsmall : ageFrom 0 x+1 < B := by rw [hage];omega
    have h := wordHazard_lt_one (k:=n/B-1) x hsmall
    linarith
  have ht0 : tail μ ((phaseAge z.1).val+1)=0 := by
    have hh : (fun d => if (phaseAge z.1).val+1 ≤ d then μ.mass d else 0) = (fun _ : ℕ => (0:ℝ)) := by
      funext d
      split_ifs with hd
      · exact hS d (by omega)
      · rfl
    rw [tail,hh,tsum_zero]
  have htail : tail μ (phaseAge z.1).val=μ.mass (phaseAge z.1).val := by
    rw [tail_step,ht0,add_zero]
  have ht := rendered_tail_pos μ hBn z hpz
  rw [← hzx,rendered_conditional μ hBn z hpz,← htail]
  exact div_self ht.ne'

lemma compatible_klReal_nonneg {p q : ℝ} (hp : 0 ≤ p ∧ p ≤ 1)
    (hq : 0 < q ∧ q ≤ 1) (he : q=1 → p=1) : 0 ≤ Boundary.klReal p q := by
  by_cases hq1 : q=1
  · simp [hq1,he hq1,Boundary.klReal]
  · have hqi : q < 1 := lt_of_le_of_ne hq.2 hq1
    rw [← Paper37.RenewalCompression.binary_klReal hp.1 hp.2 hq.1 hqi]
    apply Distribution.kl_nonneg
    intro b _
    cases b <;> simp [Paper37.RenewalCompression.binary] <;> linarith [hq.1]

/-- Conversion to the source's extended KL risk, including null-word zero
weights and the actual q=1 endpoint. No finite surrogate replaces infinity. -/
theorem risk_eq_ofReal (cycle : EquilibriumCycle.EquilibriumCyclePrinciple)
    (μ : Law) {n B : ℕ} (hS : ∀ d, B ≤ d → μ.mass d=0) (hBn : 2*B ≤ n) :
    Prediction.risk n (predictor B (n/B-1)) μ = ENNReal.ofReal
      (∑ x ∈ (words n).toFinset, blockMass μ x *
        Boundary.klReal (conditional μ x) (wordHazard B (n/B-1) x)) := by
  unfold Prediction.risk
  simp only [predictor,MeasureTheory.ProbabilityMeasure.toMeasure,MeasureTheory.lintegral_dirac]
  have heq : ∀ x ∈ (words n).toFinset,
    ENNReal.ofReal (blockMass μ x) * Boundary.kl (conditional μ x) (wordHazard B (n/B-1) x) =
      ENNReal.ofReal (blockMass μ x * Boundary.klReal (conditional μ x) (wordHazard B (n/B-1) x)) := by
    intro x hx
    by_cases hp0 : blockMass μ x=0
    · simp [hp0]
    · have hp : 0 < blockMass μ x := lt_of_le_of_ne (blockMass_nonneg μ x) (Ne.symm hp0)
      have hxlen := (mem_words n x).mp (List.mem_toFinset.mp hx)
      have hq0 := (wordHazard_pos B (n/B-1) x).ne'
      have hq1 := endpoint_compatible cycle μ hS hBn x hxlen hp
      have hkl : Boundary.kl (conditional μ x) (wordHazard B (n/B-1) x) =
          ENNReal.ofReal (Boundary.klReal (conditional μ x) (wordHazard B (n/B-1) x)) := by
        unfold Boundary.kl
        rw [if_neg (by simp only [hq0,false_and,false_or];exact fun h=>h.2 (hq1 h.1))]
      rw [hkl,← ENNReal.ofReal_mul (blockMass_nonneg μ x)]
  have hnonneg : ∀ x ∈ (words n).toFinset,
    0 ≤ blockMass μ x * Boundary.klReal (conditional μ x) (wordHazard B (n/B-1) x) := by
    intro x hx
    by_cases hp0 : blockMass μ x=0
    · simp [hp0]
    · have hp : 0 < blockMass μ x := lt_of_le_of_ne (blockMass_nonneg μ x) (Ne.symm hp0)
      have hxlen := (mem_words n x).mp (List.mem_toFinset.mp hx)
      exact mul_nonneg hp.le (compatible_klReal_nonneg (conditional_mem_unitInterval μ x)
        ⟨wordHazard_pos _ _ _,(wordHazard_mem _ _ _).2⟩
        (endpoint_compatible cycle μ hS hBn x hxlen hp))
  rw [Finset.sum_congr rfl heq]
  exact (ENNReal.ofReal_sum_of_nonneg hnonneg).symm

/-- Appendix H.1/H.2 for the actual admissible observation-word predictor and
original stationary conditional ENNReal KL risk. Its sole external parameter
is the shared published equilibrium renewal-cycle representation. -/
theorem risk_bounds (cycle : EquilibriumCycle.EquilibriumCyclePrinciple)
    (μ : Law) {n B : ℕ} [Nonempty (Fin B)]
    (hS : ∀ d, B ≤ d → μ.mass d=0) (hB : 1 ≤ B) (hBn : 2*B ≤ n) :
    let R := Prediction.risk n (predictor B (n/B-1)) μ
    R ≤ ENNReal.ofReal (((B:ℝ)-1)/(mean μ*(n/B:ℕ))) ∧
      R ≤ ENNReal.ofReal ((B:ℝ)*((B:ℝ)-1)/(mean μ*((n:ℝ)-B))) ∧
      R ≤ ENNReal.ofReal (2*(B:ℝ)^2/(mean μ*n)) ∧
      R ≤ ENNReal.ofReal (2*(B:ℝ)^2/n) := by
  dsimp only
  rw [risk_eq_ofReal cycle μ hS hBn]
  have h := realRisk_bounds cycle μ hS hB hBn
  exact ⟨ENNReal.ofReal_le_ofReal h.1,ENNReal.ofReal_le_ofReal h.2.1,
    ENNReal.ofReal_le_ofReal h.2.2.1,ENNReal.ofReal_le_ofReal h.2.2.2⟩

/-- The concrete estimator is a single source-word algorithm for the entire
known-support class; no law-dependent choice of predictor is required. -/
theorem predictor_uniform_bound (cycle : EquilibriumCycle.EquilibriumCyclePrinciple)
    {n B : ℕ} (hB : 1 ≤ B) (hBn : 2*B ≤ n) :
    ∀ μ : Law, (∀ d, B ≤ d → μ.mass d=0) →
      Prediction.risk n (predictor B (n/B-1)) μ ≤
        ENNReal.ofReal (2*(B:ℝ)^2/n) := by
  letI : Nonempty (Fin B) := ⟨⟨0,by omega⟩⟩
  intro μ hS
  exact (risk_bounds cycle μ hS hB hBn).2.2.2

/-- Minimax risk when the positive gap support bound B is known. -/
def knownSupportMinimaxRisk (n B : ℕ) : ℝ≥0∞ :=
  ⨅ q : Prediction.RandomizedPredictor,
    ⨆ μ : {μ : Law // ∀ d, B ≤ d → μ.mass d=0}, Prediction.risk n q μ.val

/-- The actual known-support minimax upper bound from H.1. -/
theorem knownSupportMinimaxRisk_le (cycle : EquilibriumCycle.EquilibriumCyclePrinciple)
    {n B : ℕ} (hB : 1 ≤ B) (hBn : 2*B ≤ n) :
    knownSupportMinimaxRisk n B ≤ ENNReal.ofReal (2*(B:ℝ)^2/n) := by
  apply iInf_le_of_le (predictor B (n/B-1))
  apply iSup_le
  intro μ
  exact predictor_uniform_bound cycle hB hBn μ.val μ.property

end Paper37.KnownSupportCycle
