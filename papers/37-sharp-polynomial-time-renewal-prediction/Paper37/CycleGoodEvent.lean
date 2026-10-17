import Paper37.EquilibriumCycle
import Paper37.BayesLowerBound
import Paper37.RenewalIntensity
import Paper37.GoodRender

/-! The actual Appendix F.3 good-event probability for the exact finite
support prior. Only the generic classical equilibrium cycle representation
is an external theorem input; all estimates below are finite probability. -/
namespace Paper37.CycleGoodEvent
open scoped BigOperators
open Paper37.LowerBound Paper37.SupportPrior Paper37.FiniteSupportLowerBound
open Paper37.EquilibriumCycle Paper37.BayesLowerBound
noncomputable section

section FiniteProbability
variable {α : Type*} [Fintype α]

lemma eventMass_mono (P : FiniteLaw α) (E F : α → Prop)
    [DecidablePred E] [DecidablePred F] (h : ∀x, E x → F x) : P.eventMass E ≤ P.eventMass F := by
  unfold FiniteLaw.eventMass
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : E x
  · simp [hx,h x hx]
  · simp only [if_neg hx]
    split_ifs
    · exact P.nonneg x
    · rfl

lemma eventMass_exists_le {ι : Type*} [Fintype ι] (P : FiniteLaw α)
    (E : ι → α → Prop) [∀i, DecidablePred (E i)]
    [DecidablePred (fun x=>∃i,E i x)] :
    P.eventMass (fun x => ∃i, E i x) ≤ ∑i, P.eventMass (E i) := by
  classical
  unfold FiniteLaw.eventMass
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : ∃i, E i x
  · obtain ⟨i,hi⟩ := hx
    simp only [if_pos (show ∃i,E i x from ⟨i,hi⟩)]
    exact le_trans (by simp [hi]) (Finset.single_le_sum
      (fun j _ => by split_ifs;exact P.nonneg x;rfl) (Finset.mem_univ i))
  · simp only [if_neg hx]
    exact Finset.sum_nonneg (fun i _ => by split_ifs; exact P.nonneg x;rfl)

lemma eventMass_cover (P : FiniteLaw α) (E G B C : α → Prop)
    [DecidablePred E] [DecidablePred G] [DecidablePred B] [DecidablePred C]
    (h : ∀x,E x → G x ∨ B x ∨ C x) :
    P.eventMass E ≤ P.eventMass G + P.eventMass B + P.eventMass C := by
  unfold FiniteLaw.eventMass
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases he : E x
  · rcases h x he with hg|hb|hc
    · simp only [if_pos he,if_pos hg]; split_ifs <;> nlinarith [P.nonneg x]
    · simp only [if_pos he,if_pos hb]; split_ifs <;> nlinarith [P.nonneg x]
    · simp only [if_pos he,if_pos hc]; split_ifs <;> nlinarith [P.nonneg x]
  · simp only [if_neg he]; split_ifs <;> nlinarith [P.nonneg x]

lemma expectation_pushforward (P : FiniteLaw α) (f : α → List Bool) (n : ℕ)
    (hf : ∀x,(f x).length=n) (g : List Bool → ℝ) :
    P.expectation (fun x => g (f x)) =
      ∑w∈(Paper37.Renewal.words n).toFinset,
        P.eventMass (fun x => f x=w)*g w := by
  classical
  unfold FiniteLaw.expectation FiniteLaw.eventMass
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  have hx : f x ∈ (Paper37.Renewal.words n).toFinset := by
    exact List.mem_toFinset.mpr ((Paper37.Renewal.mem_words n (f x)).mpr (hf x))
  rw [Finset.sum_eq_single_of_mem (f x) hx]
  · simp
  · intro w _ hw
    simp [Ne.symm hw]

lemma eventMass_pushforward (P : FiniteLaw α) (f : α → List Bool) (n : ℕ)
    (hf : ∀x,(f x).length=n) (E : List Bool → Prop) [DecidablePred E] :
    P.eventMass (fun x => E (f x)) =
      ∑w∈(Paper37.Renewal.words n).toFinset, if E w then P.eventMass (fun x=>f x=w) else 0 := by
  have h := expectation_pushforward P f n hf (fun w=>if E w then 1 else 0)
  simpa only [FiniteLaw.expectation,FiniteLaw.eventMass,mul_ite,mul_one,mul_zero] using h

lemma markov_count (P : FiniteLaw α) (f : α → ℕ) {b : ℕ} (hb : 0<b) :
    P.eventMass (fun x => b < f x) ≤ P.expectation (fun x=>(f x:ℝ))/(b:ℝ) := by
  apply (le_div_iff₀ (by exact_mod_cast hb : (0:ℝ)<(b:ℝ))).mpr
  exact P.mass_mul_le_expectation _ (fun x=>Nat.cast_nonneg (f x)) (fun x hx=>by exact_mod_cast hx.le)

end FiniteProbability

private lemma sum_fin_lt (l a : ℕ) (c : ℝ) :
    (∑j:Fin l, if j.val<a then c else 0) = ((min l a:ℕ):ℝ)*c := by
  induction l generalizing a with
  | zero => simp
  | succ l ih =>
    cases a with
    | zero => simp
    | succ a =>
      simp only [Fin.sum_univ_succ,Fin.val_zero,Nat.zero_lt_succ,if_true,
        Fin.val_succ,Nat.succ_lt_succ_iff,ih,Nat.succ_min_succ,Nat.cast_succ]
      ring

def gapPrior {b : ℕ} (z : Sample b) := uniformOn (support z) (support_nonempty z)
def cycleLaw {b : ℕ} (z : Sample b) (n : ℕ) := sampleLaw (gapPrior z) (fun i=>(i.val:ℕ)) n
def cycleWord {b : ℕ} (z : Sample b) (n : ℕ) := sampleWord (fun i : support z=>i.val) n

lemma phase_short_mass_eq {b : ℕ} (z : Sample b) (a : ℕ) :
    (phaseLaw (gapPrior z) (fun i=>(i.val:ℕ))).eventMass (fun p=>p.2.val<a) =
      (∑d∈support z, ((min (d+1) a:ℕ):ℝ)) /
        ((support z).card * Paper37.Renewal.mean (law z)) := by
  unfold FiniteLaw.eventMass
  rw [Fintype.sum_sigma]
  simp only [phaseLaw, gapPrior, uniformOn_mass, uniform_gapMean, sum_fin_lt]
  rw [← Finset.sum_mul, (support z).sum_coe_sort (fun d : ℕ => ((min (d+1) a:ℕ):ℝ))]
  change _ * (1/(↑(support z).card) / Paper37.Renewal.mean (law z)) = _
  ring

lemma phase_short_mass_lower {b : ℕ} (hb : 0<b) (z : Sample b) :
    1/4 ≤ (phaseLaw (gapPrior z) (fun i=>(i.val:ℕ))).eventMass (fun p=>p.2.val<24*b) := by
  rw [phase_short_mass_eq]
  have hnum : ((12*b:ℕ):ℝ)*((24*b:ℕ):ℝ) ≤
      ∑d∈support z, ((min (d+1) (24*b):ℕ):ℝ) := by
    calc
      _ = ∑d∈highSupport z, ((24*b:ℕ):ℝ) := by simp [highSupport_card hb z]
      _ = ∑d∈highSupport z, ((min (d+1) (24*b):ℕ):ℝ) := by
        apply Finset.sum_congr rfl
        intro d hd
        have hh := (highSupport_bounds hb z hd).1
        rw [Nat.min_eq_right (by omega)]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
        (fun d _ _ => Nat.cast_nonneg _)
  have hm := law_mean_bounds hb z
  have hpos := Paper37.Renewal.mean_pos (law z)
  have ha : (0:ℝ)<((24*b:ℕ):ℝ) := by exact_mod_cast (show 0<24*b by omega)
  rw [support_card hb z] at *
  apply (le_div_iff₀ (mul_pos ha hpos)).mpr
  norm_num only [Nat.cast_mul,Nat.cast_ofNat] at hnum hm ⊢
  nlinarith

lemma cycle_short_mass_lower {b : ℕ} (hb : 0<b) (z : Sample b) (n : ℕ) :
    1/4 ≤ (cycleLaw z n).eventMass (fun s=>s.1.2.val<24*b) := by
  have h := product_eventMass_rect (phaseLaw (gapPrior z) (fun i=>(i.val:ℕ)))
    (iidLaw (gapPrior z) n) (fun p=>p.2.val<24*b) (fun _=>True)
  simp only [FiniteLaw.eventMass,if_true] at h
  rw [(iidLaw (gapPrior z) n).total,mul_one] at h
  simpa only [cycleLaw,sampleLaw,and_true] using (phase_short_mass_lower hb z).trans_eq h.symm

lemma uniform_iid_coordinate_mass {b n : ℕ} (hb : 0<b) (z : Sample b) (i : Fin n) (g : ℕ) :
    (iidLaw (gapPrior z) n).eventMass (fun ds=>(ds i).val=g) ≤ 1/((24*b:ℕ):ℝ) := by
  classical
  by_cases hg : g∈support z
  · let x : support z := ⟨g,hg⟩
    have he : (fun ds : Fin n → support z=>(ds i).val=g) = (fun ds=>ds i=x) := by
      funext ds
      exact propext (by simp [x,Subtype.ext_iff])
    have hei : (iidLaw (gapPrior z) n).eventMass (fun ds=>(ds i).val=g) =
        (iidLaw (gapPrior z) n).eventMass (fun ds=>ds i=x) := by
      unfold FiniteLaw.eventMass
      apply Finset.sum_congr rfl
      intro ds _
      have hp : (ds i).val=g ↔ ds i=x := by simp [x,Subtype.ext_iff]
      by_cases hh : (ds i).val=g
      · simp only [if_pos hh,if_pos (hp.mp hh)]
      · simp only [if_neg hh,if_neg (fun hx=>hh (hp.mpr hx))]
    rw [hei,iidLaw_coordinate]
    simp [gapPrior,uniformOn_mass,support_card hb z]
  · have he : (iidLaw (gapPrior z) n).eventMass (fun ds=>(ds i).val=g) = 0 := by
      unfold FiniteLaw.eventMass
      apply Finset.sum_eq_zero
      intro ds _
      exact if_neg (fun h : (ds i).val=g =>hg (h ▸ (ds i).property))
    rw [he]
    exact one_div_nonneg.mpr (Nat.cast_nonneg _)

lemma cycle_coordinate_collision_le {b n : ℕ} (hb : 0<b) (z : Sample b) (i : Fin n) :
    (cycleLaw z n).eventMass (fun s=>(s.2 i).val=s.1.2.val) ≤ 1/((24*b:ℕ):ℝ) := by
  classical
  unfold FiniteLaw.eventMass
  change (∑s : Phase (fun j : support z=>j.val) × (Fin n → support z), if (s.2 i).val=s.1.2.val then
    (phaseLaw (gapPrior z) _).mass s.1 * (iidLaw (gapPrior z) n).mass s.2 else 0) ≤ _
  rw [Fintype.sum_prod_type]
  have hinner (p : Phase (fun i : support z=>i.val)) :
      (∑ds, if (ds i).val=p.2.val then
        (phaseLaw (gapPrior z) _).mass p * (iidLaw (gapPrior z) n).mass ds else 0) =
      (phaseLaw (gapPrior z) _).mass p *
        (iidLaw (gapPrior z) n).eventMass (fun ds=>(ds i).val=p.2.val) := by
    simp only [FiniteLaw.eventMass,Finset.mul_sum,mul_ite,mul_zero]
  simp_rw [hinner]
  calc
    _ ≤ ∑p, (phaseLaw (gapPrior z) _).mass p * (1/((24*b:ℕ):ℝ)) := by
      apply Finset.sum_le_sum
      intro p _
      exact mul_le_mul_of_nonneg_left (uniform_iid_coordinate_mass hb z i p.2.val)
        ((phaseLaw (gapPrior z) _).nonneg p)
    _ = _ := by rw [← Finset.sum_mul,(phaseLaw (gapPrior z) _).total,one_mul]

/-- Collision among the first b genuinely iid backward gaps, independent of
both the size-biased cycle and its uniform phase. -/
lemma cycle_collision_le {b n : ℕ} (hb : 0<b) (hbn : b≤n) (z : Sample b) :
    (cycleLaw z n).eventMass (fun s=>∃i:Fin b,(s.2 (Fin.castLE hbn i)).val=s.1.2.val) ≤ 1/24 := by
  classical
  calc
    _ ≤ ∑i:Fin b, (cycleLaw z n).eventMass
      (fun s=>(s.2 (Fin.castLE hbn i)).val=s.1.2.val) := by
      simpa only [FiniteLaw.eventMass] using eventMass_exists_le (cycleLaw z n)
        (fun (i : Fin b) s=>(s.2 (Fin.castLE hbn i)).val=s.1.2.val)
    _ ≤ ∑_i:Fin b, 1/((24*b:ℕ):ℝ) :=
      Finset.sum_le_sum (fun i _=>cycle_coordinate_collision_le hb z (Fin.castLE hbn i))
    _ = (1/24:ℝ) := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat]
      have hbR : (b:ℝ)≠0 := by exact_mod_cast hb.ne'
      field_simp


lemma cycle_word_mass (cycle : EquilibriumCyclePrinciple) {b : ℕ} (z : Sample b)
    (n : ℕ) (w : List Bool) (hw : w.length=n) :
    (cycleLaw z n).eventMass (fun s=>cycleWord z n s=w) =
      Paper37.Renewal.blockMass (law z) w := by
  exact uniform_word_mass cycle (support z) (support_nonempty z) n w hw

lemma cycle_count_expectation (cycle : EquilibriumCyclePrinciple) {b : ℕ} (z : Sample b) (n : ℕ) :
    (cycleLaw z n).expectation (fun s=>((cycleWord z n s).count true:ℝ)) =
      (n:ℝ)/Paper37.Renewal.mean (law z) := by
  rw [expectation_pushforward (cycleLaw z n) (cycleWord z n) n
    (sampleWord_length (fun i : support z=>i.val) n)
    (fun w=>(w.count true:ℝ))]
  calc
    _ = ∑w∈(Paper37.Renewal.words n).toFinset,
        Paper37.Renewal.blockMass (law z) w*(w.count true:ℝ) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [cycle_word_mass cycle z n w
        ((Paper37.Renewal.mem_words n w).mp (List.mem_toFinset.mp hw))]
    _ = _ := Paper37.RenewalIntensity.expectedRenewalCount (law z) n

/-- Markov's inequality applied to the actual stationary renewal count; its
expectation is proved from cylinder consistency rather than assumed. -/
lemma cycle_many_renewals_le (cycle : EquilibriumCyclePrinciple) {b n : ℕ}
    (hb : 0<b) (hn : n≤b*b) (z : Sample b) :
    (cycleLaw z n).eventMass (fun s=>b<(cycleWord z n s).count true) ≤ 1/12 := by
  refine (markov_count (cycleLaw z n) (fun s=>(cycleWord z n s).count true) hb).trans ?_
  rw [cycle_count_expectation cycle z n]
  apply (div_le_iff₀ (by exact_mod_cast hb : (0:ℝ)<(b:ℝ))).mpr
  apply (div_le_iff₀ (Paper37.Renewal.mean_pos (law z))).mpr
  have hm := (law_mean_bounds hb z).1
  have hnR : (n:ℝ)≤(b:ℝ)*(b:ℝ) := by exact_mod_cast hn
  norm_num only [Nat.cast_mul,Nat.cast_ofNat] at hm
  nlinarith [mul_nonneg (Nat.cast_nonneg b : (0:ℝ)≤(b:ℝ))
    (sub_nonneg.mpr hm)]

lemma cycle_good_mass_eq (cycle : EquilibriumCyclePrinciple) {b : ℕ} (z : Sample b) (n : ℕ) :
    (cycleLaw z n).eventMass (fun s=>GoodBlock b (cycleWord z n s)) =
      ∑w∈(Paper37.Renewal.words n).toFinset,
        if GoodBlock b w then Paper37.Renewal.blockMass (law z) w else 0 := by
  rw [eventMass_pushforward (cycleLaw z n) (cycleWord z n) n
    (sampleWord_length (fun i : support z=>i.val) n)]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases hg : GoodBlock b w
  · simp only [if_pos hg]
    exact cycle_word_mass cycle z n w
      ((Paper37.Renewal.mem_words n w).mp (List.mem_toFinset.mp hw))
  · simp [hg]

lemma goodPredictiveMass_average (n b : ℕ) :
    goodPredictiveMass n b = (prior b).expectation (fun z=>
      ∑w∈(Paper37.Renewal.words n).toFinset,
        if GoodBlock b w then Paper37.Renewal.blockMass (law z) w else 0) := by
  unfold goodPredictiveMass predictiveMass FiniteLaw.expectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hg : GoodBlock b w
  · simp [hg]
  · simp [hg]


/-- Every sampled support has period one, by its two consecutive forced high
lengths 2a−1 and 2a. -/
lemma source_support_aperiodic {b : ℕ} (hb : 0<b) (z : Sample b) :
    (support z).gcd (fun d=>d+1)=1 := by
  apply support_gcd_one_of_consecutive (support z) (d:=48*b-2)
  · exact forcedHigh_subset_support z (by simp [forcedHigh])
  · have h : 48*b-2+1=48*b-1 := by omega
    rw [h]
    exact forcedHigh_subset_support z (by simp [forcedHigh])

/-- The a.s. standardized-support restriction in the strengthened F.1 claim. -/
lemma source_standardized_support {b : ℕ} (hb : 0<b) (z : Sample b) :
    ∀d,0<(law z).mass d → (d:ℝ)+1≤4*Paper37.Renewal.mean (law z) := by
  intro d hd
  have hmem : d∈support z := by
    by_contra hh
    simpa [law,uniformSupportLaw_mass,hh] using hd
  have hcap := support_length_cap hb z hmem
  have hm := (law_mean_bounds hb z).1
  norm_num only [Nat.cast_mul,Nat.cast_ofNat] at hcap hm
  linarith

/-- Exact restricted family asserted by F.1: a-point uniform gap laws in
[2a], with gcd one and all positive-mass lengths at most four means. -/
def UniformHardClass (b : ℕ) (μ : Paper37.Renewal.Law) : Prop :=
  ∃(S : Finset ℕ)(hS : S.Nonempty), S.card=24*b ∧
    (∀d∈S,d<48*b) ∧ S.gcd (fun d=>d+1)=1 ∧ μ=uniformSupportLaw S hS ∧
    (∀d,0<μ.mass d → (d:ℝ)+1≤4*Paper37.Renewal.mean μ)

lemma source_law_in_hardClass {b : ℕ} (hb : 0<b) (z : Sample b) : UniformHardClass b (law z) := by
  refine ⟨support z,support_nonempty z,support_card hb z,?_,source_support_aperiodic hb z,rfl,
    source_standardized_support hb z⟩
  intro d hd
  rcases Finset.mem_union.mp hd with hl|hh
  · have h:=lowSupport_bounds z hl
    omega
  · exact (highSupport_bounds hb z hh).2

lemma bayesRisk_le_hardClass {b : ℕ} (hb : 0<b) (n : ℕ)
    (q : Paper37.Prediction.RandomizedPredictor) :
    bayesRisk n b q ≤ ⨆ μ : {μ // UniformHardClass b μ},Paper37.Prediction.risk n q μ.val := by
  have htotal : ∑z,ENNReal.ofReal ((prior b).mass z)=1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun z _=>(prior b).nonneg z),(prior b).total]
    simp
  calc
    _ ≤ ∑z,ENNReal.ofReal ((prior b).mass z)*
        (⨆ μ : {μ // UniformHardClass b μ},Paper37.Prediction.risk n q μ.val) := by
      apply Finset.sum_le_sum
      intro z _
      exact mul_le_mul_left' (le_iSup (fun μ : {μ // UniformHardClass b μ}=>
        Paper37.Prediction.risk n q μ.val) ⟨law z,source_law_in_hardClass hb z⟩) _
    _ = _ := by rw [← Finset.sum_mul,htotal,one_mul]


/-- F.3 for every actual support, at every horizon satisfying a≤n≤b².
The prior scale b is fixed independently of the horizon n. -/
lemma cycle_good_mass_lower (cycle : EquilibriumCyclePrinciple) {b n : ℕ}
    (hb : 0<b) (h24n : 24*b≤n) (hn : n≤b*b) (z : Sample b) :
    1/8 ≤ (cycleLaw z n).eventMass (fun s=>GoodBlock b (cycleWord z n s)) := by
  have hbn : b≤n := by omega
  have hc := eventMass_cover (cycleLaw z n)
    (fun s=>s.1.2.val<24*b) (fun s=>GoodBlock b (cycleWord z n s))
    (fun s=>b<(cycleWord z n s).count true)
    (fun s=>∃i:Fin b,(s.2 (Fin.castLE hbn i)).val=s.1.2.val) (by
      intro s hs
      by_cases hm : b<(cycleWord z n s).count true
      · exact Or.inr (Or.inl hm)
      · by_cases hcoll : ∃i:Fin b,(s.2 (Fin.castLE hbn i)).val=s.1.2.val
        · exact Or.inr (Or.inr hcoll)
        · apply Or.inl
          exact Paper37.GoodRender.render_goodBlock hbn
            (fun i=>(s.2 i).val) hs h24n (not_lt.mp hm) hcoll)
  have hshort := cycle_short_mass_lower hb z n
  have hmany := cycle_many_renewals_le cycle hb hn z
  have hcollision := cycle_collision_le hb hbn z
  linarith

/-- Actual F.3 after averaging over the exact normalized source support
prior. There is no good-event or risk lower-bound hypothesis. -/
lemma goodPredictiveMass_lower (cycle : EquilibriumCyclePrinciple) {b n : ℕ}
    (hb : 0<b) (h24n : 24*b≤n) (hn : n≤b*b) :
    1/8 ≤ goodPredictiveMass n b := by
  rw [goodPredictiveMass_average]
  calc
    (1/8:ℝ) = (∑z,(prior b).mass z)*(1/8) := by rw [(prior b).total,one_mul]
    _ = ∑z,(prior b).mass z*(1/8) := Finset.sum_mul _ _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro z _
      have h := cycle_good_mass_lower cycle hb h24n hn z
      rw [cycle_good_mass_eq cycle z n] at h
      exact mul_le_mul_of_nonneg_left h ((prior b).nonneg z)

lemma ceilingRoot_square (n : ℕ) : n≤ceilingRoot n*ceilingRoot n := by
  have hs : Real.sqrt (n:ℝ) ≤ (ceilingRoot n:ℝ) := Nat.le_ceil _
  have he : Real.sqrt (n:ℝ)*Real.sqrt (n:ℝ)=(n:ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hb : (0:ℝ)≤(ceilingRoot n:ℝ) := Nat.cast_nonneg _
  have hR : (n:ℝ)≤(ceilingRoot n:ℝ)*(ceilingRoot n:ℝ) := by
    nlinarith [Real.sqrt_nonneg (n:ℝ)]
  exact_mod_cast hR

/-- F.1 with its explicit source constant and all randomized predictor
quantifiers, already restricted to the stated aperiodic standardized finite
uniform support class. The only external input is the generic classical
stationary-cycle finite-projection theorem. -/
theorem finite_support_lower_bound (cycle : EquilibriumCyclePrinciple) {n : ℕ}
    (hn : 600≤n) (q : Paper37.Prediction.RandomizedPredictor) :
    ENNReal.ofReal (11*(Real.log 2-1/2)/(40600*Real.sqrt (n:ℝ))) ≤
      ⨆μ : {μ // UniformHardClass (ceilingRoot n) μ},Paper37.Prediction.risk n q μ.val := by
  obtain ⟨hb,h24n,ha25⟩ := ceilingRoot_scale_bounds hn
  have hg := goodPredictiveMass_lower cycle hb h24n (ceilingRoot_square n)
  have hBayes : ENNReal.ofReal ((1/8)*radiusConstant (ceilingRoot n)) ≤ bayesRisk n (ceilingRoot n) q := by
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤1/8)]
    exact (mul_le_mul_right' (ENNReal.ofReal_le_ofReal hg) _).trans
      (goodMass_mul_radius_le_bayesRisk hb n q)
  have ha : (0:ℝ)<((24*ceilingRoot n:ℕ):ℝ) := by positivity
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hs := lower_bound_constant_assembly ha hnR ha25 radius_coefficient_nonneg
    (risk:=(1/8)*radiusConstant (ceilingRoot n)) (le_refl _)
  exact (ENNReal.ofReal_le_ofReal hs).trans (hBayes.trans (bayesRisk_le_hardClass hb n q))

/-- The displayed F.1 inequality over all finite-mean renewal laws. -/
theorem f1_lower_bound (cycle : EquilibriumCyclePrinciple) {n : ℕ}
    (hn : 600≤n) (q : Paper37.Prediction.RandomizedPredictor) :
    ENNReal.ofReal (11*(Real.log 2-1/2)/(40600*Real.sqrt (n:ℝ))) ≤
      ⨆μ : Paper37.Renewal.Law,Paper37.Prediction.risk n q μ := by
  obtain ⟨hb,h24n,_⟩ := ceilingRoot_scale_bounds hn
  exact worstRisk_f1_of_goodMass hn
    (goodPredictiveMass_lower cycle hb h24n (ceilingRoot_square n)) q

/-- The randomized minimax lower bound in Theorem 2.3, with the same actual
stationary KL risk and source numerical constant. -/
theorem minimax_lower_bound (cycle : EquilibriumCyclePrinciple) {n : ℕ}
    (hn : 600≤n) :
    ENNReal.ofReal (11*(Real.log 2-1/2)/(40600*Real.sqrt (n:ℝ))) ≤
      Paper37.Prediction.minimaxRisk n :=
  le_iInf (fun q=>f1_lower_bound cycle hn q)

end
end Paper37.CycleGoodEvent
