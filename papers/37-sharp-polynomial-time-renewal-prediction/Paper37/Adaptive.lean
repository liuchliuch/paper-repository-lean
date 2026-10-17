import Paper37.EnvelopeBridge
import Paper37.AnalyticBounds

/-! Restricted completed-gap envelopes and the occupied-type adaptive mixture,
on the actual source binary words of Appendices B and E. -/
noncomputable section
open scoped BigOperators
namespace Paper37.Adaptive
open Paper37.Renewal Paper37.Envelope Paper37.EnvelopeBridge Paper37.Prediction

/-- Number of occupied completed-gap lengths in an ordinary binary block. -/
def nu (x : List Bool) : ℕ := (gapsFrom 0 x).toFinset.card

/-- Restricted envelope E.1, retaining the source rational arithmetic. -/
def restrictedEnvelope (s : ℕ) (x : List Bool) : ℚ :=
  if nu x ≤ s then wordEnvelope x else 0

def restrictedNormalizer (L s : ℕ) : ℚ :=
  ∑ x ∈ (words L).toFinset, restrictedEnvelope s x

def restrictedAssignment (s : ℕ) (x : List Bool) : ℚ :=
  restrictedEnvelope s x / restrictedNormalizer x.length s

def restrictedBlock (s : ℕ) (x : List Bool) : ℚ :=
  (match firstSuffix x with
  | none => 1
  | some z => restrictedAssignment s z) / (x.length+1 : ℚ)

@[simp] lemma nu_zeros (L : ℕ) : nu (List.replicate L false) = 0 := by
  unfold nu
  rw [← parseGaps_eq_gapsFrom, parseGaps_zeros]
  simp

lemma restrictedEnvelope_nonneg (s : ℕ) (x : List Bool) : 0 ≤ restrictedEnvelope s x := by
  unfold restrictedEnvelope
  split <;> simp_all [wordEnvelope_pos x |>.le]

lemma restrictedNormalizer_pos (L s : ℕ) : 0 < restrictedNormalizer L s := by
  apply Finset.sum_pos'
  · intro x hx; exact restrictedEnvelope_nonneg s x
  · refine ⟨List.replicate L false, List.mem_toFinset.mpr ((mem_words _ _).mpr (by simp)), ?_⟩
    simp [restrictedEnvelope, wordEnvelope_pos]

lemma restrictedAssignment_nonneg (s : ℕ) (x : List Bool) : 0 ≤ restrictedAssignment s x :=
  div_nonneg (restrictedEnvelope_nonneg s x) (restrictedNormalizer_pos _ _).le

lemma restrictedBlock_nonneg (s : ℕ) (x : List Bool) : 0 ≤ restrictedBlock s x := by
  unfold restrictedBlock
  apply div_nonneg _ (by positivity)
  split <;> simp_all [restrictedAssignment_nonneg]

@[simp] theorem restrictedNormalizer_zero (s : ℕ) : restrictedNormalizer 0 s = 1 := by
  simp [restrictedNormalizer, restrictedEnvelope, nu, words, wordEnvelope, gapsFrom, Prediction.gapEnvelope]

lemma restrictedAssignment_sum (L s : ℕ) :
    ∑ x ∈ (words L).toFinset, restrictedAssignment s x = 1 := by
  calc
    _ = (∑ x ∈ (words L).toFinset, restrictedEnvelope s x) / restrictedNormalizer L s := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      rw [restrictedAssignment, (mem_words L x).mp (List.mem_toFinset.mp hx)]
      rfl
    _ = 1 := div_self (restrictedNormalizer_pos L s).ne'

/-- The finite set of occupied coordinates of a feasible completed-gap histogram. -/
def histogramSupport {L : ℕ} (c : FeasibleCounts L) : Finset (Fin L) :=
  Finset.univ.filter (fun i => (c.val i).val ≠ 0)

lemma nu_encode {L : ℕ} (b : Block L) : nu (encode b) = (histogramSupport b.1).card := by
  unfold nu
  rw [← parseGaps_eq_gapsFrom, parseGaps_encode]
  have himage : ((gapList b).map Fin.val).toFinset = (gapList b).toFinset.image Fin.val := by
    ext n
    simp
  rw [himage, Finset.card_image_of_injective _ Fin.val_injective]
  congr 1
  ext i
  simp only [List.mem_toFinset, histogramSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← List.count_pos_iff, gapList_count]
  omega

/-- Feasible histograms using at most `s` distinct positive gap lengths. -/
def RestrictedCounts (L s : ℕ) := {c : FeasibleCounts L // (histogramSupport c).card ≤ s}

instance (L s : ℕ) : Fintype (RestrictedCounts L s) :=
  inferInstanceAs (Fintype {c : FeasibleCounts L // _})

lemma restrictedNormalizer_le_histograms (L s : ℕ) :
    (restrictedNormalizer L s : ℝ) ≤ Fintype.card (RestrictedCounts L s) := by
  classical
  have heq : (restrictedNormalizer L s : ℝ) =
      ∑ b : Block L, if (histogramSupport b.1).card ≤ s then M b else 0 := by
    unfold restrictedNormalizer
    push_cast
    symm
    apply Finset.sum_bij (fun b _ => encode b)
    · intro b hb
      exact List.mem_toFinset.mpr ((mem_words _ _).mpr (encode_length b))
    · intro b hb c hc heq; exact encode_injective L heq
    · intro x hx
      have hh := (mem_words L x).mp (List.mem_toFinset.mp hx)
      exact ⟨ofWord L x hh, Finset.mem_univ _, encode_ofWord L x hh⟩
    · intro b hb
      simp only [restrictedEnvelope, nu_encode]
      split <;> simp_all [wordEnvelope_encode]
  rw [heq]
  change (∑ b : Σ c : FeasibleCounts L, Ordering (fun i => (c.val i).val),
    if (histogramSupport b.1).card ≤ s then M b else 0) ≤ _
  rw [Fintype.sum_sigma]
  calc
    _ ≤ ∑ c : FeasibleCounts L, if (histogramSupport c).card ≤ s then (1:ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro c hc
      split_ifs with hs
      · exact ordering_mass_le_one _
      · simp
    _ = _ := by simp [RestrictedCounts, Fintype.card_subtype, Finset.sum_boole]

/-- A support of size `j` together with its positive counts, each at most `L`. -/
def SupportCode (L s : ℕ) :=
  Σ j : Fin (min s L + 1), Σ S : {S : Finset (Fin L) // S.card = j.val}, S.val → Fin L

instance (L s : ℕ) : Fintype (SupportCode L s) :=
  inferInstanceAs (Fintype (Σ j : Fin (min s L + 1), Σ S : {S : Finset (Fin L) // S.card = j.val}, S.val → Fin L))

def encodeCounts {L s : ℕ} (c : RestrictedCounts L s) : SupportCode L s := by
  let S := histogramSupport c.val
  have hL : S.card ≤ L := by simpa [S] using Finset.card_le_card (Finset.subset_univ (histogramSupport c.val))
  have hs : S.card ≤ s := c.prop
  refine ⟨⟨S.card, by omega⟩, ⟨S,rfl⟩, fun i => ⟨(c.val.val i.val).val - 1, ?_⟩⟩
  have hi : (c.val.val i.val).val ≠ 0 := (Finset.mem_filter.mp i.prop).2
  have hc := (c.val.val i.val).isLt
  omega

def decodeCounts {L s : ℕ} (t : SupportCode L s) (i : Fin L) : ℕ :=
  if h : i ∈ t.2.1.val then (t.2.2 ⟨i,h⟩).val+1 else 0

lemma decode_encodeCounts {L s : ℕ} (c : RestrictedCounts L s) (i : Fin L) :
    decodeCounts (encodeCounts c) i = (c.val.val i).val := by
  unfold decodeCounts encodeCounts
  dsimp
  split_ifs with hi
  · have hc := (Finset.mem_filter.mp hi).2
    omega
  · have hc : (c.val.val i).val = 0 := by simpa [histogramSupport] using hi
    exact hc.symm

lemma encodeCounts_injective (L s : ℕ) : Function.Injective (@encodeCounts L s) := by
  intro c d heq
  apply Subtype.ext
  apply Subtype.ext
  funext i
  apply Fin.ext
  have hh := congrArg (fun t => decodeCounts t i) heq
  simpa only [decode_encodeCounts] using hh

lemma supports_card (L j : ℕ) :
    Fintype.card {S : Finset (Fin L) // S.card = j} = L.choose j := by
  rw [Fintype.card_of_subtype ((Finset.univ : Finset (Fin L)).powersetCard j) (by simp)]
  simp

lemma supportCode_card (L s : ℕ) : Fintype.card (SupportCode L s) =
    Paper37.AnalyticBounds.restrictedCountBound L s := by
  unfold SupportCode
  rw [Fintype.card_sigma]
  simp_rw [Fintype.card_sigma]
  have hinner (j : Fin (min s L+1)) :
      (∑ S : {S : Finset (Fin L) // S.card = j.val}, Fintype.card (S.val → Fin L)) =
        L.choose j.val * L^j.val := by
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
    have hh : ∀ S : {S : Finset (Fin L) // S.card = j.val}, L^S.val.card = L^j.val :=
      fun S => by rw [S.prop]
    simp_rw [hh]
    simp [supports_card, mul_comm]
  simp_rw [hinner]
  change (∑ j : Fin (min s L+1), (fun n : ℕ => L.choose n * L^n) j.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => L.choose n * L^n) (min s L+1)]
  rw [Finset.sum_range_eq_add_Ico _ (by omega : 0 < min s L+1)]
  simp only [Paper37.AnalyticBounds.restrictedCountBound,Nat.choose_zero_right,pow_zero,mul_one,zero_add]
  congr 1

/-- E.2's first inequality counts actual restricted histogram fibers. -/
theorem restrictedNormalizer_le_countBound (L s : ℕ) :
    restrictedNormalizer L s ≤ Paper37.AnalyticBounds.restrictedCountBound L s := by
  have hc := Fintype.card_le_of_injective (@encodeCounts L s) (encodeCounts_injective L s)
  rw [supportCode_card] at hc
  have hh : (restrictedNormalizer L s : ℝ) ≤ (Paper37.AnalyticBounds.restrictedCountBound L s : ℝ) :=
    (restrictedNormalizer_le_histograms L s).trans (by exact_mod_cast hc)
  exact_mod_cast hh

/-- Lemma E.1, including the claimed polynomial normalization penalty. -/
theorem restrictedNormalizer_le_pow (L s : ℕ) :
    restrictedNormalizer L s ≤ (L+1:ℚ)^(2*s+1) := by
  exact (restrictedNormalizer_le_countBound L s).trans
    (by exact_mod_cast Paper37.AnalyticBounds.restrictedCountBound_le L s)

lemma gap_list_length_le_weight (g : List ℕ) : g.length ≤ (g.map (fun d => d+1)).sum := by
  induction g with
  | nil => simp
  | cons d g ih => simp only [List.length_cons, List.map_cons, List.sum_cons]; omega

lemma nu_le_length (x : List Bool) : nu x ≤ x.length := by
  unfold nu
  exact (List.toFinset_card_le _).trans ((gap_list_length_le_weight _).trans (by
    rw [← parseGaps_eq_gapsFrom]
    exact parse_weight_le x))

lemma restrictedEnvelope_eq (s : ℕ) (x : List Bool) (h : nu x ≤ s) :
    restrictedEnvelope s x = wordEnvelope x := by simp [restrictedEnvelope,h]

lemma restrictedNormalizer_eq (L s : ℕ) (h : L ≤ s) :
    restrictedNormalizer L s = ordinaryNormalizer L := by
  apply Finset.sum_congr rfl
  intro x hx
  have hl := (mem_words L x).mp (List.mem_toFinset.mp hx)
  exact restrictedEnvelope_eq s x ((nu_le_length x).trans (hl.le.trans h))

lemma restrictedAssignment_eq (s : ℕ) (x : List Bool) (h : x.length ≤ s) :
    restrictedAssignment s x = ordinaryAssignment x := by
  rw [restrictedAssignment, restrictedEnvelope_eq s x ((nu_le_length x).trans h), restrictedNormalizer_eq _ _ h]
  rfl

lemma restrictedBlock_universal (N : ℕ) (x : List Bool) (hx : x.length = N) :
    restrictedBlock N x = blockAssignment x := by
  unfold restrictedBlock blockAssignment
  cases hs : firstSuffix x with
  | none => rfl
  | some z =>
    obtain ⟨j,hj⟩ := firstSuffix_some_decomposition x z hs
    have hl : z.length ≤ N := by rw [hj] at hx; simp only [List.length_append,List.length_replicate,List.length_cons] at hx; omega
    simp only [restrictedAssignment_eq _ _ hl]

def restrictedComponentMass (s : ℕ) (x : List Bool) : ℚ :=
  match firstSuffix x with
  | none => 1
  | some z => restrictedAssignment s z

lemma restrictedComponentMass_sum (N s : ℕ) :
    (∑ x ∈ (words N).toFinset, restrictedComponentMass s x) = N+1 := by
  induction N with
  | zero => simp [words,restrictedComponentMass,firstSuffix]
  | succ N ih =>
    rw [sum_words_step]
    change (∑ x ∈ (words N).toFinset, restrictedComponentMass s x) +
      (∑ x ∈ (words N).toFinset, restrictedAssignment s x) = _
    rw [ih,restrictedAssignment_sum]
    push_cast
    ring

lemma restrictedBlock_sum (N s : ℕ) :
    (∑ x ∈ (words N).toFinset, restrictedBlock s x) = 1 := by
  calc
    _ = (∑ x ∈ (words N).toFinset, restrictedComponentMass s x) / (N+1:ℚ) := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      have hl := (mem_words N x).mp (List.mem_toFinset.mp hx)
      unfold restrictedBlock restrictedComponentMass
      rw [hl]
      rfl
    _ = 1 := by rw [restrictedComponentMass_sum]; exact div_self (by positivity)

/-- Exact weights E.3. Only indices `1 ≤ s ≤ N` enter the assignment. -/
def omegaWeight (N s : ℕ) : ℚ :=
  if s = N then 1/2 + 1/(2*N) else 1/(2*s*(s+1))

lemma base_weights_sum (N : ℕ) :
    (∑ s ∈ Finset.Icc 1 N, (1 / (2*s*(s+1)) : ℚ)) = 1/2 - 1/(2*(N+1)) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega),ih]
    have hN : (N+1:ℚ) ≠ 0 := by positivity
    have hN2 : (N+1+1:ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

lemma omegaWeight_pos {N s : ℕ} (hN : 1 ≤ N) (hs : 1 ≤ s) : 0 < omegaWeight N s := by
  unfold omegaWeight
  split_ifs <;> positivity

lemma omegaWeight_sum {N : ℕ} (hN : 1 ≤ N) :
    ∑ s ∈ Finset.Icc 1 N, omegaWeight N s = 1 := by
  have hmem : N ∈ Finset.Icc 1 N := by simp [hN]
  have hsum := base_weights_sum N
  rw [← Finset.add_sum_erase _ _ hmem] at hsum
  rw [← Finset.add_sum_erase _ _ hmem]
  have herase : (∑ s ∈ (Finset.Icc 1 N).erase N, omegaWeight N s) =
      ∑ s ∈ (Finset.Icc 1 N).erase N, (1/(2*s*(s+1)) : ℚ) := by
    apply Finset.sum_congr rfl
    intro s hs
    simp [omegaWeight,(Finset.mem_erase.mp hs).1]
  rw [herase]
  rw [show omegaWeight N N = (1/2+1/(2*N):ℚ) by simp [omegaWeight]]
  change (1/2+1/(2*N):ℚ) + (∑ s ∈ (Finset.Icc 1 N).erase N, (1/(2*s*(s+1)):ℚ)) = 1
  have hNp : (N:ℚ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hNp1 : (N+1:ℚ) ≠ 0 := by positivity
  field_simp at hsum ⊢
  nlinarith

/-- The actual adaptive block assignment E.3, at its own supplied horizon. -/
def adaptiveBlock (x : List Bool) : ℚ :=
  ∑ s ∈ Finset.Icc 1 x.length, omegaWeight x.length s * restrictedBlock s x

lemma adaptiveBlock_sum {N : ℕ} (hN : 1 ≤ N) :
    ∑ x ∈ (words N).toFinset, adaptiveBlock x = 1 := by
  have heq : (∑ x ∈ (words N).toFinset, adaptiveBlock x) =
      ∑ x ∈ (words N).toFinset, ∑ s ∈ Finset.Icc 1 N, omegaWeight N s * restrictedBlock s x := by
    apply Finset.sum_congr rfl
    intro x hx
    unfold adaptiveBlock
    rw [(mem_words N x).mp (List.mem_toFinset.mp hx)]
  rw [heq,Finset.sum_comm]
  simp_rw [← Finset.mul_sum,restrictedBlock_sum,mul_one]
  exact omegaWeight_sum hN

lemma adaptiveBlock_ge_component {N s : ℕ} (x : List Bool) (hx : x.length = N)
    (hN : 1 ≤ N) (hs : s ∈ Finset.Icc 1 N) :
    omegaWeight N s * restrictedBlock s x ≤ adaptiveBlock x := by
  unfold adaptiveBlock
  rw [hx]
  apply Finset.single_le_sum _ hs
  intro j hj
  exact mul_nonneg (omegaWeight_pos hN (Finset.mem_Icc.mp hj).1).le (restrictedBlock_nonneg j x)

lemma adaptiveBlock_ge_half {N : ℕ} (x : List Bool) (hx : x.length = N) (hN : 1 ≤ N) :
    (1/2:ℚ) * blockAssignment x ≤ adaptiveBlock x := by
  have hh := adaptiveBlock_ge_component x hx hN (show N ∈ Finset.Icc 1 N by simp [hN])
  rw [restrictedBlock_universal N x hx] at hh
  have hw : (1/2:ℚ) ≤ omegaWeight N N := by simp [omegaWeight]
  exact (mul_le_mul_of_nonneg_right hw (blockAssignment_pos x).le).trans hh

lemma adaptiveBlock_pos {N : ℕ} (x : List Bool) (hx : x.length = N) (hN : 1 ≤ N) :
    0 < adaptiveBlock x := lt_of_lt_of_le (mul_pos (by norm_num) (blockAssignment_pos x))
      (adaptiveBlock_ge_half x hx hN)

/-- Occupied internal completed-gap types after the first observed renewal. -/
def visibleTypes (x : List Bool) : ℕ :=
  match firstSuffix x with
  | none => 0
  | some z => nu z

def kappa (x : List Bool) : ℕ := max 1 (visibleTypes x)

lemma visibleTypes_le_length (x : List Bool) : visibleTypes x ≤ x.length := by
  unfold visibleTypes
  cases hs : firstSuffix x with
  | none => simp
  | some z =>
    obtain ⟨j,hj⟩ := firstSuffix_some_decomposition x z hs
    have hh := nu_le_length z
    simp only [hj,List.length_append,List.length_replicate,List.length_cons]
    omega

lemma kappa_mem {N : ℕ} (x : List Bool) (hx : x.length = N) (hN : 1 ≤ N) :
    kappa x ∈ Finset.Icc 1 N := by
  have hh := visibleTypes_le_length x
  rw [hx] at hh
  simp only [Finset.mem_Icc,kappa]
  omega

lemma omegaWeight_ge_square {N s : ℕ} (hN : 1 ≤ N) (hs : 1 ≤ s) :
    (1/(2*(s+1)^2):ℚ) ≤ omegaWeight N s := by
  have hsp : (0:ℚ) < s := by exact_mod_cast hs
  have hsp1 : (0:ℚ) < s+1 := by positivity
  unfold omegaWeight
  split_ifs with heq
  · have hden : (1/(2*(s+1)^2):ℚ) ≤ 1/2 := by
      apply (div_le_iff₀ (by positivity : (0:ℚ) < 2*(s+1)^2)).mpr
      nlinarith
    have hn : (0:ℚ) ≤ 1/(2*N) := by positivity
    linarith
  · apply (div_le_div_iff₀ (by positivity : (0:ℚ) < 2*(s+1)^2)
      (by positivity : (0:ℚ) < 2*s*(s+1))).mpr
    nlinarith

lemma restrictedBlock_pos_of_types (s : ℕ) (x : List Bool) (h : visibleTypes x ≤ s) :
    0 < restrictedBlock s x := by
  unfold restrictedBlock
  apply div_pos _ (by positivity)
  cases hs : firstSuffix x with
  | none => norm_num
  | some z =>
    have hnu : nu z ≤ s := by simpa [visibleTypes,hs] using h
    simp only
    rw [restrictedAssignment,restrictedEnvelope_eq _ _ hnu]
    exact div_pos (wordEnvelope_pos z) (restrictedNormalizer_pos _ _)

/-- Restricted B.9 plus E.1 gives the component's polynomial regret. -/
lemma restricted_ratio_le (μ : Law) (s : ℕ) (x : List Bool)
    (h : visibleTypes x ≤ s) :
    blockMass μ x / (restrictedBlock s x : ℝ) ≤ (x.length+1:ℝ)^(2*s+2) := by
  have hq : 0 < (restrictedBlock s x : ℝ) := by exact_mod_cast restrictedBlock_pos_of_types s x h
  cases hs : firstSuffix x with
  | none =>
    have hQ : (restrictedBlock s x : ℝ) = 1/(x.length+1:ℝ) := by simp [restrictedBlock,hs]
    rw [hQ]
    have hh : blockMass μ x / (1/(x.length+1:ℝ)) ≤ (x.length+1:ℝ) := by
      simp only [div_eq_mul_inv,inv_inv,one_mul]
      exact mul_le_of_le_one_left (by positivity) (EnvelopeBridge.blockMass_le_one μ x)
    exact hh.trans (le_self_pow₀ (by linarith [Nat.cast_nonneg (α:=ℝ) x.length]) (by omega))
  | some z =>
    obtain ⟨j,hj⟩ := firstSuffix_some_decomposition x z hs
    have hnu : nu z ≤ s := by simpa [visibleTypes,hs] using h
    have hp : blockMass μ x ≤ (wordEnvelope z:ℝ) := by
      rw [hj]
      exact blockMass_le_wordEnvelope_suffix μ j z
    have hQ : (restrictedBlock s x : ℝ) = (wordEnvelope z:ℝ) /
        ((x.length+1:ℝ)*(restrictedNormalizer z.length s:ℝ)) := by
      simp [restrictedBlock,restrictedAssignment,restrictedEnvelope_eq _ _ hnu,hs,div_div,mul_comm]
    have hz0 : (0:ℝ) < restrictedNormalizer z.length s := by exact_mod_cast restrictedNormalizer_pos _ _
    have hlocal : blockMass μ x / (restrictedBlock s x:ℝ) ≤
        (x.length+1:ℝ)*(restrictedNormalizer z.length s:ℝ) := by
      apply (div_le_iff₀ hq).mpr
      rw [hQ]
      rw [mul_div_cancel₀ _ (by positivity : (x.length+1:ℝ)*(restrictedNormalizer z.length s:ℝ) ≠ 0)]
      exact hp
    have hlen : z.length ≤ x.length := by simp [hj]; omega
    have hnorm : (restrictedNormalizer z.length s:ℝ) ≤ (x.length+1:ℝ)^(2*s+1) := by
      have hh : (restrictedNormalizer z.length s:ℝ) ≤ (z.length+1:ℝ)^(2*s+1) := by
        exact_mod_cast restrictedNormalizer_le_pow z.length s
      exact hh.trans (pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hlen 1) _)
    calc
      _ ≤ (x.length+1:ℝ)*(restrictedNormalizer z.length s:ℝ) := hlocal
      _ ≤ (x.length+1:ℝ)*(x.length+1:ℝ)^(2*s+1) := mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ = _ := by rw [show 2*s+2 = (2*s+1)+1 by omega,pow_succ]; ring

/-- Universal branch obtained from the actual `s=N` mixture component. -/
theorem adaptive_ratio_universal (μ : Law) (x : List Bool) (hN : 1 ≤ x.length) :
    blockMass μ x / (adaptiveBlock x:ℝ) ≤
      2*((x.length+1:ℝ)*(ordinaryNormalizer x.length:ℝ)) := by
  have hq : 0 < (blockAssignment x:ℝ) := by exact_mod_cast blockAssignment_pos x
  have ha : 0 < (adaptiveBlock x:ℝ) := by exact_mod_cast adaptiveBlock_pos x rfl hN
  have hdom : (1/2:ℝ)*(blockAssignment x:ℝ) ≤ (adaptiveBlock x:ℝ) := by
    have hh := adaptiveBlock_ge_half x rfl hN
    have hc : (((1/2:ℚ)*blockAssignment x:ℚ):ℝ) ≤ (adaptiveBlock x:ℝ) := Rat.cast_le.mpr hh
    norm_num at hc
    exact hc
  have hdiv : blockMass μ x / (adaptiveBlock x:ℝ) ≤ 2*(blockMass μ x/(blockAssignment x:ℝ)) := by
    calc
      _ ≤ blockMass μ x / ((1/2:ℝ)*(blockAssignment x:ℝ)) :=
        div_le_div_of_nonneg_left (blockMass_nonneg μ x) (by positivity) hdom
      _ = _ := by field_simp <;> ring
  exact hdiv.trans (mul_le_mul_of_nonneg_left (blockAssignment_ratio_bound μ x) (by norm_num))

/-- The occupied-type component gives the second multiplicative oracle branch. -/
theorem adaptive_ratio_occupied (μ : Law) (x : List Bool) (hN : 1 ≤ x.length) :
    blockMass μ x / (adaptiveBlock x:ℝ) ≤
      2*(kappa x+1:ℝ)^2 * (x.length+1:ℝ)^(2*kappa x+2) := by
  let s := kappa x
  have hs := kappa_mem x rfl hN
  have hsp : 1 ≤ s := (Finset.mem_Icc.mp hs).1
  have htypes : visibleTypes x ≤ s := le_max_right _ _
  have hqs : 0 < (restrictedBlock s x:ℝ) := by exact_mod_cast restrictedBlock_pos_of_types s x htypes
  have hdomq : (1/(2*(s+1)^2):ℚ)*restrictedBlock s x ≤ adaptiveBlock x :=
    (mul_le_mul_of_nonneg_right (omegaWeight_ge_square hN hsp) (restrictedBlock_nonneg s x)).trans
      (adaptiveBlock_ge_component x rfl hN hs)
  have hdom : (1/(2*(s+1)^2):ℝ)*(restrictedBlock s x:ℝ) ≤ (adaptiveBlock x:ℝ) := by
    have hc : (((1/(2*(s+1)^2):ℚ)*restrictedBlock s x:ℚ):ℝ) ≤ (adaptiveBlock x:ℝ) := Rat.cast_le.mpr hdomq
    push_cast at hc
    exact hc
  have hdiv : blockMass μ x / (adaptiveBlock x:ℝ) ≤
      2*(s+1:ℝ)^2*(blockMass μ x/(restrictedBlock s x:ℝ)) := by
    calc
      _ ≤ blockMass μ x / ((1/(2*(s+1)^2):ℝ)*(restrictedBlock s x:ℝ)) :=
        div_le_div_of_nonneg_left (blockMass_nonneg μ x) (by positivity) hdom
      _ = _ := by field_simp <;> ring
  exact hdiv.trans (mul_le_mul_of_nonneg_left (restricted_ratio_le μ s x htypes) (by positivity))

/-- Exact universal envelope penalty, before inserting the external classical
partition estimate from B.6. -/
def universalPenalty (N : ℕ) : ℝ :=
  Real.log ((N+1:ℝ)*(ordinaryNormalizer N:ℝ))

/-- The data-dependent branch in E.4. -/
def occupiedPenalty (N k : ℕ) : ℝ :=
  (2*k+2:ℝ)*Real.log (N+1:ℝ) + 2*Real.log (k+1:ℝ)

/-- E.2 on the actual adaptive assignment, with the exact ordinary normalizer
as its universal branch. No pointwise regret conclusion is assumed. -/
theorem adaptive_log_oracle (μ : Law) (x : List Bool) (hN : 1 ≤ x.length)
    (hp : 0 < blockMass μ x) :
    Real.log (blockMass μ x/(adaptiveBlock x:ℝ)) ≤ Real.log 2 +
      min (universalPenalty x.length) (occupiedPenalty x.length (kappa x)) := by
  have hqa : 0 < (adaptiveBlock x:ℝ) := by exact_mod_cast adaptiveBlock_pos x rfl hN
  have hlog0 := div_pos hp hqa
  have hZ : (0:ℝ) < ordinaryNormalizer x.length := by exact_mod_cast Prediction.ordinaryNormalizer_pos _
  have hu := Real.log_le_log hlog0 (adaptive_ratio_universal μ x hN)
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by positivity)] at hu
  have ho := Real.log_le_log hlog0 (adaptive_ratio_occupied μ x hN)
  have hb : (0:ℝ) < x.length+1 := by positivity
  have hk : (0:ℝ) < kappa x+1 := by positivity
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by positivity),Real.log_pow,Real.log_pow] at ho
  have ho' : Real.log (blockMass μ x/(adaptiveBlock x:ℝ)) ≤
      Real.log 2 + occupiedPenalty x.length (kappa x) := by
    convert ho using 1 <;> simp [occupiedPenalty] <;> push_cast <;> ring
  change Real.log (blockMass μ x/(adaptiveBlock x:ℝ)) ≤
    Real.log 2 + min (Real.log ((x.length+1:ℝ)*(ordinaryNormalizer x.length:ℝ))) _
  have hm : Real.log (blockMass μ x/(adaptiveBlock x:ℝ)) - Real.log 2 ≤
      min (Real.log ((x.length+1:ℝ)*(ordinaryNormalizer x.length:ℝ)))
        (occupiedPenalty x.length (kappa x)) := le_min (by linarith [hu]) (by linarith [ho'])
  linarith

/-- Inserting a separately proved universal estimate preserves the full oracle
minimum; the adaptive branch above remains unconditional. -/
theorem adaptive_log_oracle_of_universal (μ : Law) (x : List Bool) (hN : 1 ≤ x.length)
    (hp : 0 < blockMass μ x) (B : ℝ) (hB : universalPenalty x.length ≤ B) :
    Real.log (blockMass μ x/(adaptiveBlock x:ℝ)) ≤
      Real.log 2 + min B (occupiedPenalty x.length (kappa x)) :=
  (adaptive_log_oracle μ x hN hp).trans (add_le_add_left (min_le_min_right _ hB) _)

/-- The actual restricted continuation sum in E.7/E.9. -/
def restrictedContinuation (L s : ℕ) (z : List Bool) : ℚ :=
  ∑ v ∈ (words (L-z.length)).toFinset, restrictedEnvelope s (z++v)

def restrictedPrefix (N s : ℕ) (z : List Bool) : ℚ :=
  ∑ v ∈ (words (N-z.length)).toFinset, restrictedBlock s (z++v)

def adaptivePrefix (N : ℕ) (z : List Bool) : ℚ :=
  ∑ v ∈ (words (N-z.length)).toFinset, adaptiveBlock (z++v)

def adaptiveConditional (N : ℕ) (z : List Bool) : ℚ :=
  adaptivePrefix N (z++[true]) / adaptivePrefix N z

/-- The source adaptive suffix-averaged predictor; it receives no support or
tail parameter. -/
def adaptivePredict (n : ℕ) (x : List Bool) : ℚ :=
  (∑ t ∈ Finset.Icc 1 n, adaptiveConditional (n+1) (x.drop (n-t))) / n

@[simp] lemma restrictedContinuation_nil (L s : ℕ) :
    restrictedContinuation L s [] = restrictedNormalizer L s := by
  simp [restrictedContinuation,restrictedNormalizer]

lemma restrictedPrefix_zeros (N s t : ℕ) (ht : t ≤ N) :
    restrictedPrefix N s (List.replicate t false) = (N-t+1:ℕ)/(N+1:ℚ) := by
  unfold restrictedPrefix
  simp only [List.length_replicate]
  calc
    _ = (∑ v ∈ (words (N-t)).toFinset, restrictedComponentMass s v) / (N+1:ℚ) := by
      simp only [div_eq_mul_inv,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro v hv
      have hvlen := (mem_words (N-t) v).mp (List.mem_toFinset.mp hv)
      have hlen : (List.replicate t false++v).length = N := by simp [hvlen]; omega
      unfold restrictedBlock restrictedComponentMass
      rw [hlen,firstSuffix_zeros_prefix]
      rfl
    _ = _ := by rw [restrictedComponentMass_sum]; push_cast; rfl

/-- The actual first-renewal prefix formula E.9. -/
theorem restrictedPrefix_firstRenewal (N s j : ℕ) (z : List Bool)
    (hz : j+1+z.length ≤ N) :
    restrictedPrefix N s (List.replicate j false++true::z) =
      restrictedContinuation (N-(j+1)) s z /
        ((N+1:ℚ)*restrictedNormalizer (N-(j+1)) s) := by
  unfold restrictedPrefix restrictedContinuation
  have hrem : N-(List.replicate j false++true::z).length = N-(j+1)-z.length := by simp; omega
  rw [hrem]
  simp only [div_eq_mul_inv,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v hv
  have hvlen := (mem_words (N-(j+1)-z.length) v).mp (List.mem_toFinset.mp hv)
  have hslen : (z++v).length = N-(j+1) := by simp [hvlen]; omega
  have hlen : ((List.replicate j false++true::z)++v).length = N := by simp [hvlen]; omega
  unfold restrictedBlock
  rw [hlen]
  simp only [List.append_assoc,List.cons_append,firstSuffix_zeros_prefix,firstSuffix]
  simp [restrictedAssignment,hslen,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm]

/-- Prefix probabilities are mixed before taking their conditional ratio. -/
theorem adaptivePrefix_eq_mix (N : ℕ) (z : List Bool) (hz : z.length ≤ N) :
    adaptivePrefix N z = ∑ s ∈ Finset.Icc 1 N, omegaWeight N s * restrictedPrefix N s z := by
  unfold adaptivePrefix restrictedPrefix
  have heq : (∑ v ∈ (words (N-z.length)).toFinset, adaptiveBlock (z++v)) =
      ∑ v ∈ (words (N-z.length)).toFinset,
        ∑ s ∈ Finset.Icc 1 N, omegaWeight N s * restrictedBlock s (z++v) := by
    apply Finset.sum_congr rfl
    intro v hv
    have hvlen := (mem_words (N-z.length) v).mp (List.mem_toFinset.mp hv)
    have hlen : (z++v).length = N := by simp [hvlen]; omega
    unfold adaptiveBlock
    rw [hlen]
  rw [heq,Finset.sum_comm]
  simp_rw [Finset.mul_sum]

lemma adaptivePrefix_pos {N : ℕ} (hN : 1 ≤ N) (z : List Bool) (hz : z.length ≤ N) :
    0 < adaptivePrefix N z := by
  apply Finset.sum_pos'
  · intro v hv
    have hvlen := (mem_words (N-z.length) v).mp (List.mem_toFinset.mp hv)
    have hlen : (z++v).length = N := by simp [hvlen]; omega
    exact (adaptiveBlock_pos _ hlen hN).le
  · refine ⟨List.replicate (N-z.length) false, List.mem_toFinset.mpr ((mem_words _ _).mpr (by simp)), ?_⟩
    exact adaptiveBlock_pos _ (by simp; omega) hN

/-- The adaptive conditional is the ratio of two *mixed* prefix sums, as in E.9. -/
theorem adaptiveConditional_eq_mix (N : ℕ) (z : List Bool) (hz : z.length < N) :
    adaptiveConditional N z =
      (∑ s ∈ Finset.Icc 1 N, omegaWeight N s * restrictedPrefix N s (z++[true])) /
        (∑ s ∈ Finset.Icc 1 N, omegaWeight N s * restrictedPrefix N s z) := by
  unfold adaptiveConditional
  rw [adaptivePrefix_eq_mix _ _ (by simp; omega),adaptivePrefix_eq_mix _ _ hz.le]

/-- Harmless zero-horizon extension for generic finite-block assignment APIs.
Every positive-horizon word uses exactly E.3. -/
def adaptiveMass (x : List Bool) : ℚ := if x=[] then 1 else adaptiveBlock x

lemma adaptiveMass_eq (x : List Bool) (hx : 1 ≤ x.length) : adaptiveMass x = adaptiveBlock x := by
  have hh : x ≠ [] := by intro hh; subst x; simp at hx
  simp [adaptiveMass,hh]

lemma adaptiveMass_pos (x : List Bool) : 0 < adaptiveMass x := by
  by_cases hx : x=[]
  · simp [adaptiveMass,hx]
  · have hn : 1 ≤ x.length := by cases x <;> simp_all
    rw [adaptiveMass_eq x hn]
    exact adaptiveBlock_pos x rfl hn

lemma adaptiveMass_sum (N : ℕ) : ∑ x ∈ (words N).toFinset, adaptiveMass x = 1 := by
  cases N with
  | zero => simp [words,adaptiveMass]
  | succ N =>
    have heq : (∑ x ∈ (words (N+1)).toFinset, adaptiveMass x) =
        ∑ x ∈ (words (N+1)).toFinset, adaptiveBlock x := by
      apply Finset.sum_congr rfl
      intro x hx
      apply adaptiveMass_eq
      rw [(mem_words (N+1) x).mp (List.mem_toFinset.mp hx)]
      omega
    rw [heq]
    exact adaptiveBlock_sum (by omega)

end Paper37.Adaptive
