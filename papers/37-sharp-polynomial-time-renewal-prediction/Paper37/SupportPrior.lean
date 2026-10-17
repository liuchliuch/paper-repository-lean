import Paper37.LowerBound
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
The exact finite support prior in Appendix F. Positive gap length d+1 is
represented by index d, as in `Paper37.Renewal.Law`.
-/
namespace Paper37.SupportPrior
open scoped BigOperators
open Paper37.LowerBound

noncomputable section

/-- Uniform probability on a finite nonempty sample space. -/
def uniform {α : Type*} [Fintype α] [Nonempty α] : FiniteLaw α where
  mass _ := 1 / (Fintype.card α : ℝ)
  nonneg _ := (one_div_pos.mpr (by exact_mod_cast Fintype.card_pos)).le
  total := by simp [Fintype.card_ne_zero]

/-- Uniform probability on the members of a nonempty finite set. -/
def uniformOn {α : Type*} (T : Finset α) (hT : T.Nonempty) : FiniteLaw T := by
  letI : Nonempty T := ⟨⟨hT.choose, hT.choose_spec⟩⟩
  exact uniform

@[simp] lemma uniformOn_mass {α : Type*} (T : Finset α) (hT : T.Nonempty) (x : T) :
    (uniformOn T hT).mass x = 1 / (T.card : ℝ) := by
  simp [uniformOn, uniform, Fintype.card_coe]

lemma uniformOn_eventMass {α : Type*} [DecidableEq α]
    (T : Finset α) (hT : T.Nonempty) (E : α → Prop) [DecidablePred E] :
    (uniformOn T hT).eventMass (fun x => E x.val) =
      ((T.filter E).card : ℝ) / T.card := by
  unfold FiniteLaw.eventMass
  simp_rw [uniformOn_mass]
  rw [T.sum_coe_sort (fun x : α => if E x then 1 / (T.card : ℝ) else 0)]
  rw [← Finset.sum_filter]
  simp [div_eq_mul_inv]

/-- Every compatible k-subset is obtained by adjoining A to a (k-|A|)-subset
of the unused universe. This proves the exact conditioning cardinality. -/
def compatibleChoices {α : Type*} [DecidableEq α]
    (U : Finset α) (k : ℕ) (A : Finset α) : Finset (Finset α) :=
  (U.powersetCard k).filter (fun L => A ⊆ L)

lemma compatibleChoices_mem {α : Type*} [DecidableEq α]
    {U A L : Finset α} {k : ℕ} :
    L ∈ compatibleChoices U k A ↔ L ⊆ U ∧ L.card = k ∧ A ⊆ L := by
  simp [compatibleChoices, and_assoc]

lemma compatibleChoices_card {α : Type*} [DecidableEq α]
    (U A : Finset α) (k : ℕ) (hAU : A ⊆ U) (hAk : A.card ≤ k) :
    (compatibleChoices U k A).card = (U.card - A.card).choose (k - A.card) := by
  classical
  have hbij : (compatibleChoices U k A).card =
      ((U \ A).powersetCard (k - A.card)).card := by
    apply Finset.card_bij (fun L _ => L \ A)
    · intro L hL
      obtain ⟨hLU, hLk, hAL⟩ := compatibleChoices_mem.mp hL
      apply Finset.mem_powersetCard.mpr
      constructor
      · exact Finset.sdiff_subset_sdiff hLU (by rfl)
      · rw [Finset.card_sdiff_of_subset hAL, hLk]
    · intro L hL K hK heq
      have hAL := (compatibleChoices_mem.mp hL).2.2
      have hAK := (compatibleChoices_mem.mp hK).2.2
      calc
        L = A ∪ (L \ A) := (Finset.union_sdiff_of_subset hAL).symm
        _ = A ∪ (K \ A) := by rw [heq]
        _ = K := Finset.union_sdiff_of_subset hAK
    · intro V hV
      obtain ⟨hVU, hVk⟩ := Finset.mem_powersetCard.mp hV
      have hdis : Disjoint A V := by
        apply Finset.disjoint_left.mpr
        intro x hxA hxV
        exact (Finset.mem_sdiff.mp (hVU hxV)).2 hxA
      have hmem : A ∪ V ∈ compatibleChoices U k A := by
        apply compatibleChoices_mem.mpr
        refine ⟨Finset.union_subset hAU (fun x hx => (Finset.mem_sdiff.mp (hVU hx)).1), ?_,
          Finset.subset_union_left⟩
        rw [Finset.card_union_of_disjoint hdis, hVk]
        exact Nat.add_sub_of_le hAk
      exact ⟨A ∪ V, hmem, Finset.union_sdiff_cancel_left hdis⟩
  rw [hbij, Finset.card_powersetCard, Finset.card_sdiff_of_subset hAU]

/-- Adding the unseen candidate to the required set precisely counts the
compatible supports that contain that candidate. -/
lemma compatibleChoices_filter_mem {α : Type*} [DecidableEq α]
    (U A : Finset α) (k : ℕ) (g : α) :
    (compatibleChoices U k A).filter (fun L => g ∈ L) =
      compatibleChoices U k (insert g A) := by
  ext L
  simp [compatibleChoices, Finset.insert_subset_iff, and_assoc, and_left_comm, and_comm]

lemma compatibleChoices_nonempty {α : Type*} [DecidableEq α]
    (U A : Finset α) (k : ℕ) (hAU : A ⊆ U) (hAk : A.card ≤ k) (hkU : k ≤ U.card) :
    (compatibleChoices U k A).Nonempty := by
  apply Finset.card_pos.mp
  rw [compatibleChoices_card U A k hAU hAk]
  exact Nat.choose_pos (Nat.sub_le_sub_right hkU A.card)

/-- The original low-support prior conditioned on containing the observed low
gaps is uniform on exactly these compatible low supports. -/
def compatiblePrior {α : Type*} [DecidableEq α]
    (U A : Finset α) (k : ℕ) (hAU : A ⊆ U) (hAk : A.card ≤ k) (hkU : k ≤ U.card) :
    FiniteLaw (compatibleChoices U k A) :=
  uniformOn _ (compatibleChoices_nonempty U A k hAU hAk hkU)

lemma choose_pred_ratio {N K : ℕ} (hK : 0 < K) (hKN : K ≤ N) :
    (((N - 1).choose (K - 1) : ℕ) : ℝ) / N.choose K = (K : ℝ) / N := by
  have hN : 0 < N := lt_of_lt_of_le hK hKN
  have hNat : N * (N - 1).choose (K - 1) = N.choose K * K := by
    have h := Nat.succ_mul_choose_eq (N - 1) (K - 1)
    simpa only [Nat.succ_eq_add_one, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hN.ne'),
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hK.ne')] using h
  have hReal : (N : ℝ) * ((N - 1).choose (K - 1) : ℝ) = (N.choose K : ℝ) * K := by
    exact_mod_cast hNat
  have hden : (N.choose K : ℝ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hKN
  have hNReal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  apply (div_eq_div_iff hden hNReal).2
  nlinarith

/-- Exact hypergeometric membership after conditioning on all observed types.
This is the combinatorial content of source F.9. -/
lemma compatiblePrior_membership {α : Type*} [DecidableEq α]
    (U A : Finset α) (k : ℕ) (g : α)
    (hAU : A ⊆ U) (hAk : A.card < k) (hkU : k ≤ U.card)
    (hgU : g ∈ U) (hgA : g ∉ A) :
    (compatiblePrior U A k hAU hAk.le hkU).eventMass (fun L => g ∈ L.val) =
      ((k : ℝ) - A.card) / ((U.card : ℝ) - A.card) := by
  have hAgU : insert g A ⊆ U := Finset.insert_subset_iff.mpr ⟨hgU, hAU⟩
  have hAgk : (insert g A).card ≤ k := by rw [Finset.card_insert_of_notMem hgA]; omega
  have hAUcard := Finset.card_le_card hAU
  rw [compatiblePrior, uniformOn_eventMass _ _ (fun L : Finset α => g ∈ L), compatibleChoices_filter_mem,
    compatibleChoices_card U (insert g A) k hAgU hAgk,
    compatibleChoices_card U A k hAU hAk.le, Finset.card_insert_of_notMem hgA]
  have hUdiff : U.card - (A.card + 1) = (U.card - A.card) - 1 := by omega
  have hkdiff : k - (A.card + 1) = (k - A.card) - 1 := by omega
  rw [hUdiff, hkdiff,
    choose_pred_ratio (show 0 < k - A.card by omega) (Nat.sub_le_sub_right hkU A.card)]
  rw [Nat.cast_sub hAk.le, Nat.cast_sub hAUcard]

/-- Independent product of two finite laws. -/
def product {α β : Type*} [Fintype α] [Fintype β]
    (P : FiniteLaw α) (Q : FiniteLaw β) : FiniteLaw (α × β) where
  mass z := P.mass z.1 * Q.mass z.2
  nonneg z := mul_nonneg (P.nonneg z.1) (Q.nonneg z.2)
  total := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, Q.total, mul_one]
    exact P.total

lemma product_expectation {α β : Type*} [Fintype α] [Fintype β]
    (P : FiniteLaw α) (Q : FiniteLaw β) (f : α → β → ℝ) :
    (product P Q).expectation (fun z => f z.1 z.2) =
      P.expectation (fun x => Q.expectation (f x)) := by
  unfold FiniteLaw.expectation product
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- Source a = 24b, using b = ceil sqrt n later in the construction. -/
def scale (b : ℕ) : ℕ := 24 * b

def lowPool (b : ℕ) : Finset ℕ := Finset.range (24 * b)
def highFreePool (b : ℕ) : Finset ℕ := Finset.Ico (24 * b) (48 * b - 2)
def forcedHigh (b : ℕ) : Finset ℕ := {48 * b - 2, 48 * b - 1}
def lowChoices (b : ℕ) : Finset (Finset ℕ) := (lowPool b).powersetCard (12 * b)
def highFreeChoices (b : ℕ) : Finset (Finset ℕ) :=
  (highFreePool b).powersetCard (12 * b - 2)

lemma lowChoices_nonempty (b : ℕ) : (lowChoices b).Nonempty := by
  rw [lowChoices, Finset.powersetCard_nonempty]
  simp [lowPool]
  omega

lemma highFreeChoices_nonempty (b : ℕ) : (highFreeChoices b).Nonempty := by
  rw [highFreeChoices, Finset.powersetCard_nonempty]
  simp [highFreePool]
  omega

abbrev Sample (b : ℕ) := (↥(lowChoices b)) × (↥(highFreeChoices b))

/-- Exactly F.2: independent uniform low and free high subsets. The final two
high lengths 2a-1,2a are forced, represented by indices 2a-2,2a-1. -/
def prior (b : ℕ) : FiniteLaw (Sample b) :=
  product (uniformOn _ (lowChoices_nonempty b)) (uniformOn _ (highFreeChoices_nonempty b))

def lowSupport {b : ℕ} (z : Sample b) : Finset ℕ := z.1.val
def highSupport {b : ℕ} (z : Sample b) : Finset ℕ := z.2.val ∪ forcedHigh b
def support {b : ℕ} (z : Sample b) : Finset ℕ := lowSupport z ∪ highSupport z

lemma lowSupport_spec {b : ℕ} (z : Sample b) :
    lowSupport z ⊆ Finset.range (24 * b) ∧ (lowSupport z).card = 12 * b := by
  exact Finset.mem_powersetCard.mp z.1.property

lemma highFreeSupport_spec {b : ℕ} (z : Sample b) :
    z.2.val ⊆ Finset.Ico (24 * b) (48 * b - 2) ∧ z.2.val.card = 12 * b - 2 := by
  exact Finset.mem_powersetCard.mp z.2.property

lemma lowSupport_bounds {b : ℕ} (z : Sample b) {d : ℕ} (hd : d ∈ lowSupport z) :
    d < 24 * b := Finset.mem_range.mp ((lowSupport_spec z).1 hd)

lemma highSupport_bounds {b : ℕ} (hb : 0 < b) (z : Sample b) {d : ℕ}
    (hd : d ∈ highSupport z) : 24 * b ≤ d ∧ d < 48 * b := by
  rcases Finset.mem_union.mp hd with hfree | hforce
  · have := Finset.mem_Ico.mp ((highFreeSupport_spec z).1 hfree)
    omega
  · simp only [forcedHigh, Finset.mem_insert, Finset.mem_singleton] at hforce
    rcases hforce with rfl | rfl <;> omega

lemma highSupport_card {b : ℕ} (hb : 0 < b) (z : Sample b) :
    (highSupport z).card = 12 * b := by
  have hdis : Disjoint z.2.val (forcedHigh b) := by
    apply Finset.disjoint_left.mpr
    intro d hd hf
    have hbound := Finset.mem_Ico.mp ((highFreeSupport_spec z).1 hd)
    simp only [forcedHigh, Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with rfl | rfl <;> omega
  have hcard : (forcedHigh b).card = 2 := by
    have hne : 48 * b - 2 ≠ 48 * b - 1 := by omega
    simp [forcedHigh, hne]
  unfold highSupport
  rw [Finset.card_union_of_disjoint hdis, (highFreeSupport_spec z).2, hcard]
  omega

lemma low_high_disjoint {b : ℕ} (hb : 0 < b) (z : Sample b) :
    Disjoint (lowSupport z) (highSupport z) := by
  apply Finset.disjoint_left.mpr
  intro d hl hh
  have := lowSupport_bounds z hl
  have := (highSupport_bounds hb z hh).1
  omega

lemma support_card {b : ℕ} (hb : 0 < b) (z : Sample b) :
    (support z).card = 24 * b := by
  unfold support
  rw [Finset.card_union_of_disjoint (low_high_disjoint hb z),
    (lowSupport_spec z).2, highSupport_card hb z]
  omega

lemma forcedHigh_subset_support {b : ℕ} (z : Sample b) : forcedHigh b ⊆ support z := by
  intro d hd
  exact Finset.mem_union_right _ (Finset.mem_union_right _ hd)

lemma support_nonempty {b : ℕ} (z : Sample b) : (support z).Nonempty := by
  refine ⟨48 * b - 1, forcedHigh_subset_support z ?_⟩
  simp [forcedHigh]

/-- Every sampled support defines an actual finite-mean renewal law. -/
def law {b : ℕ} (z : Sample b) : Paper37.Renewal.Law :=
  uniformSupportLaw (support z) (support_nonempty z)

lemma expectation_indicator {α : Type*} [Fintype α] (P : FiniteLaw α)
    (E : α → Prop) [DecidablePred E] :
    P.expectation (fun x => if E x then 1 else 0) = P.eventMass E := by
  unfold FiniteLaw.expectation FiniteLaw.eventMass
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : E x <;> simp [hx]

/-- Ordinary finite Bayes conditioning on an event with positive probability. -/
def condition {α : Type*} [Fintype α] (P : FiniteLaw α)
    (E : α → Prop) [DecidablePred E] (hE : 0 < P.eventMass E) : FiniteLaw α :=
  P.reweight (fun x => if E x then 1 else 0) (by intro x; by_cases hx : E x <;> simp [hx])
    (by rwa [expectation_indicator])

lemma condition_eventMass {α : Type*} [Fintype α] (P : FiniteLaw α)
    (E M : α → Prop) [DecidablePred E] [DecidablePred M] (hE : 0 < P.eventMass E) :
    (condition P E hE).eventMass M = P.eventMass (fun x => E x ∧ M x) / P.eventMass E := by
  rw [condition, P.reweight_eventMass, expectation_indicator]
  congr 1
  unfold FiniteLaw.expectation FiniteLaw.eventMass
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : E x <;> by_cases hxM : M x <;> simp [hx, hxM]

lemma uniformOn_eventMass_pos {α : Type*} [DecidableEq α]
    (T : Finset α) (hT : T.Nonempty) (E : α → Prop) [DecidablePred E]
    (hE : (T.filter E).Nonempty) :
    0 < (uniformOn T hT).eventMass (fun x => E x.val) := by
  rw [uniformOn_eventMass T hT E]
  exact div_pos (by exact_mod_cast hE.card_pos) (by exact_mod_cast hT.card_pos)

/-- Conditioning a uniform finite law really is uniform over the compatible
choices, for every event. This identifies the original-prior conditioning. -/
lemma uniformOn_condition_eventMass {α : Type*} [DecidableEq α]
    (T : Finset α) (hT : T.Nonempty) (E M : α → Prop)
    [DecidablePred E] [DecidablePred M] (hE : (T.filter E).Nonempty) :
    (condition (uniformOn T hT) (fun x => E x.val)
      (uniformOn_eventMass_pos T hT E hE)).eventMass (fun x => M x.val) =
      (uniformOn (T.filter E) hE).eventMass (fun x => M x.val) := by
  rw [condition_eventMass,
    uniformOn_eventMass T hT (fun x => E x ∧ M x), uniformOn_eventMass T hT E,
    uniformOn_eventMass (T.filter E) hE M, Finset.filter_filter]
  have hTcard : (T.card : ℝ) ≠ 0 := by exact_mod_cast hT.card_pos.ne'
  have hEcard : ((T.filter E).card : ℝ) ≠ 0 := by exact_mod_cast hE.card_pos.ne'
  field_simp

/-- F.9 now for the original uniform k-subset prior and actual event
conditioning, rather than a separately specified compatible prior. -/
lemma uniform_subset_conditioned_membership {α : Type*} [DecidableEq α]
    (U A : Finset α) (k : ℕ) (g : α)
    (hAU : A ⊆ U) (hAk : A.card < k) (hkU : k ≤ U.card)
    (hgU : g ∈ U) (hgA : g ∉ A) :
    let T := U.powersetCard k
    let hT := Finset.powersetCard_nonempty.mpr hkU
    let hE : (T.filter (fun L => A ⊆ L)).Nonempty :=
      compatibleChoices_nonempty U A k hAU hAk.le hkU
    (condition (uniformOn T hT) (fun L => A ⊆ L.val)
      (uniformOn_eventMass_pos T hT (fun L => A ⊆ L) hE)).eventMass
        (fun L => g ∈ L.val) = ((k : ℝ) - A.card) / ((U.card : ℝ) - A.card) := by
  dsimp only
  rw [uniformOn_condition_eventMass _ _ (fun L : Finset α => A ⊆ L)
    (fun L : Finset α => g ∈ L)]
  exact compatiblePrior_membership U A k g hAU hAk hkU hgU hgA

/-- Positive finite likelihood and the exact Bayes posterior on source samples. -/
def observationLikelihood {b : ℕ} (j : ℕ) (x : List Bool) (z : Sample b) : ℝ :=
  Paper37.Renewal.blockMass (law z) (List.replicate j false ++ true :: x)

def posterior {b : ℕ} (j : ℕ) (x : List Bool)
    (hZ : 0 < (prior b).expectation (observationLikelihood j x)) : FiniteLaw (Sample b) :=
  (prior b).reweight (observationLikelihood j x)
    (fun z => Paper37.Renewal.blockMass_nonneg (law z) _) hZ

def boundaryCount {b : ℕ} (z : Sample b) (t : ℕ) : ℝ :=
  ((support z).filter (fun d => t ≤ d)).card

def boundaryWeight {b : ℕ} (j : ℕ) (x : List Bool) (z : Sample b) : ℝ :=
  boundaryCount z j * boundaryCount z (Paper37.Renewal.ageFrom 0 x) /
    Paper37.Renewal.mean (law z)

def likelihoodScale (b : ℕ) (x : List Bool) : ℝ :=
  (1 / ((24 * b : ℕ) : ℝ)) ^ ((Paper37.Renewal.gapsFrom 0 x).length + 2)

def compatible {b : ℕ} (x : List Bool) (z : Sample b) : Prop :=
  (Paper37.Renewal.gapsFrom 0 x).toFinset ⊆ support z

instance compatible_decidable {b : ℕ} (x : List Bool) (z : Sample b) :
    Decidable (compatible x z) := by
  unfold compatible
  infer_instance

lemma boundaryWeight_nonneg {b : ℕ} (j : ℕ) (x : List Bool) (z : Sample b) :
    0 ≤ boundaryWeight j x z := by
  unfold boundaryWeight boundaryCount
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (Paper37.Renewal.mean_pos _).le

lemma likelihoodScale_pos {b : ℕ} (hb : 0 < b) (x : List Bool) :
    0 < likelihoodScale b x := by
  unfold likelihoodScale
  apply pow_pos
  apply one_div_pos.mpr
  exact_mod_cast (show 0 < 24 * b by omega)

/-- The actual prior's block likelihood has exactly the indicator, common
power of a, and BOTH boundary factors from F.8. -/
lemma observationLikelihood_factor {b : ℕ} (hb : 0 < b)
    (j : ℕ) (x : List Bool) (z : Sample b) :
    observationLikelihood j x z =
      if compatible x z then likelihoodScale b x * boundaryWeight j x z else 0 := by
  unfold observationLikelihood law
  rw [uniformSupportLaw_two_boundary_likelihood, support_card hb z]
  unfold likelihoodScale boundaryWeight boundaryCount compatible law
  by_cases hc : (Paper37.Renewal.gapsFrom 0 x).toFinset ⊆ support z
  · simp [hc]
  · simp [hc]

lemma expectation_condition {α : Type*} [Fintype α] (P : FiniteLaw α)
    (E : α → Prop) [DecidablePred E] (hE : 0 < P.eventMass E) (f : α → ℝ) :
    (condition P E hE).expectation f =
      P.expectation (fun x => if E x then f x else 0) / P.eventMass E := by
  change (∑ x, (P.mass x * (if E x then 1 else 0) /
      P.expectation (fun x => if E x then 1 else 0)) * f x) = _
  rw [expectation_indicator]
  unfold FiniteLaw.expectation
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : E x <;> simp [hx, div_eq_mul_inv] <;> ring

lemma expectation_scaled_indicator {α : Type*} [Fintype α]
    (P : FiniteLaw α) (E : α → Prop) [DecidablePred E] (w : α → ℝ) (c : ℝ) :
    P.expectation (fun x => if E x then c * w x else 0) =
      c * P.expectation (fun x => if E x then w x else 0) := by
  unfold FiniteLaw.expectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : E x <;> simp [hx] <;> ring

lemma eventMass_pos_of_weighted_pos {α : Type*} [Fintype α]
    (P : FiniteLaw α) (E : α → Prop) [DecidablePred E] (w : α → ℝ)
    (h : 0 < P.expectation (fun x => if E x then w x else 0)) :
    0 < P.eventMass E := by
  have hex : ∃ x, 0 < P.mass x * (if E x then w x else 0) := by
    by_contra! hnot
    have hnonpos : P.expectation (fun x => if E x then w x else 0) ≤ 0 :=
      Finset.sum_nonpos (fun x _ => hnot x)
    linarith
  obtain ⟨x, hx⟩ := hex
  have hxE : E x := by
    by_contra hnot
    simp [hnot] at hx
  have hPx : 0 < P.mass x := by
    by_contra hnot
    have hz : P.mass x = 0 := le_antisymm (not_lt.mp hnot) (P.nonneg x)
    simp [hz] at hx
  have hsingle : P.mass x ≤ P.eventMass E := by
    unfold FiniteLaw.eventMass
    have hsingle := Finset.single_le_sum (f := fun y => if E y then P.mass y else 0)
      (s := Finset.univ) (a := x) (by
        intro y _
        by_cases hy : E y <;> simp [hy, P.nonneg y]) (Finset.mem_univ x)
    simpa [hxE] using hsingle
  exact lt_of_lt_of_le hPx hsingle

lemma observation_evidence_factor {b : ℕ} (hb : 0 < b) (j : ℕ) (x : List Bool) :
    (prior b).expectation (observationLikelihood j x) = likelihoodScale b x *
      (prior b).expectation (fun z => if compatible x z then boundaryWeight j x z else 0) := by
  have heq : observationLikelihood (b := b) j x = fun z =>
      if compatible x z then likelihoodScale b x * boundaryWeight j x z else 0 :=
    funext (observationLikelihood_factor hb j x)
  rw [heq, expectation_scaled_indicator]

lemma truncated_boundaryWeight_pos {b : ℕ} (hb : 0 < b) (j : ℕ) (x : List Bool)
    (hZ : 0 < (prior b).expectation (observationLikelihood j x)) :
    0 < (prior b).expectation (fun z => if compatible x z then boundaryWeight j x z else 0) := by
  rw [observation_evidence_factor hb j x] at hZ
  exact (mul_pos_iff.mp hZ).resolve_right (by
    intro h
    exact (not_lt_of_ge (likelihoodScale_pos hb x).le) h.1)
    |>.2

lemma compatible_probability_pos {b : ℕ} (hb : 0 < b) (j : ℕ) (x : List Bool)
    (hZ : 0 < (prior b).expectation (observationLikelihood j x)) :
    0 < (prior b).eventMass (compatible x) :=
  eventMass_pos_of_weighted_pos _ _ _ (truncated_boundaryWeight_pos hb j x hZ)

lemma conditioned_boundaryWeight_pos {b : ℕ} (hb : 0 < b) (j : ℕ) (x : List Bool)
    (hZ : 0 < (prior b).expectation (observationLikelihood j x)) :
    0 < (condition (prior b) (compatible x) (compatible_probability_pos hb j x hZ)).expectation
      (boundaryWeight j x) := by
  rw [expectation_condition]
  exact div_pos (truncated_boundaryWeight_pos hb j x hZ) (compatible_probability_pos hb j x hZ)

/-- The actual observational posterior equals the prior conditioned on seen
gaps and then reweighted by BOTH stationary boundary factors. -/
lemma posterior_conditioned_reweight_mass {b : ℕ} (hb : 0 < b) (j : ℕ) (x : List Bool)
    (hZ : 0 < (prior b).expectation (observationLikelihood j x)) (z : Sample b) :
    (posterior j x hZ).mass z =
      ((condition (prior b) (compatible x) (compatible_probability_pos hb j x hZ)).reweight
        (boundaryWeight j x) (boundaryWeight_nonneg j x)
        (conditioned_boundaryWeight_pos hb j x hZ)).mass z := by
  change (prior b).mass z * observationLikelihood j x z /
      (prior b).expectation (observationLikelihood j x) = _
  rw [observationLikelihood_factor hb j x z, observation_evidence_factor hb j x]
  change _ = ((condition (prior b) (compatible x) _).mass z * boundaryWeight j x z /
      (condition (prior b) (compatible x) _).expectation (boundaryWeight j x))
  rw [expectation_condition]
  change _ = (((prior b).mass z * (if compatible x z then 1 else 0) /
      (prior b).expectation (fun z => if compatible x z then 1 else 0)) * boundaryWeight j x z /
        ((prior b).expectation (fun z => if compatible x z then boundaryWeight j x z else 0) /
          (prior b).eventMass (compatible x)))
  rw [expectation_indicator]
  have hc := (likelihoodScale_pos hb x).ne'
  have hE := (compatible_probability_pos hb j x hZ).ne'
  have hW := (truncated_boundaryWeight_pos hb j x hZ).ne'
  by_cases hz : compatible x z
  · simp only [if_pos hz]
    field_simp
    <;> ring
  · simp [hz]

lemma eventMass_congr {α : Type*} [Fintype α] (P : FiniteLaw α)
    (E F : α → Prop) [DecidablePred E] [DecidablePred F]
    (h : ∀ x, E x ↔ F x) : P.eventMass E = P.eventMass F := by
  unfold FiniteLaw.eventMass
  apply Finset.sum_congr rfl
  intro x _
  simp only [h x]

lemma product_eventMass_rect {α β : Type*} [Fintype α] [Fintype β]
    (P : FiniteLaw α) (Q : FiniteLaw β)
    (E : α → Prop) (F : β → Prop) [DecidablePred E] [DecidablePred F] :
    (product P Q).eventMass (fun z => E z.1 ∧ F z.2) = P.eventMass E * Q.eventMass F := by
  unfold FiniteLaw.eventMass product
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hx : E x <;> by_cases hy : F y <;> simp [hx, hy]

def lowPrior (b : ℕ) : FiniteLaw (lowChoices b) := uniformOn _ (lowChoices_nonempty b)
def highPrior (b : ℕ) : FiniteLaw (highFreeChoices b) := uniformOn _ (highFreeChoices_nonempty b)

def lowSeen (b : ℕ) (A : Finset ℕ) : Finset ℕ := A.filter (fun d => d < 24 * b)
def highSeen (b : ℕ) (A : Finset ℕ) : Finset ℕ := A.filter (fun d => 24 * b ≤ d)
def lowCompatible (b : ℕ) (A : Finset ℕ) (L : lowChoices b) : Prop := lowSeen b A ⊆ L.val
def highCompatible (b : ℕ) (A : Finset ℕ) (H : highFreeChoices b) : Prop :=
  highSeen b A ⊆ H.val ∪ forcedHigh b

instance lowCompatible_decidable (b : ℕ) (A : Finset ℕ) (L : lowChoices b) :
    Decidable (lowCompatible b A L) := by unfold lowCompatible; infer_instance
instance highCompatible_decidable (b : ℕ) (A : Finset ℕ) (H : highFreeChoices b) :
    Decidable (highCompatible b A H) := by unfold highCompatible; infer_instance

/-- Source compatibility is a rectangle in the independent low/high sample
space, so conditioning does not couple the two halves. -/
lemma support_compatibility_rectangle {b : ℕ} (hb : 0 < b) (A : Finset ℕ) (z : Sample b) :
    A ⊆ support z ↔ lowCompatible b A z.1 ∧ highCompatible b A z.2 := by
  constructor
  · intro hA
    constructor
    · intro d hd
      obtain ⟨hdA, hda⟩ := Finset.mem_filter.mp hd
      rcases Finset.mem_union.mp (hA hdA) with hl | hh
      · exact hl
      · have := (highSupport_bounds hb z hh).1
        omega
    · intro d hd
      obtain ⟨hdA, hda⟩ := Finset.mem_filter.mp hd
      rcases Finset.mem_union.mp (hA hdA) with hl | hh
      · have := lowSupport_bounds z hl
        omega
      · exact hh
  · rintro ⟨hL, hH⟩ d hdA
    by_cases hda : d < 24 * b
    · exact Finset.mem_union_left _ (hL (Finset.mem_filter.mpr ⟨hdA, hda⟩))
    · exact Finset.mem_union_right _ (hH (Finset.mem_filter.mpr ⟨hdA, by omega⟩))

lemma prior_compatible_probability_factor {b : ℕ} (hb : 0 < b) (A : Finset ℕ) :
    (prior b).eventMass (fun z => A ⊆ support z) =
      (lowPrior b).eventMass (lowCompatible b A) *
        (highPrior b).eventMass (highCompatible b A) := by
  rw [eventMass_congr (prior b) _ _ (support_compatibility_rectangle hb A)]
  exact product_eventMass_rect _ _ _ _

lemma low_compatible_probability_pos {b : ℕ} (hb : 0 < b) (A : Finset ℕ)
    (hA : 0 < (prior b).eventMass (fun z => A ⊆ support z)) :
    0 < (lowPrior b).eventMass (lowCompatible b A) := by
  rw [prior_compatible_probability_factor hb A] at hA
  by_contra hnot
  have hnonpos := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hnot)
    ((highPrior b).eventMass_nonneg (highCompatible b A))
  linarith

lemma high_compatible_probability_pos {b : ℕ} (hb : 0 < b) (A : Finset ℕ)
    (hA : 0 < (prior b).eventMass (fun z => A ⊆ support z)) :
    0 < (highPrior b).eventMass (highCompatible b A) := by
  rw [prior_compatible_probability_factor hb A] at hA
  by_contra hnot
  have hnonpos := mul_nonpos_of_nonneg_of_nonpos
    ((lowPrior b).eventMass_nonneg (lowCompatible b A)) (not_lt.mp hnot)
  linarith

def seenPrior {b : ℕ} (A : Finset ℕ)
    (hA : 0 < (prior b).eventMass (fun z => A ⊆ support z)) : FiniteLaw (Sample b) :=
  condition (prior b) (fun z => A ⊆ support z) hA

def seenLowPrior {b : ℕ} (hb : 0 < b) (A : Finset ℕ)
    (hA : 0 < (prior b).eventMass (fun z => A ⊆ support z)) : FiniteLaw (lowChoices b) :=
  condition (lowPrior b) (lowCompatible b A) (low_compatible_probability_pos hb A hA)

def seenHighPrior {b : ℕ} (hb : 0 < b) (A : Finset ℕ)
    (hA : 0 < (prior b).eventMass (fun z => A ⊆ support z)) : FiniteLaw (highFreeChoices b) :=
  condition (highPrior b) (highCompatible b A) (high_compatible_probability_pos hb A hA)

/-- Exact independence under Pi_A, proved atom by atom from the original
source F.2 prior and event conditioning. -/
lemma seenPrior_mass_factor {b : ℕ} (hb : 0 < b) (A : Finset ℕ)
    (hA : 0 < (prior b).eventMass (fun z => A ⊆ support z)) (z : Sample b) :
    (seenPrior A hA).mass z =
      (seenLowPrior hb A hA).mass z.1 * (seenHighPrior hb A hA).mass z.2 := by
  change ((lowPrior b).mass z.1 * (highPrior b).mass z.2 *
      (if A ⊆ support z then 1 else 0) /
      (prior b).expectation (fun z => if A ⊆ support z then 1 else 0)) =
    (((lowPrior b).mass z.1 * (if lowCompatible b A z.1 then 1 else 0) /
        (lowPrior b).expectation (fun L => if lowCompatible b A L then 1 else 0)) *
      ((highPrior b).mass z.2 * (if highCompatible b A z.2 then 1 else 0) /
        (highPrior b).expectation (fun H => if highCompatible b A H then 1 else 0)))
  rw [expectation_indicator, expectation_indicator, expectation_indicator,
    prior_compatible_probability_factor hb A]
  simp only [support_compatibility_rectangle hb A z]
  have hL := (low_compatible_probability_pos hb A hA).ne'
  have hH := (high_compatible_probability_pos hb A hA).ne'
  by_cases hl : lowCompatible b A z.1 <;> by_cases hh : highCompatible b A z.2 <;>
    simp [hl, hh, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

lemma seenPrior_low_eventMass {b : ℕ} (hb : 0 < b) (A : Finset ℕ)
    (hA : 0 < (prior b).eventMass (fun z => A ⊆ support z))
    (M : (lowChoices b) → Prop) [DecidablePred M] :
    (seenPrior A hA).eventMass (fun z => M z.1) = (seenLowPrior hb A hA).eventMass M := by
  unfold FiniteLaw.eventMass
  simp_rw [seenPrior_mass_factor hb A hA]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro L _
  by_cases hM : M L
  · simp only [if_pos hM, ← Finset.mul_sum, (seenHighPrior hb A hA).total, mul_one]
  · simp [hM]

lemma lowSeen_subset_pool (b : ℕ) (A : Finset ℕ) : lowSeen b A ⊆ Finset.range (24 * b) := by
  intro d hd
  exact Finset.mem_range.mpr (Finset.mem_filter.mp hd).2

/-- The actual conditioned low prior has the exact hypergeometric marginal. -/
lemma seenLowPrior_membership {b : ℕ} (hb : 0 < b) (A : Finset ℕ)
    (hA : 0 < (prior b).eventMass (fun z => A ⊆ support z))
    (g : ℕ) (hg : g < 24 * b) (hgA : g ∉ A)
    (hsmall : (lowSeen b A).card < 12 * b) :
    (seenLowPrior hb A hA).eventMass (fun L => g ∈ L.val) =
      (((12 * b : ℕ) : ℝ) - (lowSeen b A).card) /
        (((24 * b : ℕ) : ℝ) - (lowSeen b A).card) := by
  have hnot : g ∉ lowSeen b A := by
    intro h
    exact hgA (Finset.mem_filter.mp h).1
  have h := uniform_subset_conditioned_membership (Finset.range (24 * b)) (lowSeen b A)
    (12 * b) g (lowSeen_subset_pool b A) hsmall (by simp; omega)
    (Finset.mem_range.mpr hg) hnot
  simpa [seenLowPrior, lowPrior, lowCompatible, lowChoices, lowPool] using h

/-- Full source F.9 under Pi_A, for membership in the sampled complete
support, with a low unseen candidate. The high-support conditioning is
retained and proved independent rather than discarded. -/
lemma seenPrior_membership {b : ℕ} (hb : 0 < b) (A : Finset ℕ)
    (hA : 0 < (prior b).eventMass (fun z => A ⊆ support z))
    (g : ℕ) (hg : g < 24 * b) (hgA : g ∉ A)
    (hsmall : (lowSeen b A).card < 12 * b) :
    (seenPrior A hA).eventMass (fun z => g ∈ support z) =
      (((12 * b : ℕ) : ℝ) - (lowSeen b A).card) /
        (((24 * b : ℕ) : ℝ) - (lowSeen b A).card) := by
  have hmember : ∀ z : Sample b, g ∈ support z ↔ g ∈ lowSupport z := by
    intro z
    constructor
    · intro hz
      rcases Finset.mem_union.mp hz with hl | hh
      · exact hl
      · have := (highSupport_bounds hb z hh).1
        omega
    · exact Finset.mem_union_left _
  rw [eventMass_congr (seenPrior A hA) _ _ hmember]
  change (seenPrior A hA).eventMass (fun z => g ∈ z.1.val) = _
  rw [seenPrior_low_eventMass hb A hA (fun L => g ∈ L.val)]
  exact seenLowPrior_membership hb A hA g hg hgA hsmall

/-- The source interval [11/23,1/2] follows for every good-event-sized seen set. -/
lemma seenPrior_membership_interval {b : ℕ} (hb : 0 < b) (A : Finset ℕ)
    (hA : 0 < (prior b).eventMass (fun z => A ⊆ support z))
    (g : ℕ) (hg : g < 24 * b) (hgA : g ∉ A)
    (hsmall : (lowSeen b A).card ≤ b) :
    11 / 23 ≤ (seenPrior A hA).eventMass (fun z => g ∈ support z) ∧
      (seenPrior A hA).eventMass (fun z => g ∈ support z) ≤ 1 / 2 := by
  rw [seenPrior_membership hb A hA g hg hgA (by omega)]
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hsmallR : ((lowSeen b A).card : ℝ) ≤ b := by exact_mod_cast hsmall
  have h := unseen_low_membership_interval (a := (24 : ℝ) * b)
    (ℓ := (lowSeen b A).card) (by positivity) (Nat.cast_nonneg _) (by linarith)
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  simpa only [show (24 : ℝ) * b / 2 = 12 * b by ring] using h

end
end Paper37.SupportPrior
