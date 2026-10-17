/-
Finite response tables, their simultaneous feasible mixture, and the
sampling comparison used in Proposition 4.1.
-/
import Paper06.ResponseTable
import Paper06.Sampling
import Paper06.Divergence
import Paper06.Posterior
import Paper06.SupportReduction
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators Classical

namespace Paper06.Response

variable {X A B : Type*} [Fintype X] [Fintype A] [Fintype B]

/-- The indicator of the response event for fixed rows and displayed pairs. -/
noncomputable def responseIndicator {M k : ℕ} (table : Fin M → X → A)
    (rows : Fin k → Fin M) (z : Fin k → X × A) : ℝ :=
  if ∀ i, table (rows i) (z i).1 = (z i).2 then 1 else 0

lemma responseIndicator_nonneg {M k : ℕ} (table : Fin M → X → A)
    (rows : Fin k → Fin M) (z : Fin k → X × A) :
    0 ≤ responseIndicator table rows z := by
  unfold responseIndicator
  split_ifs <;> norm_num

lemma responseIndicator_eq_prod {M k : ℕ} (table : Fin M → X → A)
    (rows : Fin k → Fin M) (z : Fin k → X × A) :
    responseIndicator table rows z =
      ∏ i, (if table (rows i) (z i).1 = (z i).2 then (1 : ℝ) else 0) := by
  classical
  by_cases h : ∀ i, table (rows i) (z i).1 = (z i).2
  · simp [responseIndicator, h]
  · obtain ⟨i, hi⟩ := not_forall.mp h
    rw [responseIndicator, if_neg h]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- A response experiment, written as a finite integral over the latent
outcome and the sampled row tuple.  The displayed inputs are iid `π`. -/
noncomputable def responseW (π : FinProb X) {M k : ℕ} (ν : FinProb B)
    (table : B → Fin M → X → A) (rows : FinProb (Fin k → Fin M))
    (z : Fin k → X × A) : ℝ :=
  ∑ b, ν.w b * ∑ r, rows.w r *
    (∏ i, π.w (z i).1) * responseIndicator (table b) r z

/-- Pointwise comparison of row samplers is preserved by the response
experiment.  This proof only uses nonnegative finite summation. -/
theorem responseW_le_mul (π : FinProb X) {M k : ℕ} (ν : FinProb B)
    (table : B → Fin M → X → A) (p q : FinProb (Fin k → Fin M))
    (C : ℝ) (hC : ∀ r, p.w r ≤ C * q.w r) (z : Fin k → X × A) :
    responseW π ν table p z ≤ C * responseW π ν table q z := by
  unfold responseW
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  have hin : (∑ r, p.w r * (∏ i, π.w (z i).1) *
        responseIndicator (table b) r z) ≤
      C * ∑ r, q.w r * (∏ i, π.w (z i).1) *
        responseIndicator (table b) r z := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r hr
    have hp : 0 ≤ ∏ i : Fin k, π.w (z i).1 :=
      Finset.prod_nonneg (fun i _ => π.nonneg (z i).1)
    have h := mul_le_mul_of_nonneg_right (hC r)
      (mul_nonneg hp
        (responseIndicator_nonneg (table b) r z))
    convert h using 1 <;> ring
  have h := mul_le_mul_of_nonneg_left hin (ν.nonneg b)
  convert h using 1 <;> ring

/-- The single mixing distribution: its latent law and its components are
constructed before choosing a sample size. -/
noncomputable def tableMixture (π : FinProb X) {M : ℕ} (hM : 0 < M)
    (ν : FinProb B) (table : B → Fin M → X → A) (k : ℕ) :
    FinProb (Fin k → X × A) :=
  mixtureProduct k ν.w ν.nonneg ν.sum_eq_one
    (fun b => tableLawFinProb π.w π.nonneg π.sum_eq_one M hM (table b))

/-- Every component of the common mixture has exactly the prescribed
input marginal. -/
theorem tableMixture_components_feasible (π : FinProb X) {M : ℕ} (hM : 0 < M)
    (table : B → Fin M → X → A) (b : B) (x : X) :
    ∑ a, (tableLawFinProb π.w π.nonneg π.sum_eq_one M hM (table b)).w (x,a)
      = π.w x :=
  tableLawFinProb_marginal π.w π.nonneg π.sum_eq_one M hM (table b) x

lemma table_product_expansion (π : FinProb X) {M k : ℕ} (hM : 0 < M)
    (table : Fin M → X → A) (z : Fin k → X × A) :
    (∏ i, tableLaw π.w M table (z i).1 (z i).2) =
      ∑ r : Fin k → Fin M,
        (1 / (M : ℝ)^k) * (∏ i, π.w (z i).1) * responseIndicator table r z := by
  classical
  unfold tableLaw
  simp_rw [mul_assoc]
  rw [Finset.prod_mul_distrib]
  have he : (∏ i : Fin k,
      ((1 / (M : ℝ)) * ∑ j : Fin M,
        if table j (z i).1 = (z i).2 then (1 : ℝ) else 0)) =
      (1 / (M : ℝ)^k) * ∑ r : Fin k → Fin M, responseIndicator table r z := by
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      one_div_pow]
    rw [Fintype.prod_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    exact (responseIndicator_eq_prod table r z).symm
  rw [he]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  ring

/-- Iid row sampling is precisely the product mixture, including all
collisions of row indices. -/
theorem responseW_iid_eq_tableMixture (π : FinProb X) {M k : ℕ} (hM : 0 < M)
    (ν : FinProb B) (table : B → Fin M → X → A)
    (iid : FinProb (Fin k → Fin M))
    (hiid : ∀ r, iid.w r = 1 / (M : ℝ)^k) (z : Fin k → X × A) :
    responseW π ν table iid z = (tableMixture π hM ν table k).w z := by
  unfold responseW tableMixture
  rw [mixtureProduct_w]
  apply Finset.sum_congr rfl
  intro b hb
  congr 1
  simp_rw [hiid]
  exact (table_product_expansion π hM (table b) z).symm

/-- A symmetric nonsignalling channel is specified by its finite output
marginals on every injection of physical coordinates.  This is the usual
nonsignalling equation together with permutation covariance. -/
def SymmetricNonsignalling {n : ℕ}
    (T : (Fin n → X) → FinProb (Fin n → A)) : Prop :=
  ∀ (k : ℕ) (f g : Fin k ↪ Fin n) (x y : Fin n → X),
    (∀ i, x (f i) = y (g i)) → ∀ a : Fin k → A,
      (∑ u, if (∀ i, u (f i) = a i) then (T x).w u else 0) =
      (∑ u, if (∀ i, u (g i) = a i) then (T y).w u else 0)

/-- A complete table is formed by sampling the channel once at an input
string that assigns every input to its designated site in each row. -/
def realizedTable {n M : ℕ} (ι : Fin M × X ↪ Fin n) (u : Fin n → A) :
    Fin M → X → A := fun j x => u (ι (j,x))

/-- Distinct row indices select distinct physical sites, even when the
observed input symbols coincide. -/
def selectedSites {n M k : ℕ} (ι : Fin M × X ↪ Fin n)
    (r : Fin k → Fin M) (hr : Function.Injective r) (x : Fin k → X) :
    Fin k ↪ Fin n where
  toFun i := ι (r i, x i)
  inj' := by
    intro i j h
    exact hr (congrArg Prod.fst (ι.injective h))

/-- The response event for the realized table is its physical output
cylinder event. -/
theorem realizedTable_responseIndicator {n M k : ℕ}
    (ι : Fin M × X ↪ Fin n) (r : Fin k → Fin M)
    (hr : Function.Injective r) (z : Fin k → X × A) (u : Fin n → A) :
    responseIndicator (realizedTable ι u) r z =
      if ∀ i, u (selectedSites ι r hr (fun i => (z i).1) i) = (z i).2
      then (1 : ℝ) else 0 := rfl

/-- Nonsignalling identifies every response marginal sampled from distinct
rows with the corresponding marginal at any fixed reference sites. -/
theorem distinct_response_cylinder {n M k : ℕ}
    (T : (Fin n → X) → FinProb (Fin n → A))
    (hT : SymmetricNonsignalling T) (ι : Fin M × X ↪ Fin n)
    (xbar : Fin n → X) (hxbar : ∀ j x, xbar (ι (j,x)) = x)
    (r : Fin k → Fin M) (hr : Function.Injective r)
    (g : Fin k ↪ Fin n) (y : Fin n → X)
    (z : Fin k → X × A) (hy : ∀ i, y (g i) = (z i).1) :
    (∑ u, (T xbar).w u * responseIndicator (realizedTable ι u) r z) =
      ∑ u, if ∀ i, u (g i) = (z i).2 then (T y).w u else 0 := by
  have hns := hT k (selectedSites ι r hr (fun i => (z i).1)) g xbar y
    (fun i => (hxbar (r i) (z i).1).trans (hy i).symm) (fun i => (z i).2)
  convert hns using 1
  apply Finset.sum_congr rfl
  intro u hu
  rw [realizedTable_responseIndicator ι r hr z u]
  split_ifs <;> simp

/-- The joint law obtained by drawing iid inputs and then the indicated
conditional output kernel. -/
noncomputable def channelLaw (π : FinProb X) (k : ℕ)
    (K : (Fin k → X) → FinProb (Fin k → A)) : FinProb (Fin k → X × A) :=
  mixture (productFinProb k π).w (productFinProb k π).nonneg
    (productFinProb k π).sum_eq_one
    (fun x => FinProb.map (K x) (fun a i => (x i, a i)))

lemma zip_eq_iff {k : ℕ} (x : Fin k → X) (a : Fin k → A)
    (z : Fin k → X × A) :
    (fun i => (x i, a i)) = z ↔
      x = (fun i => (z i).1) ∧ a = (fun i => (z i).2) := by
  constructor
  · intro h
    constructor <;> funext i
    · exact congrArg (fun f => (f i).1) h
    · exact congrArg (fun f => (f i).2) h
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp] theorem channelLaw_w (π : FinProb X) (k : ℕ)
    (K : (Fin k → X) → FinProb (Fin k → A)) (z : Fin k → X × A) :
    (channelLaw π k K).w z =
      (∏ i, π.w (z i).1) * (K (fun i => (z i).1)).w (fun i => (z i).2) := by
  classical
  unfold channelLaw
  rw [mixture_w]
  simp only [FinProb.map_w, zip_eq_iff]
  have hm (x : Fin k → X) :
      (∑ a : Fin k → A,
        if x = (fun i => (z i).1) ∧ a = (fun i => (z i).2)
        then (K x).w a else 0) =
      if x = (fun i => (z i).1) then (K x).w (fun i => (z i).2) else 0 := by
    by_cases hx : x = (fun i => (z i).1) <;> simp [hx]
  simp_rw [hm]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  simp [productFinProb_w]

/-- The reference `k`-site law represented by the conditional channel. -/
noncomputable def referenceLaw (π : FinProb X) {n k : ℕ}
    (T : (Fin n → X) → FinProb (Fin n → A)) (g : Fin k ↪ Fin n)
    (y : (Fin k → X) → (Fin n → X)) : FinProb (Fin k → X × A) :=
  channelLaw π k (fun x => FinProb.map (T (y x)) (fun u i => u (g i)))

/-- Sampling distinct complete rows recovers the reference marginal. -/
theorem responseW_distinct_eq_reference (π : FinProb X) {n M k : ℕ}
    (T : (Fin n → X) → FinProb (Fin n → A))
    (hT : SymmetricNonsignalling T) (ι : Fin M × X ↪ Fin n)
    (xbar : Fin n → X) (hxbar : ∀ j x, xbar (ι (j,x)) = x)
    (rows : FinProb (Fin k → Fin M))
    (hrows : ∀ r, rows.w r ≠ 0 → Function.Injective r)
    (g : Fin k ↪ Fin n) (y : (Fin k → X) → (Fin n → X))
    (hy : ∀ x i, y x (g i) = x i) (z : Fin k → X × A) :
    responseW π (T xbar) (realizedTable ι) rows z =
      (referenceLaw π T g y).w z := by
  classical
  unfold responseW
  have hs : (∑ b, (T xbar).w b * ∑ r, rows.w r *
      (∏ i, π.w (z i).1) * responseIndicator (realizedTable ι b) r z) =
      (∏ i, π.w (z i).1) * ∑ r, rows.w r *
        ∑ b, (T xbar).w b * responseIndicator (realizedTable ι b) r z := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro b hb
    ring
  rw [hs]
  unfold referenceLaw
  rw [channelLaw_w]
  congr 1
  have hc (r : Fin k → Fin M) : rows.w r *
      (∑ b, (T xbar).w b * responseIndicator (realizedTable ι b) r z) =
      rows.w r * (FinProb.map (T (y (fun i => (z i).1)))
        (fun u i => u (g i))).w (fun i => (z i).2) := by
    by_cases hr : rows.w r = 0
    · simp [hr]
    · rw [distinct_response_cylinder T hT ι xbar hxbar r (hrows r hr)
        g (y (fun i => (z i).1)) z (hy (fun i => (z i).1))]
      congr 1
      simp only [FinProb.map_w, funext_iff]
  simp_rw [hc]
  rw [← Finset.sum_mul, rows.sum_eq_one, one_mul]

/-- The without-replacement response density is pointwise dominated by
its iid-row mixture with the exact likelihood-ratio constant. -/
theorem response_table_domination (π : FinProb X) {n M k : ℕ} (hM : 0 < M)
    (hkM : k ≤ M)
    (T : (Fin n → X) → FinProb (Fin n → A))
    (hT : SymmetricNonsignalling T) (ι : Fin M × X ↪ Fin n)
    (xbar : Fin n → X) (hxbar : ∀ j x, xbar (ι (j,x)) = x)
    (g : Fin k ↪ Fin n) (y : (Fin k → X) → (Fin n → X))
    (hy : ∀ x i, y x (g i) = x i) (z : Fin k → X × A) :
    (referenceLaw π T g y).w z ≤ Sampling.densityRatio M k *
      (tableMixture π hM (T xbar) (realizedTable ι) k).w z := by
  rw [← responseW_iid_eq_tableMixture π hM (T xbar) (realizedTable ι)
    (Sampling.iidLaw M k hM) (Sampling.iidLaw_w M k hM)]
  rw [← responseW_distinct_eq_reference π T hT ι xbar hxbar
    (Sampling.distinctLaw M k hkM) ?_ g y hy z]
  · exact responseW_le_mul π (T xbar) (realizedTable ι)
      (Sampling.distinctLaw M k hkM) (Sampling.iidLaw M k hM)
      (Sampling.densityRatio M k) (Sampling.distinct_le_densityRatio_mul_iid M k hM hkM) z
  · intro r hr
    by_contra hn
    exact hr (by simp [Sampling.distinctLaw_w, hn])

/-- The response-table comparison for a fixed symmetric nonsignalling
channel.  The common components and latent law do not depend on `k`. -/
theorem response_table_KL (π : FinProb X) {n M k : ℕ} (hM : 0 < M)
    (hkM : k ≤ M)
    (T : (Fin n → X) → FinProb (Fin n → A))
    (hT : SymmetricNonsignalling T) (ι : Fin M × X ↪ Fin n)
    (xbar : Fin n → X) (hxbar : ∀ j x, xbar (ι (j,x)) = x)
    (g : Fin k ↪ Fin n) (y : (Fin k → X) → (Fin n → X))
    (hy : ∀ x i, y x (g i) = x i) :
    FinProb.klPos (referenceLaw π T g y)
      (tableMixture π hM (T xbar) (realizedTable ι) k) ≤ Sampling.cost M k := by
  apply Sampling.klPos_le_log_of_domination _ _ (Sampling.densityRatio M k)
    (Sampling.densityRatio_pos M k hM hkM)
  intro z
  rw [← responseW_iid_eq_tableMixture π hM (T xbar) (realizedTable ι)
    (Sampling.iidLaw M k hM) (Sampling.iidLaw_w M k hM)]
  rw [← responseW_distinct_eq_reference π T hT ι xbar hxbar
    (Sampling.distinctLaw M k hkM) ?_ g y hy z]
  · exact responseW_le_mul π (T xbar) (realizedTable ι)
      (Sampling.distinctLaw M k hkM) (Sampling.iidLaw M k hM)
      (Sampling.densityRatio M k) (Sampling.distinct_le_densityRatio_mul_iid M k hM hkM) z
  · intro r hr
    by_contra hn
    exact hr (by simp [Sampling.distinctLaw_w, hn])

/-! The conditional nonsignalling channel forced by the lifted constraint. -/

/-- The linear input-marginal map. -/
noncomputable def inputΓ : ((X × A) → ℝ) →ₗ[ℝ] (X → ℝ) where
  toFun w x := ∑ a, if a.1 = x then w a else 0
  map_add' w v := by
    funext x
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    split_ifs <;> simp
  map_smul' c w := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    split_ifs <;> simp

/-- Fixed-input lifted constraint, with all coordinate marginals computed
from the original joint law. -/
def FixedInputCP {κ : Type*} [Fintype κ] [DecidableEq κ]
    (π : FinProb X) (P : FinProb (κ → X × A)) : Prop :=
  ∀ i z x, (∑ a : X × A, if a.1 = x then P.w (Function.update z i a) else 0) =
    π.w x * ∑ a, P.w (Function.update z i a)

theorem fixedInputCP_of_exchangeable {κ : Type*} [Fintype κ] [DecidableEq κ]
    (π : FinProb X) (P : FinProb (κ → X × A))
    (hP : Posterior.Exchangeable P) (c : κ)
    (hCP : Posterior.LiftedCP inputΓ π.w P c) : FixedInputCP π P := by
  intro i z x
  have h := congrFun
    (Posterior.liftedCP_at_every_coordinate inputΓ π.w P hP c hCP i z) x
  simpa [inputΓ, smul_eq_mul, mul_comm] using h

/-- Repeatedly summing the lifted constraint factors all unobserved input
pins out of any event that does not inspect those coordinates. -/
theorem event_input_pins {κ : Type*} [Fintype κ] [DecidableEq κ]
    (π : FinProb X) (P : FinProb (κ → X × A)) (hCP : FixedInputCP π P)
    (E : (κ → X × A) → Prop) (J : Finset κ)
    (hE : ∀ i ∈ J, ∀ z a, E (Function.update z i a) ↔ E z)
    (x : κ → X) :
    Posterior.eventMass P (fun z => E z ∧ ∀ j ∈ J, (z j).1 = x j) =
      Posterior.eventMass P E * ∏ j ∈ J, π.w (x j) := by
  classical
  induction J using Finset.induction_on with
  | empty => simp [Posterior.eventMass]
  | @insert i J hi ih =>
    have hEi : ∀ z a, (E (Function.update z i a) ∧
        ∀ j ∈ J, ((Function.update z i a) j).1 = x j) ↔
        (E z ∧ ∀ j ∈ J, (z j).1 = x j) := by
      intro z a
      rw [hE i (Finset.mem_insert_self i J)]
      apply and_congr_right
      intro _
      apply forall_congr'
      intro j
      by_cases hj : j ∈ J
      · have hji : j ≠ i := by intro hh; subst j; exact hi hj
        simp [Function.update_of_ne hji]
      · simp [hj]
    have h := Posterior.event_input_independent P i Prod.fst π.w
      (hCP i) (fun z => E z ∧ ∀ j ∈ J, (z j).1 = x j) hEi (x i)
    have he : (fun z => E z ∧ ∀ j ∈ insert i J, (z j).1 = x j) =
        (fun z => (E z ∧ ∀ j ∈ J, (z j).1 = x j) ∧ (z i).1 = x i) := by
      funext z
      simp only [Finset.mem_insert, forall_eq_or_imp]
      exact propext (by tauto)
    rw [he, show Posterior.eventMass P
        (fun z => (E z ∧ ∀ j ∈ J, (z j).1 = x j) ∧ (z i).1 = x i) =
        π.w (x i) * Posterior.eventMass P
          (fun z => E z ∧ ∀ j ∈ J, (z j).1 = x j) from by
          convert h using 1
          unfold Posterior.eventMass
          apply Finset.sum_congr rfl
          intro z hz
          split_ifs <;> rfl]
    rw [ih (fun j hj => hE j (Finset.mem_insert_of_mem hj)), Finset.prod_insert hi]
    ring

/-- The input string has exactly the iid law forced by (CP). -/
theorem input_string_mass {κ : Type*} [Fintype κ] [DecidableEq κ]
    (π : FinProb X) (P : FinProb (κ → X × A)) (hCP : FixedInputCP π P)
    (x : κ → X) :
    Posterior.eventMass P (fun z => ∀ j, (z j).1 = x j) = ∏ j, π.w (x j) := by
  classical
  have h := event_input_pins π P hCP (fun _ => True) Finset.univ
    (by simp) x
  have hh : Posterior.eventMass P (fun z => ∀ j, (z j).1 = x j) =
      Posterior.eventMass P (fun z => True ∧ ∀ j ∈ Finset.univ, (z j).1 = x j) := by
    unfold Posterior.eventMass
    apply Finset.sum_congr rfl
    intro z hz
    simp
  rw [hh, h]
  simp [Posterior.eventMass, P.sum_eq_one]

/-- Finite disintegration along an input string, before normalization. -/
theorem input_section_sum {κ : Type*} [Fintype κ] [DecidableEq κ]
    (P : FinProb (κ → X × A)) (x : κ → X) (E : (κ → A) → Prop) :
    (∑ a, if E a then P.w (fun i => (x i, a i)) else 0) =
      Posterior.eventMass P (fun z => (∀ j, (z j).1 = x j) ∧ E (fun j => (z j).2)) := by
  classical
  unfold Posterior.eventMass
  rw [← (Equiv.arrowProdEquivProdArrow κ (fun _ => X) (fun _ => A)).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [Equiv.arrowProdEquivProdArrow_symm_apply]
  simp_rw [← funext_iff]
  rw [Finset.sum_eq_single x]
  · apply Finset.sum_congr rfl
    intro a ha
    simp [Equiv.arrowProdEquivProdArrow]
  · intro b hb hbx
    apply Finset.sum_eq_zero
    intro a ha
    simp [hbx]
  · simp

/-- Conditioning the original law on its complete positive-mass input
string.  Its normalization is proved from (CP), rather than assumed. -/
noncomputable def conditionalChannel {κ : Type*} [Fintype κ] [DecidableEq κ]
    (π : FinProb X) (hπ : ∀ x, 0 < π.w x) (P : FinProb (κ → X × A))
    (hCP : FixedInputCP π P) (x : κ → X) : FinProb (κ → A) where
  w a := P.w (fun i => (x i, a i)) / ∏ i, π.w (x i)
  nonneg a := div_nonneg (P.nonneg _) (Finset.prod_nonneg (fun i _ => le_of_lt (hπ _)))
  sum_eq_one := by
    rw [← Finset.sum_div]
    have h := input_section_sum (X := X) (A := A) P x (fun _ => True)
    simp at h
    rw [h, input_string_mass π P hCP x]
    exact div_self (ne_of_gt (Finset.prod_pos (fun i _ => hπ _)))

/-- Physical coordinates selected by an injective observation map. -/
noncomputable def selectedSet {κ J : Type*} [Fintype κ] [DecidableEq κ] [Fintype J]
    (f : J ↪ κ) : Finset κ := Finset.univ.image f

lemma mem_selectedSet {κ J : Type*} [Fintype κ] [DecidableEq κ] [Fintype J]
    (f : J ↪ κ) (j : κ) : j ∈ selectedSet f ↔ ∃ i, f i = j := by
  classical
  simp [selectedSet]

/-- Joint input/output cylinders factor out precisely the unobserved
inputs. -/
theorem selected_section_mass {κ J : Type*} [Fintype κ] [DecidableEq κ] [Fintype J]
    (π : FinProb X) (P : FinProb (κ → X × A)) (hCP : FixedInputCP π P)
    (f : J ↪ κ) (x : κ → X) (a : J → A) :
    Posterior.eventMass P (fun z =>
      (∀ j, (z j).1 = x j) ∧ ∀ i, (z (f i)).2 = a i) =
    Posterior.eventMass P (fun z => ∀ i, z (f i) = (x (f i), a i)) *
      ∏ j ∈ (selectedSet f)ᶜ, π.w (x j) := by
  classical
  let E : (κ → X × A) → Prop := fun z => ∀ i, z (f i) = (x (f i), a i)
  have hE : ∀ j ∈ (selectedSet f)ᶜ, ∀ z b,
      E (Function.update z j b) ↔ E z := by
    intro j hj z b
    apply forall_congr'
    intro i
    have hne : f i ≠ j := by
      intro heq
      exact (Finset.mem_compl.mp hj) ((mem_selectedSet f j).mpr ⟨i, heq⟩)
    simp only [Function.update_of_ne hne]
  have he : (fun z => (∀ j, (z j).1 = x j) ∧ ∀ i, (z (f i)).2 = a i) =
      (fun z => E z ∧ ∀ j ∈ (selectedSet f)ᶜ, (z j).1 = x j) := by
    funext z
    apply propext
    constructor
    · rintro ⟨hx, ha⟩
      exact ⟨fun i => Prod.ext (hx (f i)) (ha i), fun j hj => hx j⟩
    · rintro ⟨hz, hp⟩
      constructor
      · intro j
        by_cases hj : j ∈ selectedSet f
        · obtain ⟨i, rfl⟩ := (mem_selectedSet f j).mp hj
          exact congrArg Prod.fst (hz i)
        · exact hp j (Finset.mem_compl.mpr hj)
      · intro i
        exact congrArg Prod.snd (hz i)
  rw [he]
  exact event_input_pins π P hCP E (selectedSet f)ᶜ hE x

/-- Complete input weights split into selected and unselected factors. -/
lemma input_weight_split {κ J : Type*} [Fintype κ] [DecidableEq κ] [Fintype J]
    (π : FinProb X) (f : J ↪ κ) (x : κ → X) :
    (∏ j ∈ (selectedSet f)ᶜ, π.w (x j)) * (∏ i, π.w (x (f i))) =
      ∏ j, π.w (x j) := by
  classical
  have h := Finset.prod_compl_mul_prod (selectedSet f) (fun j => π.w (x j))
  have he : (∏ j ∈ selectedSet f, π.w (x j)) = ∏ i, π.w (x (f i)) := by
    unfold selectedSet
    rw [Finset.prod_image]
    intro i hi j hj hij
    exact f.injective hij
  rwa [he] at h

/-- Conditional output marginals depend only on selected inputs; the
unselected positive input masses cancel exactly. -/
theorem conditionalChannel_selected_mass {κ J : Type*}
    [Fintype κ] [DecidableEq κ] [Fintype J]
    (π : FinProb X) (hπ : ∀ x, 0 < π.w x)
    (P : FinProb (κ → X × A)) (hCP : FixedInputCP π P)
    (f : J ↪ κ) (x : κ → X) (a : J → A) :
    (∑ u, if ∀ i, u (f i) = a i then (conditionalChannel π hπ P hCP x).w u else 0) =
      Posterior.eventMass P (fun z => ∀ i, z (f i) = (x (f i), a i)) /
        ∏ i, π.w (x (f i)) := by
  classical
  have hm : (∑ u, if ∀ i, u (f i) = a i then
      (conditionalChannel π hπ P hCP x).w u else 0) =
      (∑ u : κ → A, if ∀ i, u (f i) = a i then P.w (fun i => (x i, u i)) else 0) /
        ∏ i, π.w (x i) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro u hu
    split_ifs <;> simp [conditionalChannel]
  have hsection := input_section_sum P x (fun u => ∀ i, u (f i) = a i)
  have hsection' : (∑ u : κ → A, if ∀ i, u (f i) = a i then
      P.w (fun i => (x i, u i)) else 0) =
      Posterior.eventMass P (fun z => (∀ j, (z j).1 = x j) ∧
        ∀ i, (z (f i)).2 = a i) := by
    convert hsection using 1
    apply Finset.sum_congr rfl
    intro u hu
    split_ifs <;> rfl
  rw [hm, hsection', selected_section_mass π P hCP f x a,
    ← input_weight_split π f x]
  have hr : (∏ j ∈ (selectedSet f)ᶜ, π.w (x j)) ≠ 0 :=
    ne_of_gt (Finset.prod_pos (fun j hj => hπ _))
  have hs : (∏ i, π.w (x (f i))) ≠ 0 :=
    ne_of_gt (Finset.prod_pos (fun i hi => hπ _))
  field_simp

/-- The lifted fixed-input constraint and exchangeability produce a
symmetric nonsignalling conditional channel. -/
theorem conditionalChannel_nonsignalling {n : ℕ}
    (π : FinProb X) (hπ : ∀ x, 0 < π.w x)
    (P : FinProb (Fin n → X × A)) (hP : Posterior.Exchangeable P)
    (hCP : FixedInputCP π P) :
    SymmetricNonsignalling (conditionalChannel π hπ P hCP) := by
  classical
  intro k f g x y hxy a
  have hf := conditionalChannel_selected_mass π hπ P hCP f x a
  have hg := conditionalChannel_selected_mass π hπ P hCP g y a
  have hf' : (∑ u, if ∀ i, u (f i) = a i then
      (conditionalChannel π hπ P hCP x).w u else 0) =
      Posterior.eventMass P (fun z => ∀ i, z (f i) = (x (f i), a i)) /
        ∏ i, π.w (x (f i)) := by
    convert hf using 1
    apply Finset.sum_congr rfl
    intro u hu
    split_ifs <;> rfl
  have hg' : (∑ u, if ∀ i, u (g i) = a i then
      (conditionalChannel π hπ P hCP y).w u else 0) =
      Posterior.eventMass P (fun z => ∀ i, z (g i) = (y (g i), a i)) /
        ∏ i, π.w (y (g i)) := by
    convert hg using 1
    apply Finset.sum_congr rfl
    intro u hu
    split_ifs <;> rfl
  calc
    _ = _ := hf'
    _ = _ := ?_
    _ = _ := hg'.symm
  have he : Posterior.eventMass P (fun z => ∀ i, z (f i) = (x (f i), a i)) =
      Posterior.eventMass P (fun z => ∀ i, z (g i) = (y (g i), a i)) := by
    have h := Posterior.selected_mass_eq P hP f g f.injective g.injective
      (fun i => (x (f i), a i))
    unfold Posterior.eventMass
    convert h using 1 <;> apply Finset.sum_congr rfl <;> intro u hu <;>
      split_ifs <;> simp_all only [funext_iff, hxy, not_true_eq_false]
  rw [he]
  congr 1
  exact Finset.prod_congr rfl (fun i hi => congrArg π.w (hxy i))

/-- The conditional-channel reference law is the actual marginal of the
original joint law. -/
theorem referenceLaw_eq_marginal (π : FinProb X) (hπ : ∀ x, 0 < π.w x)
    {n k : ℕ} (P : FinProb (Fin n → X × A)) (hCP : FixedInputCP π P)
    (g : Fin k ↪ Fin n) (y : (Fin k → X) → (Fin n → X))
    (hy : ∀ x i, y x (g i) = x i) :
    referenceLaw π (conditionalChannel π hπ P hCP) g y =
      FinProb.map P (fun z i => z (g i)) := by
  apply FinProb.ext
  intro z
  unfold referenceLaw
  rw [channelLaw_w, FinProb.map_w]
  simp only [funext_iff]
  have hm := conditionalChannel_selected_mass π hπ P hCP g
    (y (fun i => (z i).1)) (fun i => (z i).2)
  have hm' : (∑ u, if ∀ i, u (g i) = (z i).2 then
      (conditionalChannel π hπ P hCP (y (fun i => (z i).1))).w u else 0) =
      Posterior.eventMass P (fun u => ∀ i,
        u (g i) = (y (fun i => (z i).1) (g i), (z i).2)) /
        ∏ i, π.w (y (fun i => (z i).1) (g i)) := by
    convert hm using 1
    apply Finset.sum_congr rfl
    intro u hu
    split_ifs <;> rfl
  rw [hm']
  simp only [hy]
  have hd : (∏ i : Fin k, π.w (z i).1) ≠ 0 :=
    ne_of_gt (Finset.prod_pos (fun i hi => hπ _))
  rw [mul_div_cancel₀ _ hd]
  unfold Posterior.eventMass
  apply Finset.sum_congr rfl
  intro u hu
  congr 1
  apply propext
  simp only [Prod.mk.eta, funext_iff]

/-- **Proposition 4.1 for positive input laws.**  The latent distribution
and all feasible one-site factors are chosen once; every admissible `k`
uses those same factors.  The relative entropy is support-safe `EReal` KL. -/
theorem prop_4_1_positive (π : FinProb X) (hπ : ∀ x, 0 < π.w x)
    (n : ℕ) (P : FinProb (Fin n → X × A)) (hP : Posterior.Exchangeable P)
    (hCP : FixedInputCP π P) (hn : Fintype.card X ≤ n) :
    ∃ (ν : FinProb (Fin n → A)) (q : (Fin n → A) → FinProb (X × A)),
      (∀ u x, ∑ a, (q u).w (x,a) = π.w x) ∧
      ∀ k, 1 ≤ k → (hk : k ≤ n / Fintype.card X) →
        let Pk := FinProb.map P (fun z i => z (SupportReduction.floorReferenceSites hk i))
        let Qk := mixtureProduct k ν.w ν.nonneg ν.sum_eq_one q
        FinProb.Supports Pk Qk ∧
        FinProb.kl Pk Qk ≤ (Sampling.cost (n / Fintype.card X) k : EReal) ∧
        Sampling.cost (n / Fintype.card X) k ≤
          (k * (k - 1) : ℝ) / (2 * (((n / Fintype.card X : ℕ) : ℝ) - k + 1)) := by
  classical
  haveI : Nonempty X := ⟨(Classical.choice (SupportReduction.inputSupport_nonempty π)).val⟩
  let M := n / Fintype.card X
  have hM : 0 < M := SupportReduction.floor_rows_pos n (Fintype.card X)
    Fintype.card_pos hn
  let ι : Fin M × X ↪ Fin n := SupportReduction.floorRowsEmbedding X n
  let xbar : Fin n → X := SupportReduction.prescribedInputs ι
  have hxbar : ∀ j x, xbar (ι (j,x)) = x := SupportReduction.prescribedInputs_at ι
  let T := conditionalChannel π hπ P hCP
  have hT : SymmetricNonsignalling T := conditionalChannel_nonsignalling π hπ P hP hCP
  let ν := T xbar
  let q : (Fin n → A) → FinProb (X × A) :=
    fun u => tableLawFinProb π.w π.nonneg π.sum_eq_one M hM (realizedTable ι u)
  refine ⟨ν, q, ?_, ?_⟩
  · intro u x
    exact tableLawFinProb_marginal π.w π.nonneg π.sum_eq_one M hM (realizedTable ι u) x
  · intro k hk hkM
    let g : Fin k ↪ Fin n := SupportReduction.floorReferenceSites hkM
    let y : (Fin k → X) → Fin n → X := SupportReduction.referenceInputs g
    have hy : ∀ x i, y x (g i) = x i := SupportReduction.referenceInputs_at g
    have hdom := response_table_domination π hM hkM T hT ι xbar hxbar g y hy
    have href := referenceLaw_eq_marginal π hπ P hCP g y hy
    rw [href] at hdom
    have hsupp := Sampling.supports_of_domination _ _ (Sampling.densityRatio M k) hdom
    have hkl := Sampling.klPos_le_log_of_domination _ _ (Sampling.densityRatio M k)
      (Sampling.densityRatio_pos M k hM hkM) hdom
    refine ⟨hsupp, ?_, Sampling.cost_le M k hk hkM⟩
    change FinProb.kl (FinProb.map P (fun z i => z (g i)))
      (tableMixture π hM (T xbar) (realizedTable ι) k) ≤ (Sampling.cost M k : EReal)
    rw [FinProb.kl_of_support hsupp]
    exact EReal.coe_le_coe hkl

/-- **Proposition 4.1, with zero-mass inputs included.**  The row count is
`floor(n / |supp π|)`, and the lifted constraint is assumed at only one
site.  Exchangeability, support restriction, and data processing supply
the simultaneous feasible mixture on the original alphabet. -/
theorem prop_4_1_fixed_input (π : FinProb X) (n : ℕ)
    (P : FinProb (Fin n → X × A)) (hP : Posterior.Exchangeable P)
    (c : Fin n) (hCP : Posterior.LiftedCP inputΓ π.w P c)
    (hn : Fintype.card (SupportReduction.InputSupport π) ≤ n) :
    ∃ (ν : FinProb (Fin n → A)) (q : (Fin n → A) → FinProb (X × A)),
      (∀ u x, ∑ a, (q u).w (x,a) = π.w x) ∧
      ∀ k, 1 ≤ k → (hk : k ≤ n / Fintype.card (SupportReduction.InputSupport π)) →
        let g := SupportReduction.floorReferenceSites
          (X := SupportReduction.InputSupport π) hk
        let Pk := FinProb.map P (fun z i => z (g i))
        let Qk := mixtureProduct k ν.w ν.nonneg ν.sum_eq_one q
        FinProb.Supports Pk Qk ∧
        FinProb.kl Pk Qk ≤
          (Sampling.cost (n / Fintype.card (SupportReduction.InputSupport π)) k : EReal) ∧
        Sampling.cost (n / Fintype.card (SupportReduction.InputSupport π)) k ≤
          (k * (k - 1) : ℝ) /
            (2 * (((n / Fintype.card (SupportReduction.InputSupport π) : ℕ) : ℝ) - k + 1)) := by
  classical
  have hCPall : FixedInputCP π P := fixedInputCP_of_exchangeable π P hP c hCP
  let Ps := SupportReduction.reducedLaw π P hCPall
  have hPs : Posterior.Exchangeable Ps :=
    SupportReduction.reducedLaw_exchangeable π P hCPall hP
  have hCPs : FixedInputCP (SupportReduction.supportLaw π) Ps :=
    SupportReduction.reducedLaw_inputCP π P hCPall
  obtain ⟨ν, q, hq, hbound⟩ := prop_4_1_positive (SupportReduction.supportLaw π)
    (SupportReduction.supportLaw_positive π) n Ps hPs hCPs hn
  refine ⟨ν, (fun u => SupportReduction.liftLaw π (q u)), ?_, ?_⟩
  · intro u
    exact SupportReduction.liftLaw_feasible π (q u) (hq u)
  · intro k hk hkM
    let g := SupportReduction.floorReferenceSites
      (X := SupportReduction.InputSupport π) hkM
    obtain ⟨hsupp, hkl, hcost⟩ := hbound k hk hkM
    have hmap := FinProb.kl_map_le (FinProb.map Ps (fun z i => z (g i)))
      (mixtureProduct k ν.w ν.nonneg ν.sum_eq_one q) (SupportReduction.includeInputs π)
    have hsupport := FinProb.supports_map hsupp (SupportReduction.includeInputs π)
    rw [SupportReduction.map_reduced_marginal π P hCPall g,
      SupportReduction.map_lifted_mixtureProduct π k ν q] at hmap hsupport
    exact ⟨hsupport, hmap.trans hkl, hcost⟩

/-- Complete a possibly invalid zero-probability table entry using a
chosen valid response.  Positive-probability entries remain unchanged. -/
noncomputable def repairTable (R : X → A → Prop) (a₀ : X → A)
    {M : ℕ} (table : Fin M → X → A) : Fin M → X → A :=
  fun j x => if R x (table j x) then table j x else a₀ x

lemma repairTable_valid (R : X → A → Prop) (a₀ : X → A)
    (ha₀ : ∀ x, R x (a₀ x)) {M : ℕ} (table : Fin M → X → A) (j : Fin M) (x : X) :
    R x (repairTable R a₀ table j x) := by
  unfold repairTable
  split_ifs with h
  · exact h
  · exact ha₀ x

lemma tableLaw_zero_of_relation (π : FinProb X) {M : ℕ} (hM : 0 < M)
    (R : X → A → Prop) (table : Fin M → X → A)
    (htable : ∀ j x, R x (table j x)) (x : X) (a : A) (ha : ¬ R x a) :
    (tableLawFinProb π.w π.nonneg π.sum_eq_one M hM table).w (x,a) = 0 := by
  change tableLaw π.w M table x a = 0
  unfold tableLaw
  have hs : (∑ j : Fin M, if table j x = a then (1 : ℝ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hne : table j x ≠ a := by
      intro heq
      exact ha (heq ▸ htable j x)
    simp [hne]
  rw [hs, mul_zero]

lemma mixtureProduct_eq_of_ae (ν : FinProb B) (q r : B → FinProb (X × A))
    (h : ∀ b, ν.w b ≠ 0 → q b = r b) (k : ℕ) :
    mixtureProduct k ν.w ν.nonneg ν.sum_eq_one q =
      mixtureProduct k ν.w ν.nonneg ν.sum_eq_one r := by
  apply FinProb.ext
  intro z
  simp only [mixtureProduct_w]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hν : ν.w b = 0
  · simp [hν]
  · rw [h b hν]

/-- The response construction preserves any required input-dependent
output alphabet.  Invalid table entries can occur only under zero latent
mass, and are completed with the chosen valid response. -/
theorem prop_4_1_positive_relation (π : FinProb X) (hπ : ∀ x, 0 < π.w x)
    (R : X → A → Prop) (a₀ : X → A) (ha₀ : ∀ x, R x (a₀ x))
    (n : ℕ) (P : FinProb (Fin n → X × A)) (hP : Posterior.Exchangeable P)
    (hCP : FixedInputCP π P) (hn : Fintype.card X ≤ n)
    (hR : ∀ z, P.w z ≠ 0 → ∀ i, R (z i).1 (z i).2) :
    ∃ (ν : FinProb (Fin n → A)) (q : (Fin n → A) → FinProb (X × A)),
      (∀ u x, ∑ a, (q u).w (x,a) = π.w x) ∧
      (∀ u x a, ¬ R x a → (q u).w (x,a) = 0) ∧
      ∀ k, 1 ≤ k → (hk : k ≤ n / Fintype.card X) →
        let Pk := FinProb.map P (fun z i => z (SupportReduction.floorReferenceSites hk i))
        let Qk := mixtureProduct k ν.w ν.nonneg ν.sum_eq_one q
        FinProb.Supports Pk Qk ∧
        FinProb.kl Pk Qk ≤ (Sampling.cost (n / Fintype.card X) k : EReal) ∧
        Sampling.cost (n / Fintype.card X) k ≤
          (k * (k - 1) : ℝ) / (2 * (((n / Fintype.card X : ℕ) : ℝ) - k + 1)) := by
  classical
  haveI : Nonempty X := ⟨(Classical.choice (SupportReduction.inputSupport_nonempty π)).val⟩
  let M := n / Fintype.card X
  have hM : 0 < M := SupportReduction.floor_rows_pos n (Fintype.card X)
    Fintype.card_pos hn
  let ι : Fin M × X ↪ Fin n := SupportReduction.floorRowsEmbedding X n
  let xbar : Fin n → X := SupportReduction.prescribedInputs ι
  have hxbar : ∀ j x, xbar (ι (j,x)) = x := SupportReduction.prescribedInputs_at ι
  let T := conditionalChannel π hπ P hCP
  have hT : SymmetricNonsignalling T := conditionalChannel_nonsignalling π hπ P hP hCP
  let ν := T xbar
  let qraw : (Fin n → A) → FinProb (X × A) :=
    fun u => tableLawFinProb π.w π.nonneg π.sum_eq_one M hM (realizedTable ι u)
  let q : (Fin n → A) → FinProb (X × A) := fun u =>
    tableLawFinProb π.w π.nonneg π.sum_eq_one M hM
      (repairTable R a₀ (realizedTable ι u))
  have hqae : ∀ u, ν.w u ≠ 0 → q u = qraw u := by
    intro u hu
    have hp : P.w (fun i => (xbar i, u i)) ≠ 0 := by
      intro hp
      exact hu (by simp [ν, T, conditionalChannel, hp])
    have ht : repairTable R a₀ (realizedTable ι u) = realizedTable ι u := by
      funext j x
      have hr := hR (fun i => (xbar i, u i)) hp (ι (j,x))
      have hr' : R x (realizedTable ι u j x) := by
        simpa only [hxbar, realizedTable] using hr
      simp only [repairTable, if_pos hr']
    exact congrArg (fun t => tableLawFinProb π.w π.nonneg π.sum_eq_one M hM t) ht
  refine ⟨ν, q, ?_, ?_, ?_⟩
  · intro u x
    exact tableLawFinProb_marginal π.w π.nonneg π.sum_eq_one M hM _ x
  · intro u x a ha
    exact tableLaw_zero_of_relation π hM R _ (repairTable_valid R a₀ ha₀ _) x a ha
  · intro k hk hkM
    let g : Fin k ↪ Fin n := SupportReduction.floorReferenceSites hkM
    let y : (Fin k → X) → Fin n → X := SupportReduction.referenceInputs g
    have hy : ∀ x i, y x (g i) = x i := SupportReduction.referenceInputs_at g
    have hdom := response_table_domination π hM hkM T hT ι xbar hxbar g y hy
    have href := referenceLaw_eq_marginal π hπ P hCP g y hy
    rw [href] at hdom
    have hmix : mixtureProduct k ν.w ν.nonneg ν.sum_eq_one q =
        tableMixture π hM (T xbar) (realizedTable ι) k :=
      mixtureProduct_eq_of_ae ν q qraw hqae k
    rw [← hmix] at hdom
    have hsupp := Sampling.supports_of_domination _ _ (Sampling.densityRatio M k) hdom
    have hkl := Sampling.klPos_le_log_of_domination _ _ (Sampling.densityRatio M k)
      (Sampling.densityRatio_pos M k hM hkM) hdom
    refine ⟨hsupp, ?_, Sampling.cost_le M k hk hkM⟩
    change FinProb.kl (FinProb.map P (fun z i => z (g i)))
      (mixtureProduct k ν.w ν.nonneg ν.sum_eq_one q) ≤ (Sampling.cost M k : EReal)
    rw [FinProb.kl_of_support hsupp]
    exact EReal.coe_le_coe hkl

/-- The common mixture also preserves input-dependent output validity
when the input law has zero entries. -/
theorem prop_4_1_relation (π : FinProb X)
    (R : X → A → Prop) (a₀ : X → A) (ha₀ : ∀ x, R x (a₀ x))
    (n : ℕ) (P : FinProb (Fin n → X × A)) (hP : Posterior.Exchangeable P)
    (hCP : FixedInputCP π P)
    (hn : Fintype.card (SupportReduction.InputSupport π) ≤ n)
    (hR : ∀ z, P.w z ≠ 0 → ∀ i, R (z i).1 (z i).2) :
    ∃ (ν : FinProb (Fin n → A)) (q : (Fin n → A) → FinProb (X × A)),
      (∀ u x, ∑ a, (q u).w (x,a) = π.w x) ∧
      (∀ u x a, ¬ R x a → (q u).w (x,a) = 0) ∧
      ∀ k, 1 ≤ k → (hk : k ≤ n / Fintype.card (SupportReduction.InputSupport π)) →
        let g := SupportReduction.floorReferenceSites
          (X := SupportReduction.InputSupport π) hk
        let Pk := FinProb.map P (fun z i => z (g i))
        let Qk := mixtureProduct k ν.w ν.nonneg ν.sum_eq_one q
        FinProb.Supports Pk Qk ∧
        FinProb.kl Pk Qk ≤
          (Sampling.cost (n / Fintype.card (SupportReduction.InputSupport π)) k : EReal) ∧
        Sampling.cost (n / Fintype.card (SupportReduction.InputSupport π)) k ≤
          (k * (k - 1) : ℝ) /
            (2 * (((n / Fintype.card (SupportReduction.InputSupport π) : ℕ) : ℝ) - k + 1)) := by
  classical
  let Ps := SupportReduction.reducedLaw π P hCP
  have hPs : Posterior.Exchangeable Ps :=
    SupportReduction.reducedLaw_exchangeable π P hCP hP
  have hCPs : FixedInputCP (SupportReduction.supportLaw π) Ps :=
    SupportReduction.reducedLaw_inputCP π P hCP
  have hRs : ∀ z, Ps.w z ≠ 0 → ∀ i, R (z i).1.1 (z i).2 := by
    intro z hz i
    exact hR (SupportReduction.includeInputs π z) hz i
  obtain ⟨ν, q, hq, hqR, hbound⟩ := prop_4_1_positive_relation
    (SupportReduction.supportLaw π) (SupportReduction.supportLaw_positive π)
    (fun x a => R x.1 a) (fun x => a₀ x.1) (fun x => ha₀ x.1)
    n Ps hPs hCPs hn hRs
  refine ⟨ν, (fun u => SupportReduction.liftLaw π (q u)), ?_, ?_, ?_⟩
  · intro u
    exact SupportReduction.liftLaw_feasible π (q u) (hq u)
  · intro u x a ha
    by_cases hx : 0 < π.w x
    · change (SupportReduction.liftLaw π (q u)).w
        ((⟨x,hx⟩ : SupportReduction.InputSupport π).1, a) = 0
      rw [SupportReduction.liftLaw_w_supported]
      exact hqR u ⟨x,hx⟩ a ha
    · exact SupportReduction.liftLaw_w_unsupported π (q u) x hx a
  · intro k hk hkM
    let g := SupportReduction.floorReferenceSites
      (X := SupportReduction.InputSupport π) hkM
    obtain ⟨hsupp, hkl, hcost⟩ := hbound k hk hkM
    have hmap := FinProb.kl_map_le (FinProb.map Ps (fun z i => z (g i)))
      (mixtureProduct k ν.w ν.nonneg ν.sum_eq_one q) (SupportReduction.includeInputs π)
    have hsupport := FinProb.supports_map hsupp (SupportReduction.includeInputs π)
    rw [SupportReduction.map_reduced_marginal π P hCP g,
      SupportReduction.map_lifted_mixtureProduct π k ν q] at hmap hsupport
    exact ⟨hsupport, hmap.trans hkl, hcost⟩

/-- Linear map recording the input label of a symbol in a possibly
dependent output alphabet. -/
noncomputable def labelΓ (label : A → X) : (A → ℝ) →ₗ[ℝ] (X → ℝ) where
  toFun w x := ∑ a, if label a = x then w a else 0
  map_add' w v := by
    funext x
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    split_ifs <;> simp
  map_smul' c w := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    split_ifs <;> simp

/-- A single lifted input-label constraint suffices under exchangeability. -/
theorem labelCP_of_exchangeable {κ : Type*} [Fintype κ] [DecidableEq κ]
    (π : FinProb X) (label : A → X) (P : FinProb (κ → A))
    (hP : Posterior.Exchangeable P) (c : κ)
    (hCP : Posterior.LiftedCP (labelΓ label) π.w P c) :
    SupportReduction.InputFiberCP π label P := by
  intro i z x
  have h := congrFun
    (Posterior.liftedCP_at_every_coordinate (labelΓ label) π.w P hP c hCP i z) x
  simpa [labelΓ, smul_eq_mul, mul_comm] using h

/-- **Proposition 4.1 in its full finite-alphabet form.**  `label` records
an input and `section` chooses one allowed output for each input.  Thus
this covers the disjoint union `Σ x, A x` without a common-output-alphabet
assumption.  Zero input masses are allowed.  One finite mixing law and
one family of feasible factors work for every `1 ≤ k ≤ floor(n/|supp π|)`.
Relative entropy includes the value infinity for support mismatch. -/
theorem prop_4_1_labelled (π : FinProb X) (label : A → X)
    (response : X → A) (hsection : ∀ x, label (response x) = x)
    (n : ℕ) (P : FinProb (Fin n → A)) (hP : Posterior.Exchangeable P)
    (c : Fin n) (hCP : Posterior.LiftedCP (labelΓ label) π.w P c)
    (hn : Fintype.card (SupportReduction.InputSupport π) ≤ n) :
    ∃ (ν : FinProb (Fin n → A)) (q : (Fin n → A) → FinProb A),
      (∀ u, FinProb.map (q u) label = π) ∧
      ∀ k, 1 ≤ k → (hk : k ≤ n / Fintype.card (SupportReduction.InputSupport π)) →
        let g := SupportReduction.floorReferenceSites
          (X := SupportReduction.InputSupport π) hk
        let Pk := FinProb.map P (fun z i => z (g i))
        let Qk := mixtureProduct k ν.w ν.nonneg ν.sum_eq_one q
        FinProb.Supports Pk Qk ∧
        FinProb.kl Pk Qk ≤
          (Sampling.cost (n / Fintype.card (SupportReduction.InputSupport π)) k : EReal) ∧
        Sampling.cost (n / Fintype.card (SupportReduction.InputSupport π)) k ≤
          (k * (k - 1) : ℝ) /
            (2 * (((n / Fintype.card (SupportReduction.InputSupport π) : ℕ) : ℝ) - k + 1)) := by
  classical
  have hCPall := labelCP_of_exchangeable π label P hP c hCP
  let Pe := SupportReduction.encodedLaw label P
  have hPe : Posterior.Exchangeable Pe := SupportReduction.encodedLaw_exchangeable label P hP
  have hCPe : FixedInputCP π Pe := SupportReduction.encodedLaw_inputCP π label P hCPall
  have hRe : ∀ z, Pe.w z ≠ 0 → ∀ i, label (z i).2 = (z i).1 := by
    intro z hz i
    by_contra hi
    exact hz (SupportReduction.encodedLaw_zero_invalid label P z i hi)
  obtain ⟨ν, q, hq, hqR, hbound⟩ := prop_4_1_relation π
    (fun x a => label a = x) response hsection n Pe hPe hCPe hn hRe
  refine ⟨ν, (fun u => FinProb.map (q u) Prod.snd), ?_, ?_⟩
  · intro u
    have hfeasible := SupportReduction.map_snd_feasible π label (q u) (hq u)
      (fun z hz => hqR u z.1 z.2 hz)
    apply FinProb.ext
    intro x
    simpa only [FinProb.map_w] using hfeasible x
  · intro k hk hkM
    let g := SupportReduction.floorReferenceSites
      (X := SupportReduction.InputSupport π) hkM
    obtain ⟨hsupp, hkl, hcost⟩ := hbound k hk hkM
    have hmap := FinProb.kl_map_le (FinProb.map Pe (fun z i => z (g i)))
      (mixtureProduct k ν.w ν.nonneg ν.sum_eq_one q) (fun z i => (z i).2)
    have hsupport := FinProb.supports_map hsupp (fun z i => (z i).2)
    rw [SupportReduction.map_encoded_marginal label P g,
      SupportReduction.map_mixtureProduct k ν.w ν.nonneg ν.sum_eq_one q Prod.snd] at hmap hsupport
    exact ⟨hsupport, hmap.trans hkl, hcost⟩

end Paper06.Response
