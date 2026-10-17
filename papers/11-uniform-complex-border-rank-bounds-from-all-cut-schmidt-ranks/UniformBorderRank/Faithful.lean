import UniformBorderRank.Contraction
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.Constructions

/-! A finite-coordinate model used for the rank-growth argument.  Rows retain
all coordinate indices, so releasing a factor stays in one fixed vector space.
It will be compared to `contractCoeffs`, which removes the redundant indices. -/
noncomputable section
namespace UniformBorderRank
open Finset Filter

abbrev Covectors {N : ℕ} (d : Fin N → ℕ) := ∀ i : Fin N, Fin (d i) → ℂ
abbrev TensorIndex {N : ℕ} (d : Fin N → ℕ) := ∀ i : Fin N, Fin (d i)

def contractionWeight {N : ℕ} {d : Fin N → ℕ} (J : Finset (Fin N))
    (b : Covectors d) (u v : TensorIndex d) : ℂ :=
  ∏ i, if i ∈ J then (if v i = u i then 1 else 0) else b i (v i)

def fullContract {N : ℕ} {d : Fin N → ℕ} (T : Coeffs d)
    (J : Finset (Fin N)) (b : Covectors d) : Coeffs d :=
  fun u => ∑ v, T v * contractionWeight J b u v

def fullContractMap {N : ℕ} {d : Fin N → ℕ}
    (E : Submodule ℂ (Coeffs d)) (J : Finset (Fin N)) (b : Covectors d) :
    E →ₗ[ℂ] Coeffs d where
  toFun T := fullContract T.val J b
  map_add' T U := by ext u; simp [fullContract, add_mul, Finset.sum_add_distrib]
  map_smul' c T := by ext u; simp [fullContract, mul_assoc, Finset.mul_sum]

def fullRank {N : ℕ} {d : Fin N → ℕ}
    (E : Submodule ℂ (Coeffs d)) (J : Finset (Fin N)) (b : Covectors d) : ℕ :=
  Module.finrank ℂ (LinearMap.range (fullContractMap E J b))

def maxFullRank {N : ℕ} {d : Fin N → ℕ}
    (E : Submodule ℂ (Coeffs d)) (J : Finset (Fin N)) : ℕ :=
  sSup (Set.range (fullRank E J))

lemma contractionWeight_univ {N : ℕ} {d : Fin N → ℕ} (b : Covectors d)
    (u v : TensorIndex d) : contractionWeight univ b u v = if v = u then 1 else 0 := by
  classical
  by_cases h : v = u
  · subst v; simp [contractionWeight]
  · have hn : ∃ i, v i ≠ u i := by simpa [funext_iff] using h
    obtain ⟨i, hi⟩ := hn
    simp only [contractionWeight, mem_univ, ite_true, if_neg h]
    exact Finset.prod_eq_zero (mem_univ i) (if_neg hi)

lemma fullContract_univ {N : ℕ} {d : Fin N → ℕ} (T : Coeffs d) (b : Covectors d) :
    fullContract T univ b = T := by
  classical
  ext u
  simp [fullContract, contractionWeight_univ]

lemma fullRank_le {N : ℕ} {d : Fin N → ℕ}
    (E : Submodule ℂ (Coeffs d)) (J : Finset (Fin N)) (b : Covectors d) :
    fullRank E J b ≤ Module.finrank ℂ E := LinearMap.finrank_range_le _

lemma fullRank_le_max {N : ℕ} {d : Fin N → ℕ}
    (E : Submodule ℂ (Coeffs d)) (J : Finset (Fin N)) (b : Covectors d) :
    fullRank E J b ≤ maxFullRank E J :=
  le_csSup ⟨Module.finrank ℂ E, by rintro _ ⟨c, rfl⟩; exact fullRank_le E J c⟩ ⟨b, rfl⟩

lemma maxFullRank_le {N : ℕ} {d : Fin N → ℕ}
    (E : Submodule ℂ (Coeffs d)) (J : Finset (Fin N)) :
    maxFullRank E J ≤ Module.finrank ℂ E :=
  csSup_le ⟨_, ⟨0, rfl⟩⟩ (by rintro _ ⟨b, rfl⟩; exact fullRank_le E J b)

lemma maxFullRank_attained {N : ℕ} {d : Fin N → ℕ}
    (E : Submodule ℂ (Coeffs d)) (J : Finset (Fin N)) :
    ∃ b, fullRank E J b = maxFullRank E J := by
  have hn : (Set.range (fullRank E J)).Nonempty := ⟨_, ⟨0, rfl⟩⟩
  have hb : BddAbove (Set.range (fullRank E J)) :=
    ⟨Module.finrank ℂ E, by rintro _ ⟨b, rfl⟩; exact fullRank_le E J b⟩
  exact Nat.sSup_mem hn hb

lemma contractionWeight_update {N : ℕ} {d : Fin N → ℕ} (J : Finset (Fin N))
    (i : Fin N) (hi : i ∉ J) (b : Covectors d) (x : Fin (d i) → ℂ)
    (u v : TensorIndex d) :
    contractionWeight J (Function.update b i x) u v = x (v i) *
      ∏ j ∈ univ.erase i, if j ∈ J then (if v j = u j then 1 else 0) else b j (v j) := by
  classical
  rw [contractionWeight, ← Finset.mul_prod_erase _ _ (mem_univ i)]
  simp only [if_neg hi, Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  simp [Function.update_of_ne hji]

lemma contractionWeight_release {N : ℕ} {d : Fin N → ℕ} (J : Finset (Fin N))
    (i : Fin N) (_hi : i ∉ J) (b : Covectors d) (a : Fin (d i))
    (u v : TensorIndex d) :
    contractionWeight (insert i J) b (Function.update u i a) v =
      (if v i = a then 1 else 0) *
      ∏ j ∈ univ.erase i, if j ∈ J then (if v j = u j then 1 else 0) else b j (v j) := by
  classical
  rw [contractionWeight, ← Finset.mul_prod_erase _ _ (mem_univ i)]
  simp only [mem_insert_self, ite_true, Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  simp [hji]

lemma fullContract_update {N : ℕ} {d : Fin N → ℕ} (T : Coeffs d)
    (J : Finset (Fin N)) (i : Fin N) (hi : i ∉ J)
    (b : Covectors d) (x : Fin (d i) → ℂ) (u : TensorIndex d) :
    fullContract T J (Function.update b i x) u =
      ∑ a, x a * fullContract T (insert i J) b (Function.update u i a) := by
  classical
  simp only [fullContract, contractionWeight_update J i hi,
    contractionWeight_release J i hi, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  simp [mul_ite, ite_mul, mul_left_comm]

lemma fullContract_update_of_mem {N : ℕ} {d : Fin N → ℕ} (T : Coeffs d)
    (J : Finset (Fin N)) (i : Fin N) (hi : i ∈ J)
    (b : Covectors d) (x : Fin (d i) → ℂ) :
    fullContract T J (Function.update b i x) = fullContract T J b := by
  classical
  ext u
  apply Finset.sum_congr rfl
  intro v _
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j ∈ J
  · simp only [if_pos hj]
  · have hji : j ≠ i := by rintro rfl; exact hj hi
    simp [hj, Function.update_of_ne hji]

lemma fullContract_ker_release {N : ℕ} {d : Fin N → ℕ}
    (E : Submodule ℂ (Coeffs d)) (J : Finset (Fin N)) (i : Fin N) (hi : i ∉ J)
    (b : Covectors d) (x : Fin (d i) → ℂ) :
    LinearMap.ker (fullContractMap E (insert i J) b) ≤
      LinearMap.ker (fullContractMap E J (Function.update b i x)) := by
  intro T hT
  change fullContract T.val J (Function.update b i x) = 0
  ext u
  rw [fullContract_update T.val J i hi b x u]
  have hT' : fullContract T.val (insert i J) b = 0 := hT
  simp [hT']

lemma fullRank_mono {N : ℕ} {d : Fin N → ℕ}
    (E : Submodule ℂ (Coeffs d)) (J : Finset (Fin N)) (i : Fin N) (hi : i ∉ J)
    (b : Covectors d) (x : Fin (d i) → ℂ) :
    fullRank E J (Function.update b i x) ≤ fullRank E (insert i J) b := by
  have hker := Submodule.finrank_mono (fullContract_ker_release E J i hi b x)
  have h₁ := (fullContractMap E J (Function.update b i x)).finrank_range_add_finrank_ker
  have h₂ := (fullContractMap E (insert i J) b).finrank_range_add_finrank_ker
  unfold fullRank
  omega

lemma continuous_fullContract {N : ℕ} {d : Fin N → ℕ} (T : Coeffs d)
    (J : Finset (Fin N)) : Continuous (fun b : Covectors d => fullContract T J b) := by
  classical
  apply continuous_pi
  intro u
  unfold fullContract contractionWeight
  apply continuous_finset_sum
  intro v _
  apply Continuous.const_mul
  apply continuous_finset_prod
  intro i _
  split_ifs <;> fun_prop

/-- Maximal-rank contractions remain of maximal rank in a neighborhood. -/
lemma fullRank_eventually_ge {N : ℕ} {d : Fin N → ℕ}
    (E : Submodule ℂ (Coeffs d)) (J : Finset (Fin N)) (b : Covectors d) :
    ∀ᶠ c in nhds b, fullRank E J b ≤ fullRank E J c := by
  classical
  have hself : (fullRank E J b : Cardinal) ≤ (fullContractMap E J b).rank := by
    rw [fullRank, LinearMap.rank, Module.finrank_eq_rank]
  obtain ⟨s, hs, hli⟩ := LinearMap.le_rank_iff_exists_linearIndependent_finset.mp hself
  have hc : Continuous (fun c : Covectors d => fun x : (s : Set E) =>
      fullContractMap E J c x) := by
    apply continuous_pi
    intro x
    exact continuous_fullContract x.val.val J
  filter_upwards [hc.tendsto b hli.eventually] with c hc
  have h := LinearMap.le_rank_iff_exists_linearIndependent_finset.mpr ⟨s, hs, hc⟩
  rw [LinearMap.rank, ← Module.finrank_eq_rank] at h
  exact_mod_cast h

lemma analytic_fullContract {N : ℕ} {d : Fin N → ℕ} (T : Coeffs d)
    (J : Finset (Fin N)) (u : TensorIndex d) :
    AnalyticOnNhd ℂ (fun b : Covectors d => fullContract T J b u) Set.univ := by
  classical
  intro b _
  unfold fullContract contractionWeight
  apply Finset.analyticAt_fun_sum
  intro v _
  apply AnalyticAt.mul analyticAt_const
  apply Finset.analyticAt_fun_prod
  intro i _
  split_ifs
  · exact analyticAt_const
  · exact analyticAt_const
  · exact (((ContinuousLinearMap.proj (v i) : (Fin (d i) → ℂ) →L[ℂ] ℂ)).comp
      (ContinuousLinearMap.proj i : Covectors d →L[ℂ] (Fin (d i) → ℂ))).analyticAt b

/-- When neither endpoint can have rank exceeding `q`, maximal rank at both
endpoints makes their kernels agree. -/
lemma fullKer_update_eq {N : ℕ} {d : Fin N → ℕ}
    (E : Submodule ℂ (Coeffs d)) (J : Finset (Fin N)) (i : Fin N)
    (b : Covectors d) (x : Fin (d i) → ℂ) (q : ℕ)
    (hb : fullRank E J b = q)
    (hx : fullRank E J (Function.update b i x) = q)
    (hrelease : maxFullRank E (insert i J) ≤ q) :
    LinearMap.ker (fullContractMap E J b) =
      LinearMap.ker (fullContractMap E J (Function.update b i x)) := by
  classical
  by_cases hi : i ∈ J
  · congr 1
    ext T u
    exact (congrFun (fullContract_update_of_mem T.val J i hi b x) u).symm
  · have h₀ : LinearMap.ker (fullContractMap E (insert i J) b) ≤
        LinearMap.ker (fullContractMap E J b) := by
      simpa only [Function.update_eq_self] using fullContract_ker_release E J i hi b (b i)
    have h₁ := fullContract_ker_release E J i hi b x
    have hdim₀ := (fullContractMap E J b).finrank_range_add_finrank_ker
    have hdim₁ := (fullContractMap E J (Function.update b i x)).finrank_range_add_finrank_ker
    have hdim₂ := (fullContractMap E (insert i J) b).finrank_range_add_finrank_ker
    have hle := (fullRank_le_max E (insert i J) b).trans hrelease
    have hge := fullRank_mono E J i hi b (b i)
    simp only [Function.update_eq_self] at hge
    unfold fullRank at hb hx hle hge
    have heq₀ := Submodule.eq_of_le_of_finrank_eq h₀ (by omega)
    have heq₁ := Submodule.eq_of_le_of_finrank_eq h₁ (by omega)
    exact heq₀.symm.trans heq₁

def mixCovectors {N : ℕ} {d : Fin N → ℕ} (b c : Covectors d)
    (S : Finset (Fin N)) : Covectors d := fun i => if i ∈ S then c i else b i

@[simp] lemma mixCovectors_empty {N : ℕ} {d : Fin N → ℕ} (b c : Covectors d) :
    mixCovectors b c ∅ = b := by funext i; simp [mixCovectors]

@[simp] lemma mixCovectors_univ {N : ℕ} {d : Fin N → ℕ} (b c : Covectors d) :
    mixCovectors b c univ = c := by funext i; simp [mixCovectors]

lemma mixCovectors_insert {N : ℕ} {d : Fin N → ℕ} (b c : Covectors d)
    (S : Finset (Fin N)) (i : Fin N) :
    mixCovectors b c (insert i S) = Function.update (mixCovectors b c S) i (c i) := by
  classical
  funext j
  by_cases h : j = i
  · subst j; simp [mixCovectors]
  · simp [mixCovectors, h]

/-- If releasing every remaining site fails to increase the maximum rank,
the maximum rank was already the entire source dimension. -/
theorem maxFullRank_eq_of_no_growth {N : ℕ} {d : Fin N → ℕ}
    (E : Submodule ℂ (Coeffs d)) (J : Finset (Fin N))
    (hno : ∀ i, maxFullRank E (insert i J) ≤ maxFullRank E J) :
    maxFullRank E J = Module.finrank ℂ E := by
  classical
  obtain ⟨b, hb⟩ := maxFullRank_attained E J
  have hmix : ∀ᶠ c in nhds b, ∀ S : Finset (Fin N),
      fullRank E J (mixCovectors b c S) = maxFullRank E J := by
    rw [Filter.eventually_all]
    intro S
    have hc : Continuous (fun c : Covectors d => mixCovectors b c S) := by
      apply continuous_pi
      intro i
      by_cases hi : i ∈ S <;> simp [mixCovectors, hi] <;> fun_prop
    have he : mixCovectors b b S = b := by ext i; simp [mixCovectors]
    have ht := hc.tendsto b
    rw [he] at ht
    filter_upwards [ht (fullRank_eventually_ge E J b)] with c hc
    exact le_antisymm (fullRank_le_max E J _) (calc
      maxFullRank E J = fullRank E J b := hb.symm
      _ ≤ _ := hc)
  have hinj : Function.Injective (fullContractMap E J b) := by
    rw [← LinearMap.ker_eq_bot]
    apply le_antisymm _ bot_le
    intro T hT
    have hz : ∀ᶠ c in nhds b, fullContract T.val J c = 0 := by
      filter_upwards [hmix] with c hc
      have hk : ∀ S : Finset (Fin N),
          LinearMap.ker (fullContractMap E J b) =
            LinearMap.ker (fullContractMap E J (mixCovectors b c S)) := by
        intro S
        induction S using Finset.induction_on with
        | empty => rw [mixCovectors_empty]
        | @insert i S hi ih =>
          rw [mixCovectors_insert]
          apply ih.trans
          apply fullKer_update_eq E J i (mixCovectors b c S) (c i) (maxFullRank E J)
          · exact hc S
          · rw [← mixCovectors_insert]; exact hc (insert i S)
          · exact hno i
      have hk' := hk univ
      rw [mixCovectors_univ] at hk'
      exact (show T ∈ LinearMap.ker (fullContractMap E J c) by rwa [← hk'])
    have hall : ∀ c, fullContract T.val J c = 0 := by
      intro c
      ext u
      have hanalytic := analytic_fullContract T.val J u
      have hEq : (fun c : Covectors d => fullContract T.val J c u) = fun _ => 0 :=
        hanalytic.eq_of_eventuallyEq (analyticOnNhd_const) (hz.mono fun c hc => congrFun hc u)
      exact congrFun hEq c
    change T = 0
    apply Subtype.ext
    funext u
    have hv := congrFun (hall (fun i a => if a = u i then 1 else 0)) u
    have hw : ∀ v : TensorIndex d,
        contractionWeight J (fun i a => if a = u i then 1 else 0) u v =
          contractionWeight univ 0 u v := by
      intro v
      apply Finset.prod_congr rfl
      intro i _
      simp [mem_univ]
    change T.val u = 0
    have hu : fullContract T.val J (fun i a => if a = u i then 1 else 0) u = T.val u := by
      simp only [fullContract, hw, contractionWeight_univ]
      simp
    simpa only [hu, Pi.zero_apply] using hv
  rw [← hb]
  exact LinearMap.finrank_range_of_inj hinj

theorem maxFullRank_growth {N : ℕ} {d : Fin N → ℕ}
    (E : Submodule ℂ (Coeffs d)) (J : Finset (Fin N))
    (hlt : maxFullRank E J < Module.finrank ℂ E) :
    ∃ i ∉ J, maxFullRank E J < maxFullRank E (insert i J) := by
  classical
  by_contra! hn
  have hno : ∀ i, maxFullRank E (insert i J) ≤ maxFullRank E J := by
    intro i
    by_cases hi : i ∈ J
    · simp [insert_eq_of_mem hi]
    · exact hn i hi
  have he := maxFullRank_eq_of_no_growth E J hno
  omega

lemma fullContract_delta {N : ℕ} {d : Fin N → ℕ} (T : Coeffs d)
    (J : Finset (Fin N)) (u : TensorIndex d) :
    fullContract T J (fun i a => if a = u i then 1 else 0) u = T u := by
  classical
  have hw : ∀ v : TensorIndex d,
      contractionWeight J (fun i a => if a = u i then 1 else 0) u v =
        contractionWeight univ 0 u v := by
    intro v
    apply Finset.prod_congr rfl
    intro i _
    simp only [mem_univ, ite_true]
    split_ifs <;> rfl
  simp only [fullContract, hw, contractionWeight_univ]
  simp

lemma fullRank_empty_le {N : ℕ} {d : Fin N → ℕ}
    (E : Submodule ℂ (Coeffs d)) (b : Covectors d) :
    fullRank E ∅ b ≤ 1 := by
  classical
  have hsub : LinearMap.range (fullContractMap E ∅ b) ≤
      Submodule.span ℂ {(1 : Coeffs d)} := by
    rintro _ ⟨T, rfl⟩
    have he : fullContractMap E ∅ b T =
        (∑ v, T.val v * ∏ i, b i (v i)) • (1 : Coeffs d) := by
      ext u
      simp [fullContractMap, fullContract, contractionWeight]
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  exact (Submodule.finrank_mono hsub).trans (by simpa using finrank_span_le_card ({(1 : Coeffs d)} : Set (Coeffs d)))

lemma maxFullRank_empty {N : ℕ} {d : Fin N → ℕ}
    (E : Submodule ℂ (Coeffs d)) (hE : 0 < Module.finrank ℂ E) :
    maxFullRank E ∅ = 1 := by
  classical
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨b, rfl⟩
    exact fullRank_empty_le E b
  · haveI : Nontrivial E := Module.nontrivial_of_finrank_pos hE
    obtain ⟨T, hT⟩ := exists_ne (0 : E)
    have hn : ∃ u, T.val u ≠ 0 := by
      by_contra! hn
      apply hT
      exact Subtype.ext (funext hn)
    obtain ⟨u, hu⟩ := hn
    let b : Covectors d := fun i a => if a = u i then 1 else 0
    have hbot : LinearMap.range (fullContractMap E ∅ b) ≠ ⊥ := by
      intro hh
      have hm : fullContractMap E ∅ b T ∈ (⊥ : Submodule ℂ (Coeffs d)) := by
        rw [← hh]; exact ⟨T, rfl⟩
      have hm' := congrFun (show fullContractMap E ∅ b T = 0 from hm) u
      have he : fullContractMap E ∅ b T u = T.val u := fullContract_delta T.val ∅ u
      exact hu (he.symm.trans hm')
    have hpos : 1 ≤ fullRank E ∅ b := Submodule.one_le_finrank_iff.mpr hbot
    exact hpos.trans (fullRank_le_max E ∅ b)

/-- Faithfulness in the redundant-row coordinate model. -/
theorem faithful_full_contraction {N : ℕ} {d : Fin N → ℕ}
    (E : Submodule ℂ (Coeffs d)) (hE : 0 < Module.finrank ℂ E) :
    ∃ (J : Finset (Fin N)) (b : Covectors d),
      J.card ≤ Module.finrank ℂ E - 1 ∧ Function.Injective (fullContractMap E J b) := by
  classical
  obtain ⟨J, hJ, hr⟩ := growth_steps_bound (Module.finrank ℂ E) (maxFullRank E)
    (maxFullRank_empty E hE) (maxFullRank_le E) (maxFullRank_growth E)
  obtain ⟨b, hb⟩ := maxFullRank_attained E J
  refine ⟨J, b, hJ, ?_⟩
  rw [← LinearMap.ker_eq_bot]
  have hd := (fullContractMap E J b).finrank_range_add_finrank_ker
  change Module.finrank ℂ (LinearMap.range (fullContractMap E J b)) = _ at hb
  rw [hr] at hb
  exact Submodule.finrank_eq_zero.mp (by omega)

/-- Split a complete tensor coordinate into retained and contracted indices. -/
def contractionIndexEquiv {N : ℕ} (d : Fin N → ℕ) (J : Finset (Fin N)) :
    TensorIndex d ≃ (∀ i : J, Fin (d i)) × CompIndex d J where
  toFun u := (fun i => u i, fun i => u i)
  invFun u i := if h : i ∈ J then u.1 ⟨i, h⟩ else u.2 ⟨i, mem_compl.mpr h⟩
  left_inv u := by funext i; dsimp; split_ifs <;> rfl
  right_inv u := by
    apply Prod.ext
    · funext i
      simp only [dif_pos i.property]
    · funext i
      simp only [dif_neg (mem_compl.mp i.property)]

lemma contractionWeight_split {N : ℕ} {d : Fin N → ℕ}
    (J : Finset (Fin N)) (b : Covectors d) (u : TensorIndex d)
    (v : (∀ i : J, Fin (d i)) × CompIndex d J) :
    contractionWeight J b u ((contractionIndexEquiv d J).symm v) =
      (if v.1 = (fun i : J => u i) then 1 else 0) *
        ∏ i : (Jᶜ : Finset (Fin N)), b i (v.2 i) := by
  classical
  have hs : (∏ i : J, (if v.1 i = u i then (1 : ℂ) else 0)) =
      if v.1 = (fun i : J => u i) then 1 else 0 := by
    by_cases h : v.1 = (fun i : J => u i)
    · simp [h]
    · have hn : ∃ i : J, v.1 i ≠ u i := by simpa [funext_iff] using h
      obtain ⟨i, hi⟩ := hn
      rw [if_neg h]
      exact Finset.prod_eq_zero (mem_univ i) (if_neg hi)
  rw [← hs]
  unfold contractionWeight
  rw [← Finset.prod_mul_prod_compl J]
  congr 1
  · rw [← Finset.prod_coe_sort]
    apply Finset.prod_congr rfl
    intro i _
    simp [contractionIndexEquiv, i.property]
  · rw [← Finset.prod_coe_sort]
    apply Finset.prod_congr rfl
    intro i _
    simp [contractionIndexEquiv, mem_compl.mp i.property]

/-- The redundant-row contraction agrees with the original complementary
multi-index contraction, evaluated on the retained coordinates. -/
lemma fullContract_eq_contractCoeffs {N : ℕ} {d : Fin N → ℕ} (T : Coeffs d)
    (J : Finset (Fin N)) (b : Covectors d) (u : TensorIndex d) :
    fullContract T J b u = contractCoeffs T J b (fun i => u i) := by
  classical
  unfold fullContract
  rw [← (contractionIndexEquiv d J).symm.sum_comp]
  simp only [Fintype.sum_prod_type, contractionWeight_split, mul_ite, mul_zero,
    ite_mul, zero_mul]
  rw [Finset.sum_eq_single (fun i : J => u i)]
  · simp only [ite_true, one_mul]
    rfl
  · intro v _ hv
    simp [hv]
  · simp

theorem faithful_product_contraction_proved {N : ℕ} {d : Fin N → ℕ}
    (E : Submodule ℂ (Coeffs d)) (r : ℕ) : faithful_product_contraction E r := by
  classical
  rintro ⟨hr, hrpos⟩
  obtain ⟨J, b, hcard, hinj⟩ := faithful_full_contraction E (by omega)
  refine ⟨J, b, by omega, ?_⟩
  intro T U h
  apply hinj
  ext u
  change fullContract T.val J b u = fullContract U.val J b u
  rw [fullContract_eq_contractCoeffs, fullContract_eq_contractCoeffs]
  exact congrFun h (fun i : J => u i)

end UniformBorderRank
