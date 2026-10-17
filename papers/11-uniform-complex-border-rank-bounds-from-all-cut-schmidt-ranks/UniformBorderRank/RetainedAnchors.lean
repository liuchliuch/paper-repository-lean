import UniformBorderRank.AnchorCore
import UniformBorderRank.LocalMaps
import UniformBorderRank.FlatteningFacts

/-! The faithful product contractions on both sides of an original cut,
with their redundant coordinates removed. -/
noncomputable section
namespace UniformBorderRank
open Finset Module

namespace FiniteSites

abbrev RetainedIndex {ι : Type*} [Fintype ι] (d : ι → ℕ) (J : Finset ι) :=
  ∀ i : J, Fin (d i)

def restrictIndex {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (J : Finset ι) (u : TensorIndex d) : RetainedIndex d J := fun i => u i

def extendIndex {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ι → ℕ}
    (J : Finset ι) (u₀ : TensorIndex d) (u : RetainedIndex d J) : TensorIndex d :=
  fun i => if hi : i ∈ J then u ⟨i, hi⟩ else u₀ i

@[simp] lemma restrict_extend {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ι → ℕ}
    (J : Finset ι) (u₀ : TensorIndex d) (u : RetainedIndex d J) :
    restrictIndex J (extendIndex J u₀ u) = u := by
  funext i
  simp [restrictIndex, extendIndex]

lemma restrictIndex_surjective {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ι → ℕ}
    (J : Finset ι) (u₀ : TensorIndex d) : Function.Surjective (restrictIndex (d := d) J) :=
  fun u => ⟨extendIndex J u₀ u, restrict_extend J u₀ u⟩

lemma fullContract_eq_of_restrict_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {d : ι → ℕ} (T : TensorIndex d → ℂ) (J : Finset ι) (b : Covectors d)
    (u v : TensorIndex d) (h : restrictIndex J u = restrictIndex J v) :
    fullContract T J b u = fullContract T J b v := by
  apply sum_congr rfl
  intro w _
  congr 1
  apply prod_congr rfl
  intro i _
  by_cases hi : i ∈ J
  · have hv : u i = v i := congrFun h ⟨i, hi⟩
    simp only [contractionWeight, if_pos hi, hv]
  · simp only [contractionWeight, if_neg hi]

/-- The genuine contraction, indexed only by coordinates on the retained sites. -/
def retainedContract {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ι → ℕ}
    (T : TensorIndex d → ℂ) (J : Finset ι) (b : Covectors d)
    (u : RetainedIndex d J) : ℂ :=
  ∑ w, T w * ∏ i, if hi : i ∈ J then (if w i = u ⟨i, hi⟩ then 1 else 0) else b i (w i)

lemma retainedContract_restrict {ι : Type*} [Fintype ι] [DecidableEq ι]
    {d : ι → ℕ} (T : TensorIndex d → ℂ) (J : Finset ι) (b : Covectors d)
    (u : TensorIndex d) : retainedContract T J b (restrictIndex J u) = fullContract T J b u := by
  rfl

lemma retainedContract_extend {ι : Type*} [Fintype ι] [DecidableEq ι]
    {d : ι → ℕ} (T : TensorIndex d → ℂ) (J : Finset ι) (b : Covectors d)
    (u₀ : TensorIndex d) (u : RetainedIndex d J) :
    retainedContract T J b u = fullContract T J b (extendIndex J u₀ u) := by
  rw [← retainedContract_restrict, restrict_extend]

end FiniteSites

/-- Surjective changes of the row/column coordinates do not change matrix rank. -/
theorem rowSpan_finrank_surjective_reindex {I J I' J' : Type*}
    [Fintype J] [Fintype J'] (M : I → J → ℂ)
    (f : I' → I) (g : J' → J) (hf : Function.Surjective f) (hg : Function.Surjective g) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range (fun i' j' => M (f i') (g j')))) =
      Module.finrank ℂ (Submodule.span ℂ (Set.range M)) := by
  let l : (J → ℂ) →ₗ[ℂ] (J' → ℂ) :=
    { toFun := fun x j' => x (g j')
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hrange : Set.range (fun i' => l (M (f i'))) = Set.range (fun i => l (M i)) := by
    ext x
    constructor
    · rintro ⟨i', rfl⟩; exact ⟨f i', rfl⟩
    · rintro ⟨i, rfl⟩
      obtain ⟨i', rfl⟩ := hf i
      exact ⟨i', rfl⟩
  change Module.finrank ℂ (Submodule.span ℂ (Set.range (fun i' => l (M (f i'))))) = _
  rw [hrange]
  apply rowSpan_finrank_map_eq M l
  intro x y h
  apply Subtype.ext
  funext j
  obtain ⟨j', rfl⟩ := hg j
  exact congrFun h j'

/-- Removing the constant redundant coordinates in a two-sided contraction
preserves its matrix rank. -/
theorem retained_core_rank_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {d : ι → ℕ} {e : κ → ℕ}
    (M : FiniteSites.TensorIndex d → FiniteSites.TensorIndex e → ℂ)
    (J : Finset ι) (K : Finset κ) (b : FiniteSites.Covectors d) (c : FiniteSites.Covectors e)
    (u₀ : FiniteSites.TensorIndex d) (v₀ : FiniteSites.TensorIndex e) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range (fun u v =>
      FiniteSites.retainedContract (fun i => FiniteSites.retainedContract (M i) K c v) J b u))) =
    Module.finrank ℂ (Submodule.span ℂ (Set.range (fun u v =>
      FiniteSites.fullContract (fun i => FiniteSites.fullContract (M i) K c v) J b u))) := by
  let C := fun u v => FiniteSites.retainedContract
    (fun i => FiniteSites.retainedContract (M i) K c v) J b u
  have h := rowSpan_finrank_surjective_reindex C
    (FiniteSites.restrictIndex J) (FiniteSites.restrictIndex K)
    (FiniteSites.restrictIndex_surjective J u₀) (FiniteSites.restrictIndex_surjective K v₀)
  exact h.symm

/-- The faithful two-sided product contraction has rank `r` on the actual
retained coordinate spaces, each having at most `r-1` tensor sites. -/
theorem exists_faithful_retained_core {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {d : ι → ℕ} {e : κ → ℕ}
    (M : FiniteSites.TensorIndex d → FiniteSites.TensorIndex e → ℂ)
    (r : ℕ) (hr : 1 ≤ r)
    (hdim : Module.finrank ℂ (Submodule.span ℂ (Set.range M)) = r)
    (u₀ : FiniteSites.TensorIndex d) (v₀ : FiniteSites.TensorIndex e) :
    ∃ (J : Finset ι) (K : Finset κ) (b : FiniteSites.Covectors d) (c : FiniteSites.Covectors e),
      J.card ≤ r - 1 ∧ K.card ≤ r - 1 ∧
      Module.finrank ℂ (Submodule.span ℂ (Set.range (fun u v =>
        FiniteSites.retainedContract (fun i => FiniteSites.retainedContract (M i) K c v) J b u))) = r := by
  obtain ⟨J, K, b, c, hJ, hK, hcore⟩ := exists_faithful_anchor_core M r hr hdim
  exact ⟨J, K, b, c, hJ, hK, (retained_core_rank_eq M J K b c u₀ v₀).trans hcore⟩

/-- Coordinates on a finite set as functions on its subtype or as the
proof-indexed functions used by `flatCoeff`. -/
def subtypeIndexEquiv {N : ℕ} (d : Fin N → ℕ) (S : Finset (Fin N)) :
    FiniteSites.TensorIndex (fun i : S => d i) ≃ (∀ i ∈ S, Fin (d i)) where
  toFun u i hi := u ⟨i, hi⟩
  invFun u i := u i i.property
  left_inv _ := rfl
  right_inv _ := rfl

/-- The actual coefficient matrix of an original cut, on its two site families. -/
def siteCutMatrix {N : ℕ} (d : Fin N → ℕ) (T : Coeffs d) (S : Finset (Fin N))
    (u : FiniteSites.TensorIndex (fun i : S => d i))
    (v : FiniteSites.TensorIndex (fun i : (Sᶜ : Finset (Fin N)) => d i)) : ℂ :=
  flatCoeff d T S (subtypeIndexEquiv d S u) (subtypeIndexEquiv d Sᶜ v)

lemma siteCutMatrix_rank {N : ℕ} (d : Fin N → ℕ) (T : Coeffs d) (S : Finset (Fin N)) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range (siteCutMatrix d T S))) =
      schmidtRank d T S := by
  exact rowSpan_finrank_surjective_reindex (flatCoeff d T S)
    (subtypeIndexEquiv d S) (subtypeIndexEquiv d Sᶜ)
    (subtypeIndexEquiv d S).surjective (subtypeIndexEquiv d Sᶜ).surjective

/-- A retained rank at least two forces a retained site on each side. -/
lemma retained_sets_nonempty_of_rank {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {d : ι → ℕ} {e : κ → ℕ}
    (M : FiniteSites.TensorIndex d → FiniteSites.TensorIndex e → ℂ)
    (J : Finset ι) (K : Finset κ) (b : FiniteSites.Covectors d) (c : FiniteSites.Covectors e)
    (r : ℕ) (hr : 2 ≤ r)
    (hcore : Module.finrank ℂ (Submodule.span ℂ (Set.range (fun u v =>
      FiniteSites.retainedContract (fun i => FiniteSites.retainedContract (M i) K c v) J b u))) = r) :
    J.Nonempty ∧ K.Nonempty := by
  classical
  let C := fun u v => FiniteSites.retainedContract
    (fun i => FiniteSites.retainedContract (M i) K c v) J b u
  have hdim : Module.finrank ℂ (Submodule.span ℂ (Set.range C)) = r := hcore
  constructor
  · by_contra hJ
    have hJe : J = ∅ := not_nonempty_iff_eq_empty.mp hJ
    subst J
    have hbound := finrank_range_le_card (R := ℂ) C
    change Module.finrank ℂ (Submodule.span ℂ (Set.range C)) ≤ _ at hbound
    have hc : Fintype.card (FiniteSites.RetainedIndex d ∅) = 1 := by
      simp [FiniteSites.RetainedIndex]
    rw [hdim, hc] at hbound
    omega
  · by_contra hK
    have hKe : K = ∅ := not_nonempty_iff_eq_empty.mp hK
    subst K
    have hbound := finrank_range_le_card (R := ℂ) (fun v u => C u v)
    change Module.finrank ℂ (Submodule.span ℂ (Set.range (fun v u => C u v))) ≤ _ at hbound
    have hc : Fintype.card (FiniteSites.RetainedIndex e ∅) = 1 := by
      simp [FiniteSites.RetainedIndex]
    rw [← rowSpan_finrank_transpose C, hdim, hc] at hbound
    omega

/-- Applied to a maximal original cut, the contraction lemma produces
nonempty retained anchor families on its two disjoint sides. The matrix
entries are explicit product contractions of the original coefficients. -/
theorem exists_retained_anchors_of_maximal_cut {N : ℕ} (d : Fin N → ℕ)
    (T : Coeffs d) (hT : T ≠ 0) (S : Finset (Fin N)) (r : ℕ)
    (hr : 2 ≤ r) (hS : schmidtRank d T S = r) :
    ∃ (J : Finset S) (K : Finset (Sᶜ : Finset (Fin N)))
      (b : FiniteSites.Covectors (fun i : S => d i))
      (c : FiniteSites.Covectors (fun i : (Sᶜ : Finset (Fin N)) => d i)),
      J.Nonempty ∧ K.Nonempty ∧ J.card ≤ r - 1 ∧ K.card ≤ r - 1 ∧
      Module.finrank ℂ (Submodule.span ℂ (Set.range (fun u v =>
        FiniteSites.retainedContract
          (fun i => FiniteSites.retainedContract (siteCutMatrix d T S i) K c v) J b u))) = r := by
  classical
  obtain ⟨w, hw⟩ : ∃ w, T w ≠ 0 := by
    by_contra! h
    exact hT (funext h)
  obtain ⟨J, K, b, c, hJ, hK, hcore⟩ := exists_faithful_retained_core
    (siteCutMatrix d T S) r (by omega) ((siteCutMatrix_rank d T S).trans hS)
    (fun i => w i) (fun i => w i)
  have hne := retained_sets_nonempty_of_rank (siteCutMatrix d T S) J K b c r hr hcore
  exact ⟨J, K, b, c, hne.1, hne.2, hJ, hK, hcore⟩

/-- View sites retained inside a cut as sites of the original tensor. -/
def globalRetained {N : ℕ} (S : Finset (Fin N)) (J : Finset S) : Finset (Fin N) :=
  J.map ⟨Subtype.val, Subtype.val_injective⟩

@[simp] lemma mem_globalRetained {N : ℕ} (S : Finset (Fin N)) (J : Finset S) (i : Fin N) :
    i ∈ globalRetained S J ↔ ∃ hi : i ∈ S, (⟨i, hi⟩ : S) ∈ J := by
  classical
  constructor
  · rintro h
    obtain ⟨j, hj, he⟩ := mem_map.mp h
    subst i
    exact ⟨j.property, hj⟩
  · rintro ⟨hi, hj⟩
    exact mem_map.mpr ⟨⟨i, hi⟩, hj, rfl⟩

lemma globalRetained_subset {N : ℕ} (S : Finset (Fin N)) (J : Finset S) :
    globalRetained S J ⊆ S := by
  intro i hi
  exact (mem_globalRetained S J i).mp hi |>.choose

@[simp] lemma card_globalRetained {N : ℕ} (S : Finset (Fin N)) (J : Finset S) :
    (globalRetained S J).card = J.card := card_map _

lemma globalRetained_disjoint {N : ℕ} (S : Finset (Fin N))
    (J : Finset S) (K : Finset (Sᶜ : Finset (Fin N))) :
    Disjoint (globalRetained S J) (globalRetained Sᶜ K) := by
  apply disjoint_left.mpr
  intro i hi hj
  exact (mem_compl.mp (globalRetained_subset Sᶜ K hj)) (globalRetained_subset S J hi)

/-- Coordinate restriction along the inclusion of the retained sites in the
original tensor. -/
def globalRetainedIndex {N : ℕ} (d : Fin N → ℕ) (S : Finset (Fin N)) (J : Finset S)
    (u : FiniteSites.RetainedIndex d (globalRetained S J)) :
    FiniteSites.RetainedIndex (fun i : S => d i) J :=
  fun j => u ⟨j.val.val, mem_map.mpr ⟨j.val, j.property, rfl⟩⟩

lemma globalRetainedIndex_surjective {N : ℕ} (d : Fin N → ℕ)
    (S : Finset (Fin N)) (J : Finset S) :
    Function.Surjective (globalRetainedIndex d S J) := by
  intro u
  let v : FiniteSites.RetainedIndex d (globalRetained S J) := fun i =>
    u ⟨⟨i.val, ((mem_globalRetained S J i).mp i.property).choose⟩,
      ((mem_globalRetained S J i).mp i.property).choose_spec⟩
  refine ⟨v, ?_⟩
  funext j
  rfl

/-- Combine the independently chosen contraction covectors on the two sides
of the original cut into one covector family. -/
def cutCovectors {N : ℕ} (d : Fin N → ℕ) (S : Finset (Fin N))
    (b : FiniteSites.Covectors (fun i : S => d i))
    (c : FiniteSites.Covectors (fun i : (Sᶜ : Finset (Fin N)) => d i)) :
    FiniteSites.Covectors d :=
  fun i => if hi : i ∈ S then b ⟨i, hi⟩ else c ⟨i, mem_compl.mpr hi⟩

/-- The original tensor contracted on every site outside the two anchors.
The two output coordinates refer to the actual original anchor sites. -/
def anchorContract {N : ℕ} (d : Fin N → ℕ) (T : Coeffs d)
    (L R : Finset (Fin N)) (q : FiniteSites.Covectors d)
    (u : FiniteSites.RetainedIndex d L) (v : FiniteSites.RetainedIndex d R) : ℂ :=
  ∑ w, T w * ∏ i, if hi : i ∈ L then (if w i = u ⟨i, hi⟩ then 1 else 0)
    else if hj : i ∈ R then (if w i = v ⟨i, hj⟩ then 1 else 0) else q i (w i)

def siteCutIndexEquiv {N : ℕ} (d : Fin N → ℕ) (S : Finset (Fin N)) :
    FiniteSites.TensorIndex d ≃
      FiniteSites.TensorIndex (fun i : S => d i) ×
      FiniteSites.TensorIndex (fun i : (Sᶜ : Finset (Fin N)) => d i) where
  toFun w := (fun i => w i, fun i => w i)
  invFun xy i := if hi : i ∈ S then xy.1 ⟨i, hi⟩ else xy.2 ⟨i, mem_compl.mpr hi⟩
  left_inv w := by funext i; dsimp; split_ifs <;> rfl
  right_inv xy := by
    apply Prod.ext
    · funext i; exact dif_pos i.property
    · funext i; exact dif_neg (mem_compl.mp i.property)

lemma prod_cut_partition {N : ℕ} (S : Finset (Fin N)) (f : Fin N → ℂ) :
    (∏ i : S, f i) * (∏ i : (Sᶜ : Finset (Fin N)), f i) = ∏ i, f i := by
  rw [← Finset.prod_subtype S (by simp), ← Finset.prod_subtype Sᶜ (by simp)]
  exact prod_mul_prod_compl S f

/-- Exact identification of the two sidewise contractions with the original
product contraction outside the global retained anchor sets. -/
lemma anchorContract_globalRetained {N : ℕ} (d : Fin N → ℕ) (T : Coeffs d)
    (S : Finset (Fin N)) (J : Finset S) (K : Finset (Sᶜ : Finset (Fin N)))
    (b : FiniteSites.Covectors (fun i : S => d i))
    (c : FiniteSites.Covectors (fun i : (Sᶜ : Finset (Fin N)) => d i))
    (u : FiniteSites.RetainedIndex d (globalRetained S J))
    (v : FiniteSites.RetainedIndex d (globalRetained Sᶜ K)) :
    anchorContract d T (globalRetained S J) (globalRetained Sᶜ K) (cutCovectors d S b c) u v =
      FiniteSites.retainedContract
        (fun i => FiniteSites.retainedContract (siteCutMatrix d T S i) K c
          (globalRetainedIndex d Sᶜ K v)) J b (globalRetainedIndex d S J u) := by
  classical
  let W : FiniteSites.TensorIndex d → Fin N → ℂ := fun w i =>
    if hi : i ∈ globalRetained S J then (if w i = u ⟨i, hi⟩ then 1 else 0)
    else if hj : i ∈ globalRetained Sᶜ K then (if w i = v ⟨i, hj⟩ then 1 else 0)
    else cutCovectors d S b c i (w i)
  have hA (x : FiniteSites.TensorIndex (fun i : S => d i))
      (y : FiniteSites.TensorIndex (fun i : (Sᶜ : Finset (Fin N)) => d i)) :
      (∏ i : S, W ((siteCutIndexEquiv d S).symm (x,y)) i) =
        ∏ i : S, if hi : i ∈ J then
          (if x i = globalRetainedIndex d S J u ⟨i,hi⟩ then 1 else 0) else b i (x i) := by
    apply prod_congr rfl
    intro i _
    have hL : i.val ∈ globalRetained S J ↔ i ∈ J := by simp
    have hR : i.val ∉ globalRetained Sᶜ K := by
      intro h
      exact (mem_compl.mp (globalRetained_subset Sᶜ K h)) i.property
    by_cases hi : i ∈ J
    · simp [W, hL.mpr hi, siteCutIndexEquiv, i.property, globalRetainedIndex, hi]
    · simp [W, hL.not.mpr hi, hR, cutCovectors, siteCutIndexEquiv, i.property, hi]
  have hB (x : FiniteSites.TensorIndex (fun i : S => d i))
      (y : FiniteSites.TensorIndex (fun i : (Sᶜ : Finset (Fin N)) => d i)) :
      (∏ i : (Sᶜ : Finset (Fin N)), W ((siteCutIndexEquiv d S).symm (x,y)) i) =
        ∏ i : (Sᶜ : Finset (Fin N)), if hi : i ∈ K then
          (if y i = globalRetainedIndex d Sᶜ K v ⟨i,hi⟩ then 1 else 0) else c i (y i) := by
    apply prod_congr rfl
    intro i _
    have hiS : i.val ∉ S := mem_compl.mp i.property
    have hL : i.val ∉ globalRetained S J := by
      intro h
      exact hiS (globalRetained_subset S J h)
    have hR : i.val ∈ globalRetained Sᶜ K ↔ i ∈ K := by simp
    by_cases hi : i ∈ K
    · simp [W, hL, hR.mpr hi, siteCutIndexEquiv, hiS, globalRetainedIndex, hi]
    · simp [W, hL, hR.not.mpr hi, cutCovectors, siteCutIndexEquiv, hiS, hi]
  change (∑ w, T w * ∏ i, W w i) = _
  rw [← (siteCutIndexEquiv d S).symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  unfold FiniteSites.retainedContract
  simp only [Finset.sum_mul]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  rw [← prod_cut_partition S, hA, hB]
  change T ((siteCutIndexEquiv d S).symm (x,y)) * (_ * _) =
    T ((siteCutIndexEquiv d S).symm (x,y)) * _ * _
  ring

/-- Nonempty disjoint anchors of the original tensor, with at most `r-1`
sites each and a rank-`r` true product-contracted core. -/
theorem exists_original_anchor_core_of_cut {N : ℕ} (d : Fin N → ℕ)
    (T : Coeffs d) (hT : T ≠ 0) (S : Finset (Fin N)) (r : ℕ)
    (hr : 2 ≤ r) (hS : schmidtRank d T S = r) :
    ∃ (L R : Finset (Fin N)) (q : FiniteSites.Covectors d),
      L.Nonempty ∧ R.Nonempty ∧ Disjoint L R ∧
      L.card ≤ r - 1 ∧ R.card ≤ r - 1 ∧ L ⊆ S ∧ R ⊆ Sᶜ ∧
      Module.finrank ℂ (Submodule.span ℂ (Set.range (anchorContract d T L R q))) = r := by
  classical
  obtain ⟨J, K, b, c, hJn, hKn, hJ, hK, hcore⟩ :=
    exists_retained_anchors_of_maximal_cut d T hT S r hr hS
  refine ⟨globalRetained S J, globalRetained Sᶜ K, cutCovectors d S b c,
    ?_, ?_, globalRetained_disjoint S J K, by simpa using hJ, by simpa using hK,
    globalRetained_subset S J, globalRetained_subset Sᶜ K, ?_⟩
  · obtain ⟨j, hj⟩ := hJn
    exact ⟨j.val, mem_map.mpr ⟨j, hj, rfl⟩⟩
  · obtain ⟨k, hk⟩ := hKn
    exact ⟨k.val, mem_map.mpr ⟨k, hk, rfl⟩⟩
  · let M := fun u v => FiniteSites.retainedContract
      (fun i => FiniteSites.retainedContract (siteCutMatrix d T S i) K c v) J b u
    have hm : anchorContract d T (globalRetained S J) (globalRetained Sᶜ K) (cutCovectors d S b c) =
        fun u v => M (globalRetainedIndex d S J u) (globalRetainedIndex d Sᶜ K v) := by
      funext u v
      exact anchorContract_globalRetained d T S J K b c u v
    rw [hm]
    exact (rowSpan_finrank_surjective_reindex M
      (globalRetainedIndex d S J) (globalRetainedIndex d Sᶜ K)
      (globalRetainedIndex_surjective d S J) (globalRetainedIndex_surjective d Sᶜ K)).trans hcore

/-- The rank-`r` retained anchor core follows from the original maximal
Schmidt rank, without any normalization or support-reconstruction premise. -/
theorem exists_original_anchor_core {N : ℕ} (d : Fin N → ℕ) (hN : 2 ≤ N)
    (T : Coeffs d) (hT : T ≠ 0) (hr : 2 ≤ maxSchmidtRank d T) :
    ∃ (L R : Finset (Fin N)) (q : FiniteSites.Covectors d),
      L.Nonempty ∧ R.Nonempty ∧ Disjoint L R ∧
      L.card ≤ maxSchmidtRank d T - 1 ∧ R.card ≤ maxSchmidtRank d T - 1 ∧
      Module.finrank ℂ (Submodule.span ℂ (Set.range (anchorContract d T L R q))) =
        maxSchmidtRank d T := by
  obtain ⟨S, _, _, hS⟩ := maxSchmidtRank_attained hN T hT
  obtain ⟨L, R, q, hL, hR, hLR, hcL, hcR, _, _, hcore⟩ :=
    exists_original_anchor_core_of_cut d T hT S (maxSchmidtRank d T) hr hS
  exact ⟨L, R, q, hL, hR, hLR, hcL, hcR, hcore⟩

end UniformBorderRank
