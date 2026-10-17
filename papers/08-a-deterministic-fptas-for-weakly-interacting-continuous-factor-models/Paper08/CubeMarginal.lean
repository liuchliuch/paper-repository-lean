import Paper08.MultiMoments
import Mathlib.MeasureTheory.Integral.Pi

/-! # Actual partial expectations on the finite unit cube -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Set
namespace Paper08.CubeMarginal
open MultiMoments

def box (ι : Type*) : Set (ι → ℝ) := Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1

lemma mem_box {ι : Type*} {x : ι → ℝ} : x ∈ box ι ↔ ∀ i, 0 ≤ x i ∧ x i ≤ 1 := by
  change (∀ i, i ∈ Set.univ → 0 ≤ x i ∧ x i ≤ 1) ↔ _
  simp

lemma isCompact_box (ι : Type*) : IsCompact (box ι) :=
  isCompact_univ_pi fun _ => isCompact_Icc

lemma measurableSet_box (ι : Type*) [Fintype ι] : MeasurableSet (box ι) :=
  MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Icc

lemma unitMeasure_eq_restrict (ι : Type*) [Fintype ι] :
    unitMeasure ι = volume.restrict (box ι) := by
  rw [volume_pi, box, Measure.restrict_pi_pi]
  rfl

lemma ae_mem_box (ι : Type*) [Fintype ι] : ∀ᵐ y ∂unitMeasure ι, y ∈ box ι := by
  rw [unitMeasure_eq_restrict]
  exact ae_restrict_mem (measurableSet_box ι)

/-- Replace precisely the coordinates being averaged; all others stay frozen. -/
def overwrite {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ℝ) (y : S → ℝ) : Fin n → ℝ :=
  fun i => if hi : i ∈ S then y ⟨i, hi⟩ else x i

@[simp] lemma overwrite_of_mem {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ℝ)
    (y : S → ℝ) {i : Fin n} (hi : i ∈ S) : overwrite S x y i = y ⟨i, hi⟩ := by
  simp [overwrite, hi]

@[simp] lemma overwrite_of_notMem {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ℝ)
    (y : S → ℝ) {i : Fin n} (hi : i ∉ S) : overwrite S x y i = x i := by
  simp [overwrite, hi]

lemma overwrite_mem_cube {n : ℕ} (S : Finset (Fin n)) {x : Fin n → ℝ}
    (hx : x ∈ Integral.cube n) {y : S → ℝ} (hy : y ∈ box S) :
    overwrite S x y ∈ Integral.cube n := by
  rw [Integral.mem_cube] at hx ⊢
  rw [mem_box] at hy
  intro i
  by_cases hi : i ∈ S
  · simpa [overwrite, hi] using hy ⟨i, hi⟩
  · simpa [overwrite, hi] using hx i

lemma continuous_overwrite_left {n : ℕ} (S : Finset (Fin n)) (y : S → ℝ) :
    Continuous (fun x : Fin n → ℝ => overwrite S x y) := by
  apply continuous_pi
  intro i
  by_cases hi : i ∈ S
  · simpa [overwrite, hi] using (continuous_const : Continuous (fun _ : Fin n → ℝ => y ⟨i, hi⟩))
  · simpa [overwrite, hi] using (continuous_apply i : Continuous (fun x : Fin n → ℝ => x i))

lemma continuous_overwrite_right {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ℝ) :
    Continuous (overwrite S x) := by
  apply continuous_pi
  intro i
  by_cases hi : i ∈ S
  · simpa [overwrite, hi] using (continuous_apply (⟨i, hi⟩ : S) : Continuous (fun y : S → ℝ => y ⟨i, hi⟩))
  · simpa [overwrite, hi] using (continuous_const : Continuous (fun _ : S → ℝ => x i))

/-- Partial expectation under the actual product uniform probability measure. -/
def avg {n : ℕ} (S : Finset (Fin n)) (f : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) : ℂ :=
  ∫ y, f (overwrite S x y) ∂unitMeasure S

@[simp] theorem avg_empty {n : ℕ} (f : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) :
    avg ∅ f x = f x := by
  have hh : ∀ y : (∅ : Finset (Fin n)) → ℝ, overwrite ∅ x y = x := by
    intro y; funext i; simp [overwrite]
  simp only [avg, hh]
  simp

@[simp] theorem avg_const {n : ℕ} (S : Finset (Fin n)) (a : ℂ) (x : Fin n → ℝ) :
    avg S (fun _ => a) x = a := by simp [avg]

theorem avg_congr {n : ℕ} (S : Finset (Fin n)) {f g : (Fin n → ℝ) → ℂ}
    (hfg : ∀ y ∈ Integral.cube n, f y = g y) {x : Fin n → ℝ} (hx : x ∈ Integral.cube n) :
    avg S f x = avg S g x := by
  apply integral_congr_ae
  exact (ae_mem_box S).mono fun y hy => hfg _ (overwrite_mem_cube S hx hy)

theorem avg_eq_of_agree_compl {n : ℕ} (S : Finset (Fin n)) (f : (Fin n → ℝ) → ℂ)
    {x x' : Fin n → ℝ} (hxx' : ∀ i ∉ S, x i = x' i) : avg S f x = avg S f x' := by
  apply integral_congr_ae
  filter_upwards with y
  congr 1
  funext i
  by_cases hi : i ∈ S <;> simp [overwrite, hi, hxx']

/-- Updating a frozen coordinate commutes with the actual partial expectation. -/
theorem avg_update {n : ℕ} (S : Finset (Fin n)) (f : (Fin n → ℝ) → ℂ)
    (x : Fin n → ℝ) (j : Fin n) (a : ℝ) (hj : j ∉ S) :
    avg S f (Function.update x j a) = avg S (fun y => f (Function.update y j a)) x := by
  apply integral_congr_ae
  filter_upwards with y
  congr 1
  funext i
  by_cases hij : i = j
  · subst i; simp [overwrite, hj]
  · by_cases hi : i ∈ S <;> simp [overwrite, hi, Function.update_of_ne hij]

theorem integrable_section {n : ℕ} (S : Finset (Fin n)) {f : (Fin n → ℝ) → ℂ}
    (hf : ContinuousOn f (Integral.cube n)) {x : Fin n → ℝ} (hx : x ∈ Integral.cube n) :
    Integrable (fun y => f (overwrite S x y)) (unitMeasure S) := by
  rw [unitMeasure_eq_restrict]
  apply ContinuousOn.integrableOn_compact (isCompact_box S)
  exact hf.comp (continuous_overwrite_right S x).continuousOn (fun _ hy => overwrite_mem_cube S hx hy)

theorem continuousOn_avg {n : ℕ} (S : Finset (Fin n)) {f : (Fin n → ℝ) → ℂ}
    (hf : ContinuousOn f (Integral.cube n)) : ContinuousOn (avg S f) (Integral.cube n) := by
  obtain ⟨M, hM⟩ := (ZeroFree.isCompact_cube n).exists_bound_of_continuousOn hf
  apply continuousOn_of_dominated (bound := fun _ : S → ℝ => M)
  · intro x hx
    exact (integrable_section S hf hx).aestronglyMeasurable
  · intro x hx
    exact (ae_mem_box S).mono fun y hy => hM _ (overwrite_mem_cube S hx hy)
  · exact integrable_const M
  · exact (ae_mem_box S).mono fun y hy =>
      hf.comp (continuous_overwrite_left S y).continuousOn (fun _ hx => overwrite_mem_cube S hx hy)

theorem integrable_avg {n : ℕ} (S : Finset (Fin n)) {f : (Fin n → ℝ) → ℂ}
    (hf : ContinuousOn f (Integral.cube n)) : IntegrableOn (avg S f) (Integral.cube n) :=
  (continuousOn_avg S hf).integrableOn_compact (ZeroFree.isCompact_cube n)

theorem norm_avg_le {n : ℕ} (S : Finset (Fin n)) {f : (Fin n → ℝ) → ℂ} {M : ℝ}
    (hM : ∀ y ∈ Integral.cube n, ‖f y‖ ≤ M) {x : Fin n → ℝ} (hx : x ∈ Integral.cube n) :
    ‖avg S f x‖ ≤ M := by
  have h := norm_integral_le_of_norm_le_const
    ((ae_mem_box S).mono fun y hy => hM _ (overwrite_mem_cube S hx hy))
  simpa [avg] using h

theorem norm_avg_le_integral_norm {n : ℕ} (S : Finset (Fin n))
    (f : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) :
    ‖avg S f x‖ ≤ ∫ y, ‖f (overwrite S x y)‖ ∂unitMeasure S := norm_integral_le_integral_norm _

theorem avg_const_mul {n : ℕ} (S : Finset (Fin n)) (a : ℂ)
    (f : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) :
    avg S (fun y => a * f y) x = a * avg S f x := integral_const_mul _ _

theorem avg_mul_const {n : ℕ} (S : Finset (Fin n)) (a : ℂ)
    (f : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) :
    avg S (fun y => f y * a) x = avg S f x * a := integral_mul_const _ _

/-- A multiplier on disjoint coordinates is pulled out by genuine scope dependence. -/
theorem avg_mul_of_depends {n : ℕ} (S T : Finset (Fin n)) (hST : Disjoint S T)
    (f g : (Fin n → ℝ) → ℂ)
    (hg : ∀ x ∈ Integral.cube n, ∀ y ∈ Integral.cube n,
      (∀ i ∈ T, x i = y i) → g x = g y)
    {x : Fin n → ℝ} (hx : x ∈ Integral.cube n) :
    avg S (fun y => g y * f y) x = g x * avg S f x := by
  rw [← avg_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_mem_box S] with y hy
  rw [hg _ (overwrite_mem_cube S hx hy) x hx]
  intro i hi
  exact overwrite_of_notMem S x y (fun hs => Finset.disjoint_left.mp hST hs hi)

/-- Real-valued partial expectation on the same product probability space. -/
def realAvg {n : ℕ} (S : Finset (Fin n)) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∫ y, f (overwrite S x y) ∂unitMeasure S

@[simp] theorem avg_ofReal {n : ℕ} (S : Finset (Fin n)) (f : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) : avg S (fun y => (f y : ℂ)) x = (realAvg S f x : ℂ) := integral_ofReal

@[simp] theorem realAvg_empty {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    realAvg ∅ f x = f x := by
  apply Complex.ofReal_injective
  rw [← avg_ofReal, avg_empty]

theorem integrable_real_section {n : ℕ} (S : Finset (Fin n)) {f : (Fin n → ℝ) → ℝ}
    (hf : ContinuousOn f (Integral.cube n)) {x : Fin n → ℝ} (hx : x ∈ Integral.cube n) :
    Integrable (fun y => f (overwrite S x y)) (unitMeasure S) := by
  rw [unitMeasure_eq_restrict]
  apply ContinuousOn.integrableOn_compact (isCompact_box S)
  exact hf.comp (continuous_overwrite_right S x).continuousOn (fun _ hy => overwrite_mem_cube S hx hy)

theorem continuousOn_realAvg {n : ℕ} (S : Finset (Fin n)) {f : (Fin n → ℝ) → ℝ}
    (hf : ContinuousOn f (Integral.cube n)) : ContinuousOn (realAvg S f) (Integral.cube n) := by
  have hc := Complex.continuous_re.comp_continuousOn
    (continuousOn_avg S (Complex.continuous_ofReal.comp_continuousOn hf))
  change ContinuousOn (fun x => (avg S (fun y => (f y : ℂ)) x).re) (Integral.cube n) at hc
  simpa only [avg_ofReal, Complex.ofReal_re] using hc

theorem realAvg_mono {n : ℕ} (S : Finset (Fin n)) {f g : (Fin n → ℝ) → ℝ}
    (hf : ContinuousOn f (Integral.cube n)) (hg : ContinuousOn g (Integral.cube n))
    (hfg : ∀ y ∈ Integral.cube n, f y ≤ g y) {x : Fin n → ℝ} (hx : x ∈ Integral.cube n) :
    realAvg S f x ≤ realAvg S g x :=
  integral_mono_ae (integrable_real_section S hf hx) (integrable_real_section S hg hx)
    ((ae_mem_box S).mono fun _y hy => hfg _ (overwrite_mem_cube S hx hy))

theorem realAvg_const_mul {n : ℕ} (S : Finset (Fin n)) (a : ℝ)
    (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    realAvg S (fun y => a * f y) x = a * realAvg S f x := integral_const_mul _ _

theorem realAvg_nonneg {n : ℕ} (S : Finset (Fin n)) {f : (Fin n → ℝ) → ℝ}
    (hf : ∀ y ∈ Integral.cube n, 0 ≤ f y) {x : Fin n → ℝ} (hx : x ∈ Integral.cube n) :
    0 ≤ realAvg S f x :=
  integral_nonneg_of_ae ((ae_mem_box S).mono fun _y hy => hf _ (overwrite_mem_cube S hx hy))

theorem avg_univ {n : ℕ} (f : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) :
    avg Finset.univ f x = ∫ y in Integral.cube n, f y := by
  let e : Fin n ≃ (Finset.univ : Finset (Fin n)) :=
    (Equiv.subtypeUnivEquiv (fun i : Fin n => Finset.mem_univ i)).symm
  let em := MeasurableEquiv.piCongrLeft (fun _ : (Finset.univ : Finset (Fin n)) => ℝ) e
  have hp := measurePreserving_piCongrLeft
    (fun _ : (Finset.univ : Finset (Fin n)) => intervalMeasure) e
  have he : ∀ y : Fin n → ℝ, overwrite Finset.univ x (em y) = y := by
    intro y; funext i
    simp [overwrite, em, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, e]
  have hi := hp.integral_comp em.measurableEmbedding
    (fun y => f (overwrite Finset.univ x y))
  change (∫ y, f (overwrite Finset.univ x (em y)) ∂unitMeasure (Fin n)) = avg Finset.univ f x at hi
  simp only [he] at hi
  rw [← hi, unitMeasure_fin]

theorem avg_singleton {n : ℕ} (j : Fin n) (f : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) :
    avg {j} f x = ∫ a in Set.Icc (0 : ℝ) 1, f (Function.update x j a) := by
  letI : Unique (↥({j} : Finset (Fin n))) :=
    ⟨⟨⟨j, by simp⟩⟩, fun i => Subtype.ext (Finset.mem_singleton.mp i.property)⟩
  let em := MeasurableEquiv.piUnique (fun _ : (↥({j} : Finset (Fin n))) => ℝ)
  have hp := measurePreserving_piUnique (fun _ : (↥({j} : Finset (Fin n))) => intervalMeasure)
  have he : ∀ y : (↥({j} : Finset (Fin n))) → ℝ,
      overwrite {j} x y = Function.update x j (em y) := by
    intro y; funext i
    by_cases hi : i = j
    · subst i
      simp [overwrite, em, MeasurableEquiv.piUnique]
      exact congrArg y (Subsingleton.elim _ _)
    · simp [overwrite, hi]
  have hi := hp.integral_comp em.measurableEmbedding (fun a => f (Function.update x j a))
  simpa only [avg, he, intervalMeasure] using hi

lemma union_join_left {n : ℕ} {S T : Finset (Fin n)} (hST : Disjoint S T)
    (y : S → ℝ) (z : T → ℝ) (i : S) :
    MeasurableEquiv.piFinsetUnion (fun _ : Fin n => ℝ) hST (y, z)
      ⟨i, Finset.mem_union.mpr (Or.inl i.property)⟩ = y i := by
  change Equiv.piCongrLeft (fun _ : (S ∪ T : Finset (Fin n)) => ℝ) (Equiv.Finset.union S T hST)
    _ (Equiv.Finset.union S T hST (Sum.inl i)) = _
  rw [Equiv.piCongrLeft_apply_apply]
  rfl

lemma union_join_right {n : ℕ} {S T : Finset (Fin n)} (hST : Disjoint S T)
    (y : S → ℝ) (z : T → ℝ) (i : T) :
    MeasurableEquiv.piFinsetUnion (fun _ : Fin n => ℝ) hST (y, z)
      ⟨i, Finset.mem_union.mpr (Or.inr i.property)⟩ = z i := by
  change Equiv.piCongrLeft (fun _ : (S ∪ T : Finset (Fin n)) => ℝ) (Equiv.Finset.union S T hST)
    _ (Equiv.Finset.union S T hST (Sum.inr i)) = _
  rw [Equiv.piCongrLeft_apply_apply]
  rfl

lemma overwrite_union {n : ℕ} {S T : Finset (Fin n)} (hST : Disjoint S T)
    (x : Fin n → ℝ) (y : S → ℝ) (z : T → ℝ) :
    overwrite S (overwrite T x z) y = overwrite (S ∪ T) x
      (MeasurableEquiv.piFinsetUnion (fun _ : Fin n => ℝ) hST (y, z)) := by
  funext i
  by_cases hiS : i ∈ S
  · have hiU : i ∈ S ∪ T := Finset.mem_union.mpr (Or.inl hiS)
    rw [overwrite_of_mem S _ _ hiS, overwrite_of_mem (S ∪ T) _ _ hiU]
    exact (union_join_left hST y z ⟨i, hiS⟩).symm
  · by_cases hiT : i ∈ T
    · have hiU : i ∈ S ∪ T := Finset.mem_union.mpr (Or.inr hiT)
      rw [overwrite_of_notMem S _ _ hiS, overwrite_of_mem T _ _ hiT,
        overwrite_of_mem (S ∪ T) _ _ hiU]
      exact (union_join_right hST y z ⟨i, hiT⟩).symm
    · simp [overwrite, hiS, hiT]

/-- Actual finite-coordinate Fubini, with no factorization premise. -/
theorem avg_union {n : ℕ} (S T : Finset (Fin n)) (hST : Disjoint S T)
    {f : (Fin n → ℝ) → ℂ} (hf : ContinuousOn f (Integral.cube n))
    {x : Fin n → ℝ} (hx : x ∈ Integral.cube n) :
    avg (S ∪ T) f x = avg T (avg S f) x := by
  let e := MeasurableEquiv.piFinsetUnion (fun _ : Fin n => ℝ) hST
  have hp := measurePreserving_piFinsetUnion hST (fun _ : Fin n => intervalMeasure)
  have hi := hp.integral_comp e.measurableEmbedding (fun y => f (overwrite (S ∪ T) x y))
  have hint := hp.integrable_comp_of_integrable (integrable_section (S ∪ T) hf hx)
  change Integrable (fun p : (S → ℝ) × (T → ℝ) => f (overwrite (S ∪ T) x (e p)))
    ((unitMeasure S).prod (unitMeasure T)) at hint
  change (∫ p : (S → ℝ) × (T → ℝ), f (overwrite (S ∪ T) x (e p))
    ∂(unitMeasure S).prod (unitMeasure T)) = avg (S ∪ T) f x at hi
  rw [← hi, integral_prod_symm _ hint]
  unfold avg
  apply integral_congr_ae
  filter_upwards with z
  apply integral_congr_ae
  filter_upwards with y
  rw [overwrite_union hST x y z]

theorem avg_insert {n : ℕ} (S : Finset (Fin n)) (j : Fin n) (hj : j ∉ S)
    {f : (Fin n → ℝ) → ℂ} (hf : ContinuousOn f (Integral.cube n))
    {x : Fin n → ℝ} (hx : x ∈ Integral.cube n) :
    avg (insert j S) f x = avg {j} (avg S f) x := by
  have hd : Disjoint S {j} := Finset.disjoint_singleton_right.mpr hj
  simpa only [Finset.union_singleton] using avg_union S {j} hd hf hx

theorem realAvg_union {n : ℕ} (S T : Finset (Fin n)) (hST : Disjoint S T)
    {f : (Fin n → ℝ) → ℝ} (hf : ContinuousOn f (Integral.cube n))
    {x : Fin n → ℝ} (hx : x ∈ Integral.cube n) :
    realAvg (S ∪ T) f x = realAvg T (realAvg S f) x := by
  apply Complex.ofReal_injective
  have he := avg_union S T hST (Complex.continuous_ofReal.comp_continuousOn hf) hx
  change avg (S ∪ T) (fun y => (f y : ℂ)) x = avg T (avg S (fun y => (f y : ℂ))) x at he
  have hinner : avg S (fun y => (f y : ℂ)) = fun y => (realAvg S f y : ℂ) :=
    funext fun y => avg_ofReal S f y
  rw [hinner] at he
  simpa only [avg_ofReal] using he

theorem realAvg_insert {n : ℕ} (S : Finset (Fin n)) (j : Fin n) (hj : j ∉ S)
    {f : (Fin n → ℝ) → ℝ} (hf : ContinuousOn f (Integral.cube n))
    {x : Fin n → ℝ} (hx : x ∈ Integral.cube n) :
    realAvg (insert j S) f x = realAvg {j} (realAvg S f) x := by
  have hd : Disjoint S {j} := Finset.disjoint_singleton_right.mpr hj
  simpa only [Finset.union_singleton] using realAvg_union S {j} hd hf hx

theorem realAvg_congr {n : ℕ} (S : Finset (Fin n)) {f g : (Fin n → ℝ) → ℝ}
    (hfg : ∀ y ∈ Integral.cube n, f y = g y) {x : Fin n → ℝ} (hx : x ∈ Integral.cube n) :
    realAvg S f x = realAvg S g x := by
  apply integral_congr_ae
  exact (ae_mem_box S).mono fun y hy => hfg _ (overwrite_mem_cube S hx hy)

theorem realAvg_singleton {n : ℕ} (j : Fin n) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    realAvg {j} f x = ∫ a in Set.Icc (0 : ℝ) 1, f (Function.update x j a) := by
  apply Complex.ofReal_injective
  rw [← avg_ofReal, avg_singleton]
  exact integral_ofReal

theorem realAvg_univ {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    realAvg Finset.univ f x = Integral.cubeIntegral f := by
  apply Complex.ofReal_injective
  rw [← avg_ofReal, avg_univ]
  exact integral_ofReal

theorem norm_avg_le_realAvg_norm {n : ℕ} (S : Finset (Fin n))
    (f : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) :
    ‖avg S f x‖ ≤ realAvg S (fun y => ‖f y‖) x := norm_integral_le_integral_norm _

theorem avg_update_mem {n : ℕ} (S : Finset (Fin n)) (f : (Fin n → ℝ) → ℂ)
    (x : Fin n → ℝ) (j : Fin n) (a : ℝ) (hj : j ∈ S) :
    avg S f (Function.update x j a) = avg S f x := by
  apply avg_eq_of_agree_compl
  intro i hi
  have hij : i ≠ j := by intro he; subst i; exact hi hj
  simp [Function.update_of_ne hij]

theorem avg_add {n : ℕ} (S : Finset (Fin n)) {f g : (Fin n → ℝ) → ℂ}
    (hf : ContinuousOn f (Integral.cube n)) (hg : ContinuousOn g (Integral.cube n))
    {x : Fin n → ℝ} (hx : x ∈ Integral.cube n) :
    avg S (fun y => f y + g y) x = avg S f x + avg S g x :=
  integral_add (integrable_section S hf hx) (integrable_section S hg hx)

theorem avg_sub {n : ℕ} (S : Finset (Fin n)) {f g : (Fin n → ℝ) → ℂ}
    (hf : ContinuousOn f (Integral.cube n)) (hg : ContinuousOn g (Integral.cube n))
    {x : Fin n → ℝ} (hx : x ∈ Integral.cube n) :
    avg S (fun y => f y - g y) x = avg S f x - avg S g x :=
  integral_sub (integrable_section S hf hx) (integrable_section S hg hx)

theorem avg_comm {n : ℕ} (S T : Finset (Fin n)) (hST : Disjoint S T)
    {f : (Fin n → ℝ) → ℂ} (hf : ContinuousOn f (Integral.cube n))
    {x : Fin n → ℝ} (hx : x ∈ Integral.cube n) :
    avg T (avg S f) x = avg S (avg T f) x := by
  rw [← avg_union S T hST hf hx, ← avg_union T S hST.symm hf hx, Finset.union_comm]

/-- Split the integrated set and pull a scoped multiplier through the block
on which it is independent. This supplies the scope-intersection step of
partial-expectation induction directly from actual Fubini and scope dependence. -/
theorem avg_union_mul_of_depends {n : ℕ} (S T U : Finset (Fin n))
    (hST : Disjoint S T) (hSU : Disjoint S U)
    {f g : (Fin n → ℝ) → ℂ} (hf : ContinuousOn f (Integral.cube n))
    (hg : ContinuousOn g (Integral.cube n))
    (hdep : ∀ x ∈ Integral.cube n, ∀ y ∈ Integral.cube n,
      (∀ i ∈ U, x i = y i) → g x = g y)
    {x : Fin n → ℝ} (hx : x ∈ Integral.cube n) :
    avg (S ∪ T) (fun y => g y * f y) x = avg T (fun y => g y * avg S f y) x := by
  rw [avg_union S T hST (hg.mul hf) hx]
  apply avg_congr T _ hx
  intro y hy
  exact avg_mul_of_depends S U hSU f g hdep hy

end Paper08.CubeMarginal
