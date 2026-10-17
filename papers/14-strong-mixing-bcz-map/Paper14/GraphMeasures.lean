import Paper14.KacExcess
import Paper14.GraphDecomposition
import Paper14.ExcessCriterion
open MeasureTheory Measure Filter Set Function
open scoped ENNReal
namespace Paper14
noncomputable section

def graphMeasure {α : Type*} [MeasurableSpace α]
    (S : α → α) (ν : Measure α) : Measure (α × α) :=
  Measure.map (fun x => (x, S x)) ν

lemma measurable_graph {α : Type*} [MeasurableSpace α] {S : α → α}
    (hS : Measurable S) : Measurable (fun x => (x, S x)) := measurable_id.prodMk hS

def excessGraphMeasure {α : Type*} [MeasurableSpace α]
    (T : α → α) (μ : Measure α) (Y : Set α) (n j : ℕ) : Measure (α × α) :=
  graphMeasure (T^[n]) ((normalizedRestriction μ Y).restrict (excessLevel T Y n j))

def secondShift {α : Type*} (T : α → α) : α × α → α × α := fun p => (p.1, T p.2)

lemma secondShift_iterate {α : Type*} (T : α → α) (j : ℕ) (x y : α) :
    (secondShift T)^[j] (x, y) = (x, T^[j] y) := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [iterate_succ_apply', ih, secondShift]

lemma measurable_Rn {α : Type*} [MeasurableSpace α] {T : α → α} {Y : Set α}
    (hT : Measurable T) (hY : MeasurableSet Y) (n : ℕ) : Measurable (Rn T Y n) := by
  unfold Rn
  apply Finset.measurable_sum
  intro i hi
  exact (measurable_firstReturn hT hY).comp ((measurable_inducedMap hT hY).iterate i)

lemma measurable_excessDn {α : Type*} [MeasurableSpace α] {T : α → α} {Y : Set α}
    (hT : Measurable T) (hY : MeasurableSet Y) (n : ℕ) : Measurable (excessDn T Y n) :=
  (measurable_Rn hT hY n).sub_const n

lemma excess_partition_union {α : Type*} (T : α → α) (Y : Set α) (n : ℕ) :
    (⋃ j : ℕ, excessLevel T Y n j) = Y := by
  ext x
  simp only [mem_iUnion, mem_excessLevel]
  exact ⟨fun ⟨_, hx, _⟩ => hx, fun hx => ⟨excessDn T Y n x, hx, rfl⟩⟩

lemma normalizedRestriction_restrict {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {Y : Set α} (hY : MeasurableSet Y) :
    (normalizedRestriction μ Y).restrict Y = normalizedRestriction μ Y := by
  simp only [normalizedRestriction, Measure.restrict_smul, Measure.restrict_restrict hY, inter_self]

lemma normalizedRestriction_ae_mem {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {Y : Set α} (hY : MeasurableSet Y) :
    ∀ᵐ x ∂normalizedRestriction μ Y, x ∈ Y :=
  Measure.ae_smul_measure (ae_restrict_mem hY) ((μ Y)⁻¹)

lemma excess_partition_measure {α : Type*} [MeasurableSpace α] {T : α → α}
    (μ : Measure α) {Y : Set α} (hT : Measurable T) (hY : MeasurableSet Y) (n : ℕ) :
    Measure.sum (fun j => (normalizedRestriction μ Y).restrict (excessLevel T Y n j)) =
      normalizedRestriction μ Y := by
  rw [← Measure.restrict_iUnion (fun j k hjk => disjoint_excessLevel hjk)]
  · rw [excess_partition_union, normalizedRestriction_restrict μ hY]
  · intro j
    exact hY.inter ((measurableSet_singleton j).preimage (measurable_excessDn hT hY n))

/-- The first finite-time decomposition in paper Ex25. -/
theorem sum_excessGraphMeasure {α : Type*} [MeasurableSpace α] {T : α → α}
    (μ : Measure α) {Y : Set α} (hT : Measurable T) (hY : MeasurableSet Y) (n : ℕ) :
    Measure.sum (excessGraphMeasure T μ Y n) = graphMeasure (T^[n]) (normalizedRestriction μ Y) := by
  change Measure.sum (fun j => Measure.map (fun x => (x, T^[n] x))
    ((normalizedRestriction μ Y).restrict (excessLevel T Y n j))) = _
  rw [← Measure.map_sum (measurable_graph (hT.iterate n)).aemeasurable,
    excess_partition_measure μ hT hY n]
  rfl

lemma ae_Rn_ge {α : Type*} [MeasurableSpace α] {T : α → α} {Y : Set α}
    {μ : Measure α} [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ) (hY : MeasurableSet Y)
    (hTY : MeasurePreserving (inducedMap T Y) (normalizedRestriction μ Y)
      (normalizedRestriction μ Y)) (n : ℕ) :
    ∀ᵐ x ∂normalizedRestriction μ Y, n ≤ Rn T Y n x := by
  have hraw : ∀ᵐ y ∂μ.restrict Y, 0 < firstReturnTime T Y y := by
    rw [ae_restrict_iff' hY]
    filter_upwards [ae_return_exists hT hY] with y hy hmem
    exact (firstReturn_spec (hy hmem)).1
  have hbase : ∀ᵐ y ∂normalizedRestriction μ Y, 0 < firstReturnTime T Y y :=
    Measure.ae_smul_measure hraw ((μ Y)⁻¹)
  have hrec : ∀ᵐ y ∂normalizedRestriction μ Y, ∀ i : ℕ,
      0 < firstReturnTime T Y ((inducedMap T Y)^[i] y) :=
    ae_all_iff.mpr (fun i : ℕ => (hTY.iterate i).quasiMeasurePreserving.ae
      (p := fun y => 0 < firstReturnTime T Y y) hbase)
  filter_upwards [hrec] with x hx
  calc n = ∑ _i ∈ Finset.range n, 1 := by simp
       _ ≤ ∑ i ∈ Finset.range n, firstReturnTime T Y ((inducedMap T Y)^[i] x) :=
          Finset.sum_le_sum (fun i _ => hx i)

/-- The shifted finite-time decomposition in the first equality of Ex26. -/
theorem sum_shift_excessGraphMeasure {α : Type*} [MeasurableSpace α]
    {T : α → α} {Y : Set α} {μ : Measure α} [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (hY : MeasurableSet Y)
    (hTY : MeasurePreserving (inducedMap T Y) (normalizedRestriction μ Y)
      (normalizedRestriction μ Y)) (n : ℕ) :
    Measure.sum (fun j => Measure.map ((secondShift T)^[j]) (excessGraphMeasure T μ Y n j)) =
      graphMeasure ((inducedMap T Y)^[n]) (normalizedRestriction μ Y) := by
  have hW : Measurable (secondShift T) :=
    measurable_fst.prodMk (hT.measurable.comp measurable_snd)
  have hE (j : ℕ) : MeasurableSet (excessLevel T Y n j) :=
    hY.inter ((measurableSet_singleton j).preimage (measurable_excessDn hT.measurable hY n))
  have heq (j : ℕ) : Measure.map ((secondShift T)^[j]) (excessGraphMeasure T μ Y n j) =
      graphMeasure ((inducedMap T Y)^[n])
        ((normalizedRestriction μ Y).restrict (excessLevel T Y n j)) := by
    rw [excessGraphMeasure, graphMeasure, Measure.map_map (hW.iterate j)
      (measurable_graph (hT.measurable.iterate n))]
    apply Measure.map_congr
    have hge : ∀ᵐ x ∂(normalizedRestriction μ Y).restrict (excessLevel T Y n j),
        n ≤ Rn T Y n x := (ae_Rn_ge hT hY hTY n).filter_mono (ae_mono Measure.restrict_le_self)
    filter_upwards [ae_restrict_mem (hE j), hge] with x hx hxge
    change (secondShift T)^[j] (x, T^[n] x) = (x, (inducedMap T Y)^[n] x)
    rw [secondShift_iterate, induced_iterate_eq, (excessDn_iff_Rn_eq_add T Y n j x hxge).mp hx.2]
    congr 1
    rw [← iterate_add_apply, Nat.add_comm]
  simp_rw [heq, graphMeasure]
  rw [← Measure.map_sum (measurable_graph (hTY.measurable.iterate n)).aemeasurable,
    excess_partition_measure μ hT.measurable hY n]

lemma ae_conjugacy_iterate {α : Type*} [MeasurableSpace α] {T S φ : α → α}
    {μ : Measure α} (hT : MeasurePreserving T μ μ)
    (hc : ∀ᵐ x ∂μ, S (φ x) = φ (T x)) (n : ℕ) :
    ∀ᵐ x ∂μ, S^[n] (φ x) = φ (T^[n] x) := by
  induction n with
  | zero => exact Eventually.of_forall (fun x => rfl)
  | succ n ih =>
    have hcn := (hT.iterate n).quasiMeasurePreserving.ae (p := fun x => S (φ x) = φ (T x)) hc
    filter_upwards [ih, hcn] with x hx hcx
    rw [iterate_succ_apply', hx, hcx, iterate_succ_apply']

/-- The conjugacy identity in the second equality of Ex26. -/
theorem graphMeasure_conjugate {α : Type*} [MeasurableSpace α]
    {T φ : α → α} {Y : Set α} {μ : Measure α}
    (hT : MeasurePreserving T μ μ) (hY : MeasurableSet Y)
    (hφ : MeasurePreserving φ μ (normalizedRestriction μ Y))
    (hc : ∀ᵐ x ∂μ, inducedMap T Y (φ x) = φ (T x)) (n : ℕ) :
    graphMeasure ((inducedMap T Y)^[n]) (normalizedRestriction μ Y) =
      Measure.map (Prod.map φ φ) (graphMeasure (T^[n]) μ) := by
  have hTY := measurable_inducedMap hT.measurable hY
  rw [graphMeasure, ← hφ.map_eq, Measure.map_map (measurable_graph (hTY.iterate n)) hφ.measurable,
    graphMeasure, Measure.map_map (hφ.measurable.prodMap hφ.measurable)
      (measurable_graph (hT.measurable.iterate n))]
  apply Measure.map_congr
  filter_upwards [ae_conjugacy_iterate hT hc n] with x hx
  exact Prod.ext rfl hx

lemma graphMeasure_fst {α : Type*} [MeasurableSpace α] {S : α → α}
    (hS : Measurable S) (ν : Measure α) : (graphMeasure S ν).fst = ν := by
  rw [Measure.fst, graphMeasure, Measure.map_map measurable_fst (measurable_graph hS)]
  exact Measure.map_id

lemma graphMeasure_snd {α : Type*} [MeasurableSpace α] {S : α → α}
    (hS : Measurable S) (ν : Measure α) : (graphMeasure S ν).snd = Measure.map S ν := by
  rw [Measure.snd, graphMeasure, Measure.map_map measurable_snd (measurable_graph hS)]
  rfl

lemma normalizedRestriction_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (Y : Set α) :
    normalizedRestriction μ Y ≤ (μ Y)⁻¹ • μ := by
  apply Measure.le_iff.mpr
  intro A hA
  simp only [normalizedRestriction, Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul_left' (Measure.restrict_apply_le Y A) ((μ Y)⁻¹)

lemma excessGraphMeasure_le {α : Type*} [MeasurableSpace α]
    {T : α → α} (μ : Measure α) (Y : Set α) (hT : Measurable T) (n j : ℕ) :
    excessGraphMeasure T μ Y n j ≤ graphMeasure (T^[n]) (normalizedRestriction μ Y) :=
  Measure.map_mono Measure.restrict_le_self (measurable_graph (hT.iterate n))

/-- The finite-time marginal domination used before passage to the limit
in paper S3.p5. -/
theorem excessGraphMeasure_marginals {α : Type*} [MeasurableSpace α]
    {T : α → α} {μ : Measure α} (Y : Set α)
    (hT : MeasurePreserving T μ μ) (n j : ℕ) :
    (excessGraphMeasure T μ Y n j).fst ≤ (μ Y)⁻¹ • μ ∧
    (excessGraphMeasure T μ Y n j).snd ≤ (μ Y)⁻¹ • μ := by
  have hle := excessGraphMeasure_le μ Y hT.measurable n j
  constructor
  · calc _ ≤ (graphMeasure (T^[n]) (normalizedRestriction μ Y)).fst :=
             Measure.map_mono hle measurable_fst
         _ = normalizedRestriction μ Y := graphMeasure_fst (hT.measurable.iterate n) _
         _ ≤ (μ Y)⁻¹ • μ := normalizedRestriction_le μ Y
  · calc _ ≤ (graphMeasure (T^[n]) (normalizedRestriction μ Y)).snd :=
             Measure.map_mono hle measurable_snd
         _ = Measure.map (T^[n]) (normalizedRestriction μ Y) := graphMeasure_snd (hT.measurable.iterate n) _
         _ ≤ Measure.map (T^[n]) ((μ Y)⁻¹ • μ) :=
             Measure.map_mono (normalizedRestriction_le μ Y) (hT.measurable.iterate n)
         _ = (μ Y)⁻¹ • μ := by rw [Measure.map_smul, (hT.iterate n).map_eq]

end
end Paper14
