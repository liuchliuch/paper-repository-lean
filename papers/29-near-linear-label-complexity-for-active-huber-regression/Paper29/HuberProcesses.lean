import Paper29.ProcessTools

noncomputable section
open scoped BigOperators ENNReal
namespace Paper29.ProcessTools

abbrev Ball {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (R : ℝ) :=
  {h : Fin d → ℝ // unshifted A h ≤ R}

def zeroBall {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) {R : ℝ} (hR : 0 ≤ R) : Ball A R :=
  ⟨0, by simpa [unshifted, Matrix.mulVec_zero] using hR⟩

theorem row_huber_le {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) {R : ℝ}
    (h : Ball A R) (i : Fin n) : huber ((A.mulVec h) i) ≤ R := by
  have hterm : huber ((A.mulVec h) i) ≤ unshifted A h :=
    Finset.single_le_sum (fun j _ => huber_nonneg _) (Finset.mem_univ i)
  exact hterm.trans h.property

theorem unshiftedClass_bounded {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (R : ℝ) (i : Fin n) :
    BddAbove (Set.range (fun h : Ball A R => |huber ((A.mulVec h) i)|)) := by
  refine ⟨R, ?_⟩
  rintro v ⟨h, rfl⟩
  simpa only [abs_of_nonneg (huber_nonneg _)] using row_huber_le A h i

theorem importanceAverage_mono {n m : ℕ} (π : Fin n → ℝ) (hπ : ∀ i, 0 ≤ π i)
    (ν : Fin m → Fin n) (f g : Fin n → ℝ) (h : ∀ i, f i ≤ g i) :
    Sampling.importanceAverage π ν f ≤ Sampling.importanceAverage π ν g := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro j _
  exact div_le_div_of_nonneg_right (h (ν j)) (hπ (ν j))

def unshiftedEnvelope {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (π : Fin n → ℝ) (R : ℝ) (ν : Fin m → Fin n) : ℝ :=
  supremum (fun h : Ball A R => Sampling.sampledUnshifted π ν A h)

def unshiftedError {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (π : Fin n → ℝ) (R : ℝ) (ν : Fin m → Fin n) : ℝ :=
  errorSup π (fun i (h : Ball A R) => huber ((A.mulVec h) i)) ν

theorem sampledUnshifted_bdd {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (π : Fin n → ℝ) (hπ : ∀ i, 0 ≤ π i) (R : ℝ) (ν : Fin m → Fin n) :
    BddAbove (Set.range (fun h : Ball A R => Sampling.sampledUnshifted π ν A h)) := by
  refine ⟨Sampling.importanceAverage π ν (fun _ => R), ?_⟩
  rintro v ⟨h, rfl⟩
  exact importanceAverage_mono π hπ ν _ _ (row_huber_le A h)

theorem unshiftedError_bdd {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (π : Fin n → ℝ) (hπ : ∀ i, 0 ≤ π i) (R : ℝ) (ν : Fin m → Fin n) :
    BddAbove (Set.range (fun h : Ball A R =>
      |Sampling.sampledUnshifted π ν A h - unshifted A h|)) := by
  let U := Sampling.importanceAverage π ν (fun _ => R)
  refine ⟨U + R, ?_⟩
  rintro v ⟨h, rfl⟩
  have ha : Sampling.sampledUnshifted π ν A h ≤ U :=
    importanceAverage_mono π hπ ν _ _ (row_huber_le A h)
  have ha0 := Sampling.sampledHuber_nonneg π ν (A.mulVec h) hπ
  change 0 ≤ Sampling.sampledUnshifted π ν A h at ha0
  have hb0 : 0 ≤ unshifted A h := Finset.sum_nonneg (fun i _ => huber_nonneg _)
  exact abs_le.mpr ⟨by linarith [h.property], by linarith [h.property]⟩

theorem unshiftedError_nonneg {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (π : Fin n → ℝ) (hπ : ∀ i, 0 ≤ π i) {R : ℝ} (hR : 0 ≤ R)
    (ν : Fin m → Fin n) : 0 ≤ unshiftedError A π R ν := by
  letI : Nonempty (Ball A R) := ⟨zeroBall A hR⟩
  exact supremum_nonneg _ (unshiftedError_bdd A π hπ R ν) (fun _ => abs_nonneg _)

theorem unshiftedEnvelope_nonneg {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (π : Fin n → ℝ) (hπ : ∀ i, 0 ≤ π i) {R : ℝ} (hR : 0 ≤ R)
    (ν : Fin m → Fin n) : 0 ≤ unshiftedEnvelope A π R ν := by
  letI : Nonempty (Ball A R) := ⟨zeroBall A hR⟩
  exact supremum_nonneg _ (sampledUnshifted_bdd A π hπ R ν)
    (fun h => Sampling.sampledHuber_nonneg π ν (A.mulVec h) hπ)

/-- The actual random envelope is controlled by true radius plus actual error. -/
theorem unshiftedEnvelope_le {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (π : Fin n → ℝ) (hπ : ∀ i, 0 ≤ π i) {R : ℝ} (hR : 0 ≤ R)
    (ν : Fin m → Fin n) :
    unshiftedEnvelope A π R ν ≤ R + unshiftedError A π R ν := by
  letI : Nonempty (Ball A R) := ⟨zeroBall A hR⟩
  apply supremum_le
  intro h
  have he := le_supremum _ (unshiftedError_bdd A π hπ R ν) h
  have hh := le_abs_self (Sampling.sampledUnshifted π ν A h - unshifted A h)
  change |Sampling.sampledUnshifted π ν A h - unshifted A h| ≤
    unshiftedError A π R ν at he
  linarith [h.property]

/-- Centered scalar Huber population class, anchored at h=0. -/
def affineClass {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (z : Fin n → ℝ)
    (R : ℝ) (i : Fin n) (h : Ball A R) : ℝ :=
  huber (z i + (A.mulVec h) i) - huber (z i)

theorem affineClass_bounded {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (z : Fin n → ℝ) (R : ℝ) (i : Fin n) :
    BddAbove (Set.range (fun h : Ball A R => |affineClass A z R i h|)) := by
  refine ⟨3 * huber (z i) + 2 * R, ?_⟩
  rintro v ⟨h, rfl⟩
  have hp := huber_add_le (z i) ((A.mulVec h) i)
  have hr := row_huber_le A h i
  have hz := huber_nonneg (z i)
  have hs := huber_nonneg (z i + (A.mulVec h) i)
  exact abs_le.mpr ⟨by dsimp [affineClass]; linarith,
    by dsimp [affineClass]; linarith⟩

def shiftedEnvelope {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (z π : Fin n → ℝ) (R : ℝ) (ν : Fin m → Fin n) : ℝ :=
  supremum (fun h : Ball A R => Sampling.sampledShifted π ν A z h)

theorem sampledShifted_bdd {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (z π : Fin n → ℝ) (hπ : ∀ i, 0 ≤ π i) {R : ℝ} (hR : 0 ≤ R)
    (ν : Fin m → Fin n) :
    BddAbove (Set.range (fun h : Ball A R => Sampling.sampledShifted π ν A z h)) := by
  refine ⟨2 * Sampling.sampledShifted π ν A z 0 + 2 * unshiftedEnvelope A π R ν, ?_⟩
  rintro v ⟨h, rfl⟩
  have he := Sampling.sampledShifted_envelope π ν A z h hπ
  have hu := le_supremum _ (sampledUnshifted_bdd A π hπ R ν) h
  change Sampling.sampledUnshifted π ν A h ≤ unshiftedEnvelope A π R ν at hu
  linarith

theorem shiftedEnvelope_nonneg {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (z π : Fin n → ℝ) (hπ : ∀ i, 0 ≤ π i) {R : ℝ} (hR : 0 ≤ R)
    (ν : Fin m → Fin n) : 0 ≤ shiftedEnvelope A z π R ν := by
  letI : Nonempty (Ball A R) := ⟨zeroBall A hR⟩
  exact supremum_nonneg _ (sampledShifted_bdd A z π hπ hR ν)
    (fun h => Sampling.sampledHuber_nonneg π ν _ hπ)

theorem shiftedEnvelope_le {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (z π : Fin n → ℝ) (hπ : ∀ i, 0 ≤ π i) {R : ℝ} (hR : 0 ≤ R)
    (ν : Fin m → Fin n) : shiftedEnvelope A z π R ν ≤
      2 * Sampling.sampledShifted π ν A z 0 + 2 * unshiftedEnvelope A π R ν := by
  letI : Nonempty (Ball A R) := ⟨zeroBall A hR⟩
  apply supremum_le
  intro h
  have he := Sampling.sampledShifted_envelope π ν A z h hπ
  have hu := le_supremum _ (sampledUnshifted_bdd A π hπ R ν) h
  change Sampling.sampledUnshifted π ν A h ≤ unshiftedEnvelope A π R ν at hu
  linarith

end Paper29.ProcessTools
