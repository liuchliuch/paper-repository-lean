import Paper35.GaussianCountMeasurability
import Mathlib.Data.Sym.Card
import Mathlib.Tactic.Abel

noncomputable section
open Set MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped NNReal ENNReal

namespace Paper35.GaussianMarked

def gaussianIid (m K : ℕ) : Measure (Fin K → Source.Space m) :=
  Measure.pi (fun _ : Fin K => standardGaussian m)

instance (m K : ℕ) : IsProbabilityMeasure (gaussianIid m K) := by
  unfold gaussianIid
  infer_instance

def gaussianScores {m K : ℕ} (ψ : ℝ → Source.Space m)
    (Z : Fin K → Source.Space m) : Fin K → ℝ → ℝ := fun j s => inner ℝ (Z j) (ψ s)

def reconstruction (m n : ℕ) (a : MarkSample m n) : Fin (n+2) → Source.Space m :=
  rotatedCandidates n a.1 a.2

lemma continuous_reconstruction (m n : ℕ) : Continuous (reconstruction m n) := by
  apply continuous_pi
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp only [reconstruction, rotatedCandidates, Fin.cases_zero]
    fun_prop
  · refine Fin.cases ?_ (fun k => ?_) k
    · simp only [reconstruction, rotatedCandidates, Fin.cases_succ, Fin.cases_zero]
      fun_prop
    · simp only [reconstruction, rotatedCandidates, Fin.cases_succ]
      fun_prop

lemma reconstruction_injective (m n : ℕ) : Function.Injective (reconstruction m n) := by
  rintro ⟨D, C, G⟩ ⟨D', C', G'⟩ h
  have ha : (Real.sqrt 2)⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by norm_num)))
  have hp : C + D = C' + D' := smul_right_injective (Source.Space m) ha
    (congrFun h (0 : Fin (n+2)))
  have hm : C - D = C' - D' := smul_right_injective (Source.Space m) ha
    (congrFun h (0 : Fin (n+1)).succ)
  have hD : D = D' := by
    apply smul_right_injective (Source.Space m) (by norm_num : (2 : ℝ) ≠ 0)
    simp only [two_smul]
    calc
      D + D = (C+D) - (C-D) := by abel
      _ = (C'+D') - (C'-D') := by rw [hp, hm]
      _ = D' + D' := by abel
  have hC : C = C' := by
    rw [hD] at hp
    exact add_right_cancel hp
  have hG : G = G' := by
    funext k
    exact congrFun h k.succ.succ
  exact Prod.ext hD (Prod.ext hC hG)

lemma measurableEmbedding_reconstruction (m n : ℕ) :
    MeasurableEmbedding (reconstruction m n) :=
  (continuous_reconstruction m n).measurableEmbedding (reconstruction_injective m n)

/-- Explicit classical Gaussian orthogonal-change-of-variables input.
For every vector dimension m and n remaining candidates, independent D,C and
n standard Gaussian vectors reconstruct ((C+D)/√2,(C-D)/√2,Z_1,...,Z_n),
whose full joint law is the (n+2)-fold iid standard Gaussian law.
This is exactly the block orthogonal transformation theorem for a standard
normal sample (MIT 18.443 Lecture 4, 2006, p.25), specialized to the displayed
2-by-2 orthogonal matrix and followed by the canonical finite reindexing.
No curve, root, visibility, count or expectation appears in this input. -/
def GaussianPairReconstructionLaw : Prop :=
  ∀ m n : ℕ, ((standardGaussian m).prod (vectorMarkLaw m n)).map
    (reconstruction m n) = gaussianIid m (n+2)

lemma reconstruction_preserving (hrot : GaussianPairReconstructionLaw) (m n : ℕ) :
    MeasurePreserving (reconstruction m n)
      ((standardGaussian m).prod (vectorMarkLaw m n)) (gaussianIid m (n+2)) :=
  ⟨(continuous_reconstruction m n).measurable, hrot m n⟩

lemma gaussianScores_reconstruction (m n : ℕ) (ψ : ℝ → Source.Space m) (a : MarkSample m n) :
    gaussianScores ψ (reconstruction m n a) = rotatedScores n ψ a.1 a.2 :=
  (rotatedScores_eq_inner n ψ a.1 a.2).symm

/-- The actual iid Gaussian first-pair count is measurable; this is derived
from the actual product marked count and the injective pair reconstruction. -/
theorem aemeasurable_iid_firstPairCount (hrot : GaussianPairReconstructionLaw)
    (hregular : ClassicalCroftonRegularityLaw) (m n : ℕ) (hm : 2 ≤ m)
    (L : ℝ) (hL : 0 < L) (ψ : ℝ → Source.Space m)
    (hac : AbsolutelyContinuousOnInterval ψ 0 L) (hunit : ∀ s ∈ Icc 0 L, ‖ψ s‖ = 1)
    (hLN : VisibleCrossing.LusinNovikovInput (MarkSample m n) (CurveParameter L)) :
    AEMeasurable (fun Z => ((pairSwitchSet (gaussianScores ψ Z) L (firstPair n)).encard : ℝ≥0∞))
      (gaussianIid m (n+2)) := by
  rw [← hrot m n]
  apply (measurableEmbedding_reconstruction m n).aemeasurable_map_iff.mpr
  simpa only [Function.comp_def, gaussianScores_reconstruction] using
    aemeasurable_rotated_pairSwitchCount hregular m n hm L hL ψ hac hunit hLN

/-- The Gaussian-pair Crofton formula transported to the real iid candidate law. -/
theorem iid_first_pair_switch_crofton (hcrofton : ClassicalCroftonLaw)
    (hregular : ClassicalCroftonRegularityLaw) (hproj : GaussianUnitProjectionLaw)
    (hrot : GaussianPairReconstructionLaw) (m n : ℕ) (hm : 2 ≤ m)
    (L : ℝ) (hL : 0 < L) (ψ : ℝ → Source.Space m)
    (hac : AbsolutelyContinuousOnInterval ψ 0 L) (hunit : ∀ s ∈ Icc 0 L, ‖ψ s‖ = 1)
    (hLN : VisibleCrossing.LusinNovikovInput (MarkSample m n) (CurveParameter L)) :
    (∫⁻ Z, ((pairSwitchSet (gaussianScores ψ Z) L (firstPair n)).encard : ℝ≥0∞)
      ∂gaussianIid m (n+2)) =
      (ENNReal.ofReal (1 / Real.pi) * sphericalLength ψ L) * visibilityProbability n := by
  rw [← (reconstruction_preserving hrot m n).lintegral_comp_emb
    (measurableEmbedding_reconstruction m n)]
  simp only [gaussianScores_reconstruction]
  exact product_first_pair_switch_crofton hcrofton hregular hproj m n hm L hL ψ hac hunit hLN

/-- Finite permutations act transitively on ordered pairs of distinct candidates. -/
lemma exists_perm_pair {α : Type*} [DecidableEq α] (a b i j : α) (hab : a ≠ b) (hij : i ≠ j) :
    ∃ e : Equiv.Perm α, e a = i ∧ e b = j := by
  let e₁ := Equiv.swap a i
  have hei : e₁ a = i := Equiv.swap_apply_left a i
  have hbi : e₁ b ≠ i := by
    intro h
    exact hab (e₁.injective (h.trans hei.symm)).symm
  refine ⟨e₁.trans (Equiv.swap (e₁ b) j), ?_, ?_⟩
  · change Equiv.swap (e₁ b) j (e₁ a) = i
    rw [hei, Equiv.swap_apply_of_ne_of_ne hbi.symm hij]
  · exact Equiv.swap_apply_left _ _

/-- Reindexing candidates preserves the original pair-switch sets with their parameter count. -/
lemma pairSwitchSet_reindex {K : ℕ} (f : Fin K → ℝ → ℝ) (L : ℝ)
    (p q : OrderedCandidatePair K) (e : Equiv.Perm (Fin K))
    (hp : e p.1.1 = q.1.1) (hq : e p.1.2 = q.1.2) :
    pairSwitchSet (fun j s => f (e j) s) L p = pairSwitchSet f L q := by
  ext s
  simp only [pairSwitchSet, VisiblePair, hp, hq, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hs0, hsL, ⟨heq, hvis⟩, hsign⟩
    refine ⟨hs0, hsL, ⟨heq, ?_⟩, hsign⟩
    intro k hki hkj
    have hi : e.symm k ≠ p.1.1 := by intro h; exact hki (by rw [← hp, ← h]; simp)
    have hj : e.symm k ≠ p.1.2 := by intro h; exact hkj (by rw [← hq, ← h]; simp)
    simpa only [e.apply_symm_apply] using hvis (e.symm k) hi hj
  · rintro ⟨hs0, hsL, ⟨heq, hvis⟩, hsign⟩
    refine ⟨hs0, hsL, ⟨heq, ?_⟩, hsign⟩
    intro k hki hkj
    apply hvis (e k)
    · intro h; exact hki (e.injective (h.trans hp.symm))
    · intro h; exact hkj (e.injective (h.trans hq.symm))

/-- Coordinate permutation as a measurable equivalence. -/
def permuteCandidates {m K : ℕ} (e : Equiv.Perm (Fin K)) :
    (Fin K → Source.Space m) ≃ᵐ (Fin K → Source.Space m) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin K => Source.Space m) e).symm

lemma permuteCandidates_apply {m K : ℕ} (e : Equiv.Perm (Fin K))
    (Z : Fin K → Source.Space m) (i : Fin K) : permuteCandidates e Z i = Z (e i) := by
  simp [permuteCandidates, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_symm_apply]

lemma permuteCandidates_preserving {m K : ℕ} (e : Equiv.Perm (Fin K)) :
    MeasurePreserving (permuteCandidates (m:=m) e) (gaussianIid m K) (gaussianIid m K) := by
  exact (measurePreserving_piCongrLeft (fun _ : Fin K => standardGaussian m) e).symm

lemma pairSwitchSet_permute {m K : ℕ} (ψ : ℝ → Source.Space m) (Z : Fin K → Source.Space m)
    (L : ℝ) (p q : OrderedCandidatePair K) (e : Equiv.Perm (Fin K))
    (hp : e p.1.1 = q.1.1) (hq : e p.1.2 = q.1.2) :
    pairSwitchSet (gaussianScores ψ (permuteCandidates e Z)) L p =
      pairSwitchSet (gaussianScores ψ Z) L q := by
  have heq : gaussianScores ψ (permuteCandidates e Z) =
      fun j s => gaussianScores ψ Z (e j) s := by
    funext j s
    simp only [gaussianScores, permuteCandidates_apply]
  rw [heq]
  exact pairSwitchSet_reindex _ L p q e hp hq

/-- Every pair has the same expectation under the genuine iid Gaussian candidate law. -/
lemma iid_pair_expectations_eq {m n : ℕ} (ψ : ℝ → Source.Space m) (L : ℝ)
    (p : OrderedCandidatePair (n+2)) :
    (∫⁻ Z, ((pairSwitchSet (gaussianScores ψ Z) L p).encard : ℝ≥0∞) ∂gaussianIid m (n+2)) =
      ∫⁻ Z, ((pairSwitchSet (gaussianScores ψ Z) L (firstPair n)).encard : ℝ≥0∞)
        ∂gaussianIid m (n+2) := by
  classical
  obtain ⟨e, hp, hq⟩ := exists_perm_pair (firstPair n).1.1 (firstPair n).1.2 p.1.1 p.1.2
    (ne_of_lt (firstPair n).2) (ne_of_lt p.2)
  have h := MeasurePreserving.lintegral_map_equiv
    (fun Z => ((pairSwitchSet (gaussianScores ψ Z) L (firstPair n)).encard : ℝ≥0∞))
    (permuteCandidates (m:=m) e) (permuteCandidates_preserving e)
  simpa only [pairSwitchSet_permute ψ _ L (firstPair n) p e hp hq] using h.symm

/-- Source unordered-pair count: no K² overcount remains after strict visibility. -/
lemma orderedCandidatePair_card (K : ℕ) : Fintype.card (OrderedCandidatePair K) = K.choose 2 := by
  classical
  let f : OrderedCandidatePair K → {a : Sym2 (Fin K) // ¬a.IsDiag} :=
    fun p => ⟨Sym2.mk p.1, by simpa only [Sym2.mk_isDiag_iff] using ne_of_lt p.2⟩
  have hinj : Function.Injective f := by
    intro p q h
    have heq : Sym2.mk p.1 = Sym2.mk q.1 := congrArg Subtype.val h
    rcases Sym2.eq_iff.mp heq with ⟨h0,h1⟩ | ⟨h0,h1⟩
    · exact Subtype.ext (Prod.ext h0 h1)
    · have hlt := p.2
      rw [h0,h1] at hlt
      exact (lt_asymm q.2 hlt).elim
  have hsurj : Function.Surjective f := by
    rintro ⟨q,hq⟩
    obtain ⟨⟨a,b⟩,rfl⟩ := Quot.exists_rep q
    have hab : a ≠ b := by simpa only [Sym2.mk_isDiag_iff] using hq
    rcases lt_or_gt_of_ne hab with hlt | hlt
    · exact ⟨⟨(a,b),hlt⟩, rfl⟩
    · refine ⟨⟨(b,a),hlt⟩, ?_⟩
      apply Subtype.ext
      exact Sym2.eq_iff.mpr (Or.inr ⟨rfl,rfl⟩)
  have hcard := Fintype.card_congr (Equiv.ofBijective f ⟨hinj,hsurj⟩)
  simpa only [Sym2.card_subtype_not_diag, Fintype.card_fin] using hcard

/-- Almost-everywhere measurability of every actual iid Gaussian pair-switch count. -/
theorem aemeasurable_iid_pairCount (hrot : GaussianPairReconstructionLaw)
    (hregular : ClassicalCroftonRegularityLaw) (m n : ℕ) (hm : 2 ≤ m)
    (L : ℝ) (hL : 0 < L) (ψ : ℝ → Source.Space m)
    (hac : AbsolutelyContinuousOnInterval ψ 0 L) (hunit : ∀ s ∈ Icc 0 L, ‖ψ s‖ = 1)
    (hLN : VisibleCrossing.LusinNovikovInput (MarkSample m n) (CurveParameter L))
    (p : OrderedCandidatePair (n+2)) :
    AEMeasurable (fun Z => ((pairSwitchSet (gaussianScores ψ Z) L p).encard : ℝ≥0∞))
      (gaussianIid m (n+2)) := by
  classical
  obtain ⟨e, hp, hq⟩ := exists_perm_pair (firstPair n).1.1 (firstPair n).1.2 p.1.1 p.1.2
    (ne_of_lt (firstPair n).2) (ne_of_lt p.2)
  have h := (aemeasurable_iid_firstPairCount hrot hregular m n hm L hL ψ hac hunit hLN).comp_quasiMeasurePreserving (permuteCandidates_preserving (m:=m) e).quasiMeasurePreserving
  simpa only [Function.comp_def, pairSwitchSet_permute ψ _ L (firstPair n) p e hp hq] using h

/-- Measurability of the actual total Gaussian switch count follows by the
proved finite decomposition into the genuinely measurable visible-pair counts. -/
theorem aemeasurable_iid_switchCount (hrot : GaussianPairReconstructionLaw)
    (hregular : ClassicalCroftonRegularityLaw) (m n : ℕ) (hm : 2 ≤ m)
    (L : ℝ) (hL : 0 < L) (ψ : ℝ → Source.Space m)
    (hac : AbsolutelyContinuousOnInterval ψ 0 L) (hunit : ∀ s ∈ Icc 0 L, ‖ψ s‖ = 1)
    (hLN : VisibleCrossing.LusinNovikovInput (MarkSample m n) (CurveParameter L)) :
    AEMeasurable (fun Z => switchCount (gaussianScores ψ Z) L) (gaussianIid m (n+2)) := by
  classical
  simp only [switchCount_eq_sum_pairSwitchSet]
  have hsum := Finset.aemeasurable_sum
    (f := fun (p : OrderedCandidatePair (n+2)) (Z : Fin (n+2) → Source.Space m) =>
      ((pairSwitchSet (gaussianScores ψ Z) L p).encard : ℝ≥0∞)) Finset.univ
    (fun p _ => aemeasurable_iid_pairCount hrot hregular m n hm L hL ψ hac hunit hLN p)
  convert hsum using 1
  funext Z
  simp only [Finset.sum_apply]

/-- Lemma 6.2 in ambient dimension m≥2: the actual expected switch count is
c_K times the parameterized spherical-speed length. All upper-envelope steps
are proved; the explicitly named inputs are published classical theorems. -/
theorem gaussian_upper_envelope_crofton (hcrofton : ClassicalCroftonLaw)
    (hregular : ClassicalCroftonRegularityLaw) (hproj : GaussianUnitProjectionLaw)
    (hrot : GaussianPairReconstructionLaw) (hmax : GaussianMaxIntegralLaw)
    (m n : ℕ) (hm : 2 ≤ m) (L : ℝ) (hL : 0 < L) (ψ : ℝ → Source.Space m)
    (hac : AbsolutelyContinuousOnInterval ψ 0 L) (hunit : ∀ s ∈ Icc 0 L, ‖ψ s‖ = 1)
    (hLN : VisibleCrossing.LusinNovikovInput (MarkSample m n) (CurveParameter L)) :
    expectedSwitchCount (gaussianIid m (n+2)) (gaussianScores ψ) L =
      ENNReal.ofReal (Paper35.gaussianRankCoefficient (n+2)) * sphericalLength ψ L := by
  rw [expectedSwitchCount_eq_sum_pairSwitchSet _ _ L
    (aemeasurable_iid_pairCount hrot hregular m n hm L hL ψ hac hunit hLN)]
  simp_rw [iid_pair_expectations_eq ψ L]
  rw [iid_first_pair_switch_crofton hcrofton hregular hproj hrot m n hm L hL ψ hac hunit hLN]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, orderedCandidatePair_card]
  calc
    _ = ((Nat.choose (n+2) 2 : ℝ≥0∞) * ENNReal.ofReal (1/Real.pi) *
        visibilityProbability n) * sphericalLength ψ L := by ac_rfl
    _ = _ := by
      have h := marked_coefficient_eq_gaussianRankCoefficient hmax (n+2) (by omega)
      simpa only [Nat.add_sub_cancel] using congrArg (fun x => x * sphericalLength ψ L) h

/-- Geometric-length form of Lemma 6.2, retaining the actual metric total variation. -/
theorem gaussian_upper_envelope_length (hcrofton : ClassicalCroftonLaw)
    (hregular : ClassicalCroftonRegularityLaw) (hproj : GaussianUnitProjectionLaw)
    (hrot : GaussianPairReconstructionLaw) (hmax : GaussianMaxIntegralLaw)
    (hlength : ACCurveLengthLaw) (m n : ℕ) (hm : 2 ≤ m) (L : ℝ) (hL : 0 < L)
    (ψ : ℝ → Source.Space m) (hac : AbsolutelyContinuousOnInterval ψ 0 L)
    (hunit : ∀ s ∈ Icc 0 L, ‖ψ s‖ = 1)
    (hLN : VisibleCrossing.LusinNovikovInput (MarkSample m n) (CurveParameter L)) :
    expectedSwitchCount (gaussianIid m (n+2)) (gaussianScores ψ) L =
      ENNReal.ofReal (Paper35.gaussianRankCoefficient (n+2)) * eVariationOn ψ (Icc 0 L) := by
  rw [gaussian_upper_envelope_crofton hcrofton hregular hproj hrot hmax m n hm L hL ψ hac hunit hLN,
    sphericalLength_eq_eVariationOn hlength m L hL ψ hac]

end Paper35.GaussianMarked
