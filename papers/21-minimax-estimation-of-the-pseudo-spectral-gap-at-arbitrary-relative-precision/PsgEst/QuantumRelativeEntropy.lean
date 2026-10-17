import PsgEst.QuantumPerspective
import PsgEst.QuantumTensor
import PsgEst.QuantumVariational
import PsgEst.MatrixLogIntegral

/-! The actual quantum relative entropy is jointly convex. -/
open Matrix BigOperators Real Set MeasureTheory
namespace PsgEst.QuantumRelativeEntropy

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

open QuantumVariational

/-- The exact Sylvester resolvent kernel, including the harmless zero value
at the single endpoint `s = 0`. -/
noncomputable def entropyKernel (X A : Matrix ι ι ℝ) (s : ℝ) : ℝ :=
  (quadraticPerspective (fun ij => X ij.1 ij.2) (sylvesterMatrix s A X) - trace X) / s

/-- Each positive-time resolvent kernel is jointly convex in the two actual
matrix arguments. No entropy or trace-exponential inequality is an input. -/
theorem entropyKernel_joint_convex (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1)
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1)
    (X A : α → Matrix ι ι ℝ) (hX : ∀ a, (X a).PosDef) (hA : ∀ a, (A a).PosDef) :
    entropyKernel (∑ a, p a • X a) (∑ a, p a • A a) s ≤
      ∑ a, p a * entropyKernel (X a) (A a) s := by
  by_cases hz : s=0
  · simp only [entropyKernel, hz, div_zero, mul_zero, Finset.sum_const_zero, le_refl]
  · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hz)
    have hF := sylvester_quadraticPerspective_joint_convex s hs p hp hsum A X hA hX
    have htrace : trace (∑ a, p a • X a) = ∑ a, p a * trace (X a) := by
      simp only [Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
    unfold entropyKernel
    calc
      _ ≤ ((∑ a, p a * quadraticPerspective (fun ij => X a ij.1 ij.2)
          (sylvesterMatrix s (A a) (X a))) - trace (∑ a, p a • X a)) / s :=
        div_le_div_of_nonneg_right (sub_le_sub_right hF _) hspos.le
      _ = _ := by
        rw [htrace]
        simp only [← mul_div_assoc, mul_sub, Finset.sum_sub_distrib, Finset.sum_div, sub_div]

/-- Spectral expansion of the actual Sylvester resolvent entropy kernel. -/
theorem entropyKernel_eq_spectrum {X A : Matrix ι ι ℝ}
    (hX : X.PosDef) (hA : A.PosDef) (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
    entropyKernel X A s = ∑ i, ∑ j, overlapWeight hA.isHermitian hX.isHermitian i j *
      ((hX.isHermitian.eigenvalues j ^ 2 /
        ((1-s)*hX.isHermitian.eigenvalues j+s*hA.isHermitian.eigenvalues i) -
          hX.isHermitian.eigenvalues j) / s) := by
  have htrace : trace X = ∑ j, hX.isHermitian.eigenvalues j := by
    simpa only [spectralMap_id, id_eq] using trace_spectralMap hX.isHermitian id
  have hmass : ∑ i, ∑ j, overlapWeight hA.isHermitian hX.isHermitian i j *
      hX.isHermitian.eigenvalues j = trace X := by
    rw [Finset.sum_comm, htrace]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_mul, overlap_col_sum, one_mul]
  unfold entropyKernel
  rw [QuantumTensor.sylvester_qform_spectrum hX hA s hs, ← hmass]
  simp only [mul_div_assoc, mul_sub, Finset.sum_sub_distrib, Finset.sum_div, sub_div]

/-- The actual kernel is integrable despite assigning zero at the removable endpoint. -/
theorem entropyKernel_intervalIntegrable {X A : Matrix ι ι ℝ}
    (hX : X.PosDef) (hA : A.PosDef) :
    IntervalIntegrable (entropyKernel X A) volume 0 1 := by
  have hi (i j : ι) : IntervalIntegrable (fun s : ℝ =>
      overlapWeight hA.isHermitian hX.isHermitian i j *
        ((hX.isHermitian.eigenvalues j ^ 2 /
          ((1-s)*hX.isHermitian.eigenvalues j+s*hA.isHermitian.eigenvalues i) -
            hX.isHermitian.eigenvalues j) / s)) volume 0 1 :=
    (relative_entropy_unit_intervalIntegrable (hX.eigenvalues_pos j)
      (hA.eigenvalues_pos i)).const_mul _
  have hint := IntervalIntegrable.sum (s := Finset.univ) (fun i _ =>
    IntervalIntegrable.sum (s := Finset.univ) (fun j _ => hi i j))
  simp only [Finset.sum_fn] at hint
  apply hint.congr
  intro s hs
  symm
  exact entropyKernel_eq_spectrum hX hA s (by
    have hs' : s ∈ Ioc (0:ℝ) 1 := by
      simpa only [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hs
    exact ⟨hs'.1.le, hs'.2⟩)

/-- The actual quantum relative entropy is the finite-interval Sylvester resolvent integral. -/
theorem relativeEntropy_eq_integral {X A : Matrix ι ι ℝ}
    (hX : X.PosDef) (hA : A.PosDef) :
    relativeEntropy X A = ∫ s in (0:ℝ)..1, entropyKernel X A s := by
  rw [relativeEntropy_eq_overlap_reverse hX.isHermitian hA.isHermitian]
  have heq : (∫ s in (0:ℝ)..1, entropyKernel X A s) =
      ∫ s in (0:ℝ)..1, ∑ i, ∑ j, overlapWeight hA.isHermitian hX.isHermitian i j *
        ((hX.isHermitian.eigenvalues j ^ 2 /
          ((1-s)*hX.isHermitian.eigenvalues j+s*hA.isHermitian.eigenvalues i) -
            hX.isHermitian.eigenvalues j) / s) := by
    apply intervalIntegral.integral_congr_ae
    exact Filter.Eventually.of_forall (fun s hs => entropyKernel_eq_spectrum hX hA s (by
      have hs' : s ∈ Ioc (0:ℝ) 1 := by
        simpa only [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hs
      exact ⟨hs'.1.le, hs'.2⟩))
  rw [heq]
  have general_integral (x a : ι → ℝ) (w : ι → ι → ℝ)
      (hx : ∀ j, 0 < x j) (ha : ∀ i, 0 < a i) :
      (∑ i, ∑ j, w i j * (x j * (log (x j) - log (a i)))) =
        ∫ s in (0:ℝ)..1, ∑ i, ∑ j, w i j *
          ((x j ^ 2 / ((1-s)*x j+s*a i)-x j)/s) := by
    have hi (i j : ι) : IntervalIntegrable (fun s : ℝ =>
        w i j * ((x j ^ 2 / ((1-s)*x j+s*a i)-x j)/s)) volume 0 1 :=
      (relative_entropy_unit_intervalIntegrable (hx j) (ha i)).const_mul _
    rw [intervalIntegral.integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [intervalIntegral.integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro j _
        rw [intervalIntegral.integral_const_mul,
          ← real_relative_entropy_unit_integral (hx j) (ha i)]
      · exact fun j _ => hi i j
    · intro i _
      have hint := IntervalIntegrable.sum (s := Finset.univ) (fun j _ => hi i j)
      simpa only [Finset.sum_fn] using hint
  exact general_integral _ _ _ hX.eigenvalues_pos hA.eigenvalues_pos


/-- Joint convexity of the actual quantum relative entropy, obtained by
integrating the genuine Hilbert--Schmidt quadratic-perspective inequality. -/
theorem relativeEntropy_joint_convex
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1)
    (X A : α → Matrix ι ι ℝ) (hX : ∀ a, (X a).PosDef) (hA : ∀ a, (A a).PosDef) :
    relativeEntropy (∑ a, p a • X a) (∑ a, p a • A a) ≤
      ∑ a, p a * relativeEntropy (X a) (A a) := by
  have hXB := weighted_sum_posDef p hp hsum X hX
  have hAB := weighted_sum_posDef p hp hsum A hA
  have hi (a : α) : IntervalIntegrable (fun s => p a * entropyKernel (X a) (A a) s)
      volume 0 1 := (entropyKernel_intervalIntegrable (hX a) (hA a)).const_mul (p a)
  have hsumInt : IntervalIntegrable (fun s => ∑ a, p a * entropyKernel (X a) (A a) s)
      volume 0 1 := by
    simpa only [Finset.sum_fn] using IntervalIntegrable.sum Finset.univ (fun a _ => hi a)
  rw [relativeEntropy_eq_integral hXB hAB]
  calc
    _ ≤ ∫ s in (0:ℝ)..1, ∑ a, p a * entropyKernel (X a) (A a) s := by
      apply intervalIntegral.integral_mono_on (by norm_num) (entropyKernel_intervalIntegrable hXB hAB)
        hsumInt
      intro s hs
      exact entropyKernel_joint_convex s hs p hp hsum X A hX hA
    _ = _ := by
      rw [intervalIntegral.integral_finset_sum (fun a _ => hi a)]
      apply Finset.sum_congr rfl
      intro a _
      rw [intervalIntegral.integral_const_mul, ← relativeEntropy_eq_integral (hX a) (hA a)]

end PsgEst.QuantumRelativeEntropy
