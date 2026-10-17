import Paper08.Support
import Paper08.MultiMoments
import Paper08.Interaction
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.Data.Finsupp.Weight
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting

noncomputable section
open scoped BigOperators
namespace Paper08.ModelSupport
open MvPowerSeries

variable {ι : Type*} [DecidableEq ι]

/-- Euler derivation: multiply each monomial by its total degree. -/
def euler (F : MvPowerSeries ι ℝ) : MvPowerSeries ι ℝ :=
  fun d => (d.degree : ℝ) * coeff d F

@[simp] theorem coeff_euler (F : MvPowerSeries ι ℝ) (d : ι →₀ ℕ) :
    coeff d (euler F) = (d.degree : ℝ) * coeff d F := rfl

@[simp] theorem constantCoeff_euler (F : MvPowerSeries ι ℝ) :
    constantCoeff (euler F) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_euler]
  simp [Finsupp.degree]

theorem euler_add (F G : MvPowerSeries ι ℝ) : euler (F + G) = euler F + euler G := by
  ext d
  simp [mul_add]

theorem degree_add (a b : ι →₀ ℕ) : (a + b).degree = a.degree + b.degree := by
  rw [Finsupp.degree_eq_weight_one, map_add]

theorem euler_mul (F G : MvPowerSeries ι ℝ) :
    euler (F * G) = euler F * G + F * euler G := by
  ext d
  simp only [coeff_euler, coeff_mul, map_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := Finset.mem_antidiagonal.mp hp
  have hd : d.degree = p.1.degree + p.2.degree := by rw [← hp', degree_add]
  rw [hd, Nat.cast_add]
  ring

/-- Formal logarithm normalized at zero. The radial derivative is `Q'/Q`;
radial integration divides a monomial by its positive total degree. -/
def formalLog (Q : MvPowerSeries ι ℝ) : MvPowerSeries ι ℝ :=
  fun d => coeff d (euler Q * Q⁻¹) / (d.degree : ℝ)

@[simp] theorem coeff_formalLog (Q : MvPowerSeries ι ℝ) (d : ι →₀ ℕ) :
    coeff d (formalLog Q) = coeff d (euler Q * Q⁻¹) / (d.degree : ℝ) := rfl

@[simp] theorem constantCoeff_formalLog (Q : MvPowerSeries ι ℝ) :
    constantCoeff (formalLog Q) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_formalLog]
  simp [Finsupp.degree]

theorem euler_formalLog (Q : MvPowerSeries ι ℝ) :
    euler (formalLog Q) = euler Q * Q⁻¹ := by
  ext d
  rw [coeff_euler, coeff_formalLog]
  by_cases hd : d = 0
  · subst d
    simp [coeff_zero_eq_constantCoeff_apply, constantCoeff_euler, Finsupp.degree]
  · have hn : (d.degree : ℝ) ≠ 0 := by
      exact_mod_cast (show d.degree ≠ 0 from fun h => hd ((Finsupp.degree_eq_zero_iff d).mp h))
    exact mul_div_cancel₀ _ hn

theorem euler_injective_normalized (F G : MvPowerSeries ι ℝ)
    (hF : constantCoeff F = 0) (hG : constantCoeff G = 0) (h : euler F = euler G) : F = G := by
  ext d
  by_cases hd : d = 0
  · subst d
    simpa only [coeff_zero_eq_constantCoeff_apply, hF, hG]
  · have hn : (d.degree : ℝ) ≠ 0 := by
      exact_mod_cast (show d.degree ≠ 0 from fun h => hd ((Finsupp.degree_eq_zero_iff d).mp h))
    have hc := congrArg (coeff d) h
    simp only [coeff_euler] at hc
    exact mul_left_cancel₀ hn hc

/-- Multiplication of normalized moment series gives addition of their actual
formal logarithms; no additive-decomposition certificate is an input. -/
theorem formalLog_mul (F G : MvPowerSeries ι ℝ)
    (hF : constantCoeff F ≠ 0) (hG : constantCoeff G ≠ 0) :
    formalLog (F * G) = formalLog F + formalLog G := by
  apply euler_injective_normalized
  · exact constantCoeff_formalLog _
  · simp
  rw [euler_formalLog, euler_add, euler_formalLog, euler_formalLog,
    euler_mul, MvPowerSeries.mul_inv_rev]
  calc
    (euler F * G + F * euler G) * (G⁻¹ * F⁻¹) =
        euler F * F⁻¹ * (G * G⁻¹) + euler G * G⁻¹ * (F * F⁻¹) := by ring
    _ = euler F * F⁻¹ + euler G * G⁻¹ := by
      rw [MvPowerSeries.mul_inv_cancel F hF, MvPowerSeries.mul_inv_cancel G hG]
      simp

theorem support_add_subset (a b : ι →₀ ℕ) (B : Finset ι) :
    (a + b).support ⊆ B ↔ a.support ⊆ B ∧ b.support ⊆ B := by
  simp only [Finset.subset_iff, Finsupp.mem_support_iff, Finsupp.add_apply, ne_eq,
    Nat.add_eq_zero, not_and_or, or_imp, forall_and]

theorem restrict_mul (B : Finset ι) (F G : MvPowerSeries ι ℝ) :
    Support.restrictSeries B (F * G) = Support.restrictSeries B F * Support.restrictSeries B G := by
  ext d
  rw [Support.coeff_restrictSeries, coeff_mul]
  rw [coeff_mul]
  by_cases hd : d.support ⊆ B
  · rw [if_pos hd]
    apply Finset.sum_congr rfl
    intro p hp
    have hab : p.1.support ⊆ B ∧ p.2.support ⊆ B :=
      (support_add_subset _ _ _).mp (by rw [Finset.mem_antidiagonal.mp hp]; exact hd)
    simp only [Support.coeff_restrictSeries, if_pos hab.1, if_pos hab.2]
  · rw [if_neg hd]
    symm
    apply Finset.sum_eq_zero
    intro p hp
    have hab : ¬ (p.1.support ⊆ B ∧ p.2.support ⊆ B) := by
      rw [← support_add_subset, Finset.mem_antidiagonal.mp hp]
      exact hd
    simp only [Support.coeff_restrictSeries]
    by_cases ha : p.1.support ⊆ B
    · simp [ha, show ¬ p.2.support ⊆ B from fun hb => hab ⟨ha, hb⟩]
    · simp [ha]

@[simp] theorem constantCoeff_restrict (B : Finset ι) (F : MvPowerSeries ι ℝ) :
    constantCoeff (Support.restrictSeries B F) = constantCoeff F := by
  rw [← coeff_zero_eq_constantCoeff_apply, Support.coeff_restrictSeries]
  simp [coeff_zero_eq_constantCoeff_apply]

theorem restrict_one (B : Finset ι) : Support.restrictSeries B (1 : MvPowerSeries ι ℝ) = 1 := by
  ext d
  rw [Support.coeff_restrictSeries]
  by_cases hd : d = 0
  · subst d; simp
  · simp [coeff_one, hd]

theorem restrict_inv (B : Finset ι) (F : MvPowerSeries ι ℝ) (hF : constantCoeff F ≠ 0) :
    Support.restrictSeries B F⁻¹ = (Support.restrictSeries B F)⁻¹ := by
  apply (MvPowerSeries.eq_inv_iff_mul_eq_one (by simpa using hF)).mpr
  rw [← restrict_mul, MvPowerSeries.inv_mul_cancel F hF, restrict_one]

theorem euler_restrict (B : Finset ι) (F : MvPowerSeries ι ℝ) :
    euler (Support.restrictSeries B F) = Support.restrictSeries B (euler F) := by
  ext d
  simp only [coeff_euler, Support.coeff_restrictSeries]
  split_ifs <;> simp

/-- Restriction to a coordinate subspace commutes with the normalized formal logarithm. -/
theorem formalLog_restrict (B : Finset ι) (F : MvPowerSeries ι ℝ)
    (hF : constantCoeff F ≠ 0) :
    formalLog (Support.restrictSeries B F) = Support.restrictSeries B (formalLog F) := by
  ext d
  rw [coeff_formalLog, ← restrict_inv B F hF, euler_restrict, ← restrict_mul,
    Support.coeff_restrictSeries, Support.coeff_restrictSeries, coeff_formalLog]
  split_ifs <;> simp

/-- A logarithmic coefficient is zero if it uses a variable outside the restricted model. -/
theorem coeff_formalLog_restrict_eq_zero (B : Finset ι) (F : MvPowerSeries ι ℝ)
    (hF : constantCoeff F ≠ 0) (d : ι →₀ ℕ) (hd : ¬ d.support ⊆ B) :
    coeff d (formalLog (Support.restrictSeries B F)) = 0 := by
  rw [formalLog_restrict B F hF, Support.coeff_restrictSeries, if_neg hd]

/-- A disconnected collection has a nontrivial partition whose actual variable
sets are disjoint. This is derived from the factor-intersection graph. -/
theorem disconnected_partition {n r m : ℕ} (E : FactorFamily n r m)
    (A : Finset (Fin m)) (hne : A.Nonempty)
    (hconn : ¬ ((Interaction.graph E).induce (A : Set (Fin m))).Connected) :
    ∃ B C : Finset (Fin m), Disjoint B C ∧ B ∪ C = A ∧
      (¬ A ⊆ B) ∧ (¬ A ⊆ C) ∧
      Disjoint (MultiMoments.factorVariables E B) (MultiMoments.factorVariables E C) := by
  classical
  let G := (Interaction.graph E).induce (A : Set (Fin m))
  have hpc : ¬ G.Preconnected := by
    intro h
    obtain ⟨e, he⟩ := hne
    letI : Nonempty (A : Set (Fin m)) := ⟨⟨e, he⟩⟩
    exact hconn ⟨h⟩
  change ¬ ∀ u v, G.Reachable u v at hpc
  push_neg at hpc
  obtain ⟨u, v, huv⟩ := hpc
  let B := A.filter fun e => ∀ h : e ∈ A, G.Reachable u ⟨e, h⟩
  let C := A \ B
  have hBA : B ⊆ A := Finset.filter_subset _ _
  have huB : u.val ∈ B := by
    apply Finset.mem_filter.mpr
    exact ⟨u.property, fun _ => by simpa using (SimpleGraph.Reachable.refl (G := G) u)⟩
  have hvC : v.val ∈ C := by
    apply Finset.mem_sdiff.mpr
    refine ⟨v.property, ?_⟩
    intro hvB
    exact huv ((Finset.mem_filter.mp hvB).2 v.property)
  have hBC : Disjoint B C := by
    apply Finset.disjoint_left.mpr
    intro i hiB hiC
    exact (Finset.mem_sdiff.mp hiC).2 hiB
  refine ⟨B, C, hBC, Finset.union_sdiff_of_subset hBA,
    (fun h => Finset.disjoint_left.mp hBC (h v.property) hvC),
    (fun h => Finset.disjoint_left.mp hBC huB (h u.property)), ?_⟩
  apply Finset.disjoint_left.mpr
  intro x hxB hxC
  obtain ⟨e, heB, hxe⟩ := Finset.mem_biUnion.mp hxB
  obtain ⟨f, hfC, hxf⟩ := Finset.mem_biUnion.mp hxC
  have heA := hBA heB
  have hfA := (Finset.mem_sdiff.mp hfC).1
  have hef : e ≠ f := by
    intro heq
    subst f
    exact Finset.disjoint_left.mp hBC heB hfC
  have hadj : G.Adj ⟨e, heA⟩ ⟨f, hfA⟩ := ⟨hef, x, hxe, hxf⟩
  have hreach : G.Reachable u ⟨f, hfA⟩ :=
    ((Finset.mem_filter.mp heB).2 heA).trans hadj.reachable
  have hfB : f ∈ B := Finset.mem_filter.mpr ⟨hfA, fun _ => hreach⟩
  exact Finset.disjoint_left.mp hBC hfB hfC

/-- The actual moment integrals force disconnected full-support logarithmic
coefficients to vanish. No decomposition or vanishing hypothesis is supplied. -/
theorem supportSeries_log_eq_zero_of_disconnected {n r m : ℕ}
    (E : FactorFamily n r m) (A : Finset (Fin m)) (hne : A.Nonempty)
    (hconn : ¬ ((Interaction.graph E).induce (A : Set (Fin m))).Connected) :
    Support.supportSeries A (formalLog (MultiMoments.momentSeries E)) = 0 := by
  obtain ⟨B, C, hBC, hUnion, hAB, hAC, hvars⟩ := disconnected_partition E A hne hconn
  let Q := MultiMoments.momentSeries E
  have hQ : constantCoeff Q ≠ 0 := by simp [Q]
  have hlog : Support.restrictSeries A (formalLog Q) =
      Support.restrictSeries B (formalLog Q) + Support.restrictSeries C (formalLog Q) := by
    rw [← formalLog_restrict A Q hQ, ← hUnion,
      MultiMoments.momentSeries_restrict_mul E B C hBC hvars,
      formalLog_mul _ _ (by simp) (by simp), formalLog_restrict B Q hQ,
      formalLog_restrict C Q hQ]
  ext d
  rw [Support.coeff_supportSeries]
  by_cases hd : d.support = A
  · have hc := congrArg (coeff d) hlog
    simp only [Support.coeff_restrictSeries, map_add, hd, if_pos (Finset.Subset.refl A),
      if_neg hAB, if_neg hAC, add_zero] at hc
    simp only [hd, if_pos rfl, map_zero]
    exact hc
  · simp [hd]

/-- The coefficient of the normalized formal logarithm after the actual
specialization `w_e = z` for `e ∈ B`, zero otherwise. -/
def logCoeff {n r m : ℕ} (E : FactorFamily n r m) (B : Finset (Fin m)) (p : ℕ) : ℝ :=
  PowerSeries.coeff p (MultiMoments.diagonalHom (Fin m)
    (formalLog (Support.restrictSeries B (MultiMoments.momentSeries E))))

/-- The contribution of one exact support to a univariate coefficient. -/
def supportCoeff {n r m : ℕ} (E : FactorFamily n r m) (A : Finset (Fin m)) (p : ℕ) : ℝ :=
  PowerSeries.coeff p (MultiMoments.diagonalHom (Fin m)
    (Support.supportSeries A (formalLog (MultiMoments.momentSeries E))))

theorem supportCoeff_eq_mobius {n r m : ℕ} (E : FactorFamily n r m)
    (A : Finset (Fin m)) (p : ℕ) :
    supportCoeff E A p = Support.mobius (fun B => logCoeff E B p) A := by
  have hQ : constantCoeff (MultiMoments.momentSeries E) ≠ 0 := by simp
  simp only [supportCoeff, logCoeff, MultiMoments.coeff_diagonalHom, Support.mobius]
  simp_rw [formalLog_restrict _ _ hQ]
  simp only [Support.supportSeries, map_sum, MvPowerSeries.coeff_C_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro B hB
  rw [Finset.mul_sum]

theorem sum_supportCoeff {n r m : ℕ} (E : FactorFamily n r m) (p : ℕ) :
    (∑ A ∈ (Finset.univ : Finset (Fin m)).powerset, supportCoeff E A p) =
      logCoeff E Finset.univ p := by
  simp_rw [supportCoeff_eq_mobius]
  exact Support.sum_mobius _ _

theorem supportCoeff_empty {n r m : ℕ} (E : FactorFamily n r m) (p : ℕ) :
    supportCoeff E ∅ p = 0 := by
  unfold supportCoeff
  rw [Support.supportSeries_empty _ (constantCoeff_formalLog _)]
  simp

theorem supportCoeff_eq_zero_of_card {n r m : ℕ} (E : FactorFamily n r m)
    (A : Finset (Fin m)) (p : ℕ) (hp : p < A.card) : supportCoeff E A p = 0 := by
  unfold supportCoeff
  rw [MultiMoments.coeff_diagonalHom]
  apply Finset.sum_eq_zero
  intro d hd
  apply Support.coeff_supportSeries_eq_zero_of_degree_lt
  rw [(MultiMoments.mem_degreeIndices d p).mp hd]
  exact hp

theorem supportCoeff_eq_zero_of_disconnected {n r m : ℕ} (E : FactorFamily n r m)
    (A : Finset (Fin m)) (hne : A.Nonempty)
    (hconn : ¬ ((Interaction.graph E).induce (A : Set (Fin m))).Connected) (p : ℕ) :
    supportCoeff E A p = 0 := by
  unfold supportCoeff
  rw [supportSeries_log_eq_zero_of_disconnected E A hne hconn]
  simp

/-- Equation (2.10), for the actual moment integrals and their normalized
formal logarithm. The summation contains precisely the connected supports. -/
theorem connected_support_identity {n r m : ℕ} (E : FactorFamily n r m) (p : ℕ) :
    logCoeff E Finset.univ p =
      ∑ A ∈ ((Finset.univ : Finset (Fin m)).powerset.filter fun A : Finset (Fin m) =>
        A.Nonempty ∧ A.card ≤ p ∧ ((Interaction.graph E).induce (A : Set (Fin m))).Connected),
        ∑ B ∈ A.powerset, (-1 : ℝ) ^ (A.card - B.card) * logCoeff E B p := by
  classical
  rw [← sum_supportCoeff E p]
  have hfilter :
      (∑ A ∈ ((Finset.univ : Finset (Fin m)).powerset.filter fun A : Finset (Fin m) =>
          A.Nonempty ∧ A.card ≤ p ∧ ((Interaction.graph E).induce (A : Set (Fin m))).Connected),
        supportCoeff E A p) =
      ∑ A ∈ (Finset.univ : Finset (Fin m)).powerset, supportCoeff E A p := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro A hA
    by_cases hne : A.Nonempty
    · by_cases hcard : A.card ≤ p
      · by_cases hc : ((Interaction.graph E).induce (A : Set (Fin m))).Connected
        · simp [hne, hcard, hc]
        · simp [hne, hcard, hc, supportCoeff_eq_zero_of_disconnected E A hne hc p]
      · simp [hcard, supportCoeff_eq_zero_of_card E A p (by omega)]
    · have hempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst A
      simp [supportCoeff_empty]
  rw [← hfilter]
  apply Finset.sum_congr rfl
  intro A hA
  exact supportCoeff_eq_mobius E A p

/-- Diagonal specialization intertwines the Euler derivation with multiplication
of the scalar coefficient of order `p` by `p`. -/
theorem coeff_diagonal_euler {ι : Type*} [Fintype ι] (F : MvPowerSeries ι ℝ) (p : ℕ) :
    PowerSeries.coeff p (MultiMoments.diagonalHom ι (euler F)) =
      (p : ℝ) * PowerSeries.coeff p (MultiMoments.diagonalHom ι F) := by
  classical
  rw [MultiMoments.coeff_diagonalHom, MultiMoments.coeff_diagonalHom, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [coeff_euler, (MultiMoments.mem_degreeIndices d p).mp hd]

/-- The formal logarithm solves the Euler differential equation of the actual
moment series. -/
theorem euler_formalLog_mul (Q : MvPowerSeries ι ℝ) (hQ : constantCoeff Q ≠ 0) :
    euler (formalLog Q) * Q = euler Q := by
  rw [euler_formalLog, mul_assoc, MvPowerSeries.inv_mul_cancel Q hQ, mul_one]

end Paper08.ModelSupport
