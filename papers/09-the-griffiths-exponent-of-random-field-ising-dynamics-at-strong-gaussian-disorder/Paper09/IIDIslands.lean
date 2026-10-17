/-
The actual general i.i.d. field law and the island probability estimate of
paper.txt S2.p14. No symmetry, density, or unbounded-tail assumption is used.
-/
import Paper09.IslandPlacement

open Finset BigOperators Real MeasureTheory Classical
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Paper09.RFIM
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
local instance (priority := 2000) iidPointDecEq (d : ℕ) : DecidableEq (Point d) := Classical.decEq _
local instance (priority := 2000) iidSiteDecEq {d : ℕ} (A : Finset (Point d)) :
    DecidableEq ↥A := Classical.decEq _

/-- Independent copies of an arbitrary real one-site disorder law on `ℤᵈ`. -/
def iidEnvironmentLaw (d : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν] : Measure (Point d → ℝ) :=
  Measure.infinitePi (fun _ : Point d => ν)

instance iidEnvironmentLaw_isProbabilityMeasure (d : ℕ) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (iidEnvironmentLaw d ν) := by
  unfold iidEnvironmentLaw
  infer_instance

/-- The precise eventual small-ball hypothesis in S2.p14. -/
def PolynomialSmallBall (ν : Measure ℝ) : Prop :=
  ∃ (c : ℝ), c > 0 ∧ ∃ (α : ℝ), α > 0 ∧ ∃ (u₀ : ℝ), u₀ > 0 ∧ ∀ u : ℝ, 0 < u → u ≤ u₀ →
    c * u ^ α ≤ ν.real {x : ℝ | |x| ≤ u}

/-- Actual disjoint lattice coordinates have the product law for arbitrary
one-site real distributions, with no independence certificate premise. -/
theorem iid_environment_placement_law (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (d n m : ℕ) :
    (iidEnvironmentLaw d ν).map (fun h (k : Candidate d n m) x =>
      h (placementCoordinate ⟨k,x⟩)) =
      Measure.pi (fun _ : Candidate d n m =>
        Measure.pi (fun _ : ↥(pureBox d m) ⊕ ↥(externalBoundary (pureBox d m)) => ν)) := by
  exact ProductCoordinates.infinitePi_map_groups (fun _ : Point d => ν)
    placementCoordinate (placementCoordinate_injective d n m)

/-- Inverse-scale polynomial small balls, with an explicit eventual cutoff. -/
theorem polynomial_small_ball_inverse (ν : Measure ℝ) (ε : ℝ)
    (hε : 0 < ε) (hsmall : PolynomialSmallBall ν) :
    ∃ (a : ℝ), a > 0 ∧ ∃ (α : ℝ), α > 0 ∧ ∃ m₀ : ℕ, ∀ m : ℕ, 1 ≤ m → m₀ ≤ m →
      a / (m : ℝ)^α ≤ ν.real {x : ℝ | |x| ≤ ε/m} := by
  obtain ⟨c,hc,α,hα,u₀,hu₀,hb⟩ := hsmall
  refine ⟨c*ε^α,by positivity,α,hα,Nat.ceil (ε/u₀),?_⟩
  intro m hm hm₀
  have hmpos : (0:ℝ) < m := by exact_mod_cast (by omega : 0<m)
  have hquot : ε/u₀ ≤ (m:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hm₀)
  have hu : ε/(m:ℝ) ≤ u₀ := by
    apply (div_le_iff₀ hmpos).mpr
    have hh := (div_le_iff₀ hu₀).mp hquot
    nlinarith
  have hh := hb (ε/m) (div_pos hε hmpos) hu
  rw [Real.div_rpow hε.le hmpos.le] at hh
  convert hh using 1 <;> ring

/-- Without symmetry, the two prescribed shell signs use their own actual
one-sided probabilities. Their minimum gives a uniform sign-independent bound. -/
theorem iid_island_probability_ge (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (B S : Type*) [Fintype B] [Fintype S] (ζ : S → Bool) (u H : ℝ) :
    (ν.real {x : ℝ | |x| ≤ u}) ^ Fintype.card B *
      (min (ν.real (Set.Ici H)) (ν.real (Set.Iic (-H)))) ^ Fintype.card S ≤
    (Measure.pi (fun _ : B ⊕ S => ν)).real (Gaussian.islandEvent B S ζ u H) := by
  unfold Gaussian.islandEvent
  simp only [measureReal_def]
  rw [Measure.pi_pi,ENNReal.toReal_prod,Fintype.prod_sum_type]
  simp only [Sum.elim_inl,Sum.elim_inr]
  have hB : (∏ _b : B, (ν {x : ℝ | |x| ≤ u}).toReal) =
      (ν.real {x : ℝ | |x| ≤ u})^Fintype.card B := by simp [measureReal_def]
  rw [hB]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg measureReal_nonneg _)
  calc
    (min (ν.real (Set.Ici H)) (ν.real (Set.Iic (-H))))^Fintype.card S =
        ∏ _s : S, min (ν.real (Set.Ici H)) (ν.real (Set.Iic (-H))) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => le_min measureReal_nonneg measureReal_nonneg)
      (fun s _ => by
        cases hs : ζ s
        · simpa only [hs, Bool.false_eq_true, ↓reduceIte, measureReal_def] using
            (min_le_right (ν.real (Set.Ici H)) (ν.real (Set.Iic (-H))))
        · simpa only [hs, ↓reduceIte, measureReal_def] using
            (min_le_left (ν.real (Set.Ici H)) (ν.real (Set.Iic (-H)))))

/-- The general one-island log cost. The polynomial exponent is absorbed in
one fixed constant; both tails are needed only at the given fixed threshold. -/
theorem iid_island_log_cost (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (ε H : ℝ) (hε : 0 < ε) (hsmall : PolynomialSmallBall ν)
    (htailPos : 0 < ν.real (Set.Ici H)) (htailNeg : 0 < ν.real (Set.Iic (-H))) :
    ∃ C > 0, ∃ m₀ : ℕ, ∀ (B S : Type*) [Fintype B] [Fintype S]
      (ζ : S → Bool) (m : ℕ), 1 ≤ m → m₀ ≤ m →
      0 < (Measure.pi (fun _ : B ⊕ S => ν)).real
        (Gaussian.islandEvent B S ζ (ε/m) H) ∧
      -log ((Measure.pi (fun _ : B ⊕ S => ν)).real
        (Gaussian.islandEvent B S ζ (ε/m) H)) ≤
        C * (Fintype.card B * (log m + 1) + Fintype.card S) := by
  obtain ⟨a,ha,α,hα,m₀,hweak⟩ := polynomial_small_ball_inverse ν ε hε hsmall
  let q := min (ν.real (Set.Ici H)) (ν.real (Set.Iic (-H)))
  have hq : 0 < q := lt_min htailPos htailNeg
  let C : ℝ := max 1 (max α (max (-log a) (-log q)))
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCα : α ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCa : -log a ≤ C := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hCq : -log q ≤ C := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨C,by linarith,m₀,?_⟩
  intro B S _ _ ζ m hm hm₀
  let p := ν.real {x : ℝ | |x| ≤ ε/m}
  have hmpos : (0:ℝ)<m := by exact_mod_cast (by omega : 0<m)
  have hp : 0 < p := (div_pos ha (Real.rpow_pos_of_pos hmpos α)).trans_le (hweak m hm hm₀)
  have hplog := Real.log_le_log (div_pos ha (Real.rpow_pos_of_pos hmpos α)) (hweak m hm hm₀)
  rw [Real.log_div ha.ne' (Real.rpow_pos_of_pos hmpos α).ne',Real.log_rpow hmpos] at hplog
  have hlm : 0 ≤ log (m:ℝ) := Real.log_nonneg (by exact_mod_cast hm)
  have hpcost : -log p ≤ C*(log m+1) := by
    have hh := mul_le_mul_of_nonneg_right hCα hlm
    change log a - α*log m ≤ log p at hplog
    nlinarith only [hh,hCa,hplog]
  have hlower := iid_island_probability_ge ν B S ζ (ε/m) H
  have hpos := (mul_pos (pow_pos hp _) (pow_pos hq _)).trans_le hlower
  refine ⟨hpos,?_⟩
  have hlog := Real.log_le_log (mul_pos (pow_pos hp _) (pow_pos hq _)) hlower
  change log (p^Fintype.card B*q^Fintype.card S) ≤ _ at hlog
  rw [Real.log_mul (pow_pos hp _).ne' (pow_pos hq _).ne',Real.log_pow,Real.log_pow] at hlog
  have hbcost := mul_le_mul_of_nonneg_left hpcost (Nat.cast_nonneg (Fintype.card B) : (0:ℝ)≤_)
  have hscost := mul_le_mul_of_nonneg_left hCq (Nat.cast_nonneg (Fintype.card S) : (0:ℝ)≤_)
  nlinarith only [hlog,hbcost,hscost]

/-- The original geometric (2.10) cost for arbitrary one-site laws of S2.p14. -/
theorem iid_island_log_cost_geometric (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (d : ℕ) (ε H : ℝ) (hε : 0 < ε) (hsmall : PolynomialSmallBall ν)
    (htailPos : 0 < ν.real (Set.Ici H)) (htailNeg : 0 < ν.real (Set.Iic (-H))) :
    ∃ C > 0, ∃ m₀ : ℕ, ∀ (B S : Type*) [Fintype B] [Fintype S] (ζ : S → Bool)
      (m : ℕ), 2 ≤ m → m₀ ≤ m → Fintype.card B = m^d →
      Fintype.card S ≤ 2*d*m^(d-1) →
      0 < (Measure.pi (fun _ : B ⊕ S => ν)).real (Gaussian.islandEvent B S ζ (ε/m) H) ∧
      -log ((Measure.pi (fun _ : B ⊕ S => ν)).real (Gaussian.islandEvent B S ζ (ε/m) H)) ≤
        C*(m:ℝ)^d*log m := by
  obtain ⟨C,hC,m₀,hcost⟩ := iid_island_log_cost ν ε H hε hsmall htailPos htailNeg
  let D : ℝ := 1+(1+2*d)/log 2
  refine ⟨C*D,by dsimp [D]; positivity,m₀,?_⟩
  intro B S _ _ ζ m hm hm₀ hB hS
  obtain ⟨hp,hcost⟩ := hcost B S ζ m (by omega) hm₀
  refine ⟨hp,hcost.trans ?_⟩
  have hg := Gaussian.geometric_cost_bound (C := 1) (by norm_num) d m hm
  have hS' : (Fintype.card S : ℝ) ≤ 2*d*(m:ℝ)^(d-1) := by exact_mod_cast hS
  rw [hB]
  push_cast
  simp only [mul_one, one_mul] at hg
  calc
    C*((m:ℝ)^d*(log m+1)+(Fintype.card S:ℝ)) ≤
        C*((m:ℝ)^d*(log m+1)+2*d*(m:ℝ)^(d-1)) :=
      mul_le_mul_of_nonneg_left (add_le_add_left hS' _) hC.le
    _ ≤ C*(D*(m:ℝ)^d*log m) := mul_le_mul_of_nonneg_left hg hC.le
    _ = C*D*(m:ℝ)^d*log m := by ring

/-- Disjoint actual lattice islands obey the same absence estimate under the
precise eventual small-ball and two fixed positive-tail assumptions of S2.p14. -/
theorem no_iid_lattice_island_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (d : ℕ) (ε H : ℝ) (hε : 0 < ε) (hsmall : PolynomialSmallBall ν)
    (htailPos : 0 < ν.real (Set.Ici H)) (htailNeg : 0 < ν.real (Set.Iic (-H))) :
    ∃ C > 0, ∃ m₀ : ℕ, ∀ (n m : ℕ)
      (ζ : ↥(externalBoundary (pureBox d m)) → Bool), 2 ≤ m → m₀ ≤ m →
      (iidEnvironmentLaw d ν).real {h | ∀ k : Candidate d n m,
        h ∉ islandOccurs ζ (ε/m) H k} ≤
      exp (-((n / (m+2) : ℕ) : ℝ)^d * exp (-C*(m:ℝ)^d*log m)) := by
  obtain ⟨C,hC,m₀,hcost⟩ := iid_island_log_cost_geometric ν d ε H hε hsmall htailPos htailNeg
  refine ⟨C,hC,m₀,?_⟩
  intro n m ζ hm hm₀
  let B := ↥(pureBox d m)
  let S := ↥(externalBoundary (pureBox d m))
  let J := Candidate d n m
  let E := Gaussian.islandEvent B S ζ (ε/m) H
  let F : (Point d → ℝ) → J → (B ⊕ S → ℝ) :=
    fun h k x => h (placementCoordinate ⟨k,x⟩)
  have hE : MeasurableSet E := Gaussian.measurableSet_islandEvent B S ζ _ _
  have hmap := iid_environment_placement_law ν d n m
  have heq : (iidEnvironmentLaw d ν).real
      {h | ∀ k : J, h ∉ islandOccurs ζ (ε/m) H k} =
      (Measure.pi (fun _ : J => Measure.pi (fun _ : B ⊕ S => ν))).real
        (Set.univ.pi (fun _ : J => Eᶜ)) := by
    have hs : {h | ∀ k : J, h ∉ islandOccurs ζ (ε/m) H k} =
        F ⁻¹' (Set.univ.pi (fun _ : J => Eᶜ)) := by
      ext h
      simp only [F, E, islandOccurs, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
        forall_const, Set.mem_compl_iff, Set.mem_setOf_eq]
      rfl
    rw [hs, measureReal_def, measureReal_def, ← hmap,
      Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi (fun _ => hE.compl))]
  have hB : Fintype.card B = m^d := by simp [B]
  have hS : Fintype.card S ≤ 2*d*m^(d-1) := by
    simpa [S] using card_externalBoundary_pureBox_le d m
  obtain ⟨hp,hcost⟩ := hcost B S ζ m hm hm₀ hB hS
  have hlower : exp (-C*(m:ℝ)^d*log m) ≤
      (Measure.pi (fun _ : B ⊕ S => ν)).real E := by
    rw [← Real.exp_log hp]
    apply Real.exp_le_exp.mpr
    dsimp [E]
    linarith
  rw [heq]
  apply (Gaussian.no_occurrence_bound (J := J) (Measure.pi (fun _ : B ⊕ S => ν)) E hE).trans
  apply Real.exp_le_exp.mpr
  have hJ : (Fintype.card J : ℝ) = ((n/(m+2) : ℕ):ℝ)^d := by simp [J]
  rw [hJ]
  exact mul_le_mul_of_nonpos_left hlower (neg_nonpos.mpr (by positivity))

end Paper09.RFIM
