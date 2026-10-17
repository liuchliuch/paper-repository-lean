import PsgEst.Concentration
import PsgEst.ProbabilityResidues
import PsgEst.NormIdentity
import PsgEst.FiniteHolder
import PsgEst.PaulinSpectral

/-!
# Finite stationary Bernstein inequality

Finite exponential moments, residue classes, and the Chernoff optimization
for the corrected stationary Bernstein bound.
-/

open Matrix BigOperators Real Finset
namespace PsgEst.PaulinProof

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Exponential Markov inequality for a finite nonnegative measure. -/
theorem exponential_markov {α : Type*} [Fintype α]
    (w X : α → ℝ) (hw : ∀ x, 0 ≤ w x) (θ u : ℝ) (hθ : 0 ≤ θ) :
    (∑ x, if u ≤ X x then w x else 0) ≤
      exp (-θ*u) * ∑ x, w x * exp (θ*X x) := by
  classical
  rw [mul_sum]
  apply sum_le_sum
  intro x _
  by_cases hx : u ≤ X x
  · rw [if_pos hx]
    have he : 1 ≤ exp (θ*(X x-u)) := Real.one_le_exp_iff.mpr
      (mul_nonneg hθ (sub_nonneg.mpr hx))
    calc w x = w x * 1 := (mul_one _).symm
      _ ≤ w x * exp (θ*(X x-u)) := mul_le_mul_of_nonneg_left he (hw x)
      _ = exp (-θ*u) * (w x * exp (θ*X x)) := by
        rw [← mul_assoc, mul_comm (exp (-θ*u)) (w x), mul_assoc, ← exp_add]
        congr 2
        ring
  · rw [if_neg hx]
    exact mul_nonneg (exp_nonneg _) (mul_nonneg (hw x) (exp_nonneg _))

/-- Exact algebra in the Bernstein Chernoff optimization. -/
lemma bernstein_optimization (N V b γ u : ℝ)
    (hN : 0 < N) (hV : 0 < V) (hb : 0 ≤ b) (hγ : 0 < γ) (hu : 0 < u) :
    let θ := u*γ/(4*N*V+10*b*u)
    0 < θ ∧ 10*b*θ < γ ∧
      -θ*u + 2*N*V*θ^2/(γ-10*b*θ) =
        -(u^2*γ)/(8*N*V+20*u*b) := by
  dsimp only
  have hden : 0 < 4*N*V+10*b*u := by positivity
  have hd2 : 0 < 8*N*V+20*u*b := by positivity
  have hgap : 0 < γ-10*b*(u*γ/(4*N*V+10*b*u)) := by
    apply sub_pos.mpr
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hden).mpr
    nlinarith [mul_pos hN hV, mul_pos (mul_pos hN hV) hγ]
  refine ⟨by positivity, by linarith, ?_⟩
  field_simp
  ring

/-- A scalar MGF bound implies the one-sided Bernstein tail. -/
theorem bernstein_one_sided {α : Type*} [Fintype α]
    (w X : α → ℝ) (hw : ∀ x, 0 ≤ w x) (N V b γ u : ℝ)
    (hN : 0 < N) (hV : 0 < V) (hb : 0 ≤ b) (hγ : 0 < γ) (hu : 0 < u)
    (hmgf : ∀ θ : ℝ, 0 ≤ θ → 10*b*θ < γ →
      (∑ x, w x * exp (θ*X x)) ≤ exp (2*N*V*θ^2/(γ-10*b*θ))) :
    (∑ x, if u ≤ X x then w x else 0) ≤
      exp (-(u^2*γ)/(8*N*V+20*u*b)) := by
  let θ := u*γ/(4*N*V+10*b*u)
  obtain ⟨hθ, hdomain, heq⟩ := bernstein_optimization N V b γ u hN hV hb hγ hu
  calc _ ≤ exp (-θ*u) * ∑ x, w x * exp (θ*X x) :=
      exponential_markov w X hw θ u hθ.le
    _ ≤ exp (-θ*u) * exp (2*N*V*θ^2/(γ-10*b*θ)) :=
      mul_le_mul_of_nonneg_left (hmgf θ hθ.le hdomain) (exp_nonneg _)
    _ = _ := by rw [← exp_add, heq]

/-- The two Chernoff signs give the required absolute-deviation tail. -/
theorem bernstein_two_sided {α : Type*} [Fintype α]
    (w X : α → ℝ) (hw : ∀ x, 0 ≤ w x) (N V b γ u : ℝ)
    (hN : 0 < N) (hV : 0 < V) (hb : 0 ≤ b) (hγ : 0 < γ) (hu : 0 < u)
    (hmgf : ∀ (sgn : ℝ), sgn = 1 ∨ sgn = -1 → ∀ θ : ℝ,
      0 ≤ θ → 10*b*θ < γ →
      (∑ x, w x * exp (θ*(sgn*X x))) ≤ exp (2*N*V*θ^2/(γ-10*b*θ))) :
    (∑ x, if u ≤ |X x| then w x else 0) ≤
      2*exp (-(u^2*γ)/(8*N*V+20*u*b)) := by
  classical
  have hp := bernstein_one_sided w X hw N V b γ u hN hV hb hγ hu
    (by simpa only [one_mul] using hmgf 1 (Or.inl rfl))
  have hn := bernstein_one_sided w (fun x => -X x) hw N V b γ u hN hV hb hγ hu
    (by simpa only [neg_one_mul] using hmgf (-1) (Or.inr rfl))
  have hunion : (∑ x, if u ≤ |X x| then w x else 0) ≤
      (∑ x, if u ≤ X x then w x else 0) +
      (∑ x, if u ≤ -X x then w x else 0) := by
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro x _
    by_cases h : u ≤ |X x|
    · rw [if_pos h]
      obtain hpos | hneg := (le_abs.mp h)
      · rw [if_pos hpos]
        exact le_add_of_nonneg_right (by split_ifs <;> first | exact hw x | exact le_rfl)
      · rw [if_pos (by linarith : u ≤ -X x)]
        exact le_add_of_nonneg_left (by split_ifs <;> first | exact hw x | exact le_rfl)
    · rw [if_neg h]
      split_ifs <;> nlinarith [hw x]
  linarith

lemma stationary_shift {d : ℕ} (Q : Stoch d) (st : Stationary Q) (r : ℕ) :
    shiftedLaw Q.P st.mu r = st.mu := by
  funext j
  exact (stationaryPow Q st r).station j

lemma gamma_nonneg {d : ℕ} (Q : Stoch d) (st : Stationary Q) :
    0 ≤ gammaPS Q st :=
  gapGamma_nonneg _ (fun t => (aK_mem Q st t).2)

lemma centered_mean {d : ℕ} (Q : Stoch d) (st : Stationary Q) (f : Fin d → ℝ) :
    stationaryMean st.mu (fun i => f i-stationaryMean st.mu f) = 0 := by
  unfold stationaryMean
  simp_rw [mul_sub]
  rw [sum_sub_distrib, ← sum_mul, st.sum_one, one_mul, sub_self]

lemma variance_pos {d : ℕ} (Q : Stoch d) (st : Stationary Q) (f : Fin d → ℝ)
    (hf : ∃ i j, f i ≠ f j) : 0 < stationaryVariance st.mu f := by
  have hnonneg : ∀ i, 0 ≤ st.mu i*(f i-stationaryMean st.mu f)^2 := by
    intro i
    exact mul_nonneg (st.nonneg i) (sq_nonneg _)
  apply lt_of_le_of_ne (sum_nonneg (fun i _ => hnonneg i))
  intro hz
  have hall := (sum_eq_zero_iff_of_nonneg (fun i _ => hnonneg i)).mp hz.symm
  obtain ⟨i,j,hij⟩ := hf
  have hi : f i = stationaryMean st.mu f := by
    have hs := (mul_eq_zero.mp (hall i (mem_univ i))).resolve_left (ne_of_gt (st.pos i))
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
  have hj : f j = stationaryMean st.mu f := by
    have hs := (mul_eq_zero.mp (hall j (mem_univ j))).resolve_left (ne_of_gt (st.pos j))
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
  exact hij (hi.trans hj.symm)

lemma centered_stateSum {d m : ℕ} (Q : Stoch d) (st : Stationary Q)
    (f : Fin d → ℝ) (arrival : Bool) (Y : Fin (m+1) → Fin d) :
    stateSum (fun i => f i-stationaryMean st.mu f) arrival Y =
      stateSum f arrival Y - (m:ℝ)*stationaryMean st.mu f := by
  simp only [stateSum, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul]

/-- A finite path generating function is a product of tilted transition matrices. -/
lemma path_product_matrix {d n : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (mu h v : Fin d → ℝ) :
    (∑ Y : Fin (n+1) → Fin d,
      pathProb P mu Y * (∏ t : Fin (n+1), h (Y t)) * v (Y (Fin.last n))) =
      ∑ i, mu i*h i * (((P * diagonal h)^n) *ᵥ v) i := by
  induction n generalizing v with
  | zero =>
    rw [sum_single_path]
    simp [pathProb]
  | succ n ih =>
    rw [sum_path_snoc]
    have hprod (Y : Fin (n+1) → Fin d) (x : Fin d) :
        (∏ t : Fin (n+2), h (pathSnoc Y x t)) =
          (∏ t : Fin (n+1), h (Y t))*h x := by
      rw [Fin.prod_univ_castSucc]
      simp only [pathSnoc_castSucc, pathSnoc_last]
    simp_rw [pathProb_snoc, hprod, pathSnoc_last]
    have hinner (Y : Fin (n+1) → Fin d) :
        (∑ x, pathProb P mu Y * P (Y (Fin.last n)) x *
          ((∏ t : Fin (n+1), h (Y t)) * h x) * v x) =
        pathProb P mu Y * (∏ t : Fin (n+1), h (Y t)) *
          ((P*diagonal h)*ᵥv) (Y (Fin.last n)) := by
      simp only [mulVec, mul_diagonal, dotProduct, mul_sum]
      apply sum_congr rfl
      intro x _
      ring
    simp_rw [hinner]
    rw [ih, pow_succ, mulVec_mulVec]

lemma stationary_tilt_dot {d : ℕ} (Q : Stoch d) (st : Stationary Q)
    (h v : Fin d → ℝ) :
    st.mu ⬝ᵥ ((Q.P*diagonal h)*ᵥv) = ∑ i, st.mu i*h i*v i := by
  simp only [dotProduct, mulVec, mul_diagonal]
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  calc (∑ i, st.mu i*(Q.P i j*h j*v j)) =
      (∑ i, st.mu i*Q.P i j)*h j*v j := by
        simp_rw [sum_mul]
        apply sum_congr rfl
        intro i _
        ring
    _ = _ := by rw [st.station]

/-- Stationarity allows the initial tilt to be preceded by one transition. -/
lemma stationary_product_matrix {d n : ℕ} (Q : Stoch d) (st : Stationary Q)
    (h : Fin d → ℝ) :
    (∑ Y : Fin (n+1) → Fin d,
      pathProb Q.P st.mu Y * ∏ t : Fin (n+1), h (Y t)) =
      st.mu ⬝ᵥ (((Q.P*diagonal h)^(n+1))*ᵥ(fun _ => 1)) := by
  have hp := path_product_matrix (n:=n) Q.P st.mu h (fun _ => 1)
  simp only [mul_one] at hp
  rw [hp, pow_succ', ← mulVec_mulVec, stationary_tilt_dot]

lemma inverse_half_stVec {d : ℕ} (Q : Stoch d) (st : Stationary Q) (i : Fin d) :
    (st.mu i)^(-(1/2:ℝ))*stVec st i = 1 := by
  unfold stVec
  rw [← Real.rpow_add (st.pos i), show -(1/2:ℝ)+(1/2:ℝ)=0 by ring, Real.rpow_zero]

/-- Similarity transports a tilted transition without changing path products. -/
lemma tilted_weighted_mulVec {d : ℕ} (Q : Stoch d) (st : Stationary Q) (k : ℕ)
    (h v : Fin d → ℝ) :
    (Lk Q st k * diagonal h)*ᵥ(fun i => stVec st i*v i) =
      fun i => stVec st i * (((Q.P^k)*diagonal h)*ᵥv) i := by
  rw [← mulVec_mulVec]
  funext i
  rw [Lk_mulVec_apply]
  simp_rw [mulVec_diagonal]
  simp only [mulVec, mul_diagonal, dotProduct]
  change stVec st i * _ = stVec st i * _
  congr 1
  apply sum_congr rfl
  intro j _
  rw [show (st.mu j)^(-(1/2:ℝ))*(h j*(stVec st j*v j)) = h j*v j by
    calc _ = ((st.mu j)^(-(1/2:ℝ))*stVec st j)*(h j*v j) := by ring
      _ = _ := by rw [inverse_half_stVec, one_mul]]
  ring

lemma tilted_weighted_pow {d : ℕ} (Q : Stoch d) (st : Stationary Q) (k n : ℕ)
    (h v : Fin d → ℝ) :
    ((Lk Q st k * diagonal h)^n)*ᵥ(fun i => stVec st i*v i) =
      fun i => stVec st i * ((((Q.P^k)*diagonal h)^n)*ᵥv) i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_succ', ← mulVec_mulVec, ih, tilted_weighted_mulVec,
      mulVec_mulVec]

/-- Exact exponential moment as a Euclidean tilted matrix product. -/
lemma path_exp_matrix {d n : ℕ} (Q : Stoch d) (st : Stationary Q) (k : ℕ)
    (f : Fin d → ℝ) (θ : ℝ) :
    (∑ Y : Fin (n+1) → Fin d,
      pathProb (Q.P^k) st.mu Y * exp (θ*∑ t : Fin (n+1), f (Y t))) =
      stVec st ⬝ᵥ (((Lk Q st k*diagonal (fun i => exp (θ*f i)))^(n+1))*ᵥstVec st) := by
  have hp := stationary_product_matrix (n:=n) (Q.pow k) (stationaryPow Q st k)
    (fun i => exp (θ*f i))
  change (∑ Y, pathProb (Q.P^k) st.mu Y*_) = _ at hp
  have he (Y : Fin (n+1) → Fin d) :
      exp (θ*∑t : Fin (n+1), f (Y t)) = ∏ t : Fin (n+1), exp (θ*f (Y t)) := by
    rw [mul_sum, exp_sum]
  simp_rw [he]
  rw [hp]
  have ht := tilted_weighted_pow Q st k (n+1) (fun i => exp (θ*f i)) (fun _ => 1)
  simp only [mul_one] at ht
  rw [ht]
  simp only [dotProduct]
  apply sum_congr rfl
  intro i _
  rw [← mul_assoc, stVec_sq]
  rfl

/-- The stationary exponential moment is controlled by the true Euclidean norm. -/
theorem path_exp_le_norm {d n : ℕ} (Q : Stoch d) (st : Stationary Q) (k : ℕ)
    (f : Fin d → ℝ) (θ : ℝ) :
    (∑ Y : Fin (n+1) → Fin d,
      pathProb (Q.P^k) st.mu Y * exp (θ*∑ t : Fin (n+1), f (Y t))) ≤
      ‖Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)
        (Lk Q st k*diagonal (fun i => exp (θ*f i)))‖^(n+1) := by
  rw [path_exp_matrix]
  let A := Lk Q st k*diagonal (fun i => exp (θ*f i))
  let T := Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) A
  let v : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (stVec st)
  have hv : ‖v‖ = 1 := by
    have hs : ‖v‖^2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      change (∑ i, ‖stVec st i‖^2) = 1
      simp only [Real.norm_eq_abs]
      simp_rw [abs_of_nonneg (stVec_nonneg st _)]
      simpa only [sq] using stVec_sq_sum st
    nlinarith [norm_nonneg v]
  have he : stVec st ⬝ᵥ ((A^(n+1))*ᵥstVec st) = inner ℝ v ((T^(n+1)) v) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]
    rw [← map_pow]
    rfl
  calc _ = inner ℝ v ((T^(n+1)) v) := he
    _ ≤ |inner ℝ v ((T^(n+1)) v)| := le_abs_self _
    _ ≤ ‖v‖*‖(T^(n+1)) v‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖v‖*(‖T^(n+1)‖*‖v‖) :=
      mul_le_mul_of_nonneg_left ((T^(n+1)).le_opNorm v) (norm_nonneg _)
    _ ≤ ‖T‖^(n+1) := by simpa only [hv, one_mul, mul_one] using norm_pow_le' T (Nat.succ_pos n)

/-- Sum on an observation window, permitting an empty window. -/
def observationSum {d m : ℕ} (f : Fin d → ℝ) (Y : Fin m → Fin d) : ℝ :=
  ∑ t, f (Y t)

/-- A block sum on a single residue of that window. -/
def residueSum {d m k : ℕ} (hk : 0 < k) (r : Fin k)
    (f : Fin d → ℝ) (Y : Fin m → Fin d) : ℝ :=
  observationSum f (residueSequence hk r Y)

lemma observationSum_residues {d m k : ℕ} (hk : 0 < k)
    (f : Fin d → ℝ) (Y : Fin m → Fin d) :
    observationSum f Y = ∑ r : Fin k, residueSum hk r f Y :=
  (sum_residueIndex hk (fun t => f (Y t))).symm

lemma residueSum_path {d m k : ℕ} (hk : 0 < k) (r : Fin k)
    (hpos : 0 < residueLength m k r) (f : Fin d → ℝ) (Y : Fin m → Fin d) :
    residueSum hk r f Y = ∑ t, f (residuePath hk r hpos Y t) := by
  let he : residueLength m k r-1+1 = residueLength m k r := by omega
  exact (Equiv.sum_comp (finCongr he)
    (fun t => f (residueSequence hk r Y t))).symm

/-- The actual MGF of a residue is bounded by a power of its tilted operator norm. -/
theorem residue_mgf_le {d m k n : ℕ} (Q : Stoch d) (st : Stationary Q)
    (hk : 0 < k) (r : Fin k) (s : ℕ) (hs : s+m ≤ n+1)
    (f : Fin d → ℝ) (θ B : ℝ)
    (hnorm : ‖Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)
      (Lk Q st k*diagonal (fun i => exp (θ*f i)))‖ ≤ exp B) :
    (∑ X : Fin (n+1) → Fin d, pathProb Q.P st.mu X *
      exp (θ*residueSum hk r f (trajectoryWindow s m hs X))) ≤
      exp ((residueLength m k r:ℝ)*B) := by
  by_cases hpos : 0 < residueLength m k r
  · simp_rw [residueSum_path hk r hpos]
    have hpush := residuePath_sum Q.P st.mu Q.row_stoch hk r hpos s hs
      (fun Y => exp (θ*∑ t, f (Y t)))
    rw [hpush, stationary_shift]
    have hpath := path_exp_le_norm (n:=residueLength m k r-1) Q st k f θ
    have hpow := pow_le_pow_left₀ (norm_nonneg _) hnorm (residueLength m k r-1+1)
    have hlen : residueLength m k r-1+1 = residueLength m k r := by omega
    exact hpath.trans (hpow.trans (by rw [← exp_nat_mul, hlen]))
  · have hzero : residueLength m k r = 0 := by omega
    have hsum (X : Fin (n+1) → Fin d) :
        residueSum hk r f (trajectoryWindow s m hs X) = 0 := by
      unfold residueSum observationSum
      haveI : IsEmpty (Fin (residueLength m k r)) := by rw [hzero]; infer_instance
      exact sum_of_isEmpty _
    simp_rw [hsum, mul_zero, exp_zero, mul_one]
    rw [pathProb_sum Q.P st.mu Q.row_stoch, st.sum_one, hzero]
    simp

/-- Holder combines dependent residue blocks, retaining their exact lengths. -/
theorem window_mgf_le {d m k n : ℕ} (Q : Stoch d) (st : Stationary Q)
    (hk : 0 < k) (s : ℕ) (hs : s+m ≤ n+1) (f : Fin d → ℝ) (θ B : ℝ)
    (hnorm : ‖Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)
      (Lk Q st k*diagonal (fun i => exp (((k:ℝ)*θ)*f i)))‖ ≤ exp B) :
    (∑ X : Fin (n+1) → Fin d, pathProb Q.P st.mu X *
      exp (θ*observationSum f (trajectoryWindow s m hs X))) ≤ exp ((m:ℝ)*B/k) := by
  have hh := FiniteHolder.mgf_sum_le_exp_average k hk (pathProb Q.P st.mu)
    (fun X => pathProb_nonneg Q.P st.mu Q.nonneg st.nonneg X)
    (fun r X => residueSum hk r f (trajectoryWindow s m hs X)) θ
    (fun r => (residueLength m k r:ℝ)*B)
    (fun r => residue_mgf_le Q st hk r s hs f ((k:ℝ)*θ) B hnorm)
  simp_rw [← observationSum_residues] at hh
  have he : (∑ r : Fin k, (residueLength m k r:ℝ)*B) = (m:ℝ)*B := by
    rw [← sum_mul]
    congr 1
    exact_mod_cast sum_residueLength (m:=m) hk
  rw [he] at hh
  exact hh

lemma stateSum_window {d m : ℕ} (f : Fin d → ℝ) (arrival : Bool)
    (Y : Fin (m+1) → Fin d) :
    stateSum f arrival Y =
      observationSum f (trajectoryWindow (if arrival then 1 else 0) m
        (by split_ifs <;> omega) Y) := by
  apply sum_congr rfl
  intro t _
  congr 1
  apply congrArg Y
  apply Fin.ext
  cases arrival <;> simp [observationIndex, Nat.add_comm]

lemma mean_mul {d : ℕ} (pi f : Fin d → ℝ) (c : ℝ) :
    stationaryMean pi (fun i => c*f i) = c*stationaryMean pi f := by
  simp only [stationaryMean, mul_sum]
  apply sum_congr rfl
  intro i _
  ring

lemma variance_of_mean_zero {d : ℕ} (pi f : Fin d → ℝ)
    (hf : stationaryMean pi f = 0) : stationaryVariance pi f = ∑ i, pi i*(f i)^2 := by
  simp only [stationaryVariance, hf, sub_zero]

lemma variance_mul {d : ℕ} (pi f : Fin d → ℝ) (c : ℝ) :
    stationaryVariance pi (fun i => c*f i) = c^2*stationaryVariance pi f := by
  simp only [stationaryVariance, mean_mul, mul_sum]
  apply sum_congr rfl
  intro i _
  ring

lemma mean_div {d : ℕ} (pi f : Fin d → ℝ) (c : ℝ) :
    stationaryMean pi (fun i => f i/c) = stationaryMean pi f/c := by
  simpa only [div_eq_mul_inv, mul_comm] using mean_mul pi f c⁻¹

lemma variance_div {d : ℕ} (pi f : Fin d → ℝ) (c : ℝ) :
    stationaryVariance pi (fun i => f i/c) = stationaryVariance pi f/c^2 := by
  simpa only [div_eq_mul_inv, mul_comm, inv_pow] using variance_mul pi f c⁻¹

/-- Scaling the unit-range tilted estimate yields the exact centered MGF. -/
theorem stateSum_mgf_of_tilted {d : ℕ} (Q : Stoch d) (st : Stationary Q)
    (f : Fin d → ℝ) (b : ℝ) (hb : 0 < b)
    (γ : ℝ) (k : ℕ) (hk : 0 < k)
    (hgap : aK Q st k = (k:ℝ)*γ)
    (hunit : ∀ t : ℝ, 0 ≤ t → 10*t < aK Q st k →
      ‖Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)
        (Lk Q st k*diagonal (fun i => exp (t*(f i/b))))‖ ≤
      exp (2*stationaryVariance st.mu (fun i => f i/b)*t^2/(aK Q st k-10*t)))
    (m : ℕ) (arrival : Bool) (θ : ℝ) (hθ : 0 ≤ θ) (hsmall : 10*b*θ < γ) :
    (∑ Y : Fin (m+1) → Fin d, pathProb Q.P st.mu Y * exp (θ*stateSum f arrival Y)) ≤
      exp (2*(m:ℝ)*stationaryVariance st.mu f*θ^2/(γ-10*b*θ)) := by
  have hkR : (0:ℝ) < k := Nat.cast_pos.mpr hk
  have htsmall : 10*((k:ℝ)*θ*b) < aK Q st k := by
    rw [hgap]
    have hh := mul_lt_mul_of_pos_left hsmall hkR
    nlinarith
  have ht := hunit ((k:ℝ)*θ*b) (by positivity) htsmall
  have hexp (i : Fin d) : ((k:ℝ)*θ*b)*(f i/b) = ((k:ℝ)*θ)*f i := by
    field_simp
  simp_rw [hexp] at ht
  have hwindow := window_mgf_le Q st hk (if arrival then 1 else 0)
    (m:=m) (n:=m) (by split_ifs <;> omega) f θ
    (2*stationaryVariance st.mu (fun i => f i/b)*((k:ℝ)*θ*b)^2/
      (aK Q st k-10*((k:ℝ)*θ*b))) ht
  simp_rw [← stateSum_window] at hwindow
  convert hwindow using 1
  congr 1
  rw [variance_div, hgap]
  have hden : γ-10*b*θ ≠ 0 := ne_of_gt (sub_pos.mpr hsmall)
  field_simp

lemma eventProb_eq_ite {d m : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ)
    (mu : Fin d → ℝ) (E : (Fin (m+1) → Fin d) → Prop) :
    eventProb Q mu E = ∑ Y, if E Y then pathProb Q mu Y else 0 := by
  classical
  simp only [eventProb, pathMeasure, sum_filter]

lemma eventProb_le_one {d m : ℕ} (Q : Stoch d) (st : Stationary Q)
    (E : (Fin (m+1) → Fin d) → Prop) : eventProb Q.P st.mu E ≤ 1 := by
  classical
  rw [eventProb_eq_ite, ← st.sum_one, ← pathProb_sum (n:=m) Q.P st.mu Q.row_stoch]
  apply sum_le_sum
  intro Y _
  split_ifs
  · exact le_rfl
  · exact pathProb_nonneg Q.P st.mu Q.nonneg st.nonneg Y

/-- The zero pseudo-gap case requires no mixing assumption. -/
theorem paulin_zero_gap {d : ℕ} (Q : Stoch d) (st : Stationary Q)
    (hzero : gammaPS Q st = 0) : PaulinOriginalInput Q st (gammaPS Q st) := by
  intro m f arrival u hu hf
  rw [hzero]
  simp only [mul_zero, zero_div, neg_zero, exp_zero, mul_one]
  exact (eventProb_le_one Q st _).trans (by norm_num)

lemma centered_variance {d : ℕ} (Q : Stoch d) (st : Stationary Q) (f : Fin d → ℝ) :
    stationaryVariance st.mu (fun i => f i-stationaryMean st.mu f) =
      stationaryVariance st.mu f := by
  rw [variance_of_mean_zero _ _ (centered_mean Q st f)]
  rfl

lemma stateSum_mul {d m : ℕ} (f : Fin d → ℝ) (arrival : Bool)
    (Y : Fin (m+1) → Fin d) (c : ℝ) :
    stateSum (fun i => c*f i) arrival Y = c*stateSum f arrival Y := by
  simp only [stateSum, mul_sum]

/-- The complete finite-path deduction from the unit-range tilted estimate.
The estimate is applied only to the actual matrix `Lk * diagonal exp`.
-/
theorem paulin_of_unit_tilt {d : ℕ} (Q : Stoch d) (st : Stationary Q)
    (hoperator : ∀ (k : ℕ) (f : Fin d → ℝ),
      stationaryMean st.mu f = 0 → (∀ i, |f i| ≤ 1) → 0 < aK Q st k →
      ∀ θ : ℝ, 0 ≤ θ → 10*θ < aK Q st k →
      ‖Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)
        (Lk Q st k*diagonal (fun i => exp (θ*f i)))‖ ≤
        exp (2*stationaryVariance st.mu f*θ^2/(aK Q st k-10*θ))) :
    PaulinOriginalInput Q st (gammaPS Q st) := by
  by_cases hzero : gammaPS Q st = 0
  · exact paulin_zero_gap Q st hzero
  have hγ : 0 < gammaPS Q st := lt_of_le_of_ne (gamma_nonneg Q st) (Ne.symm hzero)
  obtain ⟨k,hk,hgap,hkinv⟩ := exists_max_lag Q st hγ
  have hkR : (0:ℝ) < k := Nat.cast_pos.mpr hk
  have hgap' : aK Q st k = (k:ℝ)*gammaPS Q st := by
    have hh := (div_eq_iff hkR.ne').mp hgap
    nlinarith
  have ha : 0 < aK Q st k := by rw [hgap']; positivity
  intro m f arrival u hu hf
  let C : Fin d → ℝ := fun i => f i-stationaryMean st.mu f
  let b := ‖C‖
  let V := stationaryVariance st.mu f
  let N := (m:ℝ)+1/gammaPS Q st
  have hN : 0 < N := by dsimp [N]; positivity
  have hV : 0 < V := variance_pos Q st f hf
  have hb : 0 < b := by
    apply norm_pos_iff.mpr
    intro hz
    obtain ⟨i,j,hij⟩ := hf
    have hi := congrFun hz i
    have hj := congrFun hz j
    apply hij
    dsimp [C] at hi hj
    linarith
  have hrange (i : Fin d) : |C i| ≤ b := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm C i
  have hmean : stationaryMean st.mu C = 0 := centered_mean Q st f
  have hmgf (sgn : ℝ) (hsgn : sgn=1 ∨ sgn = -1) (θ : ℝ)
      (hθ : 0 ≤ θ) (hsmall : 10*b*θ < gammaPS Q st) :
      (∑ Y : Fin (m+1) → Fin d, pathProb Q.P st.mu Y *
        exp (θ*(sgn*(stateSum f arrival Y-(m:ℝ)*stationaryMean st.mu f)))) ≤
          exp (2*N*V*θ^2/(gammaPS Q st-10*b*θ)) := by
    let F : Fin d → ℝ := fun i => sgn*C i
    have hsabs : |sgn| = 1 := by rcases hsgn with h | h <;> rw [h] <;> norm_num
    have hsq : sgn^2 = 1 := by rcases hsgn with h | h <;> rw [h] <;> norm_num
    have hFmean : stationaryMean st.mu F = 0 := by
      rw [show F = (fun i => sgn*C i) from rfl, mean_mul, hmean, mul_zero]
    have hFrange (i : Fin d) : |F i| ≤ b := by
      dsimp [F]
      rw [abs_mul, hsabs, one_mul]
      exact hrange i
    have hFvar : stationaryVariance st.mu F = V := by
      rw [show F = (fun i => sgn*C i) from rfl, variance_mul, hsq, one_mul,
        centered_variance]
    have hunitmean : stationaryMean st.mu (fun i => F i/b) = 0 := by
      rw [mean_div, hFmean, zero_div]
    have hunitrange (i : Fin d) : |F i/b| ≤ 1 := by
      rw [abs_div, abs_of_pos hb]
      exact (div_le_one hb).mpr (hFrange i)
    have hh := stateSum_mgf_of_tilted Q st F b hb
      (gammaPS Q st) k hk hgap'
      (hoperator k (fun i => F i/b) hunitmean hunitrange ha) m arrival θ hθ hsmall
    have he (Y : Fin (m+1) → Fin d) :
        stateSum F arrival Y = sgn*(stateSum f arrival Y-(m:ℝ)*stationaryMean st.mu f) := by
      rw [show F = (fun i => sgn*C i) from rfl, stateSum_mul, centered_stateSum Q st f]
    simp_rw [he] at hh
    rw [hFvar] at hh
    apply hh.trans
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hsmall.le)
    have hNle : (m:ℝ) ≤ N := by
      exact le_add_of_nonneg_right (by positivity)
    have hcoef : 0 ≤ 2*V*θ^2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hNle hcoef]
  have htail := bernstein_two_sided (pathProb Q.P st.mu)
    (fun Y => stateSum f arrival Y-(m:ℝ)*stationaryMean st.mu f)
    (fun Y => pathProb_nonneg Q.P st.mu Q.nonneg st.nonneg Y)
    N V b (gammaPS Q st) u hN hV hb.le hγ hu hmgf
  rw [eventProb_eq_ite]
  exact htail

lemma nonconstant_dimension {d : ℕ} (f : Fin d → ℝ)
    (hf : ∃ i j, f i ≠ f j) : 1 < d := by
  obtain ⟨i,j,hij⟩ := hf
  by_contra hd
  have heq : i = j := by
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    omega
  exact hij (congrArg f heq)

lemma paulin_small_dimension {d : ℕ} (Q : Stoch d) (st : Stationary Q)
    (hd : d ≤ 1) : PaulinOriginalInput Q st (gammaPS Q st) := by
  intro m f arrival u hu hf
  exact False.elim ((not_lt_of_ge hd) (nonconstant_dimension f hf))

/-- The corrected stationary Bernstein inequality of Paulin, Theorem 3.11,
Equation (3.25), for the actual finite Markov path law. Both observation
orientations and the zero pseudo-gap case are included.
-/
theorem paulin_original {d : ℕ} (Q : Stoch d) (st : Stationary Q) :
    PaulinOriginalInput Q st (gammaPS Q st) := by
  by_cases hd : 1 < d
  · apply paulin_of_unit_tilt Q st
    intro k f hmean hf hg θ hθ hsmall
    simpa only [paulinTilt] using
      paulin_tilted_operator_norm hd Q st k f hmean hf hg θ hθ hsmall
  · exact paulin_small_dimension Q st (by omega)

end
end PsgEst.PaulinProof
