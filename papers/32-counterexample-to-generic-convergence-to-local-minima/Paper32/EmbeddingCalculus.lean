import Paper32.Extensions
import Paper32.ClarkeBridge

open Set Filter Topology BigOperators

noncomputable section

namespace Paper32

variable {ι : Type*} [Fintype ι]

abbrev EmbeddedPoint (ι : Type*) := Point × (ι → ℝ)

/-- The ordinary Euclidean dual pairing in all `2 + card ι` coordinates. -/
def embeddedLin (w z : EmbeddedPoint ι) : ℝ :=
  lin w.1 z.1 + ∑ i, w.2 i * z.2 i

/-- The continuous linear functional of the full Euclidean gradient vector. -/
def embeddedLinCLM (w : EmbeddedPoint ι) : EmbeddedPoint ι →L[ℝ] ℝ :=
  (linCLM w.1).comp (ContinuousLinearMap.fst ℝ Point (ι → ℝ)) +
    ∑ i, (w.2 i) • ((ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.snd ℝ Point (ι → ℝ)))

@[simp] theorem embeddedLinCLM_apply (w z : EmbeddedPoint ι) :
    embeddedLinCLM w z = embeddedLin w z := by
  simp [embeddedLinCLM, embeddedLin]

/-- The actual Fréchet subgradient inequality on the full finite product. -/
def EmbeddedFrechetSubgradient (f : EmbeddedPoint ι → ℝ)
    (z w : EmbeddedPoint ι) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ u : EmbeddedPoint ι, ‖u‖ < δ →
      f z + embeddedLin w u - ε * ‖u‖ ≤ f (z + u)

/-- Reachable ordinary gradients of the full objective. -/
def embeddedGradientLimits (f : EmbeddedPoint ι → ℝ)
    (z : EmbeddedPoint ι) : Set (EmbeddedPoint ι) :=
  {w | ∃ a b : ℕ → EmbeddedPoint ι, Tendsto a atTop (𝓝 z) ∧
    Tendsto b atTop (𝓝 w) ∧ ∀ n, HasFDerivAt f (embeddedLinCLM (b n)) (a n)}

/-- The standard full-dimensional Clarke subdifferential, by closed convexification. -/
def embeddedClarkeSubdiff (f : EmbeddedPoint ι → ℝ)
    (z : EmbeddedPoint ι) : Set (EmbeddedPoint ι) :=
  closure (convexHull ℝ (embeddedGradientLimits f z))

lemma embedded_frechet_of_hasFDerivAt {f : EmbeddedPoint ι → ℝ}
    {z w : EmbeddedPoint ι} (hd : HasFDerivAt f (embeddedLinCLM w) z) :
    EmbeddedFrechetSubgradient f z w := by
  intro ε hε
  have he := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hd).bound hε
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨δ,hδ,?_⟩
  intro u hu
  have hb := hball (show u ∈ Metric.ball (0:EmbeddedPoint ι) δ by
    simpa [dist_zero_right] using hu)
  change ‖f (z+u)-f z-(embeddedLinCLM w) u‖ ≤ ε*‖u‖ at hb
  rw [Real.norm_eq_abs, embeddedLinCLM_apply] at hb
  have hlow := (abs_le.mp hb).1
  linarith

lemma embeddedFrechet_direction_le {f : EmbeddedPoint ι → ℝ}
    {z w d : EmbeddedPoint ι} (hw : EmbeddedFrechetSubgradient f z w)
    (hd : ‖d‖ = 1) {a r : ℝ} (hr : 0 < r)
    (hf : ∀ t : ℝ, 0 < t → t < r → f (z+t • d) ≤ f z+t*a) :
    embeddedLin w d ≤ a := by
  by_contra h
  have hp : 0 < (embeddedLin w d-a)/2 := by linarith
  obtain ⟨δ,hδ,hs⟩ := hw ((embeddedLin w d-a)/2) hp
  let t := min δ r/2
  have ht : 0 < t := by dsimp [t]; positivity
  have htδ : t < δ := by dsimp [t]; have := min_le_left δ r; linarith
  have htr : t < r := by dsimp [t]; have := min_le_right δ r; linarith
  have hn : ‖t • d‖ = t := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, hd, mul_one]
  have hlow := hs (t • d) (by simpa [hn] using htδ)
  have hlin : embeddedLin w (t • d) = t * embeddedLin w d := by
    simp only [← embeddedLinCLM_apply, map_smul, smul_eq_mul]
  rw [hlin,hn] at hlow
  have hupp := hf t ht htr
  nlinarith

lemma embeddedTilt_slice (v : EmbeddedPoint ι) (q : ι → ℝ) :
    (fun p : Point => embeddedTilt v (p,q)) =
      (fun p => tilt v.1 p + ∑ i, (2*|q i|-v.2 i*q i)) := by
  funext p
  exact embeddedTilt_eq v (p,q)

/-- Restricting a full derivative to the first two coordinates gives the genuine
ordinary derivative of the original tilted objective. -/
lemma embedded_hasFDerivAt_projection {v z w : EmbeddedPoint ι}
    (hd : HasFDerivAt (embeddedTilt v) (embeddedLinCLM w) z) :
    HasFDerivAt (tilt v.1) (linCLM w.1) z.1 := by
  let I : Point →L[ℝ] EmbeddedPoint ι :=
    (ContinuousLinearMap.id ℝ Point).prod (0 : Point →L[ℝ] (ι → ℝ))
  have hI : HasFDerivAt (fun p : Point => (p,z.2)) I z.1 := by
    simpa [I] using (hasFDerivAt_id z.1).prodMk (hasFDerivAt_const z.2 z.1)
  have hd' := hd.comp z.1 hI
  have heq : (embeddedLinCLM w).comp I = linCLM w.1 := by
    apply ContinuousLinearMap.ext
    intro p
    simp [I,embeddedLin]
  rw [heq] at hd'
  change HasFDerivAt (fun p : Point => embeddedTilt v (p,z.2)) _ _ at hd'
  rw [embeddedTilt_slice] at hd'
  convert hd'.sub_const (∑ i, (2*|z.2 i|-v.2 i*z.2 i)) using 1 <;> simp

lemma embeddedGradientLimits_projection {v z w : EmbeddedPoint ι}
    (hw : w ∈ embeddedGradientLimits (embeddedTilt v) z) :
    w.1 ∈ gradientLimits (tilt v.1) z.1 := by
  obtain ⟨a,b,ha,hb,hd⟩ := hw
  exact ⟨fun n => (a n).1, fun n => (b n).1, (continuous_fst.tendsto z).comp ha, (continuous_fst.tendsto w).comp hb,
    fun n => embedded_hasFDerivAt_projection (hd n)⟩

/-- Every full Clarke oracle projects to an actual Clarke oracle in the first
 two coordinates; this follows from gradients and closed convex hulls. -/
theorem embeddedClarke_projection {v z w : EmbeddedPoint ι}
    (hw : w ∈ embeddedClarkeSubdiff (embeddedTilt v) z) :
    w.1 ∈ clarkeSubdiff (tilt v.1) z.1 := by
  let S : Set (EmbeddedPoint ι) := Prod.fst ⁻¹' clarkeSubdiff (tilt v.1) z.1
  have hc : IsClosed S := isClosed_closure.preimage continuous_fst
  have hvx : Convex ℝ S :=
    ((convex_convexHull ℝ (gradientLimits (tilt v.1) z.1)).closure).linear_preimage
      (LinearMap.fst ℝ Point (ι → ℝ))
  have hsub : embeddedGradientLimits (embeddedTilt v) z ⊆ S := by
    intro u hu
    exact subset_closure (subset_convexHull ℝ _ (embeddedGradientLimits_projection hu))
  exact closure_minimal (convexHull_min hsub hvx) hc hw

/-- The coordinate direction in an extra factor. -/
def extraDirection (i : ι) : EmbeddedPoint ι := by
  classical
  exact (0, Pi.single i 1)

@[simp] lemma norm_extraDirection (i : ι) : ‖extraDirection i‖ = 1 := by
  classical
  simp [extraDirection, Prod.norm_def, Pi.norm_single]

@[simp] lemma embeddedLin_extraDirection (w : EmbeddedPoint ι) (i : ι) :
    embeddedLin w (extraDirection i) = w.2 i := by
  classical
  simp [embeddedLin,extraDirection,Pi.single_apply,lin]

lemma embeddedTilt_extra_increment (v z : EmbeddedPoint ι) (i : ι) (t : ℝ) :
    embeddedTilt v (z+t • extraDirection i) = embeddedTilt v z +
      (2*|z.2 i+t|-2*|z.2 i|-v.2 i*t) := by
  classical
  rw [embeddedTilt_eq,embeddedTilt_eq]
  have hsum : ∑ j, (2*|(z+t • extraDirection i).2 j|-v.2 j*(z+t • extraDirection i).2 j) =
      ∑ j, (2*|z.2 j|-v.2 j*z.2 j) +
        (2*|z.2 i+t|-2*|z.2 i|-v.2 i*t) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
      ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    have hrest : ∑ j ∈ Finset.univ.erase i,
        (2*|(z+t • extraDirection i).2 j|-v.2 j*(z+t • extraDirection i).2 j) =
        ∑ j ∈ Finset.univ.erase i, (2*|z.2 j|-v.2 j*z.2 j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      simp [extraDirection,Pi.single_apply,hji,Ne.symm hji]
    rw [hrest]
    simp [extraDirection,Pi.single_apply]
    ring
  rw [hsum]
  simp [extraDirection]
  ring

/-- Full regular subgradients satisfy the exact global extra-coordinate bound. -/
lemma embeddedFrechet_extra_bound {v z w : EmbeddedPoint ι}
    (hw : EmbeddedFrechetSubgradient (embeddedTilt v) z w) (i : ι) :
    |w.2 i+v.2 i| ≤ 2 := by
  have hp := embeddedFrechet_direction_le hw (norm_extraDirection i) (r:=1)
    (a:=2-v.2 i) (by norm_num) (fun t ht _ => by
      rw [embeddedTilt_extra_increment]
      have h := abs_add_le (z.2 i) t
      rw [abs_of_pos ht] at h
      nlinarith)
  have hm := embeddedFrechet_direction_le hw (d:= -extraDirection i)
    (by simp) (r:=1) (a:=2+v.2 i) (by norm_num) (fun t ht _ => by
      rw [smul_neg,← neg_smul,embeddedTilt_extra_increment]
      have h := abs_add_le (z.2 i) (-t)
      rw [abs_neg,abs_of_pos ht] at h
      nlinarith)
  simp only [embeddedLin_extraDirection] at hp
  have hneg : embeddedLin w (-extraDirection i) = -w.2 i := by
    rw [← embeddedLinCLM_apply,map_neg,embeddedLinCLM_apply,embeddedLin_extraDirection]
  rw [hneg] at hm
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- Away from a coordinate hyperplane, the actual full Fréchet oracle has the
ordinary derivative of `2 |qᵢ|` in that coordinate. -/
lemma embeddedFrechet_extra_eq {v z w : EmbeddedPoint ι}
    (hw : EmbeddedFrechetSubgradient (embeddedTilt v) z w) (i : ι)
    (hz : z.2 i ≠ 0) : w.2 i = 2*Real.sign (z.2 i)-v.2 i := by
  have hp := embeddedFrechet_direction_le hw (norm_extraDirection i)
    (r:=|z.2 i|) (a:=2*Real.sign (z.2 i)-v.2 i) (abs_pos.mpr hz)
    (fun t ht htr => by
      rw [embeddedTilt_extra_increment,abs_add_small hz (by rwa [abs_of_pos ht])]
      linarith)
  have hm := embeddedFrechet_direction_le hw (d:= -extraDirection i)
    (by simp) (r:=|z.2 i|) (a:=-(2*Real.sign (z.2 i)-v.2 i)) (abs_pos.mpr hz)
    (fun t ht htr => by
      rw [smul_neg,← neg_smul,embeddedTilt_extra_increment,
        abs_add_small hz (by simpa [abs_of_pos ht] using htr)]
      linarith)
  simp only [embeddedLin_extraDirection] at hp
  have hneg : embeddedLin w (-extraDirection i) = -w.2 i := by
    rw [← embeddedLinCLM_apply,map_neg,embeddedLinCLM_apply,embeddedLin_extraDirection]
  rw [hneg] at hm
  linarith


lemma embeddedGradientLimits_extra_bound {v z w : EmbeddedPoint ι}
    (hw : w ∈ embeddedGradientLimits (embeddedTilt v) z) (i : ι) :
    |w.2 i+v.2 i| ≤ 2 := by
  obtain ⟨a,b,ha,hb,hd⟩ := hw
  have hc : IsClosed {u : EmbeddedPoint ι | |u.2 i+v.2 i| ≤ 2} :=
    isClosed_le (by fun_prop) continuous_const
  exact hc.mem_of_tendsto hb (Filter.Eventually.of_forall
    (fun n => embeddedFrechet_extra_bound (embedded_frechet_of_hasFDerivAt (hd n)) i))

/-- The full Clarke oracle satisfies the extra-coordinate bound also at zero. -/
theorem embeddedClarke_extra_bound {v z w : EmbeddedPoint ι}
    (hw : w ∈ embeddedClarkeSubdiff (embeddedTilt v) z) (i : ι) :
    |w.2 i+v.2 i| ≤ 2 := by
  let S : Set (EmbeddedPoint ι) := {u | |u.2 i+v.2 i| ≤ 2}
  have hc : IsClosed S := isClosed_le (by fun_prop) continuous_const
  have hvx : Convex ℝ S := by
    intro a ha b hb s t hs ht hst
    change |a.2 i+v.2 i| ≤ 2 at ha
    change |b.2 i+v.2 i| ≤ 2 at hb
    have ha' := abs_le.mp ha
    have hb' := abs_le.mp hb
    have halg : (s • a+t • b).2 i+v.2 i =
        s*(a.2 i+v.2 i)+t*(b.2 i+v.2 i) := by
      simp only [Prod.snd_add,Prod.smul_snd,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      nlinarith [congrArg (fun r : ℝ => r*v.2 i) hst]
    change |(s • a+t • b).2 i+v.2 i| ≤ 2
    rw [halg]
    apply abs_le.mpr
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left ha'.1 hs,mul_le_mul_of_nonneg_left hb'.1 ht]
    · nlinarith [mul_le_mul_of_nonneg_left ha'.2 hs,mul_le_mul_of_nonneg_left hb'.2 ht]
  exact closure_minimal (convexHull_min (fun u hu => embeddedGradientLimits_extra_bound hu i) hvx) hc hw

lemma embeddedGradientLimits_extra_eq {v z w : EmbeddedPoint ι}
    (hw : w ∈ embeddedGradientLimits (embeddedTilt v) z) (i : ι)
    (hz : z.2 i ≠ 0) : w.2 i = 2*Real.sign (z.2 i)-v.2 i := by
  obtain ⟨a,b,ha,hb,hd⟩ := hw
  have hcoord : Tendsto (fun n => (a n).2 i) atTop (𝓝 (z.2 i)) :=
    ((continuous_apply i).comp continuous_snd).continuousAt.tendsto.comp ha
  have hsign : ∀ᶠ n in atTop, (a n).2 i ≠ 0 ∧ Real.sign ((a n).2 i) = Real.sign (z.2 i) := by
    rcases lt_or_gt_of_ne hz with hz | hz
    · filter_upwards [hcoord.eventually (Iio_mem_nhds hz)] with n hn
      exact ⟨ne_of_lt hn,by rw [Real.sign_of_neg hn,Real.sign_of_neg hz]⟩
    · filter_upwards [hcoord.eventually (Ioi_mem_nhds hz)] with n hn
      exact ⟨ne_of_gt hn,by rw [Real.sign_of_pos hn,Real.sign_of_pos hz]⟩
  have heq : ∀ᶠ n in atTop, (b n).2 i = 2*Real.sign (z.2 i)-v.2 i := by
    filter_upwards [hsign] with n hn
    rw [embeddedFrechet_extra_eq (embedded_frechet_of_hasFDerivAt (hd n)) i hn.1,hn.2]
  have hlim : Tendsto (fun n => (b n).2 i) atTop (𝓝 (w.2 i)) :=
    ((continuous_apply i).comp continuous_snd).continuousAt.tendsto.comp hb
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (heq.mono (fun _ h => h.symm)))

/-- The full Clarke oracle has the exact ordinary derivative in every nonzero
extra coordinate, proved before imposing a stochastic recurrence. -/
theorem embeddedClarke_extra_eq {v z w : EmbeddedPoint ι}
    (hw : w ∈ embeddedClarkeSubdiff (embeddedTilt v) z) (i : ι)
    (hz : z.2 i ≠ 0) : w.2 i = 2*Real.sign (z.2 i)-v.2 i := by
  let S : Set (EmbeddedPoint ι) := {u | u.2 i = 2*Real.sign (z.2 i)-v.2 i}
  have hc : IsClosed S := isClosed_eq (by fun_prop) continuous_const
  have hvx : Convex ℝ S := by
    intro a ha b hb s t hs ht hst
    change (s • a+t • b).2 i = _
    change a.2 i = _ at ha
    change b.2 i = _ at hb
    simp only [Prod.snd_add,Prod.smul_snd,Pi.add_apply,Pi.smul_apply,smul_eq_mul,ha,hb]
    rw [← add_mul,hst,one_mul]
  exact closure_minimal (convexHull_min (fun u hu => embeddedGradientLimits_extra_eq hu i hz) hvx) hc hw


/-- The actual limiting subdifferential, with full Fréchet sequences and values. -/
def embeddedLimitingSubdiff (f : EmbeddedPoint ι → ℝ) (z : EmbeddedPoint ι) :
    Set (EmbeddedPoint ι) :=
  {w | ∃ a b : ℕ → EmbeddedPoint ι, Tendsto a atTop (𝓝 z) ∧
    Tendsto (f ∘ a) atTop (𝓝 (f z)) ∧ Tendsto b atTop (𝓝 w) ∧
    ∀ n, EmbeddedFrechetSubgradient f (a n) (b n)}

lemma embeddedFrechet_projection {v z w : EmbeddedPoint ι}
    (hw : EmbeddedFrechetSubgradient (embeddedTilt v) z w) :
    FrechetSubgradient (tilt v.1) z.1 w.1 := by
  intro ε hε
  obtain ⟨δ,hδ,hs⟩ := hw ε hε
  refine ⟨δ,hδ,?_⟩
  intro u hu
  have hn : ‖(u,(0:ι → ℝ))‖ = ‖u‖ := by simp [Prod.norm_def]
  have h := hs (u,0) (by simpa only [hn] using hu)
  simp only [embeddedTilt_eq,embeddedLin,Prod.fst_add,Prod.snd_add,
    Prod.fst_zero,Prod.snd_zero,Pi.add_apply,Pi.zero_apply,add_zero,mul_zero,
    Finset.sum_const_zero,hn] at h
  linarith

lemma embeddedLimiting_projection {v z w : EmbeddedPoint ι}
    (hw : w ∈ embeddedLimitingSubdiff (embeddedTilt v) z) :
    w.1 ∈ limitingSubdiff (tilt v.1) z.1 := by
  obtain ⟨a,b,ha,hfa,hb,hd⟩ := hw
  have hap : Tendsto (fun n => (a n).1) atTop (𝓝 z.1) :=
    (continuous_fst.tendsto z).comp ha
  exact ⟨fun n => (a n).1,fun n => (b n).1,hap,
    (continuous_tilt v.1).continuousAt.tendsto.comp hap,
    (continuous_fst.tendsto w).comp hb,fun n => embeddedFrechet_projection (hd n)⟩

/-- The exact convex subgradient conditions for the separable absolute values. -/
def extraSupport (v z w : EmbeddedPoint ι) : Prop :=
  ∀ i, |w.2 i+v.2 i| ≤ 2 ∧ (z.2 i ≠ 0 → w.2 i=2*Real.sign (z.2 i)-v.2 i)

lemma embeddedFrechet_extraSupport {v z w : EmbeddedPoint ι}
    (hw : EmbeddedFrechetSubgradient (embeddedTilt v) z w) : extraSupport v z w :=
  fun i => ⟨embeddedFrechet_extra_bound hw i,embeddedFrechet_extra_eq hw i⟩

lemma embeddedFrechet_of_projection {v z w : EmbeddedPoint ι}
    (hb : FrechetSubgradient (tilt v.1) z.1 w.1) (he : extraSupport v z w) :
    EmbeddedFrechetSubgradient (embeddedTilt v) z w := by
  intro ε hε
  obtain ⟨δ,hδ,hs⟩ := hb ε hε
  refine ⟨δ,hδ,?_⟩
  intro u hu
  have hn : ‖u.1‖ ≤ ‖u‖ := norm_fst_le u
  have hbase := hs u.1 (hn.trans_lt hu)
  have hextra : ∀ i, (2*|z.2 i|-v.2 i*z.2 i)+w.2 i*u.2 i ≤
      2*|z.2 i+u.2 i|-v.2 i*(z.2 i+u.2 i) := by
    intro i
    by_cases hz : z.2 i=0
    · have h := mul_le_abs_bound (he i).1 (t:=u.2 i)
      simp only [hz,abs_zero,mul_zero,sub_zero,zero_add] at *
      nlinarith
    · rw [(he i).2 hz]
      nlinarith [sign_support (z.2 i) (u.2 i)]
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hextra i)
  simp only [Finset.sum_add_distrib] at hsum
  simp only [embeddedTilt_eq,embeddedLin,Prod.fst_add,Prod.snd_add,Pi.add_apply]
  nlinarith [mul_le_mul_of_nonneg_left hn hε.le]

/-- Exact Fréchet product rule, established from the defining inequality. -/
theorem embeddedFrechet_product {v z w : EmbeddedPoint ι} :
    EmbeddedFrechetSubgradient (embeddedTilt v) z w ↔
      FrechetSubgradient (tilt v.1) z.1 w.1 ∧ extraSupport v z w :=
  ⟨fun h => ⟨embeddedFrechet_projection h,embeddedFrechet_extraSupport h⟩,
    fun h => embeddedFrechet_of_projection h.1 h.2⟩

lemma continuous_embeddedTilt (v : EmbeddedPoint ι) : Continuous (embeddedTilt v) := by
  unfold embeddedTilt embeddedObjective lin
  have hF : Continuous (fun z : EmbeddedPoint ι => F z.1) := continuous_F.comp continuous_fst
  fun_prop

lemma embeddedLimiting_extraSupport {v z w : EmbeddedPoint ι}
    (hw : w ∈ embeddedLimitingSubdiff (embeddedTilt v) z) : extraSupport v z w := by
  obtain ⟨a,b,ha,hfa,hb,hd⟩ := hw
  intro i
  constructor
  · have hc : IsClosed {u : EmbeddedPoint ι | |u.2 i+v.2 i| ≤ 2} :=
      isClosed_le (by fun_prop) continuous_const
    exact hc.mem_of_tendsto hb (Filter.Eventually.of_forall
      (fun n => embeddedFrechet_extra_bound (hd n) i))
  · intro hz
    have hcoord : Tendsto (fun n => (a n).2 i) atTop (𝓝 (z.2 i)) :=
      ((continuous_apply i).comp continuous_snd).continuousAt.tendsto.comp ha
    have hsign : ∀ᶠ n in atTop, (a n).2 i ≠ 0 ∧ Real.sign ((a n).2 i) = Real.sign (z.2 i) := by
      rcases lt_or_gt_of_ne hz with hz | hz
      · filter_upwards [hcoord.eventually (Iio_mem_nhds hz)] with n hn
        exact ⟨ne_of_lt hn,by rw [Real.sign_of_neg hn,Real.sign_of_neg hz]⟩
      · filter_upwards [hcoord.eventually (Ioi_mem_nhds hz)] with n hn
        exact ⟨ne_of_gt hn,by rw [Real.sign_of_pos hn,Real.sign_of_pos hz]⟩
    have heq : ∀ᶠ n in atTop, (b n).2 i = 2*Real.sign (z.2 i)-v.2 i := by
      filter_upwards [hsign] with n hn
      rw [embeddedFrechet_extra_eq (hd n) i hn.1,hn.2]
    have hlim : Tendsto (fun n => (b n).2 i) atTop (𝓝 (w.2 i)) :=
      ((continuous_apply i).comp continuous_snd).continuousAt.tendsto.comp hb
    exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (heq.mono (fun _ h => h.symm)))

/-- Exact limiting product rule, proved with actual Fréchet sequences. -/
theorem embeddedLimiting_product {v z w : EmbeddedPoint ι} :
    w ∈ embeddedLimitingSubdiff (embeddedTilt v) z ↔
      w.1 ∈ limitingSubdiff (tilt v.1) z.1 ∧ extraSupport v z w := by
  constructor
  · intro h
    exact ⟨embeddedLimiting_projection h,embeddedLimiting_extraSupport h⟩
  · rintro ⟨⟨a,b,ha,hfa,hb,hd⟩,he⟩
    have hap : Tendsto (fun n => (a n,z.2)) atTop (𝓝 z) := by
      simpa only [Prod.mk.eta] using ha.prodMk_nhds (tendsto_const_nhds (x:=z.2))
    refine ⟨fun n => (a n,z.2),fun n => (b n,w.2),hap,
      (continuous_embeddedTilt v).continuousAt.tendsto.comp hap,?_,?_⟩
    · simpa only [Prod.mk.eta] using hb.prodMk_nhds (tendsto_const_nhds (x:=w.2))
    · intro n
      exact embeddedFrechet_of_projection (hd n) he


/-- Ordinary differentiation of the full separable objective. -/
lemma embedded_hasFDerivAt_of_base {v z : EmbeddedPoint ι} {p : Point}
    (hb : HasFDerivAt (tilt v.1) (linCLM p) z.1)
    (hz : ∀ i, z.2 i ≠ 0) :
    HasFDerivAt (embeddedTilt v)
      (embeddedLinCLM (p,fun i => 2*Real.sign (z.2 i)-v.2 i)) z := by
  let L : ι → EmbeddedPoint ι →L[ℝ] ℝ := fun i =>
    (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ Point (ι → ℝ))
  have ht : ∀ i, HasFDerivAt (fun q : EmbeddedPoint ι => 2*|q.2 i|-v.2 i*q.2 i)
      ((2*Real.sign (z.2 i)-v.2 i) • L i) z := by
    intro i
    have ha : HasFDerivAt (fun q : EmbeddedPoint ι => |q.2 i|)
        (Real.sign (z.2 i) • L i) z := by
      rcases lt_or_gt_of_ne (hz i) with hn | hp
      · have heq : Real.sign (z.2 i) • L i = -L i := by
          apply ContinuousLinearMap.ext
          intro u
          simp [Real.sign_of_neg hn]
        rw [heq]
        exact (L i).hasFDerivAt.abs_of_neg hn
      · simpa only [Real.sign_of_pos hp,one_smul] using (L i).hasFDerivAt.abs_of_pos hp
    have h := (ha.const_mul 2).sub ((L i).hasFDerivAt.const_mul (v.2 i))
    convert h using 1
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
    ring
  have hs := HasFDerivAt.fun_sum (u:=Finset.univ) (fun i _ => ht i)
  have hb' := hb.comp z (ContinuousLinearMap.fst ℝ Point (ι → ℝ)).hasFDerivAt
  have h := hb'.add hs
  convert h using 1
  · funext q
    exact embeddedTilt_eq v q

/-- The product of the actual endpoint gradients in the extra factors. -/
def extraVertexSet (v z : EmbeddedPoint ι) : Set (ι → ℝ) :=
  Set.univ.pi (fun i => if z.2 i=0 then {-2-v.2 i,2-v.2 i}
    else {2*Real.sign (z.2 i)-v.2 i})

lemma endpoint_sign_div {q v : ℝ} (hq : |q+v|=2) (n : ℕ) :
    (q+v)/(n+1:ℝ) ≠ 0 ∧ 2*Real.sign ((q+v)/(n+1:ℝ))-v=q := by
  have hn : 0 < (n+1:ℝ) := by positivity
  constructor
  · apply div_ne_zero _ hn.ne'
    intro h
    simp [h] at hq
  · rcases le_total 0 (q+v) with hp | hm
    · rw [abs_of_nonneg hp] at hq
      rw [Real.sign_of_pos (div_pos (by linarith) hn)]
      linarith
    · rw [abs_of_nonpos hm] at hq
      rw [Real.sign_of_neg (div_neg_of_neg_of_pos (by linarith) hn)]
      linarith

/-- All independently chosen extra endpoint gradients can accompany any genuine
reachable base gradient. -/
lemma embeddedGradientLimits_lift {v z : EmbeddedPoint ι} {p : Point} {q : ι → ℝ}
    (hp : p ∈ gradientLimits (tilt v.1) z.1) (hq : q ∈ extraVertexSet v z) :
    (p,q) ∈ embeddedGradientLimits (embeddedTilt v) z := by
  classical
  obtain ⟨a,b,ha,hb,hd⟩ := hp
  let c : ℕ → ι → ℝ := fun n i =>
    if z.2 i=0 then (q i+v.2 i)/(n+1:ℝ) else z.2 i
  have hc : Tendsto c atTop (𝓝 z.2) := by
    apply tendsto_pi_nhds.2
    intro i
    by_cases hz : z.2 i=0
    · have hlim := (tendsto_const_nhds (x:=q i+v.2 i)).mul
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa only [c,if_pos hz,hz,div_eq_mul_inv,mul_zero,one_mul] using hlim
    · simpa only [c,if_neg hz] using (tendsto_const_nhds (x:=z.2 i) (f:=atTop))
  have hcoord : ∀ n i, c n i ≠ 0 ∧ 2*Real.sign (c n i)-v.2 i=q i := by
    intro n i
    have hqi := hq i (Set.mem_univ i)
    by_cases hz : z.2 i=0
    · have he : |q i+v.2 i|=2 := by
        simp only [if_pos hz,mem_insert_iff,mem_singleton_iff] at hqi
        rcases hqi with hqi | hqi <;> rw [hqi] <;> norm_num
      simpa only [c,if_pos hz] using endpoint_sign_div he n
    · simp only [if_neg hz,mem_singleton_iff] at hqi
      exact ⟨by simpa only [c,if_neg hz] using hz,by simpa only [c,if_neg hz] using hqi.symm⟩
  refine ⟨fun n => (a n,c n),fun n => (b n,q),?_,?_,?_⟩
  · simpa only [Prod.mk.eta] using ha.prodMk_nhds hc
  · exact hb.prodMk_nhds tendsto_const_nhds
  · intro n
    have h := embedded_hasFDerivAt_of_base (v:=v) (z:=(a n,c n)) (hd n)
      (fun i => (hcoord n i).1)
    have he : (fun i => 2*Real.sign (c n i)-v.2 i)=q := funext (fun i => (hcoord n i).2)
    simpa only [he] using h

lemma extraSupport_mem_convexHull_vertices {v z w : EmbeddedPoint ι}
    (hw : extraSupport v z w) : w.2 ∈ convexHull ℝ (extraVertexSet v z) := by
  classical
  apply mem_convexHull_pi
  intro i _
  by_cases hz : z.2 i=0
  · simp only [if_pos hz]
    rw [convexHull_pair,segment_eq_Icc (by linarith : -2-v.2 i ≤ 2-v.2 i)]
    have hb := abs_le.mp (hw i).1
    exact ⟨by linarith,by linarith⟩
  · simp only [if_neg hz,convexHull_singleton,mem_singleton_iff]
    exact (hw i).2 hz

/-- Exact Clarke product rule derived from ordinary gradients, closed convex
hulls and independent extra endpoint sequences. -/
theorem embeddedClarke_product {v z w : EmbeddedPoint ι} :
    w ∈ embeddedClarkeSubdiff (embeddedTilt v) z ↔
      w.1 ∈ clarkeSubdiff (tilt v.1) z.1 ∧ extraSupport v z w := by
  constructor
  · intro hw
    exact ⟨embeddedClarke_projection hw,
      fun i => ⟨embeddedClarke_extra_bound hw i,embeddedClarke_extra_eq hw i⟩⟩
  · rintro ⟨hb,he⟩
    have hex := extraSupport_mem_convexHull_vertices he
    let S : Set Point := {p | (p,w.2) ∈ embeddedClarkeSubdiff (embeddedTilt v) z}
    have hc : IsClosed S := isClosed_closure.preimage (continuous_id.prodMk continuous_const)
    have hsub : convexHull ℝ (gradientLimits (tilt v.1) z.1) ⊆ S := by
      intro p hp
      have hpair := mk_mem_convexHull_prod hp hex
      have hgl : gradientLimits (tilt v.1) z.1 ×ˢ extraVertexSet v z ⊆
          embeddedGradientLimits (embeddedTilt v) z := by
        intro u hu
        exact embeddedGradientLimits_lift hu.1 hu.2
      exact subset_closure (convexHull_mono hgl hpair)
    exact closure_minimal hsub hc hb


/-- Appendix A.3 (A1.Ex10), for the actual untitled separable objective. -/
theorem embeddedLimiting_zero :
    embeddedLimitingSubdiff (embeddedObjective : EmbeddedPoint ι → ℝ) 0 =
      limitingSubdiff F 0 ×ˢ {q : ι → ℝ | ∀ i, |q i| ≤ 2} := by
  have he : embeddedTilt (0:EmbeddedPoint ι) = embeddedObjective := by
    funext z
    simp [embeddedTilt,lin]
  have ht : tilt (0:Point) = F := by funext z; simp [tilt,lin]
  rw [← he]
  ext w
  rw [embeddedLimiting_product]
  simp [extraSupport,ht]

/-- Appendix A.3 (A1.Ex11), proved by actual gradient convexification. -/
theorem embeddedClarke_zero :
    embeddedClarkeSubdiff (embeddedObjective : EmbeddedPoint ι → ℝ) 0 =
      clarkeSubdiff F 0 ×ˢ {q : ι → ℝ | ∀ i, |q i| ≤ 2} := by
  have he : embeddedTilt (0:EmbeddedPoint ι) = embeddedObjective := by
    funext z
    simp [embeddedTilt,lin]
  have ht : tilt (0:Point) = F := by funext z; simp [tilt,lin]
  rw [← he]
  ext w
  rw [embeddedClarke_product]
  simp [extraSupport,ht]

end Paper32
