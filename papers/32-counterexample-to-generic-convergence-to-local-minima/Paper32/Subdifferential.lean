import Paper32.Geometry
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.FiniteDimension

open Set Filter Topology

namespace Paper32

/-- Standard Fréchet subgradient inequality, in the product norm on ℝ².
The product norm is equivalent to the Euclidean norm, so this is the usual
Fréchet subdifferential, with the Euclidean dual pairing `lin`. -/
def FrechetSubgradient (f : Point → ℝ) (z w : Point) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ u : Point, ‖u‖ < δ → f z + lin w u - ε * ‖u‖ ≤ f (z + u)

def frechetSubdiff (f : Point → ℝ) (z : Point) : Set Point :=
  {w | FrechetSubgradient f z w}

/-- The Mordukhovich subdifferential, defined by actual Fréchet sequences. -/
def limitingSubdiff (f : Point → ℝ) (z : Point) : Set Point :=
  {w | ∃ a b : ℕ → Point, Tendsto a atTop (𝓝 z) ∧
    Tendsto (f ∘ a) atTop (𝓝 (f z)) ∧ Tendsto b atTop (𝓝 w) ∧
    ∀ n, FrechetSubgradient f (a n) (b n)}

/-- Reachable ordinary gradients, before convexification. -/
def gradientLimits (f : Point → ℝ) (z : Point) : Set Point :=
  {w | ∃ a b : ℕ → Point, Tendsto a atTop (𝓝 z) ∧
    Tendsto b atTop (𝓝 w) ∧ ∀ n, HasFDerivAt f (linCLM (b n)) (a n)}

/-- Standard Clarke subdifferential: the closed convex hull of limits of
ordinary gradients at differentiability points approaching `z`. -/
def clarkeSubdiff (f : Point → ℝ) (z : Point) : Set Point :=
  closure (convexHull ℝ (gradientLimits f z))

lemma frechet_of_hasFDerivAt {f : Point → ℝ} {z w : Point}
    (hd : HasFDerivAt f (linCLM w) z) : FrechetSubgradient f z w := by
  intro ε hε
  have he := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hd).bound hε
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨δ,hδ,?_⟩
  intro u hu
  have hb := hball (show u ∈ Metric.ball (0:Point) δ by simpa [dist_zero_right] using hu)
  change ‖f (z+u)-f z-(linCLM w) u‖ ≤ ε*‖u‖ at hb
  rw [Real.norm_eq_abs] at hb
  have hlow := (abs_le.mp hb).1
  change -(ε*‖u‖) ≤ f (z+u)-f z-lin w u at hlow
  linarith

@[simp] lemma lin_smul_right (w d : Point) (t : ℝ) :
    lin w (t • d) = t * lin w d := by simp [lin]; ring

lemma frechet_direction_le {f : Point → ℝ} {z w d : Point}
    (hw : FrechetSubgradient f z w) (hd : ‖d‖ = 1) {a r : ℝ} (hr : 0 < r)
    (hf : ∀ t : ℝ, 0 < t → t < r → f (z + t • d) ≤ f z + t * a) :
    lin w d ≤ a := by
  by_contra h
  have hp : 0 < (lin w d - a) / 2 := by linarith
  obtain ⟨δ, hδ, hs⟩ := hw ((lin w d - a) / 2) hp
  let t := min δ r / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have htδ : t < δ := by dsimp [t]; have := min_le_left δ r; linarith
  have htr : t < r := by dsimp [t]; have := min_le_right δ r; linarith
  have hn : ‖t • d‖ = t := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, hd, mul_one]
  have hlow := hs (t • d) (by simpa [hn] using htδ)
  rw [lin_smul_right, hn] at hlow
  have hupp := hf t ht htr
  nlinarith

lemma frechet_x_eq {f : Point → ℝ} {z w : Point} {a r : ℝ}
    (hw : FrechetSubgradient f z w) (hr : 0 < r)
    (hf : ∀ t : ℝ, |t| < r → f (z + (t,0)) ≤ f z + a*t) : w.1 = a := by
  have hp := frechet_direction_le hw (d := (1,0)) (a := a) (by norm_num [Prod.norm_def]) hr
    (fun t ht htr => by simpa [Prod.smul_mk, smul_eq_mul, mul_comm] using hf t (by rwa [abs_of_pos ht]))
  have hm := frechet_direction_le hw (d := (-1,0)) (a := -a) (by norm_num [Prod.norm_def]) hr
    (fun t ht htr => by simpa [Prod.smul_mk, smul_eq_mul, mul_comm] using hf (-t) (by simpa [abs_of_pos ht] using htr))
  simp [lin] at hp hm
  linarith

lemma frechet_y_eq {f : Point → ℝ} {z w : Point} {a r : ℝ}
    (hw : FrechetSubgradient f z w) (hr : 0 < r)
    (hf : ∀ t : ℝ, |t| < r → f (z + (0,t)) ≤ f z + a*t) : w.2 = a := by
  have hp := frechet_direction_le hw (d := (0,1)) (a := a) (by norm_num [Prod.norm_def]) hr
    (fun t ht htr => by simpa [Prod.smul_mk, smul_eq_mul, mul_comm] using hf t (by rwa [abs_of_pos ht]))
  have hm := frechet_direction_le hw (d := (0,-1)) (a := -a) (by norm_num [Prod.norm_def]) hr
    (fun t ht htr => by simpa [Prod.smul_mk, smul_eq_mul, mul_comm] using hf (-t) (by simpa [abs_of_pos ht] using htr))
  simp [lin] at hp hm
  linarith

lemma abs_add_small {x t : ℝ} (hx : x ≠ 0) (ht : |t| < |x|) :
    |x+t| = |x| + Real.sign x*t := by
  rcases lt_or_gt_of_ne hx with hx | hx
  · rw [abs_of_neg hx, Real.sign_of_neg hx]
    rw [abs_of_neg (by have := le_abs_self t; rw [abs_of_neg hx] at ht; linarith)]
    ring
  · rw [abs_of_pos hx, Real.sign_of_pos hx]
    rw [abs_of_pos (by have := neg_abs_le t; rw [abs_of_pos hx] at ht; linarith)]
    ring

/-- The origin has no regular subgradient; both vertical directions descend. -/
theorem frechet_g_zero_empty : frechetSubdiff g 0 = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro w hw
  have hp := frechet_direction_le hw (d := (0,1)) (by norm_num [Prod.norm_def])
    (r := 1) (a := -1) (by norm_num) (fun t ht _ => by
      simp [g, abs_of_pos ht])
  have hm := frechet_direction_le hw (d := (0,-1)) (by norm_num [Prod.norm_def])
    (r := 1) (a := -1) (by norm_num) (fun t ht _ => by
      simp [g, abs_of_pos ht])
  simp [lin] at hp hm
  linarith

/-- The two actual segments appearing in Proposition 3.2. -/
def limitingSegments : Set Point :=
  {w | (|w.1| = 1 ∧ |w.2| ≤ 2) ∨ (|w.1| ≤ 7 ∧ |w.2| = 1)}

lemma g_le_p (z : Point) : g z ≤ |z.1|+2*|z.2| := min_le_left _ _
lemma g_le_q (z : Point) : g z ≤ 7*|z.1|-|z.2| := min_le_right _ _

lemma g_le_p_xy (z : Point) (x y : ℝ) :
    g (z+(x,y)) ≤ |z.1+x|+2*|z.2+y| := by
  change min (|z.1+x|+2*|z.2+y|) (7*|z.1+x|-|z.2+y|) ≤ _
  exact min_le_left _ _
lemma g_le_q_xy (z : Point) (x y : ℝ) :
    g (z+(x,y)) ≤ 7*|z.1+x|-|z.2+y| := by
  change min (|z.1+x|+2*|z.2+y|) (7*|z.1+x|-|z.2+y|) ≤ _
  exact min_le_right _ _

lemma frechet_g_active_p {z w : Point} (hw : FrechetSubgradient g z w)
    (hz : |z.2| ≤ 2 * |z.1|) (hx : z.1 ≠ 0) :
    w.1 = Real.sign z.1 ∧ |w.2| ≤ 2 := by
  have hgz := g_horizontal hz
  constructor
  · apply frechet_x_eq hw (abs_pos.mpr hx)
    intro t ht
    calc
      g (z+(t,0)) ≤ |z.1+t| + 2*|z.2| := by simpa only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,Prod.smul_mk,smul_eq_mul,mul_zero,mul_one,mul_neg_one,add_zero,zero_add] using g_le_p_xy z t 0
      _ = g z + Real.sign z.1*t := by rw [hgz, abs_add_small hx ht]; ring
  · have hp := frechet_direction_le hw (d := (0,1)) (by norm_num [Prod.norm_def])
      (r := 1) (a := 2) (by norm_num) (fun t ht _ => by
        have h := abs_add_le z.2 t
        calc
          g (z+t • (0,1)) ≤ |z.1| + 2*|z.2+t| := by simpa only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,Prod.smul_mk,smul_eq_mul,mul_zero,mul_one,mul_neg_one,add_zero,zero_add] using g_le_p_xy z 0 t
          _ ≤ g z + t*2 := by rw [hgz, abs_of_pos ht] at *; linarith)
    have hm := frechet_direction_le hw (d := (0,-1)) (by norm_num [Prod.norm_def])
      (r := 1) (a := 2) (by norm_num) (fun t ht _ => by
        have h := abs_sub z.2 t
        calc
          g (z+t • (0,-1)) ≤ |z.1| + 2*|z.2-t| := by simpa only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,Prod.smul_mk,smul_eq_mul,mul_zero,mul_one,mul_neg_one,add_zero,zero_add,sub_eq_add_neg] using g_le_p_xy z 0 (-t)
          _ ≤ g z + t*2 := by rw [hgz, abs_of_pos ht] at *; linarith)
    simp [lin] at hp hm
    exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma frechet_g_active_q {z w : Point} (hw : FrechetSubgradient g z w)
    (hz : 2 * |z.1| ≤ |z.2|) (hy : z.2 ≠ 0) :
    |w.1| ≤ 7 ∧ w.2 = -Real.sign z.2 := by
  have hgz := g_vertical hz
  constructor
  · have hp := frechet_direction_le hw (d := (1,0)) (by norm_num [Prod.norm_def])
      (r := 1) (a := 7) (by norm_num) (fun t ht _ => by
        have h := abs_add_le z.1 t
        calc
          g (z+t • (1,0)) ≤ 7*|z.1+t| - |z.2| := by simpa only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,Prod.smul_mk,smul_eq_mul,mul_zero,mul_one,mul_neg_one,add_zero,zero_add] using g_le_q_xy z t 0
          _ ≤ g z + t*7 := by rw [hgz, abs_of_pos ht] at *; linarith)
    have hm := frechet_direction_le hw (d := (-1,0)) (by norm_num [Prod.norm_def])
      (r := 1) (a := 7) (by norm_num) (fun t ht _ => by
        have h := abs_sub z.1 t
        calc
          g (z+t • (-1,0)) ≤ 7*|z.1-t| - |z.2| := by simpa only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,Prod.smul_mk,smul_eq_mul,mul_zero,mul_one,mul_neg_one,add_zero,zero_add,sub_eq_add_neg] using g_le_q_xy z (-t) 0
          _ ≤ g z + t*7 := by rw [hgz, abs_of_pos ht] at *; linarith)
    simp [lin] at hp hm
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · apply frechet_y_eq hw (abs_pos.mpr hy)
    intro t ht
    calc
      g (z+(0,t)) ≤ 7*|z.1| - |z.2+t| := by simpa only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,Prod.smul_mk,smul_eq_mul,mul_zero,mul_one,mul_neg_one,add_zero,zero_add] using g_le_q_xy z 0 t
      _ = g z + (-Real.sign z.2)*t := by rw [hgz, abs_add_small hy ht]; ring

lemma abs_sign_of_ne {x : ℝ} (hx : x ≠ 0) : |Real.sign x| = 1 := by
  rcases lt_or_gt_of_ne hx with hx | hx
  · simp [Real.sign_of_neg hx]
  · simp [Real.sign_of_pos hx]

/-- Every actual Fréchet value belongs to one of the displayed segments.
This is an inclusion theorem, not the definition of either subdifferential. -/
theorem frechet_g_subset_segments {z w : Point} (hw : FrechetSubgradient g z w) :
    w ∈ limitingSegments := by
  have hne : z ≠ 0 := by
    intro hz
    subst z
    have : w ∈ frechetSubdiff g 0 := hw
    rw [frechet_g_zero_empty] at this
    exact this
  by_cases hh : |z.2| ≤ 2*|z.1|
  · have hx : z.1 ≠ 0 := by
      intro hx
      have hy : z.2 = 0 := abs_eq_zero.mp (by simpa [hx] using hh)
      exact hne (Prod.ext hx hy)
    obtain ⟨h1,h2⟩ := frechet_g_active_p hw hh hx
    exact Or.inl ⟨by rw [h1]; exact abs_sign_of_ne hx, h2⟩
  · have hv : 2*|z.1| ≤ |z.2| := le_of_lt (lt_of_not_ge hh)
    have hy : z.2 ≠ 0 := by intro hy; simp [hy] at hh
    obtain ⟨h1,h2⟩ := frechet_g_active_q hw hv hy
    exact Or.inr ⟨h1, by rw [h2, abs_neg]; exact abs_sign_of_ne hy⟩

lemma norm_coord_bounds (u : Point) : |u.1| ≤ ‖u‖ ∧ |u.2| ≤ ‖u‖ := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  exact ⟨le_max_left _ _, le_max_right _ _⟩

lemma sign_support (x t : ℝ) : |x| + Real.sign x * t ≤ |x+t| := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [abs_of_neg hx, Real.sign_of_neg hx]
    nlinarith [neg_abs_le (x+t)]
  · simp
  · rw [abs_of_pos hx, Real.sign_of_pos hx]
    nlinarith [le_abs_self (x+t)]

lemma mul_le_abs_bound {a t C : ℝ} (ha : |a| ≤ C) : a*t ≤ C*|t| := by
  calc
    a*t ≤ |a*t| := le_abs_self _
    _ = |a| * |t| := abs_mul _ _
    _ ≤ C*|t| := mul_le_mul_of_nonneg_right ha (abs_nonneg _)

/-- Every point of the horizontal regular segment is a genuine Fréchet value. -/
theorem frechet_g_horizontal_axis {x η : ℝ} (hx : x ≠ 0) (hη : |η| ≤ 2) :
    FrechetSubgradient g (x,0) (Real.sign x,η) := by
  intro ε hε
  refine ⟨|x|/4, by positivity, ?_⟩
  intro u hu
  obtain ⟨hu1,hu2⟩ := norm_coord_bounds u
  have htri : |x| ≤ |x+u.1|+|u.1| := by
    simpa using abs_sub (x+u.1) u.1
  have hsector : |( ((x,0):Point) + u).2| ≤ 2*|(((x,0):Point)+u).1| := by
    simp only [Prod.fst_add, Prod.snd_add, zero_add]
    linarith [abs_nonneg x]
  rw [g_horizontal hsector, g_horizontal (z := (x,0)) (by simp)]
  simp only [Prod.fst_add, Prod.snd_add, zero_add, abs_zero, mul_zero, add_zero, lin]
  have hs := sign_support x u.1
  have hm := mul_le_abs_bound (t := u.2) hη
  have hn := mul_nonneg (le_of_lt hε) (norm_nonneg u)
  linarith

/-- Every point of the vertical regular segment is a genuine Fréchet value. -/
theorem frechet_g_vertical_axis {y ξ : ℝ} (hy : y ≠ 0) (hξ : |ξ| ≤ 7) :
    FrechetSubgradient g (0,y) (ξ,-Real.sign y) := by
  intro ε hε
  refine ⟨|y|/8, by positivity, ?_⟩
  intro u hu
  obtain ⟨hu1,hu2⟩ := norm_coord_bounds u
  have htri : |y| ≤ |y+u.2|+|u.2| := by
    simpa using abs_sub (y+u.2) u.2
  have hsector : 2*|(((0,y):Point)+u).1| ≤ |(((0,y):Point)+u).2| := by
    simp only [Prod.fst_add, Prod.snd_add, zero_add]
    linarith [abs_nonneg y]
  have hsmall : |u.2| < |y| := by linarith [abs_pos.mpr hy]
  rw [g_vertical hsector, g_vertical (z := (0,y)) (by simp)]
  simp only [Prod.fst_add, Prod.snd_add, zero_add, abs_zero, mul_zero, zero_sub, lin]
  rw [abs_add_small hy hsmall]
  have hm := mul_le_abs_bound (t := u.1) hξ
  have hn := mul_nonneg (le_of_lt hε) (norm_nonneg u)
  linarith

lemma isClosed_limitingSegments : IsClosed limitingSegments := by
  change IsClosed ({w : Point | |w.1| = 1 ∧ |w.2| ≤ 2} ∪
    {w : Point | |w.1| ≤ 7 ∧ |w.2| = 1})
  have h1 : Continuous (fun w : Point => |w.1|) := continuous_abs.comp continuous_fst
  have h2 : Continuous (fun w : Point => |w.2|) := continuous_abs.comp continuous_snd
  exact ((isClosed_eq h1 continuous_const).inter (isClosed_le h2 continuous_const)).union
    ((isClosed_le h1 continuous_const).inter (isClosed_eq h2 continuous_const))

lemma limiting_g_subset_segments {w : Point} (hw : w ∈ limitingSubdiff g 0) :
    w ∈ limitingSegments := by
  obtain ⟨a,b,ha,hga,hb,hf⟩ := hw
  exact isClosed_limitingSegments.mem_of_tendsto hb
    (Filter.Eventually.of_forall (fun n => frechet_g_subset_segments (hf n)))

lemma sign_eq_of_abs_eq_one {x : ℝ} (hx : |x| = 1) : Real.sign x = x := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [abs_of_neg h] at hx
    rw [Real.sign_of_neg h]
    linarith
  · simp [h] at hx
  · rw [abs_of_pos h] at hx
    rw [Real.sign_of_pos h]
    linarith

lemma sign_div_natSucc {x : ℝ} (hx : x ≠ 0) (n : ℕ) :
    Real.sign (x / (n+1 : ℝ)) = Real.sign x := by
  have hn : 0 < (n+1 : ℝ) := by positivity
  rcases lt_or_gt_of_ne hx with h | h
  · rw [Real.sign_of_neg h, Real.sign_of_neg (div_neg_of_neg_of_pos h hn)]
  · rw [Real.sign_of_pos h, Real.sign_of_pos (div_pos h hn)]

/-- Exact limiting geometry (3.7), obtained from regular subgradients. -/
theorem limiting_g_zero : limitingSubdiff g 0 = limitingSegments := by
  apply Set.Subset.antisymm
  · exact fun _ => limiting_g_subset_segments
  · intro w hw
    rcases hw with ⟨hw1,hw2⟩ | ⟨hw1,hw2⟩
    · have hx : w.1 ≠ 0 := by intro h; simp [h] at hw1
      let a : ℕ → Point := fun n => (w.1/(n+1 : ℝ),0)
      have ha : Tendsto a atTop (𝓝 0) := by
        have ht := (tendsto_const_nhds (x := w.1)).mul tendsto_one_div_add_atTop_nhds_zero_nat
        simpa [a, div_eq_mul_inv] using ht.prodMk_nhds (tendsto_const_nhds (x := (0:ℝ)))
      refine ⟨a,fun _ => w,ha,continuous_g.continuousAt.tendsto.comp ha,tendsto_const_nhds,?_⟩
      intro n
      have hh := frechet_g_horizontal_axis (x := w.1/(n+1 : ℝ))
        (div_ne_zero hx (by positivity)) hw2
      simpa [a,sign_div_natSucc hx,sign_eq_of_abs_eq_one hw1] using hh
    · have hy : -w.2 ≠ 0 := neg_ne_zero.mpr (by intro h; simp [h] at hw2)
      let a : ℕ → Point := fun n => (0,-w.2/(n+1 : ℝ))
      have ha : Tendsto a atTop (𝓝 0) := by
        have ht := (tendsto_const_nhds (x := -w.2)).mul tendsto_one_div_add_atTop_nhds_zero_nat
        simpa [a, div_eq_mul_inv] using (tendsto_const_nhds (x := (0:ℝ))).prodMk_nhds ht
      refine ⟨a,fun _ => w,ha,continuous_g.continuousAt.tendsto.comp ha,tendsto_const_nhds,?_⟩
      intro n
      have hh := frechet_g_vertical_axis (y := -w.2/(n+1 : ℝ))
        (div_ne_zero hy (by positivity)) hw1
      have hs : -Real.sign (-w.2) = w.2 := by
        rw [Real.sign_neg, sign_eq_of_abs_eq_one hw2, neg_neg]
      simpa [a,sign_div_natSucc hy,hs] using hh

/-- A fixed rectangle containing every ordinary gradient and every Clarke value. -/
def gradientBox : Set Point := Set.Icc (-7 : ℝ) 7 ×ˢ Set.Icc (-2 : ℝ) 2

lemma isClosed_gradientBox : IsClosed gradientBox := isClosed_Icc.prod isClosed_Icc
lemma convex_gradientBox : Convex ℝ gradientBox := (convex_Icc _ _).prod (convex_Icc _ _)

lemma gradient_g_mem_box {z w : Point} (hw : HasFDerivAt g (linCLM w) z) :
    w ∈ gradientBox := by
  have hs := frechet_g_subset_segments (frechet_of_hasFDerivAt hw)
  rcases hs with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · have h1' : |w.1| ≤ 7 := by linarith
    exact ⟨abs_le.mp h1', abs_le.mp h2⟩
  · have h2' : |w.2| ≤ 2 := by linarith
    exact ⟨abs_le.mp h1, abs_le.mp h2'⟩

lemma gradientLimits_g_subset_box (z : Point) : gradientLimits g z ⊆ gradientBox := by
  rintro w ⟨a,b,ha,hb,hd⟩
  exact isClosed_gradientBox.mem_of_tendsto hb
    (Filter.Eventually.of_forall (fun n => gradient_g_mem_box (hd n)))

/-- The coordinate bound used for every admissible first oracle value. -/
theorem clarke_g_coordinate_bound {z w : Point} (hw : w ∈ clarkeSubdiff g z) :
    |w.1| ≤ 7 ∧ |w.2| ≤ 2 := by
  have hs : clarkeSubdiff g z ⊆ gradientBox :=
    closure_minimal (convexHull_min (gradientLimits_g_subset_box z) convex_gradientBox)
      isClosed_gradientBox
  exact ⟨abs_le.mpr (hs hw).1, abs_le.mpr (hs hw).2⟩

lemma hasFDerivAt_neg_gradient {f : Point → ℝ} {z w : Point}
    (hd : HasFDerivAt f (linCLM w) z) :
    HasFDerivAt (fun q => -f q) (linCLM (-w)) z := by
  have hn : linCLM (-w) = -(linCLM w) := by
    apply ContinuousLinearMap.ext
    intro u
    change lin (-w) u = -(lin w u)
    simp only [lin,Prod.fst_neg,Prod.snd_neg]
    ring
  rw [hn]
  exact hd.neg

lemma no_gradient_g_horizontal_axis {x : ℝ} {w : Point} (hx : x ≠ 0) :
    ¬ HasFDerivAt g (linCLM w) (x,0) := by
  intro hd
  have hn := frechet_of_hasFDerivAt (hasFDerivAt_neg_gradient hd)
  have hp := frechet_direction_le hn (d := (0,1)) (by norm_num [Prod.norm_def])
    (r := |x|) (a := -2) (abs_pos.mpr hx) (fun t ht htx => by
      have hg := g_horizontal (z := (x,t)) (by rw [abs_of_pos ht]; linarith [abs_nonneg x])
      have hg0 := g_horizontal (z := (x,0)) (by simp)
      simp [hg,hg0,abs_of_pos ht]
      linarith)
  have hm := frechet_direction_le hn (d := (0,-1)) (by norm_num [Prod.norm_def])
    (r := |x|) (a := -2) (abs_pos.mpr hx) (fun t ht htx => by
      have hg := g_horizontal (z := (x,-t)) (by rw [abs_neg,abs_of_pos ht]; linarith [abs_nonneg x])
      have hg0 := g_horizontal (z := (x,0)) (by simp)
      simp [hg,hg0,abs_of_pos ht]
      linarith)
  simp [lin] at hp hm
  linarith

lemma no_gradient_g_vertical_axis {y : ℝ} {w : Point} (hy : y ≠ 0) :
    ¬ HasFDerivAt g (linCLM w) (0,y) := by
  intro hd
  have hn := frechet_of_hasFDerivAt (hasFDerivAt_neg_gradient hd)
  have hp := frechet_direction_le hn (d := (1,0)) (by norm_num [Prod.norm_def])
    (r := |y|/4) (a := -7) (by positivity) (fun t ht hty => by
      have hg := g_vertical (z := (t,y)) (by rw [abs_of_pos ht]; linarith)
      have hg0 := g_vertical (z := (0,y)) (by simp)
      simp only [Prod.smul_fst,Prod.smul_snd,Prod.smul_mk,smul_eq_mul,mul_one,mul_zero,Prod.mk_add_mk,zero_add,add_zero]
      rw [hg,hg0,abs_of_pos ht]
      simp
      ring_nf
      exact le_refl _)
  have hm := frechet_direction_le hn (d := (-1,0)) (by norm_num [Prod.norm_def])
    (r := |y|/4) (a := -7) (by positivity) (fun t ht hty => by
      have hg := g_vertical (z := (-t,y)) (by rw [abs_neg,abs_of_pos ht]; linarith)
      have hg0 := g_vertical (z := (0,y)) (by simp)
      simp only [Prod.smul_fst,Prod.smul_snd,Prod.smul_mk,smul_eq_mul,mul_neg_one,mul_zero,Prod.mk_add_mk,zero_add,add_zero]
      rw [hg,hg0,abs_neg,abs_of_pos ht]
      simp
      ring_nf
      exact le_refl _)
  simp [lin] at hp hm
  linarith

/-- The eight ordinary gradients in the two sector families. -/
def sectorGradients : Set Point :=
  {w | (|w.1| = 1 ∧ |w.2| = 2) ∨ (|w.1| = 7 ∧ |w.2| = 1)}

lemma gradient_g_mem_eight {z w : Point} (hd : HasFDerivAt g (linCLM w) z) :
    w ∈ sectorGradients := by
  have hf := frechet_of_hasFDerivAt hd
  have hz : z ≠ 0 := by
    intro hz
    subst z
    have : w ∈ frechetSubdiff g 0 := hf
    rw [frechet_g_zero_empty] at this
    exact this
  have hx : z.1 ≠ 0 := by
    intro hx
    have hy : z.2 ≠ 0 := by intro hy; exact hz (Prod.ext hx hy)
    have he : z = (0,z.2) := Prod.ext hx rfl
    rw [he] at hd
    exact no_gradient_g_vertical_axis hy hd
  have hy : z.2 ≠ 0 := by
    intro hy
    have he : z = (z.1,0) := Prod.ext rfl hy
    rw [he] at hd
    exact no_gradient_g_horizontal_axis hx hd
  by_cases hh : |z.2| ≤ 2*|z.1|
  · have hxw := (frechet_g_active_p hf hh hx).1
    have hyw : w.2 = 2*Real.sign z.2 := by
      apply frechet_y_eq hf (abs_pos.mpr hy)
      intro t ht
      calc
        g (z+(0,t)) ≤ |z.1|+2*|z.2+t| := by simpa only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,Prod.smul_mk,smul_eq_mul,mul_zero,mul_one,mul_neg_one,add_zero,zero_add] using g_le_p_xy z 0 t
        _ = g z + (2*Real.sign z.2)*t := by
          rw [g_horizontal hh,abs_add_small hy ht]
          ring
    exact Or.inl ⟨by rw [hxw]; exact abs_sign_of_ne hx,
      by rw [hyw,abs_mul,abs_sign_of_ne hy]; norm_num⟩
  · have hv : 2*|z.1| ≤ |z.2| := le_of_lt (lt_of_not_ge hh)
    have hyw := (frechet_g_active_q hf hv hy).2
    have hxw : w.1 = 7*Real.sign z.1 := by
      apply frechet_x_eq hf (abs_pos.mpr hx)
      intro t ht
      calc
        g (z+(t,0)) ≤ 7*|z.1+t|-|z.2| := by simpa only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,Prod.smul_mk,smul_eq_mul,mul_zero,mul_one,mul_neg_one,add_zero,zero_add] using g_le_q_xy z t 0
        _ = g z + (7*Real.sign z.1)*t := by
          rw [g_vertical hv,abs_add_small hx ht]
          ring
    exact Or.inr ⟨by rw [hxw,abs_mul,abs_sign_of_ne hx]; norm_num,
      by rw [hyw,abs_neg]; exact abs_sign_of_ne hy⟩

lemma isClosed_sectorGradients : IsClosed sectorGradients := by
  change IsClosed ({w : Point | |w.1|=1 ∧ |w.2|=2} ∪
    {w : Point | |w.1|=7 ∧ |w.2|=1})
  have h1 : Continuous (fun w : Point => |w.1|) := continuous_abs.comp continuous_fst
  have h2 : Continuous (fun w : Point => |w.2|) := continuous_abs.comp continuous_snd
  exact ((isClosed_eq h1 continuous_const).inter (isClosed_eq h2 continuous_const)).union
    ((isClosed_eq h1 continuous_const).inter (isClosed_eq h2 continuous_const))

lemma sectorGradients_subset_box : sectorGradients ⊆ gradientBox := by
  rintro w (⟨h1,h2⟩ | ⟨h1,h2⟩)
  · exact ⟨abs_le.mp (by linarith),abs_le.mp (by linarith)⟩
  · exact ⟨abs_le.mp (by linarith),abs_le.mp (by linarith)⟩

lemma finite_abs_level (c : ℝ) : {x : ℝ | |x|=c}.Finite := by
  apply (Set.Finite.insert c (Set.finite_singleton (-c))).subset
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  by_cases h : 0 ≤ x
  · left
    simpa [abs_of_nonneg h] using hx
  · right
    have : -x=c := by simpa [abs_of_neg (lt_of_not_ge h)] using hx
    linarith

lemma finite_sectorGradients : sectorGradients.Finite := by
  exact ((finite_abs_level 1).prod (finite_abs_level 2)).union
    ((finite_abs_level 7).prod (finite_abs_level 1))

lemma isCompact_sectorGradients : IsCompact sectorGradients :=
  (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset isClosed_sectorGradients sectorGradients_subset_box

lemma gradientLimits_g_subset_eight (z : Point) : gradientLimits g z ⊆ sectorGradients := by
  rintro w ⟨a,b,ha,hb,hd⟩
  exact isClosed_sectorGradients.mem_of_tendsto hb
    (Filter.Eventually.of_forall (fun n => gradient_g_mem_eight (hd n)))

lemma horizontal_gradient_reachable {σ τ : ℝ} (hσ : |σ|=1) (hτ : |τ|=1) :
    (σ,2*τ) ∈ gradientLimits g 0 := by
  have hσ0 : σ ≠ 0 := by intro h; simp [h] at hσ
  have hτ0 : τ ≠ 0 := by intro h; simp [h] at hτ
  let a : ℕ → Point := fun n => (σ/(n+1 : ℝ),τ/(n+1 : ℝ))
  have ha : Tendsto a atTop (𝓝 0) := by
    have hs : Tendsto (fun n : ℕ => σ/(n+1 : ℝ)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using (tendsto_const_nhds (x := σ)).mul tendsto_one_div_add_atTop_nhds_zero_nat
    have ht : Tendsto (fun n : ℕ => τ/(n+1 : ℝ)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using (tendsto_const_nhds (x := τ)).mul tendsto_one_div_add_atTop_nhds_zero_nat
    exact hs.prodMk_nhds ht
  refine ⟨a,fun _ => (σ,2*τ),ha,tendsto_const_nhds,?_⟩
  intro n
  have hn : 0 < (n+1 : ℝ) := by positivity
  have hh : |(a n).2| < 2*|(a n).1| := by
    dsimp [a]
    rw [abs_div,abs_div,hσ,hτ,abs_of_pos hn]
    have := one_div_pos.mpr hn
    linarith
  have hd := hasFDerivAt_g_horizontal (z := a n)
    (div_ne_zero hσ0 (ne_of_gt hn)) (div_ne_zero hτ0 (ne_of_gt hn)) hh
  simpa [a,sign_div_natSucc hσ0,sign_div_natSucc hτ0,
    sign_eq_of_abs_eq_one hσ,sign_eq_of_abs_eq_one hτ] using hd

lemma vertical_gradient_reachable {σ τ : ℝ} (hσ : |σ|=1) (hτ : |τ|=1) :
    (7*σ,τ) ∈ gradientLimits g 0 := by
  have hσ0 : σ ≠ 0 := by intro h; simp [h] at hσ
  have hτ0 : -3*τ ≠ 0 := mul_ne_zero (by norm_num) (by intro h; simp [h] at hτ)
  let a : ℕ → Point := fun n => (σ/(n+1 : ℝ),(-3*τ)/(n+1 : ℝ))
  have ha : Tendsto a atTop (𝓝 0) := by
    have hs : Tendsto (fun n : ℕ => σ/(n+1 : ℝ)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using (tendsto_const_nhds (x := σ)).mul tendsto_one_div_add_atTop_nhds_zero_nat
    have ht : Tendsto (fun n : ℕ => (-3*τ)/(n+1 : ℝ)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using (tendsto_const_nhds (x := -3*τ)).mul tendsto_one_div_add_atTop_nhds_zero_nat
    exact hs.prodMk_nhds ht
  refine ⟨a,fun _ => (7*σ,τ),ha,tendsto_const_nhds,?_⟩
  intro n
  have hn : 0 < (n+1 : ℝ) := by positivity
  have hv : 2*|(a n).1| < |(a n).2| := by
    dsimp [a]
    rw [abs_div,abs_div,abs_mul,hσ,hτ,abs_of_pos hn]
    norm_num
    have := one_div_pos.mpr hn
    simp only [div_eq_mul_inv,one_mul] at *
    linarith
  have hd := hasFDerivAt_g_vertical (z := a n)
    (div_ne_zero hσ0 (ne_of_gt hn)) (div_ne_zero hτ0 (ne_of_gt hn)) hv
  have hs : -Real.sign (-3*τ) = τ := by
    rcases lt_trichotomy τ 0 with h | h | h
    · rw [Real.sign_of_pos (by nlinarith : 0 < -3*τ),abs_of_neg h] at *
      linarith
    · simp [h] at hτ
    · rw [Real.sign_of_neg (by nlinarith : -3*τ < 0),abs_of_pos h] at *
      linarith
  change HasFDerivAt g
    (linCLM (7*Real.sign (σ/(n+1:ℝ)),-Real.sign ((-3*τ)/(n+1:ℝ)))) (a n) at hd
  rw [sign_div_natSucc hσ0,sign_div_natSucc hτ0,sign_eq_of_abs_eq_one hσ,hs] at hd
  exact hd

/-- Exactly the eight sector gradients are reachable at the origin. -/
theorem gradientLimits_g_zero : gradientLimits g 0 = sectorGradients := by
  apply Set.Subset.antisymm (gradientLimits_g_subset_eight 0)
  intro w hw
  rcases hw with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · have hhalf : |w.2/2|=1 := by rw [abs_div]; norm_num; linarith
    have h := horizontal_gradient_reachable h1 hhalf
    convert h using 1 <;> ext <;> simp <;> ring
  · have hseventh : |w.1/7|=1 := by rw [abs_div]; norm_num; linarith
    have h := vertical_gradient_reachable hseventh h2
    convert h using 1 <;> ext <;> simp <;> ring

/-- Exact Clarke geometry (3.8), from the standard gradient-limit definition. -/
theorem clarke_g_zero : clarkeSubdiff g 0 = convexHull ℝ sectorGradients := by
  unfold clarkeSubdiff
  rw [gradientLimits_g_zero]
  exact finite_sectorGradients.isClosed_convexHull.closure_eq

/-- The inner horizontal rectangle (3.9) belongs to the genuine Clarke value. -/
theorem rectangle_subset_clarke_g_zero {w : Point} (hx : |w.1|≤1) (hy : |w.2|≤2) :
    w ∈ clarkeSubdiff g 0 := by
  rw [clarke_g_zero]
  have hc := convex_convexHull ℝ sectorGradients
  have hcorner (x y : ℝ) (hx : |x|=1) (hy : |y|=2) :
      (x,y) ∈ convexHull ℝ sectorGradients := subset_convexHull ℝ _ (Or.inl ⟨hx,hy⟩)
  have hm : (w.1,-2) ∈ convexHull ℝ sectorGradients := by
    have h := hc (hcorner (-1) (-2) (by norm_num) (by norm_num))
      (hcorner 1 (-2) (by norm_num) (by norm_num))
      (show 0≤(1-w.1)/2 by linarith [(abs_le.mp hx).2])
      (show 0≤(1+w.1)/2 by linarith [(abs_le.mp hx).1])
      (show (1-w.1)/2+(1+w.1)/2=1 by ring)
    convert h using 1 <;> ext <;> simp <;> ring
  have hp : (w.1,2) ∈ convexHull ℝ sectorGradients := by
    have h := hc (hcorner (-1) 2 (by norm_num) (by norm_num))
      (hcorner 1 2 (by norm_num) (by norm_num))
      (show 0≤(1-w.1)/2 by linarith [(abs_le.mp hx).2])
      (show 0≤(1+w.1)/2 by linarith [(abs_le.mp hx).1])
      (show (1-w.1)/2+(1+w.1)/2=1 by ring)
    convert h using 1 <;> ext <;> simp <;> ring
  have h := hc hm hp (show 0≤(2-w.2)/4 by linarith [(abs_le.mp hy).2])
    (show 0≤(2+w.2)/4 by linarith [(abs_le.mp hy).1])
    (show (2-w.2)/4+(2+w.2)/4=1 by ring)
  convert h using 1 <;> ext <;> simp <;> ring

/-- The source's Euclidean norm, written explicitly on the two coordinates. -/
noncomputable def euclideanNorm (u : Point) : ℝ := Real.sqrt (u.1^2+u.2^2)

lemma norm_le_euclideanNorm (u : Point) : ‖u‖ ≤ euclideanNorm u := by
  rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
  apply max_le
  · apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg u.2, sq_abs u.1]
  · apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg u.1, sq_abs u.2]

lemma euclideanNorm_le_two_norm (u : Point) : euclideanNorm u ≤ 2*‖u‖ := by
  apply Real.sqrt_le_iff.mpr
  obtain ⟨h1,h2⟩ := norm_coord_bounds u
  have hn := norm_nonneg u
  constructor
  · positivity
  · have ha1 := abs_nonneg u.1
    have ha2 := abs_nonneg u.2
    nlinarith [sq_abs u.1,sq_abs u.2]

/-- The literal Euclidean epsilon-neighborhood definition from Section 2.1. -/
def EuclideanFrechetSubgradient (f : Point → ℝ) (z w : Point) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ u : Point, euclideanNorm u < δ →
      f z + lin w u - ε*euclideanNorm u ≤ f (z+u)

/-- Checked norm invariance: the regular subdifferential used in this file is
exactly the paper's Euclidean regular subdifferential. -/
theorem frechet_iff_euclidean {f : Point → ℝ} {z w : Point} :
    FrechetSubgradient f z w ↔ EuclideanFrechetSubgradient f z w := by
  constructor
  · intro h ε hε
    obtain ⟨δ,hδ,hs⟩ := h ε hε
    refine ⟨δ,hδ,?_⟩
    intro u hu
    have hn := norm_le_euclideanNorm u
    have hl := hs u (hn.trans_lt hu)
    nlinarith
  · intro h ε hε
    obtain ⟨δ,hδ,hs⟩ := h (ε/2) (by positivity)
    refine ⟨δ/2,by positivity,?_⟩
    intro u hu
    have hn := euclideanNorm_le_two_norm u
    have hl := hs u (by linarith)
    nlinarith

end Paper32
