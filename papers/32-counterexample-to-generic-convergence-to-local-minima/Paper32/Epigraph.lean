import Paper32.Strata

open Set Filter Topology
namespace Paper32

abbrev EpiPoint := Point × ℝ

/-- The ordinary Euclidean dual pairing on ℝ²×ℝ. -/
def epiLin (n d : EpiPoint) : ℝ := lin n.1 d.1 + n.2*d.2

def epigraph (f : Point → ℝ) : Set EpiPoint := {p | f p.1 ≤ p.2}

/-- The regular (Fréchet) normal cone, defined by its neighborhood inequality. -/
def regularNormal (s : Set EpiPoint) (p : EpiPoint) : Set EpiPoint :=
  {n | p ∈ s ∧ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ q ∈ s, ‖q-p‖ < δ → epiLin n (q-p) ≤ ε*‖q-p‖}

/-- The limiting normal cone is the actual sequential outer limit of regular normals. -/
def limitingNormal (s : Set EpiPoint) (p : EpiPoint) : Set EpiPoint :=
  {n | p ∈ s ∧ ∃ a b : ℕ → EpiPoint,
    Tendsto a atTop (𝓝 p) ∧ Tendsto b atTop (𝓝 n) ∧
      ∀ i, b i ∈ regularNormal s (a i)}

/-- Clarke regularity of the epigraph, in the standard normal-cone convention:
regular and limiting normals agree at its graph point. Both normal cones above
are independently defined by their usual geometric inequalities and limits. -/
def EpigraphClarkeRegularAt (f : Point → ℝ) (z : Point) : Prop :=
  regularNormal (epigraph f) (z,f z) = limitingNormal (epigraph f) (z,f z)

lemma isClosed_epigraph_F : IsClosed (epigraph F) :=
  isClosed_le (continuous_F.comp continuous_fst) continuous_snd

/-- A regular subgradient gives a genuine regular normal to the epigraph. -/
lemma epi_regularNormal_of_frechet {f : Point → ℝ} {z w : Point}
    (hw : FrechetSubgradient f z w) :
    (w,-1) ∈ regularNormal (epigraph f) (z,f z) := by
  refine ⟨by change f z ≤ f z; exact le_rfl,?_⟩
  intro ε hε
  obtain ⟨δ,hδ,hs⟩ := hw ε hε
  refine ⟨δ,hδ,?_⟩
  intro q hq hqδ
  have hn : ‖q.1-z‖ ≤ ‖q-(z,f z)‖ := norm_fst_le (q-(z,f z))
  have hl := hs (q.1-z) (hn.trans_lt hqδ)
  have he : z+(q.1-z) = q.1 := by abel
  rw [he] at hl
  change f q.1 ≤ q.2 at hq
  change lin w (q.1-z) + (-1)*(q.2-f z) ≤ ε*‖q-(z,f z)‖
  nlinarith

/-- At graph points of this globally Lipschitz function, regular epigraph
normals with last coordinate -1 recover the genuine regular subgradient. -/
lemma frechet_of_epi_regularNormal_F {z w : Point}
    (hw : (w,-1) ∈ regularNormal (epigraph F) (z,F z)) :
    FrechetSubgradient F z w := by
  intro ε hε
  obtain ⟨δ,hδ,hs⟩ := hw.2 (ε/8) (by positivity)
  refine ⟨δ/8,by positivity,?_⟩
  intro u hu
  let q : EpiPoint := (z+u,F (z+u))
  have hq : q ∈ epigraph F := by change F (z+u) ≤ F (z+u); exact le_rfl
  have hf : |F (z+u)-F z| ≤ 8*‖u‖ := by
    simpa [dist_eq_norm,Real.norm_eq_abs] using lipschitz_F.dist_le_mul (z+u) z
  have hdist : ‖q-(z,F z)‖ ≤ 8*‖u‖ := by
    have he : q-(z,F z) = (u,F (z+u)-F z) := by
      apply Prod.ext
      · change (z+u)-z=u
        abel
      · rfl
    rw [he,Prod.norm_def,Real.norm_eq_abs]
    exact max_le (by nlinarith [norm_nonneg u]) hf
  have hb := hs q hq (hdist.trans_lt (by linarith))
  have he : (z+u)-z = u := by abel
  change lin w ((z+u)-z) + (-1)*(F (z+u)-F z) ≤ (ε/8)*‖q-(z,F z)‖ at hb
  rw [he] at hb
  nlinarith

/-- Limiting subgradients yield actual limiting epigraph normals via the same
realizing sequence. Value convergence in the subgradient definition supplies
the third epigraph coordinate. -/
lemma epi_limitingNormal_of_limiting {f : Point → ℝ} {z w : Point}
    (hw : w ∈ limitingSubdiff f z) :
    (w,-1) ∈ limitingNormal (epigraph f) (z,f z) := by
  obtain ⟨a,b,ha,hfa,hb,hd⟩ := hw
  refine ⟨by change f z ≤ f z; exact le_rfl,fun n => (a n,f (a n)),fun n => (b n,-1),
    ha.prodMk_nhds hfa,hb.prodMk_nhds tendsto_const_nhds,?_⟩
  intro n
  exact epi_regularNormal_of_frechet (hd n)

/-- The explicit witness to failure of epigraph Clarke regularity. -/
theorem epigraph_F_normal_gap :
    (((1,0),-1) : EpiPoint) ∈ limitingNormal (epigraph F) (0,F 0) ∧
    (((1,0),-1) : EpiPoint) ∉ regularNormal (epigraph F) (0,F 0) := by
  constructor
  · apply epi_limitingNormal_of_limiting
    rw [limiting_F_zero]
    left
    norm_num
  · intro hn
    have hf := frechet_of_epi_regularNormal_F hn
    have hm : ((1,0) : Point) ∈ frechetSubdiff F 0 := hf
    rw [frechet_F_zero_empty] at hm
    exact hm

/-- Corollary 3.3: the epigraph fails standard Clarke regularity at the origin. -/
theorem not_epigraphClarkeRegular_F_zero : ¬ EpigraphClarkeRegularAt F 0 := by
  intro h
  exact epigraph_F_normal_gap.2 (h.symm ▸ epigraph_F_normal_gap.1)

end Paper32
