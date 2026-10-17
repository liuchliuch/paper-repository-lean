import Paper35.DeepSwitch
import Paper35.CrossingRegularity

/-! Actual breakpoint inclusion. The deterministic part explicitly requires
no triple ties; the probability part derives that condition from the original
conditional-density source laws. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal
namespace Paper35.DeepBreaks
open Paper35.CurveCalculus

/-- Local affine behavior in the original real parameter. -/
def LocallyAffineAt {E : Type*} [AddCommGroup E] [Module ℝ E] (f : ℝ → E) (t : ℝ) : Prop :=
  ∃ a b : E, f =ᶠ[𝓝 t] (fun s => s • a+b)

def NoTriple {K : ℕ} (f : Fin K → ℝ → ℝ) (t : ℝ) : Prop :=
  ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ (f i t=f j t ∧ f i t=f k t)

def breakSet {d : ℕ} (η : ℝ → Space d) (L : ℝ) : Set ℝ :=
  {t | t ∈ Ioo 0 L ∧ ¬ LocallyAffineAt η t}

set_option maxHeartbeats 500000 in
/-- A finite maximum of locally affine scalar scores is locally affine or has
an actual Definition 2.1 switch, if three candidates cannot tie. -/
theorem finiteMax_locallyAffine_or_switch {K : ℕ} (hK : 0 < K)
    (f : Fin K → ℝ → ℝ) {L t : ℝ} (ht : t ∈ Ioo 0 L)
    (hf : ∀ j, LocallyAffineAt (f j) t) (htriple : NoTriple f t) :
    LocallyAffineAt (fun s => finiteSup hK (fun j => f j s)) t ∨ Paper35.ActiveSwitch f L t := by
  classical
  choose a b hab using hf
  have heq (j : Fin K) : f j t=t*a j+b j := by
    simpa only [smul_eq_mul] using (hab j).eq_of_nhds
  have hd (j : Fin K) : HasDerivAt (f j) (a j) t := by
    have H := ((hasDerivAt_id t).mul_const (a j)).add_const (b j)
    simp only [one_mul] at H
    exact H.congr_of_eventuallyEq (by simpa only [smul_eq_mul] using hab j)
  let i := winner hK (fun j => f j t)
  have hmax (j : Fin K) : f j t ≤ f i t := winner_is_max hK (fun j => f j t) j
  by_cases hsame : ∀ j, f j t=f i t → a j=a i
  · left
    refine ⟨a i,b i,?_⟩
    have hle (j : Fin K) : ∀ᶠ s in 𝓝 t, f j s ≤ f i s := by
      by_cases hj : f j t=f i t
      · have ha := hsame j hj
        have hb : b j=b i := by rw [heq j,heq i,ha] at hj; linarith
        filter_upwards [hab j,hab i] with s hsj hsi
        rw [hsj,hsi,ha,hb]
      · have hjlt : f j t < f i t := lt_of_le_of_ne (hmax j) hj
        exact ((hd j).continuousAt.eventually_lt (hd i).continuousAt hjlt).mono (fun s hs => hs.le)
    filter_upwards [Filter.eventually_all.mpr hle,hab i] with s hs hsi
    have H : finiteSup hK (fun j => f j s)=f i s :=
      le_antisymm (Finset.sup'_le _ _ (fun j _ => hs j))
        (Finset.le_sup' (fun j => f j s) (Finset.mem_univ i))
    exact H.trans hsi
  · push_neg at hsame
    obtain ⟨j,hj,ha⟩ := hsame
    have hij : i ≠ j := by intro H; subst j; exact ha rfl
    have hvis (k : Fin K) (hki : k ≠ i) (hkj : k ≠ j) : f k t < f i t := by
      apply lt_of_le_of_ne (hmax k)
      intro hk
      exact htriple i j k hij hki.symm hkj.symm ⟨hj.symm,hk.symm⟩
    right
    refine ⟨ht.1,ht.2,i,j,hij,hj.symm,hvis,?_⟩
    exact Paper35.signChanges_of_hasDerivAt_ne_zero ((hd i).sub (hd j))
      (sub_eq_zero.mpr hj.symm) (sub_ne_zero.mpr ha.symm)

/-- A compact-time no-triple event is Borel, by closed projection. This is
an elementary measurability proof for the actual entire-curve condition. -/
lemma measurableSet_noTriple_family {X T : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [TopologicalSpace T] [CompactSpace T]
    {K : ℕ} (f : Fin K → X × T → ℝ) (hf : ∀ j, Continuous (f j)) :
    MeasurableSet {x | ∀ i j k : Fin K, i ≠ j → i ≠ k → j ≠ k →
      ∀ t : T, ¬ (f i (x,t)=f j (x,t) ∧ f i (x,t)=f k (x,t))} := by
  rw [show {x | ∀ i j k : Fin K, i ≠ j → i ≠ k → j ≠ k →
      ∀ t : T, ¬ (f i (x,t)=f j (x,t) ∧ f i (x,t)=f k (x,t))} =
      ⋂ i : Fin K, ⋂ j : Fin K, ⋂ k : Fin K,
        {x | i ≠ j → i ≠ k → j ≠ k → ∀ t : T,
          ¬ (f i (x,t)=f j (x,t) ∧ f i (x,t)=f k (x,t))} by ext x; simp]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro k
  by_cases hij : i=j
  · simp [hij]
  by_cases hik : i=k
  · simp [hik]
  by_cases hjk : j=k
  · simp [hjk]
  have H : IsClosed (Prod.fst '' {p : X × T | f i p=f j p ∧ f i p=f k p}) :=
    isClosedMap_fst_of_compactSpace _ ((isClosed_eq (hf i) (hf j)).inter (isClosed_eq (hf i) (hf k)))
  convert H.measurableSet.compl using 1
  ext x
  simp [hij,hik,hjk]

end Paper35.DeepBreaks
namespace Paper35.DeepModel.Network
open Paper35.DeepBreaks Paper35.CurveCalculus
variable (m : DeepModel.Network)

set_option maxHeartbeats 500000 in
lemma layerMap_locallyAffine_of_no_switch (n : ℕ) (θ : m.Parameter n)
    (η : ℝ → Space (m.width n)) {L t : ℝ} (ht : t ∈ Ioo 0 L)
    (hη : LocallyAffineAt η t) (htriple : ∀ r, NoTriple (m.layerScores n θ η r) t)
    (hswitch : t ∉ m.layerSwitchTimes n θ η L) :
    LocallyAffineAt (fun s => m.layerMap n θ (η s)) t := by
  rcases hη with ⟨a,b,hab⟩
  have hlocal (r : Fin (m.width (n+1))) (j : Fin (m.rank n r)) :
      LocallyAffineAt (m.layerScores n θ η r j) t := by
    refine ⟨inner ℝ (θ r j).1 a,inner ℝ (θ r j).1 b+(θ r j).2,?_⟩
    filter_upwards [hab] with s hs
    dsimp [layerScores]
    rw [hs,inner_add_right,inner_smul_right]
    ring
  have hresult (r : Fin (m.width (n+1))) :
      LocallyAffineAt (fun s => finiteSup (m.rank_pos n r) (fun j => m.layerScores n θ η r j s)) t := by
    rcases finiteMax_locallyAffine_or_switch (m.rank_pos n r) _ ht (hlocal r) (htriple r) with h | h
    · exact h
    · exact False.elim (hswitch (mem_iUnion.mpr ⟨r,h⟩))
  choose A B hAB using hresult
  refine ⟨WithLp.toLp 2 A,WithLp.toLp 2 B,?_⟩
  filter_upwards [Filter.eventually_all.mpr hAB] with s hs
  ext r
  exact hs r

/-- Actual no-triple condition, recursively for all layers already sampled. -/
def NoTripleThrough (m : DeepModel.Network) : (N : ℕ) → m.Sample N →
    (ℝ → Space (m.width 0)) → ℝ → Prop
  | 0, _, _, _ => True
  | N+1, ω, γ, L => NoTripleThrough m N ω.1 γ L ∧
      ∀ t ∈ Icc 0 L, ∀ r, NoTriple (m.layerScores N ω.2 (m.curve N ω.1 γ) r) t

/-- Deterministic local-affine induction, retaining the original parameter and
actual union of switch times. -/
theorem locallyAffine_network_of_no_switch (N : ℕ) (ω : m.Sample N)
    (γ : ℝ → Space (m.width 0)) {L t : ℝ} (ht : t ∈ Ioo 0 L)
    (hgood : m.NoTripleThrough N ω γ L) (hγ : LocallyAffineAt γ t)
    (hswitch : t ∉ m.switchTimes N ω γ L) : LocallyAffineAt (m.curve N ω γ) t := by
  induction N with
  | zero => exact hγ
  | succ N ih =>
    apply m.layerMap_locallyAffine_of_no_switch N ω.2 (m.curve N ω.1 γ) ht
    · exact ih ω.1 hgood.1 (fun h => hswitch (Or.inl h))
    · exact hgood.2 t ⟨ht.1.le,ht.2.le⟩
    · exact fun h => hswitch (Or.inr h)

/-- The deterministic geometric content of (8.12). No-triple is explicit;
it is not silently asserted for arbitrary parameters. -/
theorem breakSet_network_subset (N : ℕ) (ω : m.Sample N) (γ : ℝ → Space (m.width 0)) (L : ℝ)
    (hgood : m.NoTripleThrough N ω γ L) :
    breakSet (m.curve N ω γ) L ⊆ breakSet γ L ∪ m.switchTimes N ω γ L := by
  intro t ht
  by_cases hγ : LocallyAffineAt γ t
  · right
    by_contra hs
    exact ht.2 (m.locallyAffine_network_of_no_switch N ω γ ht.1 hgood hγ hs)
  · exact Or.inl ⟨ht.1,hγ⟩

/-- Joint continuity in all sampled parameters and the spatial input. -/
lemma continuous_networkEval (N : ℕ) :
    Continuous (fun p : m.Sample N × Space (m.width 0) => m.networkMap N p.1 p.2) := by
  induction N with
  | zero => exact continuous_snd
  | succ N ih =>
    have hp : Continuous (fun p : (m.Sample N × m.Parameter N) × Space (m.width 0) =>
        (p.1.2,m.networkMap N p.1.1 p.2)) :=
      continuous_fst.snd.prodMk (ih.comp (continuous_fst.fst.prodMk continuous_snd))
    have H := (m.continuous_layerEval N).comp hp
    dsimp only [Function.comp_def] at H
    exact H

/-- The no-triple condition on the entire actual incoming curve is measurable
in both the past and the new layer, as required for conditioning. -/
lemma measurableSet_currentNoTriple (N : ℕ) (γ : ℝ → Space (m.width 0)) (L : ℝ)
    (hγ : ContinuousOn γ (Icc 0 L)) :
    MeasurableSet {p : m.Sample N × m.Parameter N | ∀ t ∈ Icc 0 L,
      ∀ r, NoTriple (m.layerScores N p.2 (m.curve N p.1 γ) r) t} := by
  have hcont : Continuous (fun p : (m.Sample N × m.Parameter N) × Icc 0 L =>
      m.networkMap N p.1.1 (γ p.2)) :=
    (m.continuous_networkEval N).comp
      (continuous_fst.fst.prodMk (hγ.restrict.comp continuous_snd))
  have H (r : Fin (m.width (N+1))) := measurableSet_noTriple_family
    (fun j (p : (m.Sample N × m.Parameter N) × Icc 0 L) =>
      inner ℝ (p.1.2 r j).1 (m.networkMap N p.1.1 (γ p.2))+(p.1.2 r j).2)
    (fun j => by
      have hw : Continuous (fun p : (m.Sample N × m.Parameter N) × Icc 0 L => (p.1.2 r j).1) := by fun_prop
      have hb : Continuous (fun p : (m.Sample N × m.Parameter N) × Icc 0 L => (p.1.2 r j).2) := by fun_prop
      exact (hw.inner hcont).add hb)
  have hall := MeasurableSet.iInter H
  convert hall using 1
  ext p
  simp only [mem_setOf_eq,mem_iInter,NoTriple,layerScores,curve]
  constructor
  · intro hp r i j k hij hik hjk t
    exact hp t t.2 r i j k hij hik hjk
  · intro hp t ht r i j k hij hik hjk
    exact hp r i j k hij hik hjk ⟨t,ht⟩

namespace LayerSource
open Paper35.ClassicalInputs Paper35.Source.CrossingRegularity
variable {m : DeepModel.Network} {n : ℕ} (a : m.LayerSource n)

/-- The no-triple condition along an arbitrary actual rectifiable incoming
curve follows from the original source laws, including zero-length curves. -/
theorem ae_noTripleOn (a : m.LayerSource n) (hLN : LusinNovikovLaw) (hUP : BorelProjectionLaw)
    (harc : ArclengthFactorizationInput)
    (η : ℝ → Space (m.width n)) (L : ℝ) (hL : 0 ≤ L)
    (hcont : ContinuousOn η (Icc 0 L)) (hfinite : eVariationOn η (Icc 0 L) ≠ ∞) :
    ∀ᵐ θ ∂m.layerLaw n, ∀ t ∈ Icc 0 L, ∀ r, NoTriple (m.layerScores n θ η r) t := by
  obtain ⟨x,u,σ,hx,hmu,hu,hderiv,hσcont,hσmono,himage,hfactor⟩ :=
    harc _ (m.width_pos n) η L hL hcont hfinite
  let T := (eVariationOn η (Icc 0 L)).toReal
  have hunit (r : Fin (m.width (n+1))) :
      ∀ᵐ ξ ∂(a.unit r).iid (m.rank n r), ∀ t ∈ Icc 0 L,
        NoTriple (fun j t => inner ℝ (ξ j).1 (η t)+(ξ j).2) t := by
    by_cases hT : 0 < T
    · have hvar : eVariationOn x (Icc 0 T) = ENNReal.ofReal T := by
        calc
          _ = eVariationOn (x ∘ σ) (Icc 0 L) := by
            rw [eVariationOn.comp_eq_of_monotoneOn _ _ hσmono,himage]
          _ = eVariationOn η (Icc 0 L) := (eVariationOn.eq_of_eqOn hfactor).symm
          _ = _ := (ENNReal.ofReal_toReal hfinite).symm
      let p : Paper35.Source.Probe (m.width n) := ⟨x,T,hT,hx.lipschitzOnWith,hvar⟩
      have H := ae_no_triple_ties_closed p (fun _ : Fin (m.rank n r) => a.unit r) (hLN _ _) (hUP _ _)
      filter_upwards [H] with ξ hξ
      intro t ht i j k hij hik hjk heq
      have hσt : σ t ∈ Icc 0 T := by rw [← himage]; exact mem_image_of_mem σ ht
      apply hξ i j k hij hik hjk (σ t) hσt
      have he : η t=x (σ t) := hfactor ht
      simpa only [Paper35.Source.WeightedModel.scores,p,← he] using heq
    · have hT0 : T=0 := le_antisymm (le_of_not_gt hT) ENNReal.toReal_nonneg
      have H := ae_no_fixed_ties (fun _ : Fin (m.rank n r) => a.unit r) (x 0)
      filter_upwards [H] with ξ hξ
      intro t ht i j k hij hik hjk heq
      have hσt : σ t=0 := by
        have H : σ t ∈ Icc 0 T := by rw [← himage]; exact mem_image_of_mem σ ht
        rw [hT0] at H
        exact le_antisymm H.2 H.1
      have hηt : η t=x 0 := by rw [hfactor ht]; simp only [Function.comp_apply,hσt]
      apply hξ i j hij
      simpa only [Paper35.VisibleCrossing.scoreValue,hηt] using heq.1
  have hmarg (r : Fin (m.width (n+1))) :
      ∀ᵐ θ ∂m.layerLaw n, ∀ t ∈ Icc 0 L, NoTriple (m.layerScores n θ η r) t := by
    have H : ∀ᵐ ξ ∂(m.layerLaw n).map (fun θ => θ r), ∀ t ∈ Icc 0 L,
        NoTriple (fun j t => inner ℝ (ξ j).1 (η t)+(ξ j).2) t := by
      rw [a.marginal r]
      exact hunit r
    exact ae_of_ae_map (measurable_pi_apply r).aemeasurable H
  filter_upwards [ae_all_iff.mpr hmarg] with θ hθ
  exact fun t ht r => hθ r t ht

end LayerSource

set_option maxHeartbeats 600000 in
/-- Actual almost-sure no-triple regularity through all independent layers.
The conditional curve is the real past-network output; the layer assumptions
are only its original source conditional-density/iid marginals. -/
theorem ae_noTripleThrough (hLN : Paper35.ClassicalInputs.LusinNovikovLaw)
    (hUP : Paper35.ClassicalInputs.BorelProjectionLaw)
    (harc : ArclengthFactorizationInput) (models : ∀ n, m.LayerSource n)
    (γ : ℝ → Space (m.width 0)) (L : ℝ) (hL : 0 ≤ L)
    (hcont : ContinuousOn γ (Icc 0 L)) (hfinite : eVariationOn γ (Icc 0 L) ≠ ∞) :
    ∀ N, ∀ᵐ ω ∂m.law N, m.NoTripleThrough N ω γ L := by
  intro N
  induction N with
  | zero => exact Filter.Eventually.of_forall (fun _ => True.intro)
  | succ N ih =>
    letI := m.layer_probability N
    have hcurrent : ∀ᵐ p ∂(m.law N).prod (m.layerLaw N), ∀ t ∈ Icc 0 L,
        ∀ r, NoTriple (m.layerScores N p.2 (m.curve N p.1 γ) r) t := by
      apply (Measure.ae_prod_iff_ae_ae (m.measurableSet_currentNoTriple N γ L hcont)).mpr
      apply Filter.Eventually.of_forall
      intro ω
      obtain ⟨C,hC⟩ := m.networkMap_lipschitz N ω
      have H := (models N).ae_noTripleOn hLN hUP harc (m.curve N ω γ) L hL
        (hC.continuous.comp_continuousOn hcont) (hC.comp_boundedVariationOn hfinite)
      exact H
    change ∀ᵐ p : m.Sample N × m.Parameter N ∂(m.law N).prod (m.layerLaw N),
      m.NoTripleThrough N p.1 γ L ∧
        ∀ t ∈ Icc 0 L, ∀ r, NoTriple (m.layerScores N p.2 (m.curve N p.1 γ) r) t
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae ih,hcurrent] with p hp hc
    exact ⟨hp,hc⟩

/-- Full source (8.12), almost surely under the original actual random network
law. It holds in particular for every rectifiable CPWL input. -/
theorem ae_breakSet_network_subset (hLN : Paper35.ClassicalInputs.LusinNovikovLaw)
    (hUP : Paper35.ClassicalInputs.BorelProjectionLaw)
    (harc : ArclengthFactorizationInput) (models : ∀ n, m.LayerSource n)
    (γ : ℝ → Space (m.width 0)) (L : ℝ) (hL : 0 ≤ L)
    (hcont : ContinuousOn γ (Icc 0 L)) (hfinite : eVariationOn γ (Icc 0 L) ≠ ∞)
    (N : ℕ) :
    ∀ᵐ ω ∂m.law N, breakSet (m.curve N ω γ) L ⊆ breakSet γ L ∪ m.switchTimes N ω γ L := by
  filter_upwards [m.ae_noTripleThrough hLN hUP harc models γ L hL hcont hfinite N] with ω hω
  exact m.breakSet_network_subset N ω γ L hω

end Paper35.DeepModel.Network
