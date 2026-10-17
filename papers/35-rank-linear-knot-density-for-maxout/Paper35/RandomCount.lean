import Paper35.VisibleCrossing
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.Interval
import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Actual switch-count measurability for continuous and random probes

We code a finite continuous path in the Polish space `C([0,1], ℝᵈ)`. The
coding map is measurable from the source's jointly measurable arclength
representation, even when the original sample space is not standard Borel.

The original strict two-sided `SignChanges` relation is Borel: each compact
subinterval's failure of a strict sign is a closed projection, and rational
interval widths give a countable union. Actual switch sections are countable
by `Crossing.switchSet_countable`. Thus the sole explicit external theorem
input is the generic Lusin–Novikov statement recorded in `VisibleCrossing`
(Kechris, Classical Descriptive Set Theory, Theorem 18.10). No density,
transversality, zero-variance exclusion, or count-measurability hypothesis is
used in these measurability results.
-/

noncomputable section
open MeasureTheory Set Topology TopologicalSpace
open scoped ENNReal

namespace Paper35.RandomCount
open Source VisibleCrossing

abbrev UnitTime := Icc (0 : ℝ) 1
abbrev PathCode (d : ℕ) := C(UnitTime, Space d)

instance unitTimeNonempty : Nonempty UnitTime := ⟨⟨0, by norm_num⟩⟩
instance pathCodeMeasurableSpace {d : ℕ} : MeasurableSpace (PathCode d) := borel _
instance pathCodeBorelSpace {d : ℕ} : BorelSpace (PathCode d) := ⟨rfl⟩
instance pathCodeStandardBorel {d : ℕ} : StandardBorelSpace (PathCode d) := inferInstance

/-- Continuous paths are measurably coded by their values on one fixed
countable dense sequence. The original sample space need not be standard Borel. -/
theorem measurable_pathCode_of_eval {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (f : Ω → PathCode d) (hf : ∀ t : UnitTime, Measurable (fun ω => f ω t)) :
    Measurable f := by
  let e : PathCode d → (ℕ → Space d) := fun g n => g (denseSeq UnitTime n)
  have he : Measurable e := measurable_pi_lambda _ fun n =>
    (continuous_eval_const (denseSeq UnitTime n)).measurable
  have hi : Function.Injective e := by
    intro g h hgh
    apply DFunLike.coe_injective
    exact (denseRange_denseSeq UnitTime).equalizer g.continuous h.continuous hgh
  exact (he.measurableEmbedding hi).measurable_comp_iff.mp
    (measurable_pi_lambda _ fun n => hf (denseSeq UnitTime n))

/-- Universal strict inequalities on a moving open interval are Borel for
a continuous family on a compact parameter space. This is an elementary
compact-projection argument; no count-measurability theorem is assumed. -/
theorem measurableSet_forall_interval_lt {X T : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace T] [CompactSpace T]
    (F : X × T → ℝ) (hF : Continuous F)
    (v : T → ℝ) (hv : Continuous v)
    (a b : X → ℝ) (ha : Continuous a) (hb : Continuous b) :
    MeasurableSet {x | ∀ t, a x < v t → v t < b x → F (x,t) < 0} := by
  let D (r : ℚ) : Set (X × T) :=
    {z | a z.1 + (r : ℝ) ≤ v z.2 ∧ v z.2 ≤ b z.1 - (r : ℝ) ∧ 0 ≤ F z}
  have hD (r : ℚ) : IsClosed (D r) :=
    (isClosed_le ((ha.comp continuous_fst).add continuous_const) (hv.comp continuous_snd)).inter
      ((isClosed_le (hv.comp continuous_snd) ((hb.comp continuous_fst).sub continuous_const)).inter
        (isClosed_le continuous_const hF))
  have hmeas : MeasurableSet (⋃ r : ℚ, ⋃ (_hr : 0 < r), Prod.fst '' D r) :=
    MeasurableSet.iUnion fun r => MeasurableSet.iUnion fun _ =>
      (isClosedMap_fst_of_compactSpace _ (hD r)).measurableSet
  have hbad (x : X) :
      x ∈ (⋃ r : ℚ, ⋃ (_hr : 0 < r), Prod.fst '' D r) ↔
        ∃ t, a x < v t ∧ v t < b x ∧ 0 ≤ F (x,t) := by
    constructor
    · simp only [mem_iUnion, mem_image]
      rintro ⟨r, hr, ⟨z, hz, rfl⟩⟩
      have hr' : (0 : ℝ) < r := by exact_mod_cast hr
      dsimp [D] at hz
      exact ⟨z.2, by linarith [hz.1], by linarith [hz.2.1], hz.2.2⟩
    · rintro ⟨t, hat, htb, hft⟩
      obtain ⟨r, hr, hrmin⟩ := exists_pos_rat_lt (lt_min (sub_pos.mpr hat) (sub_pos.mpr htb))
      simp only [mem_iUnion, mem_image]
      refine ⟨r, hr, (x,t), ?_, rfl⟩
      dsimp [D]
      exact ⟨by linarith [(lt_min_iff.mp hrmin).1],
        by linarith [(lt_min_iff.mp hrmin).2], hft⟩
  convert hmeas.compl using 1
  ext x
  rw [mem_compl_iff, hbad]
  simp only [mem_setOf_eq, not_exists, not_and, not_le]

lemma signChanges_iff_rat_on_unit {f : ℝ → ℝ} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    SignChanges f s ↔ ∃ r : ℚ, 0 < r ∧ (r : ℝ) < s ∧ (r : ℝ) < 1-s ∧
      (((∀ t : UnitTime, s-r < (t : ℝ) → (t : ℝ) < s → f t < 0) ∧
        (∀ t : UnitTime, s < (t : ℝ) → (t : ℝ) < s+r → 0 < f t)) ∨
       ((∀ t : UnitTime, s-r < (t : ℝ) → (t : ℝ) < s → 0 < f t) ∧
        (∀ t : UnitTime, s < (t : ℝ) → (t : ℝ) < s+r → f t < 0))) := by
  constructor
  · rintro ⟨δ, hδ, hsign⟩
    obtain ⟨r, hr, hsmall⟩ := exists_pos_rat_lt (lt_min hδ (lt_min hs0 (sub_pos.mpr hs1)))
    have hrδ := (lt_min_iff.mp hsmall).1
    obtain ⟨hrs, hr1⟩ := lt_min_iff.mp (lt_min_iff.mp hsmall).2
    refine ⟨r, hr, hrs, hr1, ?_⟩
    rcases hsign with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · exact Or.inl ⟨fun t htl htr => hl t ⟨by linarith, htr⟩,
        fun t htl htr => hr t ⟨htl, by linarith⟩⟩
    · exact Or.inr ⟨fun t htl htr => hl t ⟨by linarith, htr⟩,
        fun t htl htr => hr t ⟨htl, by linarith⟩⟩
  · rintro ⟨r, hr, hrs, hr1, hsign⟩
    have hr' : (0 : ℝ) < r := by exact_mod_cast hr
    refine ⟨r, hr', ?_⟩
    have hleft {t : ℝ} (ht : t ∈ Ioo (s-r) s) : t ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith [ht.1, ht.2]
    have hright {t : ℝ} (ht : t ∈ Ioo s (s+r)) : t ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith [ht.1, ht.2]
    rcases hsign with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · exact Or.inl ⟨fun t ht => hl ⟨t,hleft ht⟩ ht.1 ht.2,
        fun t ht => hr ⟨t,hright ht⟩ ht.1 ht.2⟩
    · exact Or.inr ⟨fun t ht => hl ⟨t,hleft ht⟩ ht.1 ht.2,
        fun t ht => hr ⟨t,hright ht⟩ ht.1 ht.2⟩

/-- Borel measurability of the original strict two-sided sign-change relation,
for an arbitrary continuous parameterized family. -/
theorem measurableSet_signChanges_unit {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (F : X × ℝ → ℝ) (hF : Continuous F) :
    MeasurableSet {z : X × ℝ | 0 < z.2 ∧ z.2 < 1 ∧
      SignChanges (fun t => F (z.1,t)) z.2} := by
  let G : (X × ℝ) × UnitTime → ℝ := fun z => F (z.1.1,z.2)
  have hG : Continuous G := hF.comp (continuous_fst.fst.prodMk
    (continuous_subtype_val.comp continuous_snd))
  have hnegG : Continuous (fun z => -G z) := hG.neg
  have hleft (r : ℚ) : MeasurableSet {z : X × ℝ |
      ∀ t : UnitTime, z.2-r < (t : ℝ) → (t : ℝ) < z.2 → F (z.1,t) < 0} :=
    measurableSet_forall_interval_lt G hG _ continuous_subtype_val
      _ _ (continuous_snd.sub continuous_const) continuous_snd
  have hright (r : ℚ) : MeasurableSet {z : X × ℝ |
      ∀ t : UnitTime, z.2 < (t : ℝ) → (t : ℝ) < z.2+r → F (z.1,t) < 0} :=
    measurableSet_forall_interval_lt G hG _ continuous_subtype_val
      _ _ continuous_snd (continuous_snd.add continuous_const)
  have hleftpos (r : ℚ) : MeasurableSet {z : X × ℝ |
      ∀ t : UnitTime, z.2-r < (t : ℝ) → (t : ℝ) < z.2 → 0 < F (z.1,t)} := by
    simpa only [neg_lt_zero] using measurableSet_forall_interval_lt (fun z => -G z) hnegG
      _ continuous_subtype_val _ _ (continuous_snd.sub continuous_const) continuous_snd
  have hrightpos (r : ℚ) : MeasurableSet {z : X × ℝ |
      ∀ t : UnitTime, z.2 < (t : ℝ) → (t : ℝ) < z.2+r → 0 < F (z.1,t)} := by
    simpa only [neg_lt_zero] using measurableSet_forall_interval_lt (fun z => -G z) hnegG
      _ continuous_subtype_val _ _ continuous_snd (continuous_snd.add continuous_const)
  let R (r : ℚ) : Set (X × ℝ) := {z | 0 < r ∧ (r : ℝ) < z.2 ∧ (r : ℝ) < 1-z.2 ∧
      (((∀ t : UnitTime, z.2-r < (t : ℝ) → (t : ℝ) < z.2 → F (z.1,t) < 0) ∧
        (∀ t : UnitTime, z.2 < (t : ℝ) → (t : ℝ) < z.2+r → 0 < F (z.1,t))) ∨
       ((∀ t : UnitTime, z.2-r < (t : ℝ) → (t : ℝ) < z.2 → 0 < F (z.1,t)) ∧
        (∀ t : UnitTime, z.2 < (t : ℝ) → (t : ℝ) < z.2+r → F (z.1,t) < 0)))}
  have hR (r : ℚ) : MeasurableSet (R r) :=
    (MeasurableSet.const _).inter ((measurableSet_lt measurable_const measurable_snd).inter
      ((measurableSet_lt measurable_const (measurable_const.sub measurable_snd)).inter
        (((hleft r).inter (hrightpos r)).union ((hleftpos r).inter (hright r)))))
  convert (measurableSet_lt measurable_const measurable_snd).inter
    ((measurableSet_lt measurable_snd measurable_const).inter (MeasurableSet.iUnion hR)) using 1
  ext z
  simp only [mem_setOf_eq, mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨hs0,hs1,hsgn⟩
    exact ⟨hs0,hs1,(signChanges_iff_rat_on_unit hs0 hs1).mp hsgn⟩
  · rintro ⟨hs0,hs1,hsgn⟩
    exact ⟨hs0,hs1,(signChanges_iff_rat_on_unit hs0 hs1).mpr hsgn⟩

abbrev CodeParameter (d K : ℕ) := PathCode d × (Fin K → Candidate d)

def codeScores {d K : ℕ} (z : CodeParameter d K) (k : Fin K) (s : ℝ) : ℝ :=
  inner ℝ (z.2 k).1 (z.1 (projIcc (0 : ℝ) 1 zero_le_one s)) + (z.2 k).2

lemma continuous_codeScore {d K : ℕ} (k : Fin K) :
    Continuous (fun z : CodeParameter d K × ℝ => codeScores z.1 k z.2) := by
  unfold codeScores
  have hclip : Continuous (fun z : CodeParameter d K × ℝ =>
      projIcc (0 : ℝ) 1 zero_le_one z.2) :=
    (show Continuous (projIcc (0 : ℝ) 1 zero_le_one) from continuous_projIcc).comp continuous_snd
  have heval : Continuous (fun z : CodeParameter d K × ℝ =>
      z.1.1 (projIcc (0 : ℝ) 1 zero_le_one z.2)) :=
    continuous_eval.comp (continuous_fst.fst.prodMk hclip)
  exact (((continuous_apply k).comp continuous_fst.snd).fst.inner heval).add
    (((continuous_apply k).comp continuous_fst.snd).snd)

lemma measurableSet_codePairGraph {d K : ℕ} (q : OrderedCandidatePair K) :
    MeasurableSet {z : CodeParameter d K × ℝ | z.2 ∈ pairSwitchSet (codeScores z.1) 1 q} := by
  classical
  have hvis : MeasurableSet {z : CodeParameter d K × ℝ | VisiblePair (codeScores z.1) z.2 q} := by
    have heq := measurableSet_eq_fun (continuous_codeScore (d := d) q.1.1).measurable
      (continuous_codeScore (d := d) q.1.2).measurable
    have hrest (k : Fin K) : MeasurableSet {z : CodeParameter d K × ℝ |
        k ≠ q.1.1 → k ≠ q.1.2 → codeScores z.1 k z.2 < codeScores z.1 q.1.1 z.2} := by
      by_cases hi : k = q.1.1
      · simp [hi]
      by_cases hj : k = q.1.2
      · simp [hj]
      simpa [hi,hj] using measurableSet_lt (continuous_codeScore (d := d) k).measurable
        (continuous_codeScore (d := d) q.1.1).measurable
    convert heq.inter (MeasurableSet.iInter hrest) using 1
    ext z
    simp [VisiblePair]
  have hsign := measurableSet_signChanges_unit
    (fun z : CodeParameter d K × ℝ => codeScores z.1 q.1.1 z.2-codeScores z.1 q.1.2 z.2)
    ((continuous_codeScore (d := d) q.1.1).sub (continuous_codeScore (d := d) q.1.2))
  convert hsign.inter hvis using 1
  ext z
  simp only [pairSwitchSet, mem_setOf_eq, mem_inter_iff]
  tauto

/-- The canonical count uses the original strict sign-change definition,
including every parameter visit. Its graph is Borel and has countable sections. -/
theorem measurable_codeSwitchCount {d K : ℕ}
    (hLN : LusinNovikovInput (CodeParameter d K) ℝ) :
    Measurable (fun z : CodeParameter d K => switchCount (codeScores z) 1) := by
  let R : Set (CodeParameter d K × ℝ) := {z | z.2 ∈ switchSet (codeScores z.1) 1}
  have hR : MeasurableSet R := by
    have heq : R = ⋃ q : OrderedCandidatePair K,
        {z : CodeParameter d K × ℝ | z.2 ∈ pairSwitchSet (codeScores z.1) 1 q} := by
      ext z
      simp only [R, mem_setOf_eq, mem_iUnion, switchSet_eq_iUnion_pairSwitchSet]
    rw [heq]
    exact MeasurableSet.iUnion measurableSet_codePairGraph
  exact measurable_sectionCount_of_LusinNovikov hLN hR
    (fun z => switchSet_countable (codeScores z) 1)

lemma signChanges_comp_pos_mul_of {f : ℝ → ℝ} {c s : ℝ} (hc : 0 < c)
    (h : SignChanges f (c*s)) : SignChanges (fun t => f (c*t)) s := by
  rcases h with ⟨δ,hδ,h⟩
  refine ⟨δ/c, div_pos hδ hc, ?_⟩
  have hmapleft {t : ℝ} (ht : t ∈ Ioo (s-δ/c) s) : c*t ∈ Ioo (c*s-δ) (c*s) := by
    constructor
    · have := (lt_div_iff₀ hc).mp (show s-t < δ/c by linarith [ht.1])
      nlinarith
    · exact mul_lt_mul_of_pos_left ht.2 hc
  have hmapright {t : ℝ} (ht : t ∈ Ioo s (s+δ/c)) : c*t ∈ Ioo (c*s) (c*s+δ) := by
    constructor
    · exact mul_lt_mul_of_pos_left ht.1 hc
    · have := (lt_div_iff₀ hc).mp (show t-s < δ/c by linarith [ht.2])
      nlinarith
  rcases h with ⟨hl,hr⟩ | ⟨hl,hr⟩
  · exact Or.inl ⟨fun t ht => hl _ (hmapleft ht), fun t ht => hr _ (hmapright ht)⟩
  · exact Or.inr ⟨fun t ht => hl _ (hmapleft ht), fun t ht => hr _ (hmapright ht)⟩

lemma signChanges_comp_pos_mul {f : ℝ → ℝ} {c s : ℝ} (hc : 0 < c) :
    SignChanges (fun t => f (c*t)) s ↔ SignChanges f (c*s) := by
  constructor
  · intro h
    have h' : SignChanges (fun t => f (c*t)) (c⁻¹*(c*s)) := by
      simpa only [inv_mul_cancel_left₀ hc.ne'] using h
    have H := signChanges_comp_pos_mul_of (inv_pos.mpr hc) h'
    simpa only [mul_inv_cancel_left₀ hc.ne'] using H
  · exact signChanges_comp_pos_mul_of hc

lemma activeSwitch_comp_pos_mul {K : ℕ} (f : Fin K → ℝ → ℝ) {c : ℝ} (hc : 0 < c) (s : ℝ) :
    ActiveSwitch (fun k t => f k (c*t)) 1 s ↔ ActiveSwitch f c (c*s) := by
  simp only [ActiveSwitch]
  constructor
  · rintro ⟨hs0,hs1,i,j,hij,heq,hvis,hsgn⟩
    exact ⟨mul_pos hc hs0, by nlinarith, i,j,hij,heq,hvis,
      (signChanges_comp_pos_mul hc).mp hsgn⟩
  · rintro ⟨hs0,hs1,i,j,hij,heq,hvis,hsgn⟩
    exact ⟨by nlinarith, by nlinarith, i,j,hij,heq,hvis,
      (signChanges_comp_pos_mul hc).mpr hsgn⟩

/-- Positive rescaling preserves the original parameter multiplicity. -/
theorem switchCount_comp_pos_mul {K : ℕ} (f : Fin K → ℝ → ℝ) {c : ℝ} (hc : 0 < c) :
    switchCount (fun k t => f k (c*t)) 1 = switchCount f c := by
  have heq : switchSet f c = (fun s => c*s) '' switchSet (fun k t => f k (c*t)) 1 := by
    ext s
    constructor
    · intro hs
      refine ⟨s/c, ?_, mul_div_cancel₀ _ hc.ne'⟩
      apply (activeSwitch_comp_pos_mul f hc (s/c)).mpr
      simpa only [mul_div_cancel₀ _ hc.ne'] using hs
    · rintro ⟨t,ht,rfl⟩
      exact (activeSwitch_comp_pos_mul f hc t).mp ht
  unfold switchCount
  rw [heq, (mul_right_injective₀ hc.ne').encard_image]

lemma signChanges_of_congrOn_interval {f g : ℝ → ℝ} {L s : ℝ}
    (hs0 : 0 < s) (hsL : s < L) (hfg : EqOn f g (Icc 0 L))
    (h : SignChanges f s) : SignChanges g s := by
  rcases h with ⟨δ,hδ,h⟩
  let ε := min δ (min s (L-s))
  have hε : 0 < ε := lt_min hδ (lt_min hs0 (sub_pos.mpr hsL))
  have hεδ : ε ≤ δ := min_le_left _ _
  have hεs : ε ≤ s := (min_le_right _ _).trans (min_le_left _ _)
  have hεL : ε ≤ L-s := (min_le_right _ _).trans (min_le_right _ _)
  have hleft {t : ℝ} (ht : t ∈ Ioo (s-ε) s) : t ∈ Icc 0 L ∧ t ∈ Ioo (s-δ) s := by
    exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, ⟨by linarith [ht.1], ht.2⟩⟩
  have hright {t : ℝ} (ht : t ∈ Ioo s (s+ε)) : t ∈ Icc 0 L ∧ t ∈ Ioo s (s+δ) := by
    exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, ⟨ht.1, by linarith [ht.2]⟩⟩
  refine ⟨ε,hε,?_⟩
  rcases h with ⟨hl,hr⟩ | ⟨hl,hr⟩
  · exact Or.inl ⟨fun t ht => by rw [← hfg (hleft ht).1]; exact hl t (hleft ht).2,
      fun t ht => by rw [← hfg (hright ht).1]; exact hr t (hright ht).2⟩
  · exact Or.inr ⟨fun t ht => by rw [← hfg (hleft ht).1]; exact hl t (hleft ht).2,
      fun t ht => by rw [← hfg (hright ht).1]; exact hr t (hright ht).2⟩

theorem switchCount_congrOn_interval {K : ℕ} {f g : Fin K → ℝ → ℝ} (L : ℝ)
    (hfg : ∀ k, EqOn (f k) (g k) (Icc 0 L)) : switchCount f L = switchCount g L := by
  suffices switchSet f L = switchSet g L by rw [switchCount, switchCount, this]
  ext s
  constructor <;> rintro ⟨hs0,hsL,i,j,hij,heq,hvis,hsgn⟩
  · have hs : s ∈ Icc 0 L := ⟨hs0.le,hsL.le⟩
    refine ⟨hs0,hsL,i,j,hij,?_,?_,?_⟩
    · simpa only [← hfg i hs, ← hfg j hs] using heq
    · intro k hki hkj
      simpa only [← hfg k hs, ← hfg i hs] using hvis k hki hkj
    · exact signChanges_of_congrOn_interval hs0 hsL
        (fun t ht => by rw [hfg i ht,hfg j ht]) hsgn
  · have hs : s ∈ Icc 0 L := ⟨hs0.le,hsL.le⟩
    refine ⟨hs0,hsL,i,j,hij,?_,?_,?_⟩
    · simpa only [hfg i hs, hfg j hs] using heq
    · intro k hki hkj
      simpa only [hfg k hs, hfg i hs] using hvis k hki hkj
    · exact signChanges_of_congrOn_interval hs0 hsL
        (fun t ht => by rw [hfg i ht,hfg j ht]) hsgn

def normalizedCurve {d : ℕ} (γ : ℝ → Space d) (L : ℝ) (hL : 0 ≤ L)
    (hγ : ContinuousOn γ (Icc 0 L)) : PathCode d :=
  ⟨fun t => γ (L*t), hγ.comp_continuous (continuous_const.mul continuous_subtype_val)
    (fun t => ⟨mul_nonneg hL t.2.1, by nlinarith [t.2.2]⟩)⟩

lemma codeSwitchCount_normalized {d K : ℕ} (γ : ℝ → Space d) (L : ℝ) (hL : 0 < L)
    (hγ : ContinuousOn γ (Icc 0 L)) (θ : Fin K → Candidate d) :
    switchCount (codeScores (normalizedCurve γ L hL.le hγ,θ)) 1 =
      switchCount (fun k s => inner ℝ (θ k).1 (γ s)+(θ k).2) L := by
  rw [← switchCount_comp_pos_mul (fun k s => inner ℝ (θ k).1 (γ s)+(θ k).2) hL]
  apply switchCount_congrOn_interval
  intro k s hs
  simp only [codeScores, projIcc_of_mem zero_le_one hs, normalizedCurve, ContinuousMap.coe_mk]

/-- A fixed continuous probe has a Borel actual switch count as a function
of all affine coefficients. No density, nondegeneracy, or covariance inverse
is assumed, so this also applies to singular Gaussian affine pushforwards. -/
theorem measurable_affineSwitchCount {d K : ℕ} (γ : ℝ → Space d) (L : ℝ) (hL : 0 < L)
    (hγ : ContinuousOn γ (Icc 0 L))
    (hLN : LusinNovikovInput (CodeParameter d K) ℝ) :
    Measurable (fun θ : Fin K → Candidate d =>
      switchCount (fun k s => inner ℝ (θ k).1 (γ s)+(θ k).2) L) := by
  have H := (measurable_codeSwitchCount hLN).comp
    ((measurable_const : Measurable (fun _ : Fin K → Candidate d => normalizedCurve γ L hL.le hγ)).prodMk
      (measurable_id : Measurable (id : (Fin K → Candidate d) → Fin K → Candidate d)))
  convert H using 1
  funext θ
  exact (codeSwitchCount_normalized γ L hL hγ θ).symm

/-- The actual varying compact parameter domain of a random probe. -/
abbrev RandomProbeDomain {Ω : Type*} (p : Ω → Probe d) :=
  {z : Ω × ℝ // z.2 ∈ Icc 0 (p z.1).length}

/-- Joint measurability of the arclength parametrization on its actual domain
implies measurable canonical continuous-path coding. -/
theorem measurable_normalizedRandomProbe {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (p : Ω → Probe d) (hL : Measurable (fun ω => (p ω).length))
    (hγ : Measurable (fun z : RandomProbeDomain p => (p z.1.1).curve z.1.2)) :
    Measurable (fun ω => normalizedCurve (p ω).curve (p ω).length
      (p ω).length_pos.le (p ω).lipschitz.continuousOn) := by
  apply measurable_pathCode_of_eval
  intro t
  have hmem (ω : Ω) : (p ω).length * (t : ℝ) ∈ Icc 0 (p ω).length :=
    ⟨mul_nonneg (p ω).length_pos.le t.2.1, by nlinarith [t.2.2, (p ω).length_pos]⟩
  have hmap : Measurable (fun ω : Ω =>
      (⟨(ω,(p ω).length*(t : ℝ)),hmem ω⟩ : RandomProbeDomain p)) :=
    (measurable_id.prodMk (hL.mul_const (t : ℝ))).subtype_mk
  exact hγ.comp hmap

/-- The original random-probe switch count is jointly measurable under the
source assumptions. The sample space is arbitrary; only the canonical path
code space, where Lusin–Novikov is applied, is standard Borel. -/
theorem measurable_randomProbeSwitchCount {Ω : Type*} [MeasurableSpace Ω] {d K : ℕ}
    (p : Ω → Probe d) (hL : Measurable (fun ω => (p ω).length))
    (hγ : Measurable (fun z : RandomProbeDomain p => (p z.1.1).curve z.1.2))
    (hLN : LusinNovikovInput (CodeParameter d K) ℝ) :
    Measurable (fun z : Ω × (Fin K → Candidate d) =>
      switchCount (WeightedModel.scores (p z.1) z.2) (p z.1).length) := by
  have hcode := measurable_normalizedRandomProbe p hL hγ
  have H := (measurable_codeSwitchCount hLN).comp ((hcode.comp measurable_fst).prodMk measurable_snd)
  convert H using 1
  funext z
  exact (codeSwitchCount_normalized (p z.1).curve (p z.1).length (p z.1).length_pos
    (p z.1).lipschitz.continuousOn z.2).symm

/-- The common globally measurable representation is a special case; no
measurability outside a path's actual compact domain is needed above. -/
theorem measurable_randomProbeSwitchCount_of_global {Ω : Type*} [MeasurableSpace Ω] {d K : ℕ}
    (p : Ω → Probe d) (hL : Measurable (fun ω => (p ω).length))
    (hγ : Measurable (fun z : Ω × ℝ => (p z.1).curve z.2))
    (hLN : LusinNovikovInput (CodeParameter d K) ℝ) :
    Measurable (fun z : Ω × (Fin K → Candidate d) =>
      switchCount (WeightedModel.scores (p z.1) z.2) (p z.1).length) :=
  measurable_randomProbeSwitchCount p hL (hγ.comp measurable_subtype_coe) hLN

end Paper35.RandomCount
