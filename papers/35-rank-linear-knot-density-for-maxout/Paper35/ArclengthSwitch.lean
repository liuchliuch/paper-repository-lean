import Paper35.Basic
import Mathlib.Data.Set.Card

/-! Strict source switches survive monotone arclength collapse. Flat pauses
cannot contain a strict two-sided switch, and distinct switch times therefore
have distinct arclength parameters. This is proved, not a calculus input. -/
noncomputable section
open Set
open scoped ENNReal
namespace Paper35.ArclengthSwitch

lemma signChanges_not_flat {g σ : ℝ → ℝ} {L t s : ℝ}
    (hm : MonotoneOn σ (Icc 0 L)) (ht : t ∈ Ioo 0 L) (hs : s ∈ Icc 0 L)
    (hzero : g (σ t)=0) (hchange : SignChanges (g ∘ σ) t)
    (heq : σ t=σ s) : t=s := by
  rcases hchange with ⟨δ,hδ,hchange⟩
  by_contra hts
  rcases lt_or_gt_of_ne hts with hlt | hgt
  · let v := t + min δ (s-t)/2
    have hmin : 0 < min δ (s-t) := lt_min hδ (sub_pos.mpr hlt)
    have hv : v ∈ Ioo t (t+δ) := by
      dsimp [v]
      constructor <;> linarith [min_le_left δ (s-t)]
    have hvs : v ≤ s := by dsimp [v]; linarith [min_le_right δ (s-t)]
    have hvi : v ∈ Icc 0 L := ⟨ht.1.le.trans hv.1.le,hvs.trans hs.2⟩
    have hconst : σ v=σ t := le_antisymm
      ((hm hvi hs hvs).trans_eq heq.symm) (hm ⟨ht.1.le,ht.2.le⟩ hvi hv.1.le)
    rcases hchange with ⟨_,hr⟩ | ⟨_,hr⟩
    · have H := hr v hv; simpa [Function.comp_apply,hconst,hzero] using H
    · have H := hr v hv; simpa [Function.comp_apply,hconst,hzero] using H
  · let v := t - min δ (t-s)/2
    have hmin : 0 < min δ (t-s) := lt_min hδ (sub_pos.mpr hgt)
    have hv : v ∈ Ioo (t-δ) t := by
      dsimp [v]
      constructor <;> linarith [min_le_left δ (t-s)]
    have hsv : s ≤ v := by dsimp [v]; linarith [min_le_right δ (t-s)]
    have hvi : v ∈ Icc 0 L := ⟨hs.1.trans hsv,hv.2.le.trans ht.2.le⟩
    have hconst : σ v=σ t := le_antisymm
      (hm hvi ⟨ht.1.le,ht.2.le⟩ hv.2.le) (heq.trans_le (hm hs hvi hsv))
    rcases hchange with ⟨hl,_⟩ | ⟨hl,_⟩
    · have H := hl v hv; simpa [Function.comp_apply,hconst,hzero] using H
    · have H := hl v hv; simpa [Function.comp_apply,hconst,hzero] using H

/-- A strict sign change factors through every monotone surjection onto the
arclength interval. No strict monotonicity or injectivity of σ is assumed. -/
lemma signChanges_of_monotone_surj {g σ : ℝ → ℝ} {L T t : ℝ}
    (hm : MonotoneOn σ (Icc 0 L)) (himage : σ '' Icc 0 L = Icc 0 T)
    (ht : t ∈ Ioo 0 L) (hzero : g (σ t)=0) (hchange : SignChanges (g ∘ σ) t) :
    σ t ∈ Ioo 0 T ∧ SignChanges g (σ t) := by
  rcases hchange with ⟨δ,hδ,hchange⟩
  let ε := min δ (min t (L-t))/2
  have heps : 0 < ε := div_pos
    (lt_min hδ (lt_min ht.1 (sub_pos.mpr ht.2))) (by norm_num)
  have hed : ε < δ := by
    have H : 0 < min δ (min t (L-t)) := lt_min hδ (lt_min ht.1 (sub_pos.mpr ht.2))
    dsimp [ε]; linarith [min_le_left δ (min t (L-t))]
  have het : ε < t := by
    have H : min δ (min t (L-t)) ≤ t := (min_le_right _ _).trans (min_le_left _ _)
    dsimp [ε]; linarith [ht.1]
  have heL : ε < L-t := by
    have H : min δ (min t (L-t)) ≤ L-t := (min_le_right _ _).trans (min_le_right _ _)
    dsimp [ε]; linarith [ht.2]
  have ha : t-ε ∈ Icc 0 L := ⟨by linarith,by linarith [ht.2]⟩
  have hb : t+ε ∈ Icc 0 L := ⟨by linarith [ht.1],by linarith⟩
  have hti : t ∈ Icc 0 L := ⟨ht.1.le,ht.2.le⟩
  have hlt : σ (t-ε) < σ t := by
    apply lt_of_le_of_ne (hm ha hti (by linarith))
    intro h
    have H := signChanges_not_flat hm ht ha hzero ⟨δ,hδ,hchange⟩ h.symm
    linarith
  have hgt : σ t < σ (t+ε) := by
    apply lt_of_le_of_ne (hm hti hb (by linarith))
    intro h
    have H := signChanges_not_flat hm ht hb hzero ⟨δ,hδ,hchange⟩ h
    linarith
  have hmaps : MapsTo σ (Icc 0 L) (Icc 0 T) := by rw [← himage]; exact mapsTo_image _ _
  have htarget : σ t ∈ Ioo 0 T :=
    ⟨(hmaps ha).1.trans_lt hlt,hgt.trans_le (hmaps hb).2⟩
  refine ⟨htarget,min (σ t-σ (t-ε)) (σ (t+ε)-σ t),
    lt_min (sub_pos.mpr hlt) (sub_pos.mpr hgt),?_⟩
  have hpreleft {y : ℝ} (hy : y ∈ Ioo
      (σ t-min (σ t-σ (t-ε)) (σ (t+ε)-σ t)) (σ t)) :
      ∃ s ∈ Ioo (t-δ) t, σ s=y := by
    have hylo : σ (t-ε) < y := by linarith [hy.1,min_le_left (σ t-σ (t-ε)) (σ (t+ε)-σ t)]
    have hyi : y ∈ Icc 0 T := ⟨(hmaps ha).1.trans hylo.le,hy.2.le.trans htarget.2.le⟩
    rw [← himage] at hyi
    rcases hyi with ⟨s,hs,hsy⟩
    have has : t-ε < s := by
      by_contra H
      have H' := hm hs ha (le_of_not_gt H)
      rw [hsy] at H'
      exact (not_le_of_gt hylo) H'
    have hst : s < t := by
      by_contra H
      have H' := hm hti hs (le_of_not_gt H)
      rw [hsy] at H'
      exact (not_le_of_gt hy.2) H'
    exact ⟨s,⟨by linarith,hst⟩,hsy⟩
  have hpreright {y : ℝ} (hy : y ∈ Ioo (σ t)
      (σ t+min (σ t-σ (t-ε)) (σ (t+ε)-σ t))) :
      ∃ s ∈ Ioo t (t+δ), σ s=y := by
    have hyhi : y < σ (t+ε) := by linarith [hy.2,min_le_right (σ t-σ (t-ε)) (σ (t+ε)-σ t)]
    have hyi : y ∈ Icc 0 T := ⟨htarget.1.le.trans hy.1.le,hyhi.le.trans (hmaps hb).2⟩
    rw [← himage] at hyi
    rcases hyi with ⟨s,hs,hsy⟩
    have hts : t < s := by
      by_contra H
      have H' := hm hs hti (le_of_not_gt H)
      rw [hsy] at H'
      exact (not_le_of_gt hy.1) H'
    have hsb : s < t+ε := by
      by_contra H
      have H' := hm hb hs (le_of_not_gt H)
      rw [hsy] at H'
      exact (not_le_of_gt hyhi) H'
    exact ⟨s,⟨hts,by linarith⟩,hsy⟩
  rcases hchange with ⟨hl,hr⟩ | ⟨hl,hr⟩
  · left
    constructor
    · intro y hy
      obtain ⟨s,hs,rfl⟩ := hpreleft hy
      exact hl s hs
    · intro y hy
      obtain ⟨s,hs,rfl⟩ := hpreright hy
      exact hr s hs
  · right
    constructor
    · intro y hy
      obtain ⟨s,hs,rfl⟩ := hpreleft hy
      exact hl s hs
    · intro y hy
      obtain ⟨s,hs,rfl⟩ := hpreright hy
      exact hr s hs

lemma activeSwitch_comp {K : ℕ} (f : Fin K → ℝ → ℝ) (σ : ℝ → ℝ) (L T : ℝ)
    (hm : MonotoneOn σ (Icc 0 L)) (himage : σ '' Icc 0 L = Icc 0 T)
    {t : ℝ} (ht : ActiveSwitch (fun j => f j ∘ σ) L t) : ActiveSwitch f T (σ t) := by
  rcases ht with ⟨ht0,htL,i,j,hij,heq,hvis,hchange⟩
  have H := signChanges_of_monotone_surj hm himage ⟨ht0,htL⟩
    (g := fun s => f i s-f j s) (by exact sub_eq_zero.mpr heq) hchange
  exact ⟨H.1.1,H.1.2,i,j,hij,heq,hvis,H.2⟩

/-- Flat pauses do not merge two actual strict switches, even if the two
switches occur in different parallel units. -/
theorem joint_count_comp_le {ι : Type*} (K : ι → ℕ)
    (f : (r : ι) → Fin (K r) → ℝ → ℝ) (σ : ℝ → ℝ) (L T : ℝ)
    (hm : MonotoneOn σ (Icc 0 L)) (himage : σ '' Icc 0 L = Icc 0 T) :
    ((⋃ r, switchSet (fun j => f r j ∘ σ) L).encard : ℝ≥0∞) ≤
      ((⋃ r, switchSet (f r) T).encard : ℝ≥0∞) := by
  have hmap : MapsTo σ (⋃ r, switchSet (fun j => f r j ∘ σ) L)
      (⋃ r, switchSet (f r) T) := by
    intro t ht
    rcases mem_iUnion.mp ht with ⟨r,hr⟩
    exact mem_iUnion.mpr ⟨r,activeSwitch_comp (f r) σ L T hm himage hr⟩
  have hinj : InjOn σ (⋃ r, switchSet (fun j => f r j ∘ σ) L) := by
    intro t ht s hs heq
    rcases mem_iUnion.mp ht with ⟨r,ht0,htL,i,j,hij,hzero,hvis,hchange⟩
    rcases mem_iUnion.mp hs with ⟨r',hs0,hsL,hrest⟩
    exact signChanges_not_flat hm ⟨ht0,htL⟩ ⟨hs0.le,hsL.le⟩
      (g := fun x => f r i x-f r j x) (sub_eq_zero.mpr hzero) hchange heq
  exact ENat.toENNReal_mono (Set.encard_le_encard_of_injOn hmap hinj)

end Paper35.ArclengthSwitch
