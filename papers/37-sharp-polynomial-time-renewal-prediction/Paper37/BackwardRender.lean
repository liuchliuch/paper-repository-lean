import Paper37.OccupiedTypesBridge
import Paper37.KnownSupport
import Paper37.BoundaryHazard

/-! Deterministic observation and recovery from the standard stationary cycle
construction. All geometry here is proved; no sampling visibility is assumed. -/
namespace Paper37.BackwardRender
open Paper37.Renewal Paper37.Envelope Paper37.EnvelopeBridge
open Paper37.OccupiedTypesBridge

def render (n age : ℕ) (ds : List ℕ) : List Bool :=
  let full := (true :: encodeGaps ds.reverse) ++ List.replicate age false
  full.drop (full.length-n)

def extract (k : ℕ) (x : List Bool) : List ℕ := (visibleGaps x).reverse.take k

lemma gap_parse_append_renewal (a : ℕ) (u z : List Bool) :
    gapsFrom a (u ++ true::z) = gapsFrom a (u ++ [true]) ++ gapsFrom 0 z := by
  induction u generalizing a with
  | nil => simp [gapsFrom]
  | cons b u ih => cases b <;> simp [gapsFrom,ih]

lemma visible_append_renewal (u z : List Bool) :
    ∃ g, visibleGaps (u ++ true::z) = g ++ gapsFrom 0 z := by
  induction u with
  | nil => exact ⟨[],rfl⟩
  | cons b u ih =>
    cases b with
    | false => simpa [visibleGaps,Paper37.Prediction.firstSuffix] using ih
    | true =>
      refine ⟨gapsFrom 0 (u ++ [true]), ?_⟩
      change gapsFrom 0 (u ++ true::z) = _
      exact gap_parse_append_renewal 0 u z

lemma visibleGaps_suffix {x y : List Bool} (h : x.IsSuffix y) :
    (visibleGaps x).IsSuffix (visibleGaps y) := by
  obtain ⟨u,hu⟩ := h
  cases hs : Paper37.Prediction.firstSuffix x with
  | none => simp [visibleGaps,hs]
  | some z =>
    obtain ⟨j,hj⟩ := firstSuffix_some_decomposition x z hs
    have hh := visible_append_renewal (u ++ List.replicate j false) z
    obtain ⟨g,hg⟩ := hh
    refine ⟨g,?_⟩
    rw [show visibleGaps x = gapsFrom 0 z by simp [visibleGaps,hs]]
    rw [← hu,hj]
    simpa only [List.append_assoc] using hg.symm

lemma visible_full (age : ℕ) (ds : List ℕ) :
    visibleGaps ((true::encodeGaps ds) ++ List.replicate age false) = ds := by
  change gapsFrom 0 (encodeGaps ds ++ List.replicate age false) = ds
  rw [← parseGaps_eq_gapsFrom]
  exact parseGaps_encodeGaps ds age

lemma ageFrom_append (a : ℕ) (u z : List Bool) :
    ageFrom a (u++z) = ageFrom (ageFrom a u) z := by
  induction u generalizing a with
  | nil => rfl
  | cons b u ih => cases b <;> exact ih _

lemma encodeGaps_append (xs ys : List ℕ) : encodeGaps (xs++ys) = encodeGaps xs ++ encodeGaps ys := by
  induction xs with
  | nil => rfl
  | cons d xs ih => simp [encodeGaps,ih,List.append_assoc]

lemma encodeGaps_end (ds : List ℕ) : ∃ u, true::encodeGaps ds = u++[true] := by
  induction ds with
  | nil => exact ⟨[],rfl⟩
  | cons d ds ih =>
    obtain ⟨u,hu⟩ := ih
    refine ⟨true::(List.replicate d false ++ u),?_⟩
    simp only [encodeGaps,List.cons_append,List.append_assoc]
    rw [hu]

/-- Cropping to the observation horizon preserves any short enough suffix. -/
lemma crop_preserves_suffix (n : ℕ) (u v : List Bool) (hv : v.length ≤ n) :
    ∃ a, (u++v).drop ((u++v).length-n) = a++v := by
  have hm : (u++v).length-n ≤ u.length := by simp only [List.length_append]; omega
  refine ⟨u.drop ((u++v).length-n),?_⟩
  rw [List.drop_append, Nat.sub_eq_zero_of_le hm]
  simp

/-- The observed word has exactly the requested horizon once enough positive
backward gaps have been supplied by the cycle representation. -/
theorem render_length {n age : ℕ} {ds : List ℕ} (hds : n ≤ ds.length) :
    (render n age ds).length = n := by
  have hw : ds.length ≤ (ds.map (fun d => d+1)).sum := Paper37.Adaptive.gap_list_length_le_weight ds
  have hrev : ((ds.reverse).map (fun d => d+1)).sum = (ds.map (fun d => d+1)).sum := by
    simp [List.map_reverse]
  simp only [render,List.length_drop,List.length_append,List.length_cons,
    List.length_replicate,encodeGaps_length,hrev]
  omega

/-- The last visible renewal survives cropping whenever the terminal age is
shorter than the observed block. -/
lemma render_ends_renewal {n age : ℕ} (ds : List ℕ) (ha : age < n) :
    ∃ u, render n age ds = u ++ true::List.replicate age false := by
  obtain ⟨u,hu⟩ := encodeGaps_end ds.reverse
  have he : (true::encodeGaps ds.reverse) ++ List.replicate age false =
      u ++ true::List.replicate age false := by rw [hu]; simp
  unfold render
  rw [he]
  exact crop_preserves_suffix n u (true::List.replicate age false) (by simp;omega)

/-- The actual parser always returns a newest-first prefix of the supplied
past gaps; censoring can delete only the oldest completed observations. -/
theorem render_visible_prefix (n age : ℕ) (ds : List ℕ) :
    (visibleGaps (render n age ds)).reverse = ds.take (visibleGaps (render n age ds)).length := by
  have hs : (render n age ds).IsSuffix ((true::encodeGaps ds.reverse) ++ List.replicate age false) :=
    List.drop_suffix _ _
  have hv := visibleGaps_suffix hs
  rw [visible_full] at hv
  have hp := List.reverse_prefix.mpr hv
  simp only [List.reverse_reverse] at hp
  have ht := List.prefix_iff_eq_take.mp hp
  simpa only [List.length_reverse] using ht

/-- Full deterministic F.3 parsing information: first visible renewal,
terminal age, and the newest-first iid prefix recovered from the word. -/
theorem render_parse {n age : ℕ} {ds : List ℕ} (ha : age < n) :
    ∃ j x, render n age ds = List.replicate j false ++ true::x ∧
      ageFrom 0 x = age ∧
      (gapsFrom 0 x).reverse = ds.take (gapsFrom 0 x).length := by
  obtain ⟨u,hu⟩ := render_ends_renewal ds ha
  have hseen : true ∈ render n age ds := by rw [hu];simp
  cases hs : Paper37.Prediction.firstSuffix (render n age ds) with
  | none =>
    have hz := firstSuffix_none_iff _ |>.mp hs
    rw [hz] at hseen
    simp at hseen
  | some x =>
    obtain ⟨j,hj⟩ := firstSuffix_some_decomposition _ x hs
    refine ⟨j,x,hj,?_,?_⟩
    · have hage : ageFrom 0 (render n age ds)=age := by
        rw [hu,ageFrom_append]
        simp only [ageFrom]
        simpa using Paper37.Boundary.ageFrom_zeros 0 age
      rw [hj,ageFrom_append] at hage
      exact hage
    · have hp := render_visible_prefix n age ds
      simpa only [visibleGaps,hs] using hp


/-- Every sufficiently short newest-first block of past gaps is recoverable
from the observed word by the explicit parser-based extractor. -/
theorem render_extract {n age k : ℕ} {ds : List ℕ} (hk : k ≤ ds.length)
    (hbudget : 1+age+((ds.take k).map (fun d => d+1)).sum ≤ n) :
    extract k (render n age ds) = ds.take k := by
  let old := (ds.drop k).reverse
  let sel := (ds.take k).reverse
  have hsplit : ds.reverse = old++sel := by
    dsimp [old,sel]
    rw [← List.reverse_append,List.take_append_drop]
  obtain ⟨u,hu⟩ := encodeGaps_end old
  have hfull : (true::encodeGaps ds.reverse) ++ List.replicate age false =
      u ++ true::(encodeGaps sel ++ List.replicate age false) := by
    rw [hsplit,encodeGaps_append]
    rw [← List.cons_append,hu]
    simp only [List.append_assoc,List.cons_append,List.nil_append]
  have hlen : (true::(encodeGaps sel ++ List.replicate age false)).length ≤ n := by
    dsimp [sel]
    simpa [encodeGaps_length,List.map_reverse,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hbudget
  have hr : ∃ a, render n age ds = a ++ true::(encodeGaps sel ++ List.replicate age false) := by
    unfold render
    rw [hfull]
    exact crop_preserves_suffix n u _ hlen
  obtain ⟨a,ha⟩ := hr
  obtain ⟨g,hg⟩ := visible_append_renewal a (encodeGaps sel ++ List.replicate age false)
  have hparse : gapsFrom 0 (encodeGaps sel ++ List.replicate age false) = sel := by
    rw [← parseGaps_eq_gapsFrom]
    exact parseGaps_encodeGaps sel age
  rw [hparse,← ha] at hg
  have hklen : sel.length=k := by simp [sel,List.length_take,Nat.min_eq_left hk]
  have hvlen : k ≤ (visibleGaps (render n age ds)).length := by
    rw [hg,List.length_append,hklen]
    omega
  unfold extract
  rw [render_visible_prefix,List.take_take,Nat.min_eq_left hvlen]

/-- The H.1 choice k=floor(n/B)−1 satisfies the extractor's visibility budget
on every path with bounded positive gap lengths and age below B. -/
theorem render_extract_bounded {n age B : ℕ} {ds : List ℕ}
    (hB : 1 ≤ B) (hBn : 2*B ≤ n) (hds : n ≤ ds.length)
    (ha : age < B) (hgap : ∀ d ∈ ds, d < B) :
    extract (n/B-1) (render n age ds) = ds.take (n/B-1) := by
  let k := n/B-1
  have hkle : k ≤ ds.length := by
    have hdiv : n/B ≤ n := Nat.div_le_self n B
    dsimp [k]
    omega
  apply render_extract hkle
  have hsum : ((ds.take k).map (fun d => d+1)).sum ≤ k*B := by
    have hh : ∀ v ∈ (ds.take k).map (fun d => d+1), v ≤ B := by
      intro v hv
      obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hv
      have hmem : d ∈ ds := List.mem_of_mem_take hd
      have := hgap d hmem
      omega
    have hb := List.sum_le_card_nsmul ((ds.take k).map (fun d => d+1)) B hh
    simpa [List.length_take,Nat.min_eq_left hkle] using hb
  have hdivp : 1 ≤ n/B := (Nat.le_div_iff_mul_le (by omega : 0 < B)).mpr (by omega)
  have hmul : (k+1)*B ≤ n := by
    have he : k+1=n/B := by dsimp [k];omega
    rw [he]
    exact Nat.div_mul_le_self n B
  nlinarith

end Paper37.BackwardRender
