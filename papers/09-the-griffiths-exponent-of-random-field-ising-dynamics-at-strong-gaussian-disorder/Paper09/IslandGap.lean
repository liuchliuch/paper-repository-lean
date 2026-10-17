import Paper09.Relabel
import Paper09.RFIM
import Paper09.SoftShellFull
import Paper09.IslandPlacement

open Finset BigOperators Classical Real
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Paper09.RFIM

local instance (priority := 2000) islandGapPointDecEq (d : ℕ) : DecidableEq (Point d) := Classical.decEq _
local instance (priority := 2000) islandGapSiteDecEq {d : ℕ} (A : Finset (Point d)) : DecidableEq ↥A := Classical.decEq _
local instance (priority := 2000) islandGapSumDecEq {I O : Type*} : DecidableEq (I ⊕ O) := Classical.decEq _

/-- The actual finite domain split into an island and its exterior. -/
def islandSplit {d : ℕ} (Ω B : Finset (Point d)) (hB : B ⊆ Ω) :
    (↥B ⊕ ↥(Ω \ B)) ≃ ↥Ω where
  toFun := Sum.elim (fun i => ⟨i.val, hB i.property⟩)
    (fun o => ⟨o.val, (mem_sdiff.mp o.property).1⟩)
  invFun x := if hx : x.val ∈ B then Sum.inl ⟨x.val, hx⟩ else
    Sum.inr ⟨x.val, mem_sdiff.mpr ⟨x.property, hx⟩⟩
  left_inv x := by
    cases x with
    | inl i => simp [i.property]
    | inr o => simp [(mem_sdiff.mp o.property).2]
  right_inv x := by dsimp only; split_ifs <;> rfl

/-- The genuine external vertex boundary, in exterior site coordinates. -/
def islandShell {d : ℕ} (Ω B : Finset (Point d)) : Finset ↥(Ω \ B) :=
  univ.filter fun o => o.val ∈ externalBoundary B

theorem islandShell_card {d : ℕ} (Ω B : Finset (Point d))
    (hbdy : externalBoundary B ⊆ Ω) : (islandShell Ω B).card = (externalBoundary B).card := by
  apply Finset.card_bij (fun o _ => o.val)
  · intro o ho
    exact (mem_filter.mp ho).2
  · intro o ho o' ho' he
    exact Subtype.ext he
  · intro y hy
    let o : ↥(Ω \ B) := ⟨y, mem_sdiff.mpr ⟨hbdy hy, (mem_externalBoundary.mp hy).1⟩⟩
    exact ⟨o, mem_filter.mpr ⟨mem_univ _, hy⟩, rfl⟩

private theorem outside_field_eq {d : ℕ} (Ω B : Finset (Point d))
    (hbdy : externalBoundary B ⊆ Ω) (ζ : Point d → Spin) (i : ↥B) :
    (∑ o : ↥(Ω \ B), if LatticeGeometry.Adj i.val o.val then spinVal (ζ o.val) else 0) =
      ∑ y ∈ externalBoundary B, if LatticeGeometry.Adj i.val y then spinVal (ζ y) else 0 := by
  have hs := Finset.sum_coe_sort (Ω \ B) (fun y => if LatticeGeometry.Adj i.val y then spinVal (ζ y) else 0)
  convert hs.trans ?_ using 1
  symm
  apply sum_subset
  · intro y hy
    exact mem_sdiff.mpr ⟨hbdy hy, (mem_externalBoundary.mp hy).1⟩
  · intro y hy hnot
    apply if_neg
    intro ha
    exact hnot (mem_externalBoundary.mpr ⟨(mem_sdiff.mp hy).2, i.val, i.property, ha⟩)

/-- The deterministic soft-shell island estimate in the original finite
lattice coordinates. All exterior spins remain part of the dynamics. -/
theorem island_gap_bound {d : ℕ} (Ω B : Finset (Point d))
    (hB : B ⊆ Ω) (hBn : B.Nonempty) (hbdy : externalBoundary B ⊆ Ω)
    (h : Point d → ℝ) (β H : ℝ) (hβ : 0 ≤ β) (ζ : Point d → Spin)
    (hh : ∀ y ∈ externalBoundary B, H ≤ spinVal (ζ y) * h y) :
    spectralGap (freeGibbs Ω h β) ≤ spectralGap (pinnedGibbs B (fun _ => 0) β ζ) *
      exp (4 * (∑ x ∈ B, |h x|) + ((externalBoundary B).card : ℝ) * qH H d β *
        (exp (8 * (d : ℝ) * β) - 1 + 8 * (d : ℝ) * β)) := by
  letI : Nonempty ↥B := ⟨⟨hBn.choose, hBn.choose_spec⟩⟩
  let e := islandSplit Ω B hB
  let Λ := Relabel.lattice (domainLattice Ω) e.symm
  let hsum : ↥B ⊕ ↥(Ω \ B) → ℝ := fun s => h (e s).val
  let ζout : ↥(Ω \ B) → Spin := fun o => ζ o.val
  have hS : ∀ (i : ↥B) (o : ↥(Ω \ B)), Λ.adj (Sum.inl i) (Sum.inr o) → o ∈ islandShell Ω B := by
    intro i o ha
    apply mem_filter.mpr
    refine ⟨mem_univ _, mem_externalBoundary.mpr ⟨(mem_sdiff.mp o.property).2, i.val, i.property, ?_⟩⟩
    exact ha
  have hdeg : (Λ.maxDegree : ℝ) ≤ 2 * (d : ℝ) := by dsimp [Λ, Relabel.lattice, domainLattice]; norm_num
  have hsoft := gibbs_soft_shell_defect_gap Λ hsum β H d hβ hdeg
    (islandShell Ω B) hS ζout (by
      intro o ho
      exact hh o.val (mem_filter.mp ho).2)
  have hfull : spectralGap (gibbs Λ hsum β univ ∅ (fun _ => 0)) = spectralGap (freeGibbs Ω h β) := by
    exact Relabel.gibbs_gap_transport (domainLattice Ω) Λ e.symm
      (by intro x y; dsimp [Λ, Relabel.lattice]; simp) (fun x => h x.val) hsum
      (by intro x; dsimp [hsum]; rw [e.apply_symm_apply]) β
  have hpure : spectralGap (sumInteriorGibbs Λ (fun _ => 0) β ζout) =
      spectralGap (pinnedGibbs B (fun _ => 0) β ζ) := by
    apply Relabel.gibbs_gap_transport (domainLattice B) Λ.sumLeft (Equiv.refl _) (fun _ _ => Iff.rfl)
      (effectiveField B (fun _ => 0) β ζ) (Λ.sumConditionalField (fun _ => 0) β ζout) ?_ β
    intro i
    dsimp [Lattice.sumConditionalField, Λ, Relabel.lattice, e, islandSplit, ζout, domainLattice]
    convert congrArg (fun r : ℝ => 0 + β*r) (outside_field_eq Ω B hbdy ζ i) using 1
    congr 2
    apply sum_congr rfl
    intro o ho
    congr 1
  have hmass : fieldMass hsum Lattice.leftSites = ∑ x ∈ B, |h x| := by
    simp only [fieldMass, Lattice.leftSites, sum_map, Function.Embedding.coeFn_mk]
    exact Finset.sum_coe_sort B (fun x => |h x|)
  dsimp only at hsoft
  rw [hfull, hpure, hmass, islandShell_card Ω B hbdy] at hsoft
  let b := 4 * β * (shellDegree Λ Lattice.leftSites (Lattice.rightShell (islandShell Ω B)) : ℝ)
  have hb : b ≤ 8 * (d : ℝ) * β := by
    have hs := shellDegree_le_maxDegree Λ Lattice.leftSites (Lattice.rightShell (islandShell Ω B))
    have hs' : (shellDegree Λ Lattice.leftSites (Lattice.rightShell (islandShell Ω B)) : ℝ) ≤ 2*(d:ℝ) :=
      (by exact_mod_cast hs)
    dsimp [b]
    nlinarith
  apply hsoft.trans
  apply mul_le_mul_of_nonneg_left _ (spectralGap_nonneg _)
  apply exp_le_exp.mpr
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Nat.cast_nonneg _) (qH_pos H d β).le)
  have he := exp_le_exp.mpr hb
  change exp b - 1 + b ≤ _
  linarith

/-- Translation gives an actual bijection between the two site sets. -/
def translatedSites {d : ℕ} (t : Point d) (A : Finset (Point d)) : ↥A ≃ ↥(translate t A) where
  toFun x := ⟨x.val+t, mem_translate.mpr (by simpa using x.property)⟩
  invFun y := ⟨y.val-t, mem_translate.mp y.property⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv y := by apply Subtype.ext; simp

@[simp] theorem card_translate {d : ℕ} (t : Point d) (A : Finset (Point d)) :
    (translate t A).card = A.card := by
  exact card_image_of_injective A (fun _ _ hh => add_right_cancel hh)

/-- Fixed boundary spins translate with the box, and the genuine pinned
pure-system heat-bath gap is unchanged. -/
theorem pinned_gap_translate {d : ℕ} (t : Point d) (A : Finset (Point d))
    (β : ℝ) (ζ : Point d → Spin) :
    spectralGap (pinnedGibbs (translate t A) (fun _ => 0) β (fun y => ζ (y-t))) =
      spectralGap (pinnedGibbs A (fun _ => 0) β ζ) := by
  apply Relabel.gibbs_gap_transport (domainLattice A) (domainLattice (translate t A))
    (translatedSites t A) ?_ (effectiveField A (fun _ => 0) β ζ)
    (effectiveField (translate t A) (fun _ => 0) β (fun y => ζ (y-t))) ?_ β
  · intro x y
    exact adj_add_iff x.val y.val t
  · intro x
    unfold effectiveField
    rw [externalBoundary_translate]
    change 0 + β * (∑ y ∈ translate t (externalBoundary A),
      if LatticeGeometry.Adj (x.val+t) y then spinVal (ζ (y-t)) else 0) = _
    rw [translate, Finset.sum_image]
    · simp only [adj_add_iff, add_sub_cancel_right]
    · intro a ha b hb hh
      exact add_right_cancel hh

/-- The actual island comparison for a translated pure box. -/
theorem translated_box_gap_bound {d m : ℕ} (Ω : Finset (Point d)) (t : Point d)
    (hm : 1 ≤ m) (hB : translate t (pureBox d m) ⊆ Ω)
    (hbdy : externalBoundary (translate t (pureBox d m)) ⊆ Ω)
    (h : Point d → ℝ) (β H : ℝ) (hβ : 0 ≤ β) (ζ : Point d → Spin)
    (hh : ∀ y ∈ externalBoundary (translate t (pureBox d m)),
      H ≤ spinVal (ζ (y-t)) * h y) :
    spectralGap (freeGibbs Ω h β) ≤ pureBoxGap d m β ζ *
      exp (4 * (∑ x ∈ translate t (pureBox d m), |h x|) +
        ((externalBoundary (pureBox d m)).card : ℝ) * qH H d β *
          (exp (8*(d:ℝ)*β)-1+8*(d:ℝ)*β)) := by
  have hn : (pureBox d m).Nonempty := ⟨(fun _ => 1), mem_pureBox.mpr (by intro j; constructor <;> omega)⟩
  have hnt : (translate t (pureBox d m)).Nonempty := by
    obtain ⟨x, hx⟩ := hn
    exact ⟨x+t, mem_translate.mpr (by simpa using hx)⟩
  have hb := island_gap_bound Ω (translate t (pureBox d m)) hB hnt hbdy h β H hβ
    (fun y => ζ (y-t)) hh
  rw [pinned_gap_translate, externalBoundary_translate, card_translate] at hb
  exact hb

/-- Interior fields bounded by `ε/m` have the required surface-order mass. -/
theorem translated_fieldMass_le {d m : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m)
    (t : Point d) (h : Point d → ℝ) (ε : ℝ)
    (hh : ∀ x ∈ translate t (pureBox d m), |h x| ≤ ε/(m:ℝ)) :
    (∑ x ∈ translate t (pureBox d m), |h x|) ≤ ε*(m:ℝ)^(d-1) := by
  calc (∑ x ∈ translate t (pureBox d m), |h x|) ≤
      ∑ _x ∈ translate t (pureBox d m), ε/(m:ℝ) := sum_le_sum hh
    _ = ε*(m:ℝ)^(d-1) := by
      simp only [sum_const, nsmul_eq_mul, card_translate, card_pureBox, Nat.cast_pow]
      have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
      have hde : d = (d-1)+1 := by omega
      rw [hde, pow_succ]
      have hexp : d - 1 + 1 - 1 = d-1 := by omega
      rw [hexp]
      field_simp

/-- Proposition 2.1's deterministic barrier on an actual translated island,
with exactly the original pure-gap input and the shrinking interior fields. -/
theorem gap_on_translated_island {d m : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m)
    (Ω : Finset (Point d)) (t : Point d)
    (hB : translate t (pureBox d m) ⊆ Ω)
    (hbdy : externalBoundary (translate t (pureBox d m)) ⊆ Ω)
    (h : Point d → ℝ) (β H c₀ ε : ℝ) (hβ : 0 ≤ β) (hc₀ : 0 < c₀)
    (ζ : Point d → Spin) (hε : ε = c₀/16)
    (hpure : pureBoxGap d m β ζ ≤ exp (-c₀*(m:ℝ)^(d-1)))
    (hthreshold : 2*(d:ℝ)*qH H d β*(exp (8*(d:ℝ)*β)-1+8*(d:ℝ)*β) ≤ c₀/4)
    (hsmall : ∀ x ∈ translate t (pureBox d m), |h x| ≤ ε/(m:ℝ))
    (hshell : ∀ y ∈ externalBoundary (translate t (pureBox d m)),
      H ≤ spinVal (ζ (y-t))*h y) :
    spectralGap (freeGibbs Ω h β) ≤ exp (-(c₀/2)*(m:ℝ)^(d-1)) := by
  let M := (m:ℝ)^(d-1)
  let F := exp (8*(d:ℝ)*β)-1+8*(d:ℝ)*β
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hF : 0 ≤ F := by
    have hb : 0 ≤ 8*(d:ℝ)*β := by positivity
    have he : 1 ≤ exp (8*(d:ℝ)*β) := Real.one_le_exp_iff.mpr hb
    dsimp [F]; linarith
  have hmass := translated_fieldMass_le hd hm t h ε hsmall
  have hcard : ((externalBoundary (pureBox d m)).card : ℝ) ≤ 2*(d:ℝ)*M := by
    have hh := card_externalBoundary_pureBox_le d m
    dsimp [M]
    exact_mod_cast hh
  have hcost : 4*(∑ x ∈ translate t (pureBox d m), |h x|) +
      ((externalBoundary (pureBox d m)).card : ℝ)*qH H d β*F ≤
      4*ε*M + 2*(d:ℝ)*M*qH H d β*F := by
    have hh := mul_le_mul_of_nonneg_right hcard (mul_nonneg (qH_pos H d β).le hF)
    nlinarith
  have hgap := translated_box_gap_bound Ω t hm hB hbdy h β H hβ ζ hshell
  have hfirst : spectralGap (freeGibbs Ω h β) ≤
      exp (-c₀*M)*exp (4*ε*M+2*(d:ℝ)*M*qH H d β*F) := by
    apply hgap.trans
    apply mul_le_mul hpure (exp_le_exp.mpr hcost) (exp_nonneg _) (exp_nonneg _)
  have hh := mul_le_mul_of_nonneg_right hthreshold hM
  rw [← exp_add] at hfirst
  apply hfirst.trans
  apply exp_le_exp.mpr
  rw [hε]
  dsimp [F] at *
  nlinarith

/-- The Boolean signs used by the product Gaussian island event agree with
the prescribed pure-system spins. -/
def islandSigns {d m : ℕ} (ζ : Point d → Spin) :
    ↥(externalBoundary (pureBox d m)) → Bool := fun s => decide (ζ s.val = 1)

/-- The original Gaussian candidate event implies the deterministic barrier
for the actual RFIM in `Λ_n`; containment is proved from the placement itself. -/
theorem gap_on_candidate_island {d n m : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m)
    (h : Point d → ℝ) (β H c₀ ε : ℝ) (hβ : 0 ≤ β) (hc₀ : 0 < c₀)
    (ζ : Point d → Spin) (hε : ε = c₀/16)
    (hpure : pureBoxGap d m β ζ ≤ exp (-c₀*(m:ℝ)^(d-1)))
    (hthreshold : 2*(d:ℝ)*qH H d β*(exp (8*(d:ℝ)*β)-1+8*(d:ℝ)*β) ≤ c₀/4)
    (k : Candidate d n m)
    (hocc : h ∈ islandOccurs (islandSigns ζ) (ε/(m:ℝ)) H k) :
    spectralGap (freeGibbs (volumeBox d n) h β) ≤ exp (-(c₀/2)*(m:ℝ)^(d-1)) := by
  let t := islandOffset k
  have hB : translate t (pureBox d m) ⊆ volumeBox d n := by
    intro x hx
    let i : ↥(pureBox d m) := ⟨x-t, mem_translate.mp hx⟩
    have hh := placementCoordinate_in_volume ⟨k, Sum.inl i⟩
    simpa only [placementCoordinate, islandBasePoint, Sum.elim_inl, i, t, sub_add_cancel] using hh
  have hbdy : externalBoundary (translate t (pureBox d m)) ⊆ volumeBox d n := by
    intro x hx
    rw [externalBoundary_translate] at hx
    let s : ↥(externalBoundary (pureBox d m)) := ⟨x-t, mem_translate.mp hx⟩
    have hh := placementCoordinate_in_volume ⟨k, Sum.inr s⟩
    simpa only [placementCoordinate, islandBasePoint, Sum.elim_inr, s, t, sub_add_cancel] using hh
  have hbase : (fun x => h (placementCoordinate ⟨k,x⟩)) ∈
      Gaussian.islandEvent ↥(pureBox d m) ↥(externalBoundary (pureBox d m))
        (islandSigns ζ) (ε/(m:ℝ)) H := hocc
  have hsmall : ∀ x ∈ translate t (pureBox d m), |h x| ≤ ε/(m:ℝ) := by
    intro x hx
    let i : ↥(pureBox d m) := ⟨x-t, mem_translate.mp hx⟩
    have hh := Set.mem_pi.mp hbase (Sum.inl i) (Set.mem_univ _)
    change |h (placementCoordinate ⟨k, Sum.inl i⟩)| ≤ ε/(m:ℝ) at hh
    simpa only [placementCoordinate, islandBasePoint, Sum.elim_inl, i, t, sub_add_cancel] using hh
  have hshell : ∀ y ∈ externalBoundary (translate t (pureBox d m)),
      H ≤ spinVal (ζ (y-t))*h y := by
    intro y hy
    rw [externalBoundary_translate] at hy
    let s : ↥(externalBoundary (pureBox d m)) := ⟨y-t, mem_translate.mp hy⟩
    have hh := Set.mem_pi.mp hbase (Sum.inr s) (Set.mem_univ _)
    change h (placementCoordinate ⟨k, Sum.inr s⟩) ∈
      (if islandSigns ζ s then Set.Ici H else Set.Iic (-H)) at hh
    have hcoord : placementCoordinate ⟨k, Sum.inr s⟩ = y := by
      simp only [placementCoordinate, islandBasePoint, Sum.elim_inr, s, t, sub_add_cancel]
    rw [hcoord] at hh
    by_cases hz : ζ (y-t) = 0
    · have hn : ζ (y-t) ≠ 1 := by rw [hz]; decide
      have hs : islandSigns ζ s = false := by simp [islandSigns, s, hn]
      rw [hs] at hh
      change h y ≤ -H at hh
      rw [hz, spinVal_zero, neg_one_mul]
      linarith
    · have ho : ζ (y-t) = 1 := by
        apply Fin.ext
        have hlt := (ζ (y-t)).isLt
        have hn : (ζ (y-t)).val ≠ 0 := fun hh => hz (Fin.ext hh)
        change (ζ (y-t)).val = 1
        omega
      have hs : islandSigns ζ s = true := by simp [islandSigns, s, ho]
      rw [hs] at hh
      change H ≤ h y at hh
      simpa only [ho, spinVal_one, one_mul] using hh
  exact gap_on_translated_island hd hm (volumeBox d n) t hB hbdy h β H c₀ ε hβ hc₀
    ζ hε hpure hthreshold hsmall hshell

end Paper09.RFIM
