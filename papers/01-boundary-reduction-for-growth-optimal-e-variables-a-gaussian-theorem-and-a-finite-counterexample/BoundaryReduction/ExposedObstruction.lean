import BoundaryReduction.ExposedVertex

open Real Set BigOperators Filter
open scoped Classical
namespace BoundaryReduction.FiniteExponential

variable {α : Type} [Fintype α] [Nonempty α] {d : ℕ}
variable (p : FinProb α) (hp : ∀ y, 0 < p.w y) (Y : α → E d)

include hp

structure Prior (C : Set (E d)) where
  index : Type
  finite : Fintype index
  weights : @FinProb index finite
  parameter : index → E d
  admissible : ∀ i, mean p hp Y (parameter i) ∈ C

attribute [instance] Prior.finite

noncomputable def Prior.prob {C : Set (E d)} (F : Prior p hp Y C) : FinProb α where
  w := fun y => ∑ i, F.weights.w i*(tilt p hp Y (F.parameter i)).w y
  nonneg := fun y => Finset.sum_nonneg (fun i _ => mul_nonneg (F.weights.nonneg i) (tilt_pos p hp Y _ y).le)
  sum_eq_one := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum,(tilt p hp Y _).sum_eq_one,mul_one]
    exact F.weights.sum_eq_one

noncomputable def information (C : Set (E d)) : ℝ :=
  sInf {x : ℝ | ∃ F : Prior p hp Y C, x = FinProb.klPos F.prob p}

lemma information_bddBelow (C : Set (E d)) :
    BddBelow {x : ℝ | ∃ F : Prior p hp Y C, x = FinProb.klPos F.prob p} :=
  ⟨0,by rintro x ⟨F,rfl⟩; exact FinProb.klPos_nonneg hp⟩

variable (V : Finset α) (hV : V.Nonempty)

include hV

noncomputable def vertexMass : ℝ := ∑ v : V, p.w v

lemma vertexMass_pos : 0 < vertexMass p V := by
  letI : Nonempty V := ⟨⟨hV.choose,hV.choose_spec⟩⟩
  exact Finset.sum_pos (fun v _ => hp v) Finset.univ_nonempty

noncomputable def vertexWeights : FinProb V where
  w := fun v => p.w v/vertexMass p V
  nonneg := fun v => (div_pos (hp v) (vertexMass_pos p hp V hV)).le
  sum_eq_one := by rw [← Finset.sum_div]; exact div_self (vertexMass_pos p hp V hV).ne'

noncomputable def conditional : FinProb α where
  w := fun y => ∑ v : V, (vertexWeights p hp V hV).w v*(if y = (v : α) then 1 else 0)
  nonneg := fun y => Finset.sum_nonneg (fun v _ => mul_nonneg ((vertexWeights p hp V hV).nonneg v) (by split_ifs <;> norm_num))
  sum_eq_one := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum]
    simp
    exact (vertexWeights p hp V hV).sum_eq_one

lemma conditional_mass (y : α) :
    (conditional p hp V hV).w y = if y ∈ V then p.w y/vertexMass p V else 0 := by
  by_cases hy : y ∈ V
  · change (∑ v : V, _ ) = _
    rw [Finset.sum_eq_single (⟨y,hy⟩ : V)]
    · simp [hy,vertexWeights]
    · intro v _ hv
      have hne : y ≠ (v : α) := by intro h; apply hv; exact Subtype.ext h.symm
      simp [hne]
    · simp
  · change (∑ v : V, _) = _
    rw [if_neg hy]
    apply Finset.sum_eq_zero
    intro v _
    have hne : y ≠ (v : α) := fun h => hy (h ▸ v.2)
    simp [hne]

/-- The conditional reconstruction has divergence exactly -log α. -/
lemma conditional_kl : FinProb.klPos (conditional p hp V hV) p = -log (vertexMass p V) := by
  have hm := (conditional p hp V hV).sum_eq_one
  have heq (y : α) : (conditional p hp V hV).w y*log ((conditional p hp V hV).w y/p.w y) =
      (conditional p hp V hV).w y*(-log (vertexMass p V)) := by
    by_cases hy : y ∈ V
    · rw [conditional_mass p hp V hV y,if_pos hy]
      rw [div_div,show p.w y/(vertexMass p V*p.w y) = (vertexMass p V)⁻¹ by
        field_simp [(hp y).ne',(vertexMass_pos p hp V hV).ne'],log_inv]
    · simp [conditional_mass p hp V hV y,hy]
  simp_rw [FinProb.klPos,heq]
  rw [← Finset.sum_mul,hm,one_mul]

variable (normal : V → E d)
variable (hexpose : ∀ v : V, ∀ y, y ≠ (v : α) → inner ℝ (normal v) (Y y) < inner ℝ (normal v) (Y v))

noncomputable def remoteProb (t : ℝ) : FinProb α where
  w := fun y => ∑ v : V, (vertexWeights p hp V hV).w v*(tilt p hp Y (t • normal v)).w y
  nonneg := fun y => Finset.sum_nonneg (fun v _ => mul_nonneg ((vertexWeights p hp V hV).nonneg v) (tilt_pos p hp Y _ y).le)
  sum_eq_one := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum,(tilt p hp Y _).sum_eq_one,mul_one]
    exact (vertexWeights p hp V hV).sum_eq_one

include hexpose

theorem remoteProb_tendsto (y : α) :
    Tendsto (fun t : ℝ => (remoteProb p hp Y V hV normal t).w y) atTop
      (nhds ((conditional p hp V hV).w y)) := by
  exact tendsto_finset_sum Finset.univ (fun v _ =>
    (tilt_tendsto_vertex p hp Y v (normal v) (hexpose v) y).const_mul _)

lemma continuous_kl_summand (y : α) : Continuous (fun x : ℝ => x*log (x/p.w y)) := by
  have heq (x : ℝ) : x*log (x/p.w y) = p.w y*((x/p.w y)*log (x/p.w y)) := by field_simp [(hp y).ne']
  simp_rw [heq]
  exact continuous_const.mul (continuous_mul_log.comp (continuous_id.div_const _))

/-- Continuity at zero masses is included; the limiting conditional law is allowed to vanish. -/
theorem remote_kl_tendsto :
    Tendsto (fun t : ℝ => FinProb.klPos (remoteProb p hp Y V hV normal t) p) atTop
      (nhds (-log (vertexMass p V))) := by
  rw [← conditional_kl p hp V hV]
  exact tendsto_finset_sum Finset.univ (fun y _ =>
    (continuous_kl_summand p hp Y V hV normal hexpose y).continuousAt.tendsto.comp
      (remoteProb_tendsto p hp Y V hV normal hexpose y))

variable (B : Set (E d))

/-- Compact containment forces the remote exposed means to be exterior eventually. -/
lemma remote_exterior_eventually (hVoutside : ∀ v : V, Y v ∉ closure B) :
    ∀ᶠ t : ℝ in atTop, ∀ v : V, mean p hp Y (t • normal v) ∉ B := by
  rw [Filter.eventually_all]
  intro v
  have hlim := mean_tendsto_vertex p hp Y v (normal v) (hexpose v)
  have hmem : (closure B)ᶜ ∈ nhds (Y v) := isClosed_closure.isOpen_compl.mem_nhds (hVoutside v)
  exact (hlim.eventually hmem).mono (fun _ ht hb => ht (subset_closure hb))

/-- Proposition 3.2, exposed reconstruction bound (3.22). -/
theorem information_exterior_le (hVoutside : ∀ v : V, Y v ∉ closure B) :
    information p hp Y Bᶜ ≤ -log (vertexMass p V) := by
  apply ge_of_tendsto (remote_kl_tendsto p hp Y V hV normal hexpose)
  filter_upwards [remote_exterior_eventually p hp Y V hV normal hexpose B hVoutside] with t ht
  let F : Prior p hp Y Bᶜ := ⟨V,inferInstance,vertexWeights p hp V hV,fun v => t • normal v,ht⟩
  exact csInf_le (information_bddBelow p hp Y Bᶜ) ⟨F,rfl⟩

end BoundaryReduction.FiniteExponential
