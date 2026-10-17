import Paper13.PortedBounds
import Paper13.MultiAngleClassification
import Paper13.Amplification
noncomputable section
namespace Paper13
attribute [local instance] Classical.propDecidable

lemma nonbip_two_le {n : ℕ} (G : SimpleGraph (Fin n)) (hnb : ¬Nonempty (G.Coloring (Fin 2))) : 2 ≤ n := by
  by_contra hn
  have hn' : n ≤ 2 := by omega
  apply hnb
  refine ⟨⟨Fin.castLE hn',?_⟩⟩
  intro u v huv he
  exact huv.ne (Fin.castLE_injective hn' he)

lemma power_dim_half (h k : ℕ) (hk : 1 ≤ k) :
    2^(2*(k*(h+1))-1)=(2^(h+1))^(2*k)/2 := by
  have hn0 : 0 < k*(h+1) := Nat.mul_pos (by omega) (by omega)
  have he : 2^(2*(k*(h+1))-1)*2=(2^(h+1))^(2*k) := by
    rw [←pow_succ,show 2*(k*(h+1))-1+1=2*(k*(h+1)) by omega,←pow_mul]
    congr 1
    ring
  omega

lemma squared_complement_even (r d : ℕ) (hr : r ≤ d) (hd : 2 ∣ d) : 2 ∣ r^2+(d-r)^2 := by
  have h := congrArg (fun t => t%2) (Nat.add_sub_of_le hr)
  change (r+(d-r))%2=d%2 at h
  have hd0 := Nat.mod_eq_zero_of_dvd hd
  rw [Nat.add_mod,hd0] at h
  rcases Nat.mod_two_eq_zero_or_one r with hr0 | hr1 <;>
    rcases Nat.mod_two_eq_zero_or_one (d-r) with hs0 | hs1
  · apply Nat.dvd_of_mod_eq_zero
    simp [Nat.add_mod,Nat.pow_mod,hr0,hs0]
  · omega
  · omega
  · apply Nat.dvd_of_mod_eq_zero
    simp [Nat.add_mod,Nat.pow_mod,hr1,hs1]

/-- Full finite-k Proposition 5, with actual dimensions and the original hypotheses. -/
theorem proposition5_actual {h k : ℕ} (hk : 1 ≤ k) (K : PortedGadget h) (B : SimpleGraph (Fin k)) :
    Proposition5Claim K B := by
  let Γ := portedAssemblyOrdinal K B
  let d := 2^(h+1)
  let r := Module.finrank ℂ (LinearMap.range (Matrix.toLin' K.projector))
  let A := r^2+(d-r)^2
  have hb := proposition5_original_bounds hk K B
  change Module.finrank ℝ (graphStd Γ) ≤ A^k/2-1 ∧ largestIrrep Γ ≤ (max r (d-r))^k/2 ∧ _
  refine ⟨hb.1,hb.2,?_⟩
  rintro ⟨hc,hnb,hrigid,hncy⟩
  have hn := nonbip_two_le Γ hnb
  have hdim : Module.finrank ℝ (graphNat Γ)=d^(2*k)/2-2 := by
    rw [graphNat_eq_ma_of_rigid Γ hrigid,graphMa_dimension_of_nonbip hn Γ hc hnb hncy,power_dim_half h k hk]
  refine ⟨hdim,?_⟩
  have hr : r ≤ d := K.rank_lt.le
  have hdeven : 2 ∣ d := dvd_pow (by norm_num) (by omega : h+1≠0)
  have hAeven : 2 ∣ A := squared_complement_even r d hr hdeven
  have hApos : 0 < A := by
    have hrpos : 0 < r := K.rank_pos
    dsimp [A]
    positivity
  have hdge : 2 ≤ d := by
    dsimp [d]
    rw [pow_succ]
    have hp : 1 ≤ (2 : ℕ)^h := one_le_pow₀ (by norm_num)
    omega
  have h4 : 4 ≤ d^(2*k) := by
    calc 4 ≤ d^2 := by nlinarith
         _ ≤ d^(2*k) := Nat.pow_le_pow_right (by omega) (by omega)
  have hnumEven : 2 ∣ d^(2*k) := dvd_pow hdeven (by omega)
  have hdenEven : 2 ∣ A^k := dvd_pow hAeven (by omega)
  have hfield := ratio_bound_arith_q hApos k hnumEven hdenEven h4
  have hstdpos := graphStd_finrank_pos Γ (by omega)
  have hle : Module.finrank ℝ (graphStd Γ) ≤ A^k/2 := le_trans hb.1 (Nat.sub_le _ _)
  have hstdQ : (0 : ℚ) < Module.finrank ℝ (graphStd Γ) := by exact_mod_cast hstdpos
  have hleQ : (Module.finrank ℝ (graphStd Γ) : ℚ) ≤ (A^k/2 : ℕ) := by exact_mod_cast hle
  rw [hdim,←hfield]
  exact div_le_div_of_nonneg_left (by positivity) hstdQ hleQ

/-- The actual ratio diverges for every assembly family eventually satisfying the graph hypotheses. -/
theorem proposition5_actual_divergence {h : ℕ} (K : PortedGadget h) (B : (k : ℕ) → SimpleGraph (Fin k))
    (hgraphs : ∀ᶠ k : ℕ in Filter.atTop,
      let Γ := portedAssemblyOrdinal K (B k)
      Γ.Connected ∧ ¬Nonempty (Γ.Coloring (Fin 2)) ∧
        (∀ φ : Γ ≃g Γ, φ=SimpleGraph.Iso.refl) ∧ ¬Γ.IsRegularOfDegree 2) :
    Filter.Tendsto (fun k : ℕ =>
      (Module.finrank ℝ (graphNat (portedAssemblyOrdinal K (B k))) : ℚ) /
        Module.finrank ℝ (graphStd (portedAssemblyOrdinal K (B k)))) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop.mpr
  intro M
  obtain ⟨k₀,hk₀⟩ := amplification_ratio_diverges _ _ K.rank_pos K.rank_lt M
  filter_upwards [hgraphs,Filter.eventually_ge_atTop (max 1 k₀)] with k hG hk
  have hk1 : 1 ≤ k := le_trans (le_max_left _ _) hk
  have hp := proposition5_actual hk1 K (B k)
  exact (hk₀ k (le_trans (le_max_right _ _) hk)).trans (hp.2.2 hG).2
end Paper13
