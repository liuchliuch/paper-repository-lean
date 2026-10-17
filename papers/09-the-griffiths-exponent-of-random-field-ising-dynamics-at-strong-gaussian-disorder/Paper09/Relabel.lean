import Paper09.Disintegration

open Finset BigOperators Classical Real
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Paper09
namespace Relabel

variable {V W : Type*} [Fintype V] [Fintype W]

/-- Change the site labels without changing any spin values. -/
def configEquiv (e : V ≃ W) : Config V ≃ Config W where
  toFun η w := η (e.symm w)
  invFun θ v := θ (e v)
  left_inv η := by funext v; simp
  right_inv θ := by funext w; simp

theorem oneSite_iff (e : V ≃ W) (η θ : Config W) :
    oneSite ((configEquiv e).symm η) ((configEquiv e).symm θ) ↔ oneSite η θ := by
  constructor
  · rintro ⟨v, hv, hr⟩
    refine ⟨e v, hv, ?_⟩
    intro w hw
    have hh : e.symm w ≠ v := by intro hh; exact hw (by simpa using congrArg e hh)
    simpa [configEquiv] using hr (e.symm w) hh
  · rintro ⟨w, hw, hr⟩
    refine ⟨e.symm w, ?_, ?_⟩
    · simpa [configEquiv] using hw
    · intro v hv
      apply hr (e v)
      intro hh
      exact hv (by simpa using congrArg e.symm hh)

theorem heatBathGraph_relabel (e : V ≃ W) :
    (heatBathGraph V).reindex (configEquiv e) = heatBathGraph W := by
  cases hg : (heatBathGraph V).reindex (configEquiv e) with
  | mk edge symm =>
    cases hh : heatBathGraph W with
    | mk edge' symm' =>
      have he : edge = edge' := by
        funext η θ
        have hi := oneSite_iff e η θ
        change ((heatBathGraph V).reindex (configEquiv e)).edge η θ ↔ (heatBathGraph W).edge η θ at hi
        rw [hg, hh] at hi
        exact propext hi
      cases he
      rfl

/-- The actual heat-bath variational gap is invariant under site relabeling. -/
theorem spectralGap_relabel (p : FinProb (Config V)) (e : V ≃ W) :
    spectralGap (p.reindex (configEquiv e)) = spectralGap p := by
  rw [← UpdateGraph.variationalGap_eq_spectralGap,
    ← heatBathGraph_relabel e, UpdateGraph.variationalGap_reindex,
    UpdateGraph.variationalGap_eq_spectralGap]

/-- The same finite interaction graph in new site coordinates. -/
def lattice (Λ : Lattice V) (e : V ≃ W) : Lattice W where
  adj w w' := Λ.adj (e.symm w) (e.symm w')
  symm := Λ.symm
  irrefl w := Λ.irrefl _
  maxDegree := Λ.maxDegree
  degree_le w := by
    apply le_trans (Finset.card_le_card_of_injOn (fun w' : W => e.symm w') ?_ ?_)
      (Λ.degree_le (e.symm w))
    · intro w' hw
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hw).2⟩
    · intro a ha b hb hh
      exact e.symm.injective hh

/-- Interaction energies agree for any adjacency-preserving site equivalence. -/
theorem interaction_transport (Λ : Lattice V) (Γ : Lattice W) (e : V ≃ W)
    (hadj : ∀ v v', Γ.adj (e v) (e v') ↔ Λ.adj v v')
    (β : ℝ) (θ : Config W) :
    Γ.interaction β univ θ = Λ.interaction β univ (fun v => θ (e v)) := by
  unfold Lattice.interaction
  congr 1
  calc (∑ w : W, ∑ w' : W, if Γ.adj w w' then spinVal (θ w)*spinVal (θ w') else 0) =
      ∑ v : V, ∑ v' : V, if Γ.adj (e v) (e v') then spinVal (θ (e v))*spinVal (θ (e v')) else 0 := by
        rw [← e.sum_comp]
        apply sum_congr rfl; intro v hv
        exact (e.sum_comp _).symm
    _ = _ := by simp only [hadj]

theorem field_transport (e : V ≃ W) (h : V → ℝ) (g : W → ℝ)
    (hh : ∀ v, g (e v) = h v) (θ : Config W) :
    Lattice.fieldEnergy g univ θ = Lattice.fieldEnergy h univ (fun v => θ (e v)) := by
  unfold Lattice.fieldEnergy
  rw [← e.sum_comp]
  simp only [hh]

/-- Gibbs weights, including their genuine partition functions, are preserved
by adjacency- and field-preserving changes of site labels. -/
theorem gibbs_transport (Λ : Lattice V) (Γ : Lattice W) (e : V ≃ W)
    (hadj : ∀ v v', Γ.adj (e v) (e v') ↔ Λ.adj v v')
    (h : V → ℝ) (g : W → ℝ) (hh : ∀ v, g (e v) = h v) (β : ℝ) :
    gibbs Γ g β univ ∅ (fun _ => 0) =
      (gibbs Λ h β univ ∅ (fun _ => 0)).reindex (configEquiv e) := by
  have hw (θ : Config W) : isingWeight Γ g β univ ∅ (fun _ => 0) θ =
      isingWeight Λ h β univ ∅ (fun _ => 0) ((configEquiv e).symm θ) := by
    simp only [isingWeight, Lattice.boundEnergy, sum_empty, sum_const_zero, mul_zero, add_zero]
    rw [interaction_transport Λ Γ e hadj, field_transport e h g hh]
    rfl
  have hz : isingZ Γ g β univ ∅ (fun _ => 0) = isingZ Λ h β univ ∅ (fun _ => 0) := by
    unfold isingZ
    simp_rw [hw]
    exact (configEquiv e).symm.sum_comp _
  cases hp : gibbs Γ g β univ ∅ (fun _ => 0) with
  | mk w nonneg sum_one =>
    cases hq : (gibbs Λ h β univ ∅ (fun _ => 0)).reindex (configEquiv e) with
    | mk w' nonneg' sum_one' =>
      have he : w = w' := by
        funext θ
        have hi : (gibbs Γ g β univ ∅ (fun _ => 0)).w θ =
            ((gibbs Λ h β univ ∅ (fun _ => 0)).reindex (configEquiv e)).w θ := by
          change isingWeight Γ g β univ ∅ (fun _ => 0) θ / isingZ Γ g β univ ∅ (fun _ => 0) = _
          rw [hw, hz]
          rfl
        simpa only [hp, hq] using hi
      cases he
      rfl

theorem gibbs_gap_transport (Λ : Lattice V) (Γ : Lattice W) (e : V ≃ W)
    (hadj : ∀ v v', Γ.adj (e v) (e v') ↔ Λ.adj v v')
    (h : V → ℝ) (g : W → ℝ) (hh : ∀ v, g (e v) = h v) (β : ℝ) :
    spectralGap (gibbs Γ g β univ ∅ (fun _ => 0)) =
      spectralGap (gibbs Λ h β univ ∅ (fun _ => 0)) := by
  rw [gibbs_transport Λ Γ e hadj h g hh, spectralGap_relabel]

end Relabel
end Paper09
