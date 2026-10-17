import ELV.OneDirectionWitness

/-! Proposition 4.2 on actual query trajectories: forbidding either direction
forces the uniform Las Vegas cost to infinity for every exact admissible circuit. -/
noncomputable section
namespace ELV.Costs
open ELV.Model ELV.Query ELV.Stabilize
variable {gap : Gap} {n : ℕ} [NeZero n]

/-- Every actual forward query amplitude vanishes. -/
def Realization.NoForward (T : Realization gap n) : Prop :=
  ∀ O : promisedFamily n gap.δ, ∀ i : Fin T.circuit.length, ∀ j : T.Control,
    (Query.trace (bidirectional T.Control O.val) T.circuit
      (WithLp.toLp 2 (publicBasis 0,T.catalyst O)) i j).fst = 0

/-- Every actual inverse query amplitude vanishes. -/
def Realization.NoInverse (T : Realization gap n) : Prop :=
  ∀ O : promisedFamily n gap.δ, ∀ i : Fin T.circuit.length, ∀ j : T.Control,
    (Query.trace (bidirectional T.Control O.val) T.circuit
      (WithLp.toLp 2 (publicBasis 0,T.catalyst O)) i j).snd = 0

/-- Operational Proposition 4.2, including dim W=1 and all larger nonzero workspaces. -/
theorem oneDirection_infinite (T : Realization gap n) (hT : T.Admissible)
    (hdir : T.NoForward ∨ T.NoInverse) : T.uniformCost = ⊤ := by
  by_contra hfinite
  obtain ⟨f,g,hfg,hcost,htrace⟩ := extract_signedGram_full T hT
  have hb (O : promisedFamily n gap.δ) :
      ‖f O‖ ^ 2 + ‖g O‖ ^ 2 ≤ T.uniformCost.toReal := by
    apply (ENNReal.ofReal_le_iff_le_toReal hfinite).mp
    rw [← hcost O]
    exact le_iSup T.pointwiseCost O
  rcases hdir with hno | hno
  · have hfzero : ∀ O, f O = 0 := by
      intro O
      apply (WithLp.equiv 2 (Fin T.circuit.length → lp (fun _ : T.Control => ℂ) 2)).injective
      funext i
      apply Subtype.ext
      funext j
      have hz := hno O i j
      rw [htrace O i] at hz
      change (f O i j) • knownInput n = 0 at hz
      have hs : knownInput n ≠ 0 := by
        intro hs
        have hn := knownInput_norm n
        rw [hs,norm_zero] at hn
        norm_num at hn
      exact (smul_eq_zero.mp hz).resolve_right hs
    have hc : OneDirectionConstraint gap (-1) g := by
      intro O O'
      have hh := hfg O O'
      rw [hfzero O,hfzero O'] at hh
      simpa [genState] using hh
    exact oneDirection_no_uniform_bound gap (-1) (by norm_num) g hc T.uniformCost.toReal
      (fun O => by simpa [hfzero O] using hb O)
  · have hgzero : ∀ O, g O = 0 := by
      intro O
      apply (WithLp.equiv 2 (Fin T.circuit.length → lp (fun _ : T.Control => ℂ) 2)).injective
      funext i
      apply Subtype.ext
      funext j
      have hz := hno O i j
      rw [htrace O i] at hz
      change (g O i j) • O.val.phi = 0 at hz
      have hs : O.val.phi ≠ 0 := by
        intro hs
        have hn := O.val.phi_norm
        rw [hs,norm_zero] at hn
        norm_num at hn
      exact (smul_eq_zero.mp hz).resolve_right hs
    have hc : OneDirectionConstraint gap 1 f := by
      intro O O'
      have hh := hfg O O'
      rw [hgzero O,hgzero O'] at hh
      simpa [genState] using hh
    exact oneDirection_no_uniform_bound gap 1 (by norm_num) f hc T.uniformCost.toReal
      (fun O => by simpa [hgzero O] using hb O)

/-- Minimax cost for exact admissible realizations using only one direction. -/
def oneDirectionValue (gap : Gap) (n : ℕ) [NeZero n] : ENNReal :=
  sInf {c | ∃ T : Realization gap n, T.Admissible ∧ (T.NoForward ∨ T.NoInverse) ∧ T.uniformCost = c}

theorem oneDirection_optimum_infinite (gap : Gap) (n : ℕ) [NeZero n] :
    oneDirectionValue gap n = ⊤ := by
  apply top_unique
  apply le_sInf
  rintro c ⟨T,hT,hdir,rfl⟩
  rw [oneDirection_infinite T hT hdir]

end ELV.Costs
