import Paper22.Reliability
import Paper22.Activation

/-! Eliminate the formerly external one-bit activation input using its matrix proof. -/
noncomputable section
namespace Paper22

/-- The exact activation input is now a proved theorem, not an extra assumption. -/
theorem activationIdentity_proved : ExternalActivationIdentity :=
  ⟨fun V m hm => activation_identity V m hm⟩

/-- The source EReal reliability conclusion now requires only the remaining
meta-converse exponent theorem. This is deliberately still labelled conditional. -/
theorem theorem_2_reliability_source_of_meta
    (extMeta : ExternalMetaConverseLimit) {n d : ℕ}
    (W : CQChannel n d) (hW : W.FullRank) {R : ℝ}
    (hR : 0 < R) (hRC : R < holevoCapacity W) :
    Filter.Tendsto (nsErrorExpEReal W R) Filter.atTop (nhds (spherePackingExtended W R)) ∧
    Filter.Tendsto (ansErrorExpEReal W R) Filter.atTop (nhds (spherePackingExtended W R)) :=
  theorem_2_reliability_source extMeta activationIdentity_proved W hW hR hRC

end Paper22
end
