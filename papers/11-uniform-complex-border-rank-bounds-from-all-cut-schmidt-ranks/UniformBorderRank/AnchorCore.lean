import UniformBorderRank.FiniteSites
import UniformBorderRank.SupportRank

/-! The two faithful anchor contractions preserve a full-rank core of a
maximal cut. This is the first reduction in Proposition 2.2. -/
noncomputable section
namespace UniformBorderRank
open Finset Module

namespace FiniteSites

def fullLinearMap {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ι → ℕ}
    (J : Finset ι) (b : Covectors d) : (TensorIndex d → ℂ) →ₗ[ℂ] (TensorIndex d → ℂ) :=
  (fullContractMap ⊤ J b).comp
    (Submodule.topEquiv : (⊤ : Submodule ℂ (TensorIndex d → ℂ)) ≃ₗ[ℂ] (TensorIndex d → ℂ)).symm.toLinearMap

lemma fullLinearMap_comp_subtype {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ι → ℕ}
    (E : Submodule ℂ (TensorIndex d → ℂ)) (J : Finset ι) (b : Covectors d) :
    (fullLinearMap J b).comp E.subtype = fullContractMap E J b := by
  ext T u
  rfl

end FiniteSites

/-- Both support spaces can be faithfully contracted while retaining at
most `r-1` sites per side, and the contracted coefficient matrix still has
rank `r`. The contraction is explicitly the original product contraction. -/
theorem exists_faithful_anchor_core {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {d : ι → ℕ} {e : κ → ℕ}
    (M : FiniteSites.TensorIndex d → FiniteSites.TensorIndex e → ℂ)
    (r : ℕ) (hr : 1 ≤ r)
    (hdim : Module.finrank ℂ (Submodule.span ℂ (Set.range M)) = r) :
    ∃ (J : Finset ι) (K : Finset κ) (b : FiniteSites.Covectors d) (c : FiniteSites.Covectors e),
      J.card ≤ r - 1 ∧ K.card ≤ r - 1 ∧
      Module.finrank ℂ (Submodule.span ℂ (Set.range (fun u v =>
        FiniteSites.fullContract (fun i => FiniteSites.fullContract (M i) K c v) J b u))) = r := by
  classical
  let EA := Submodule.span ℂ (Set.range (fun j i => M i j))
  let EB := Submodule.span ℂ (Set.range M)
  have hdA : Module.finrank ℂ EA = r := (rowSpan_finrank_transpose M).symm.trans hdim
  have hdB : Module.finrank ℂ EB = r := hdim
  obtain ⟨J, b, hJ, hJA⟩ := FiniteSites.faithful_full_contraction EA (by omega)
  obtain ⟨K, c, hK, hKB⟩ := FiniteSites.faithful_full_contraction EB (by omega)
  refine ⟨J, K, b, c, by omega, by omega, ?_⟩
  let l := FiniteSites.fullLinearMap (d := d) J b
  let f := FiniteSites.fullLinearMap (d := e) K c
  have hl : Function.Injective (l.comp EA.subtype) := by
    simpa only [l, FiniteSites.fullLinearMap_comp_subtype] using hJA
  have hf : Function.Injective (f.comp EB.subtype) := by
    simpa only [f, FiniteSites.fullLinearMap_comp_subtype] using hKB
  have h := rowSpan_finrank_faithful_maps M l f hl hf
  exact h.trans hdim

end UniformBorderRank
