import ELV.AdmissibleOperational

/-! The full public bit flip (4.3), realized by the same one-query work unitary
and with no additional query cost. -/
noncomputable section
namespace ELV.Costs
open ELV.Query ELV.Stabilize

def bitSign (b : Fin 2) : ℂ := (-1) ^ b.val

lemma bitSign_inner {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q]
    (b c : Fin 2) (v w : Q) :
    inner ℂ (bitSign b • v) (bitSign c • w) = bitSign b * bitSign c * inner ℂ v w := by
  fin_cases b <;> fin_cases c <;> simp [bitSign]

lemma public_bitflip_gram (b c r s : Fin 2) :
    inner ℂ (publicBasis b) (publicBasis c) - inner ℂ (publicBasis (b+r)) (publicBasis (c+s)) =
      bitSign b * bitSign c * (if r = s then (0 : ℂ) else 1) := by
  fin_cases b <;> fin_cases c <;> fin_cases r <;> fin_cases s <;>
    norm_num [public_basis_inner,bitSign,Fin.add_def,Fin.ext_iff]

variable {Q X : Type} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

/-- Extend witnesses for the required zero input to witnesses for both bit inputs. -/
theorem bitflip_witness (O : X → Q ≃ₗᵢ[ℂ] Q) (r : X → Fin 2) (v : X → Q)
    (h : Query.Witness O (fun _ => publicBasis 0) (fun x => publicBasis (r x)) v) :
    Query.Witness (fun bx : Fin 2 × X => O bx.2)
      (fun bx => publicBasis bx.1) (fun bx => publicBasis (bx.1+r bx.2))
      (fun bx => bitSign bx.1 • v bx.2) := by
  rintro ⟨b,x⟩ ⟨c,y⟩
  have hh := h x y
  rw [public_gram_difference] at hh
  rw [public_bitflip_gram]
  simp only [map_smul,bitSign_inner]
  rw [← mul_sub,← hh]

/-- Both public inputs are handled by one actual fixed finite query circuit. -/
theorem bitflip_realization (O : X → Q ≃ₗᵢ[ℂ] Q) (r : X → Fin 2) (v : X → Q)
    (h : Query.Witness O (fun _ => publicBasis 0) (fun x => publicBasis (r x)) v) :
    ∃ (I : Set (HilbertPair Public Q))
      (c : Circuit (HilbertPair Public (CanonicalPrivate I Public Q))
        (HilbertPair Public (Gram.StabilizingSpace I)) Q)
      (w : X → CanonicalPrivate I Public Q),
      ∀ x b, run (O x) c (WithLp.toLp 2 (publicBasis b,bitSign b • w x)) =
        WithLp.toLp 2 (publicBasis (b+r x),bitSign b • w x) ∧
      cost (O x) c (WithLp.toLp 2 (publicBasis b,bitSign b • w x)) = ‖v x‖ ^ 2 := by
  have hw := bitflip_witness O r v h
  obtain ⟨I,bV,_⟩ := exists_hilbertBasis ℂ (HilbertPair Public Q)
  let v' := fun bx : Fin 2 × X => bitSign bx.1 • v bx.2
  let w := fun x => canonicalCatalyst (I := I) (H := Public) v x
  have hc (x : X) (b : Fin 2) :
      canonicalCatalyst (I := I) (H := Public) v' (b,x) = bitSign b • w x := by
    apply (WithLp.equiv 2 (Q × Gram.StabilizingSpace I)).injective
    change (bitSign b • v x, (0 : Gram.StabilizingSpace I)) =
      (bitSign b • v x,bitSign b • (0 : Gram.StabilizingSpace I))
    simp
  refine ⟨I,canonicalCircuit bV hw,w,?_⟩
  intro x b
  constructor
  · have he := canonical_exact bV hw (b,x)
    change run (O x) (canonicalCircuit bV hw)
      (WithLp.toLp 2 (publicBasis b,canonicalCatalyst v' (b,x))) =
      WithLp.toLp 2 (publicBasis (b+r x),canonicalCatalyst v' (b,x)) at he
    simpa only [hc] using he
  · have hcost := canonical_cost bV hw (b,x)
    rw [hc] at hcost
    rw [hcost]
    fin_cases b <;> simp [v',bitSign]

end ELV.Costs
