import Paper36.SourceConditional

/-! Measure-level transport used by the concrete episode induction. The block
kernel is allowed to retain arbitrary continuous history. -/
namespace Paper36.SourceInduction
noncomputable section
open scoped ENNReal
open MeasureTheory ProbabilityTheory

variable {X Y H R O : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace H] [MeasurableSpace R] [MeasurableSpace O]

/-- An actual execution can be reduced to the information and unused window
that its next block reads. This is a proved transport of actual measures. -/
theorem transport_step (μ : Measure X) [SFinite μ]
    (step : Kernel X Y) [IsMarkovKernel step] (summary : X → H) (hs : Measurable summary)
    (output : Y → O) (ho : Measurable output) (block : Kernel H O) [IsMarkovKernel block]
    (hstep : ∀ x, (step x).map output = block (summary x)) :
    (step ∘ₘ μ).map output = block ∘ₘ μ.map summary := by
  apply (Measure.ext_iff_lintegral _).mpr
  intro f hf
  have hout : Measurable (fun y => f (output y)) := hf.comp ho
  have hlocal : Measurable (fun h => ∫⁻ o, f o ∂block h) := hf.lintegral_kernel
  calc
    _ = ∫⁻ x, ∫⁻ y, f (output y) ∂step x ∂μ := by
      rw [lintegral_map hf ho]
      exact Measure.lintegral_bind step.aemeasurable hout.aemeasurable
    _ = ∫⁻ x, ∫⁻ o, f o ∂block (summary x) ∂μ := by
      apply lintegral_congr_ae
      apply ae_of_all
      intro x
      dsimp only
      rw [← lintegral_map hf ho, hstep x]
    _ = ∫⁻ h, ∫⁻ o, f o ∂block h ∂μ.map summary :=
      (lintegral_map hlocal hs).symm
    _ = _ := (Measure.lintegral_bind block.aemeasurable hf.aemeasurable).symm

/-- If a block block maps a product of the observed history and fresh rows to
its next observed history and fresh rows, the same factorization holds after
mixing over every prior observed history. -/
theorem mix_local_factorization (ν : Measure H) [SFinite ν]
    (fresh : Kernel H R) [IsMarkovKernel fresh]
    (block : Kernel (H × R) O) [IsMarkovKernel block]
    (factor : Kernel H O) [IsMarkovKernel factor]
    (hfactor : (fresh ⊗ₖ block).map Prod.snd = factor) :
    block ∘ₘ (ν ⊗ₘ fresh) = factor ∘ₘ ν := by
  apply (Measure.ext_iff_lintegral _).mpr
  intro f hf
  calc
    _ = ∫⁻ hr, ∫⁻ o, f o ∂block hr ∂ν ⊗ₘ fresh :=
      Measure.lintegral_bind block.aemeasurable hf.aemeasurable
    _ = ∫⁻ h, ∫⁻ r, ∫⁻ o, f o ∂block (h,r) ∂fresh h ∂ν := by
      rw [Measure.lintegral_compProd hf.lintegral_kernel]
    _ = ∫⁻ h, ∫⁻ z, f z.2 ∂(fresh ⊗ₖ block) h ∂ν := by
      apply lintegral_congr_ae
      apply ae_of_all
      intro h
      exact (Kernel.lintegral_compProd _ _ _ (hf.comp measurable_snd)).symm
    _ = ∫⁻ h, ∫⁻ o, f o ∂factor h ∂ν := by
      apply lintegral_congr_ae
      apply ae_of_all
      intro h
      dsimp only
      rw [← Kernel.lintegral_map _ measurable_snd _ hf, hfactor]
    _ = _ := (Measure.lintegral_bind factor.aemeasurable hf.aemeasurable).symm


/-- A history transition followed by a fresh-row kernel may be mixed before or
before after the history transition, with exactly the same joint law. -/
theorem mix_transition_fresh {N : Type*} [MeasurableSpace N]
    (ν : Measure H) [SFinite ν] (next : Kernel H N) [IsMarkovKernel next]
    (fresh : Kernel N R) [IsMarkovKernel fresh] :
    (next ⊗ₖ fresh.prodMkLeft H) ∘ₘ ν = (next ∘ₘ ν) ⊗ₘ fresh := by
  apply (Measure.ext_iff_lintegral _).mpr
  intro f hf
  have hi : Measurable (fun n => ∫⁻ r, f (n,r) ∂fresh n) :=
    hf.lintegral_kernel_prod_right'
  calc
    _ = ∫⁻ h, ∫⁻ n, ∫⁻ r, f (n,r) ∂fresh n ∂next h ∂ν := by
      rw [Measure.lintegral_bind (next ⊗ₖ fresh.prodMkLeft H).aemeasurable hf.aemeasurable]
      apply lintegral_congr_ae
      apply ae_of_all
      intro h
      dsimp only
      rw [Kernel.lintegral_compProd _ _ _ hf]
      rfl
    _ = ∫⁻ n, ∫⁻ r, f (n,r) ∂fresh n ∂next ∘ₘ ν :=
      (Measure.lintegral_bind next.aemeasurable hi.aemeasurable).symm
    _ = _ := (Measure.lintegral_compProd hf).symm

section Recursion
variable {State Obs : ℕ → Type*} {Raw : ℕ → Type*}
  [∀ k, MeasurableSpace (State k)] [∀ k, MeasurableSpace (Obs k)]
  [∀ L, MeasurableSpace (Raw L)]

/-- Freshness is propagated from the original tape law by the actual block
recursion. Local assumptions are kernel equalities to be proved for one
physical block; the all-episode freshness conclusion is not an assumption. -/
theorem propagate_fresh (T : ℕ)
    (actual : (k : ℕ) → Measure (State k)) [∀ k, IsProbabilityMeasure (actual k)]
    (hist : (k : ℕ) → Measure (Obs k)) [∀ k, IsProbabilityMeasure (hist k)]
    (step : (k : ℕ) → Kernel (State k) (State (k+1))) [∀ k, IsMarkovKernel (step k)]
    (next : (k : ℕ) → Kernel (Obs k) (Obs (k+1))) [∀ k, IsMarkovKernel (next k)]
    (fresh : (k L : ℕ) → Kernel (Obs k) (Raw L)) [∀ k L, IsMarkovKernel (fresh k L)]
    (summary : (k L : ℕ) → State k → Obs k × Raw L)
    (hs : ∀ k L, Measurable (summary k L))
    (block : (k L : ℕ) → Kernel (Obs k × Raw (L+T)) (Obs (k+1) × Raw L))
    [∀ k L, IsMarkovKernel (block k L)]
    (hactual : ∀ k, actual (k+1) = step k ∘ₘ actual k)
    (hhist : ∀ k, hist (k+1) = next k ∘ₘ hist k)
    (hzero : ∀ L, (actual 0).map (summary 0 L) = hist 0 ⊗ₘ fresh 0 L)
    (hstep : ∀ k L x, (step k x).map (summary (k+1) L) = block k L (summary k (L+T) x))
    (hblock : ∀ k L, (fresh k (L+T) ⊗ₖ block k L).map Prod.snd =
      next k ⊗ₖ (fresh (k+1) L).prodMkLeft (Obs k)) :
    ∀ k L, (actual k).map (summary k L) = hist k ⊗ₘ fresh k L := by
  intro k
  induction k with
  | zero => exact hzero
  | succ k ih =>
    intro L
    rw [hactual, transport_step (actual k) (step k) (summary k (L+T)) (hs k (L+T))
      (summary (k+1) L) (hs (k+1) L) (block k L) (hstep k L), ih (L+T),
      mix_local_factorization (hist k) (fresh k (L+T)) (block k L) _ (hblock k L),
      mix_transition_fresh, ← hhist]

end Recursion
end
end Paper36.SourceInduction
