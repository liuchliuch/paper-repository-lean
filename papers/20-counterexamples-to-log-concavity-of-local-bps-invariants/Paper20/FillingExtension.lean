import Paper20.FillingBubble

namespace Paper20.YoungShapes
open Paper20.YoungCorners
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

/-- Extend an actual preceding standard filling by a proved actual
single-box cover. This uses the already proved path/filling bijection. -/
def extendFilling {n : ℕ} (μ : Shape (n+1)) (ν : Shape n) (hν : Covers ν.val μ.val)
    (s : StandardFilling ν) : StandardFilling μ :=
  pathFilling (⟨⟨ν,hν⟩,fillingPath n ν s⟩:Path (n+1) μ)

@[simp] theorem extendFilling_castSucc {n : ℕ} (μ : Shape (n+1)) (ν : Shape n)
    (hν : Covers ν.val μ.val) (s : StandardFilling ν) (i : Fin n) :
    ((extendFilling μ ν hν s).val i.castSucc).val=(s.val i).val := by
  change position (⟨⟨ν,hν⟩,fillingPath n ν s⟩:Path (n+1) μ) i.castSucc=_
  rw [position_castSucc]
  exact fillingPath_position s i

@[simp] theorem extendFilling_last {n : ℕ} (μ : Shape (n+1)) (ν : Shape n)
    (hν : Covers ν.val μ.val) (s : StandardFilling ν) :
    ((extendFilling μ ν hν s).val (Fin.last n)).val=(stepCorner ⟨ν,hν⟩).val := by
  exact position_last (⟨⟨ν,hν⟩,fillingPath n ν s⟩:Path (n+1) μ)

theorem extendFilling_exchangeable {n : ℕ} (μ : Shape (n+1)) (ν : Shape n)
    (hν : Covers ν.val μ.val) (s : StandardFilling ν) (i j : Fin n) :
    Exchangeable (extendFilling μ ν hν s) i.castSucc j.castSucc ↔ Exchangeable s i j := by
  change (¬((extendFilling μ ν hν s).val i.castSucc).val≤
      ((extendFilling μ ν hν s).val j.castSucc).val ∧
    ¬((extendFilling μ ν hν s).val j.castSucc).val≤
      ((extendFilling μ ν hν s).val i.castSucc).val) ↔ _
  rw [extendFilling_castSucc,extendFilling_castSucc]
  rfl

lemma swap_castSucc {n : ℕ} (i j k : Fin n) :
    Equiv.swap i.castSucc j.castSucc k.castSucc=(Equiv.swap i j k).castSucc := by
  by_cases hi : k=i
  · subst k; simp
  · by_cases hj : k=j
    · subst k; simp
    · have hi' : k.castSucc≠i.castSucc := fun h => hi (Fin.castSucc_injective n h)
      have hj' : k.castSucc≠j.castSucc := fun h => hj (Fin.castSucc_injective n h)
      simp only [Equiv.swap_apply_of_ne_of_ne hi hj,Equiv.swap_apply_of_ne_of_ne hi' hj']

/-- Extending by the same final box preserves actual adjacent exchanges
in the preceding filling. -/
theorem extendFilling_exchange {n : ℕ} (μ : Shape (n+1)) (ν : Shape n)
    (hν : Covers ν.val μ.val) (s : StandardFilling ν) (i j : Fin n)
    (hij : j.val=i.val+1) (he : Exchangeable s i j) :
    extendFilling μ ν hν (exchange s i j hij he)=
      exchange (extendFilling μ ν hν s) i.castSucc j.castSucc hij
        ((extendFilling_exchangeable μ ν hν s i j).mpr he) := by
  apply Subtype.ext
  apply Equiv.ext
  intro k
  apply Subtype.ext
  refine Fin.lastCases ?_ (fun a => ?_) k
  · rw [exchange_apply,Equiv.swap_apply_of_ne_of_ne
      (Fin.castSucc_ne_last i).symm (Fin.castSucc_ne_last j).symm]
    rw [extendFilling_last,extendFilling_last]
  · rw [exchange_apply,swap_castSucc,extendFilling_castSucc,extendFilling_castSucc,exchange_apply]

theorem extendFilling_step {n : ℕ} (μ : Shape (n+1)) (ν : Shape n)
    (hν : Covers ν.val μ.val) {s t : StandardFilling ν} (h : FillingStep s t) :
    FillingStep (extendFilling μ ν hν s) (extendFilling μ ν hν t) := by
  obtain ⟨i,j,hij,he,rfl⟩ := h
  exact ⟨i.castSucc,j.castSucc,hij,(extendFilling_exchangeable μ ν hν s i j).mpr he,
    extendFilling_exchange μ ν hν s i j hij he⟩

theorem extendFilling_reachable {n : ℕ} (μ : Shape (n+1)) (ν : Shape n)
    (hν : Covers ν.val μ.val) {s t : StandardFilling ν} (h : FillingReachable s t) :
    FillingReachable (extendFilling μ ν hν s) (extendFilling μ ν hν t) :=
  Relation.ReflTransGen.lift (extendFilling μ ν hν) (fun _ _ he => extendFilling_step μ ν hν he) h

lemma extendFilling_prefix {n : ℕ} {μ : Shape (n+1)} (t : StandardFilling μ) :
    extendFilling μ (fillingPrevious t) (erase_covers _ _ (filling_last_removable t))
      (fillingPrefix t)=t := pathFilling_fillingPath (n+1) μ t

lemma extendFilling_cast {n : ℕ} (μ : Shape (n+1)) (ν ν' : Shape n) (h : ν=ν')
    (hν : Covers ν.val μ.val) (hν' : Covers ν'.val μ.val) (s : StandardFilling ν) :
    extendFilling μ ν' hν' (h ▸ s)=extendFilling μ ν hν s := by
  cases h
  rfl

end
end Paper20.YoungShapes
