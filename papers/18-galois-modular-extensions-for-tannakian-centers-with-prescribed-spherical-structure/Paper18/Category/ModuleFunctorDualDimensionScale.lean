import Paper18.Category.ModuleFunctorDualDimensionScaling

/-! # The derived scaling factor of an actual module functor -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators MonoidalLeftAction
universe v u vM uM w wM
namespace Paper18.Category.ModuleFunctor
open MonoidalLeftAction
variable {M : Type uM} [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [HasKernels M] [HasFiniteBiproducts M]
  [∀ X Y : M, FiniteDimensional ℂ (X ⟶ Y)]
  {κ : Type wM} [Fintype κ] (SM : FiniteSemisimpleSkeleton M κ)
  (r : κ → ℝ) (j₀ : κ)

/-- Evaluate the actual image weight at one actual simple and normalize. -/
def moduleFunctorScale (F : M ⥤ M) : ℝ :=
  moduleObjectWeight SM r (F.obj (SM.simpleObject j₀)) / r j₀

omit [HasKernels M] [∀ X Y : M, FiniteDimensional ℂ (X ⟶ Y)] in
lemma moduleFunctorScale_iso {F G : M ⥤ M} (e : F ≅ G) :
    moduleFunctorScale SM r j₀ F = moduleFunctorScale SM r j₀ G := by
  unfold moduleFunctorScale
  rw [moduleObjectWeight_iso SM r (e.app _)]

lemma moduleFunctorScale_id (hr : 0 < r j₀) :
    moduleFunctorScale SM r j₀ (𝟭 M) = 1 := by
  simp [moduleFunctorScale, hr.ne']

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalLeftAction C M]
  [∀ c : C, (actionLeft M c).Additive]
  [∀ X : M, (actionRight C X).Additive]
  {ι : Type w} [Fintype ι] (SC : FiniteSemisimpleSkeleton C ι)
  (hconn : ∀ j k : κ, ∃ X : C, Nonempty (Retract (SM.simpleObject k) (X ⊙ₗ SM.simpleObject j)))
  (d : ι → ℝ) (hr : ∀ j, 0 < r j)
  (hR : ∀ a j, ∑ k, (moduleActionCoeff SC SM a j k : ℝ) * r k = d a * r j)

include hconn hr hR in
/-- The scaling law holds for all actual module functors, including zero. -/
theorem moduleFunctorScale_spec (F : M ⥤ M) [F.Additive] [F.LeftLinear C] (X : M) :
    moduleObjectWeight SM r (F.obj X) =
      moduleFunctorScale SM r j₀ F * moduleObjectWeight SM r X := by
  letI : Nonempty κ := ⟨j₀⟩
  by_cases hF : (𝟙 F : F ⟶ F) = 0
  · have hz (Y : M) : moduleObjectWeight SM r (F.obj Y) = 0 := by
      apply (moduleObjectWeight_eq_zero_iff SM r hr _).mpr
      apply (IsZero.iff_id_eq_zero _).mpr
      exact congrArg (fun τ : F ⟶ F => τ.app Y) hF
    simp only [moduleFunctorScale, hz, zero_div, zero_mul]
  · obtain ⟨c, _hc, hh⟩ := moduleFunctor_scales_weight SC SM hconn d r hr hR F hF
    have hc₀ := hh (SM.simpleObject j₀)
    rw [moduleObjectWeight_simple] at hc₀
    have hs : moduleFunctorScale SM r j₀ F = c := by
      simp only [moduleFunctorScale, hc₀, mul_div_cancel_right₀ _ (hr j₀).ne']
    rw [hs]
    exact hh X

include hconn hr hR in
/-- Nonzero actual module functors have a strictly positive derived factor. -/
lemma moduleFunctorScale_pos (F : M ⥤ M) [F.Additive] [F.LeftLinear C]
    (hF : (𝟙 F : F ⟶ F) ≠ 0) : 0 < moduleFunctorScale SM r j₀ F := by
  letI : Nonempty κ := ⟨j₀⟩
  apply div_pos _ (hr j₀)
  exact moduleFunctorWeight_pos SC SM hconn d r hr hR F hF j₀

include hconn hr hR in
/-- Actual composition multiplies the derived scaling factors. -/
lemma moduleFunctorScale_comp (F G : M ⥤ M)
    [F.Additive] [F.LeftLinear C] [G.Additive] [G.LeftLinear C] :
    moduleFunctorScale SM r j₀ (F ⋙ G) =
      moduleFunctorScale SM r j₀ F * moduleFunctorScale SM r j₀ G := by
  unfold moduleFunctorScale at ⊢
  change moduleObjectWeight SM r (G.obj (F.obj (SM.simpleObject j₀))) / r j₀ = _
  rw [moduleFunctorScale_spec SM r j₀ SC hconn d hr hR G,
    moduleFunctorScale_spec SM r j₀ SC hconn d hr hR F, moduleObjectWeight_simple]
  rw [mul_div_assoc, mul_div_cancel_right₀ _ (hr j₀).ne']
  dsimp only [moduleFunctorScale]
  ring

end Paper18.Category.ModuleFunctor
