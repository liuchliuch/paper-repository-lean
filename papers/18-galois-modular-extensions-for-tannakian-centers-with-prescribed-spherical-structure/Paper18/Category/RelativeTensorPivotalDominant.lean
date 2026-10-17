import Paper18.Category.RigidDoubleDual
import Mathlib.CategoryTheory.Retract

/-! # Detecting actual monoidal coherence on a retract-dominant image -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal
universe v u v' u'
namespace Paper18.Category.RelativeTensor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal] (G : D ⥤ D) [G.Monoidal]
  (τ : 𝟭 D ⟶ G) [NatTrans.IsMonoidal (Functor.whiskerLeft F τ)]

/-- Actual monoidal coherence on a strong monoidal retract-dominant image
implies actual monoidal coherence on the whole target. -/
theorem isMonoidal_of_retract_dominant
    (hF : ∀ X : D, ∃ Y : C, Nonempty (Retract X (F.obj Y))) :
    NatTrans.IsMonoidal τ where
  unit := by
    have h := NatTrans.IsMonoidal.unit (τ := Functor.whiskerLeft F τ)
    change (𝟙 _ ≫ ε F) ≫ τ.app (F.obj (𝟙_ C)) = ε G ≫ G.map (ε F) at h
    change 𝟙 _ ≫ τ.app (𝟙_ D) = ε G
    rw [id_comp]
    apply (cancel_mono (G.map (ε F))).mp
    rw [← τ.naturality (ε F)]
    simpa only [id_comp] using h
  tensor X Y := by
    change 𝟙 _ ≫ τ.app (X ⊗ Y) = _
    rw [id_comp]
    have hf (V W : C) : τ.app (F.obj V ⊗ F.obj W) =
        (τ.app (F.obj V) ⊗ₘ τ.app (F.obj W)) ≫ μ G (F.obj V) (F.obj W) := by
      have h := NatTrans.IsMonoidal.tensor (τ := Functor.whiskerLeft F τ) V W
      change (𝟙 _ ≫ μ F V W) ≫ τ.app (F.obj (V ⊗ W)) =
        (τ.app (F.obj V) ⊗ₘ τ.app (F.obj W)) ≫ μ G (F.obj V) (F.obj W) ≫
          G.map (μ F V W) at h
      apply (cancel_mono (G.map (μ F V W))).mp
      rw [← τ.naturality (μ F V W)]
      simpa only [id_comp, assoc, Functor.id_map] using h
    obtain ⟨V, ⟨R⟩⟩ := hF X
    obtain ⟨W, ⟨Q⟩⟩ := hF Y
    have he : Epi (R.r ⊗ₘ Q.r) := by
      let split : SplitEpi (R.r ⊗ₘ Q.r) :=
        ⟨R.i ⊗ₘ Q.i, by rw [tensorHom_comp_tensorHom, R.retract, Q.retract,
          tensorHom_id, id_whiskerRight]⟩
      exact split.epi
    letI := he
    apply (cancel_epi (R.r ⊗ₘ Q.r)).mp
    erw [τ.naturality (R.r ⊗ₘ Q.r), hf, assoc, ← Functor.LaxMonoidal.μ_natural,
      ← assoc, tensorHom_comp_tensorHom, ← τ.naturality R.r,
      ← τ.naturality Q.r, ← tensorHom_comp_tensorHom, assoc]
    rfl

end Paper18.Category.RelativeTensor
