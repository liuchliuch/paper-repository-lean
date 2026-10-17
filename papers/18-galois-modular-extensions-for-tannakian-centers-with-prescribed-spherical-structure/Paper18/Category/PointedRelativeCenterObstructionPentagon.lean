import Paper18.Category.PointedRelativeCenterObstructionBasic
import Paper18.Category.QuasiFusionPentagon
import Paper18.Category.CrossedExtensionCochain

/-! # The actual cochain pentagon defect on quotient-coset objects -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
namespace Paper18.Category.PointedRelativeCenterObstruction
open FiniteCohomologyKilling QuasiFusion GradedObject.Monoidal
variable {Γ G : Type} [Group Γ] [Fintype Γ] [Group G] (p : Γ →* G)
  (ψ : ThreeCochain Γ ℂˣ) (ω : FourCocycle G ℂˣ)
local notation "V" => PointedVec (Additive Γ)
local notation "r" => (fun (a b c : Additive Γ) => ψ.val (Additive.toMul a) (Additive.toMul b) (Additive.toMul c))

set_option maxHeartbeats 2000000 in
/-- The inverse cochain associators have exactly inverse fourth-cocycle
defect on actual coset-supported convolution objects. -/
lemma quasiAssociator_pentagon_inv_on_support
    (hψ : ∀ a b c d, dThree ψ.val a b c d = ω.val (p a) (p b) (p c) (p d))
    {g0 g1 g2 g3 : G} (W X Y Z : V)
    (hW : Supported p g0 W) (hX : Supported p g1 X)
    (hY : Supported p g2 Y) (hZ : Supported p g3 Z) :
    W ◁ (quasiAssociator ψ X Y Z).inv ≫
      (quasiAssociator ψ W (X ⊗ Y) Z).inv ≫
        (quasiAssociator ψ W X Y).inv ▷ Z =
      (((ω.val g0 g1 g2 g3)⁻¹ : ℂˣ) : ℂ) •
        ((quasiAssociator ψ W X (Y ⊗ Z)).inv ≫
          (quasiAssociator ψ (W ⊗ X) Y Z).inv) := by
  apply GradedObject.hom_ext
  intro j
  apply tensorObj₄_ext (X₁ := W) (X₂ := X) (X₃ := Y) (X₄ := Z)
  intro a b c d h
  by_cases ha : p a.toMul = g0
  swap
  · exact ((tensorRight (X b ⊗ (Y c ⊗ Z d))).map_isZero (hW a ha)).eq_of_src _ _
  by_cases hb : p b.toMul = g1
  swap
  · exact ((tensorLeft (W a)).map_isZero
      ((tensorRight (Y c ⊗ Z d)).map_isZero (hX b hb))).eq_of_src _ _
  by_cases hc : p c.toMul = g2
  swap
  · exact ((tensorLeft (W a)).map_isZero
      ((tensorLeft (X b)).map_isZero
        ((tensorRight (Z d)).map_isZero (hY c hc)))).eq_of_src _ _
  by_cases hd' : p d.toMul = g3
  swap
  · exact ((tensorLeft (W a)).map_isZero
      ((tensorLeft (X b)).map_isZero
        ((tensorLeft (Y c)).map_isZero (hZ d hd')))).eq_of_src _ _
  change ιTensorObj₄ W X Y Z a b c d j h ≫
      (GradedObject.Monoidal.tensorHom (𝟙 W) (scalarAssociator r X Y Z).inv j ≫
        (scalarAssociator r W (GradedObject.Monoidal.tensorObj X Y) Z).inv j ≫
        GradedObject.Monoidal.tensorHom (scalarAssociator r W X Y).inv (𝟙 Z) j) =
    ιTensorObj₄ W X Y Z a b c d j h ≫
      ((((ω.val g0 g1 g2 g3)⁻¹ : ℂˣ) : ℂ) •
        ((scalarAssociator r W X (GradedObject.Monoidal.tensorObj Y Z)).inv j ≫
          (scalarAssociator r (GradedObject.Monoidal.tensorObj W X) Y Z).inv j))
  rw [Linear.comp_smul]
  dsimp only [PointedVec.instMonoidalCategory, GradedObject.monoidalCategory]
  conv_lhs =>
    rw [ιTensorObj₄_eq W X Y Z a b c d j h _ rfl, assoc, ι_tensorHom_assoc]
    dsimp only [PointedVec.id_apply, GradedObject.categoryOfGradedObjects_id, id_eq, eq_mpr_eq_cast, cast_eq]
    rw [MonoidalCategory.id_tensorHom, ← MonoidalCategory.whiskerLeft_comp_assoc,
      inclusion_scalarAssociator_inv]
    simp only [MonoidalLinear.whiskerLeft_smul, Linear.smul_comp, Linear.comp_smul, assoc]
    rw [ιTensorObj₃'_eq X Y Z b c d _ rfl _ rfl,
      MonoidalCategory.whiskerLeft_comp_assoc, MonoidalCategory.whiskerLeft_comp_assoc]
    rw [← ιTensorObj₃_eq_assoc W (GradedObject.Monoidal.tensorObj X Y) Z a (b + c) d j
        (by simp only [← add_assoc, h]) (b + c + d) rfl
          ((scalarAssociator r W (GradedObject.Monoidal.tensorObj X Y) Z).inv j ≫
            GradedObject.Monoidal.tensorHom (scalarAssociator r W X Y).inv (𝟙 Z) j),
      inclusion_scalarAssociator_inv_assoc]
    simp only [Linear.smul_comp, Linear.comp_smul, assoc]
    rw [ιTensorObj₃'_eq_assoc W (GradedObject.Monoidal.tensorObj X Y) Z a (b + c) d j
        (by simp only [← add_assoc, h]) (a + b + c) (by rw [add_assoc]), ι_tensorHom]
    dsimp only [id_eq, eq_mpr_eq_cast, PointedVec.id_apply, GradedObject.categoryOfGradedObjects_id]
    rw [MonoidalCategory.tensorHom_id, whisker_assoc_symm_assoc, Iso.hom_inv_id_assoc,
      ← MonoidalCategory.comp_whiskerRight_assoc, ← MonoidalCategory.comp_whiskerRight_assoc,
      ← ιTensorObj₃_eq W X Y a b c _ rfl _ rfl, inclusion_scalarAssociator_inv]
    simp only [MonoidalLinear.smul_whiskerRight, Linear.smul_comp, Linear.comp_smul, assoc]
    rw [MonoidalCategory.comp_whiskerRight_assoc, MonoidalCategory.pentagon_inv_assoc]
  conv_rhs =>
    rw [ιTensorObj₄_eq W X Y Z a b c d _ _ _ rfl,
      ιTensorObj₃_eq X Y Z b c d _ rfl _ rfl, assoc,
      MonoidalCategory.whiskerLeft_comp_assoc,
      ← ιTensorObj₃_eq_assoc W X (GradedObject.Monoidal.tensorObj Y Z) a b (c + d) j
        (by rw [← add_assoc, h]) (b + c + d) (by rw [add_assoc]),
      inclusion_scalarAssociator_inv_assoc]
    simp only [Linear.smul_comp, Linear.comp_smul, assoc]
    rw [associator_inv_naturality_right_assoc,
      ιTensorObj₃'_eq_assoc W X (GradedObject.Monoidal.tensorObj Y Z) a b (c + d) j
        (by rw [← add_assoc, h]) _ rfl, whisker_exchange_assoc,
      ← ιTensorObj₃_eq_assoc (GradedObject.Monoidal.tensorObj W X) Y Z (a + b) c d j h _ rfl,
      inclusion_scalarAssociator_inv]
    simp only [Linear.smul_comp, Linear.comp_smul, assoc]
    rw [whiskerRight_tensor_assoc, Iso.hom_inv_id_assoc,
      ιTensorObj₃'_eq (GradedObject.Monoidal.tensorObj W X) Y Z (a + b) c d j h _ rfl,
      ← MonoidalCategory.comp_whiskerRight_assoc,
      ← ιTensorObj₃'_eq W X Y a b c _ rfl _ rfl]
  simp only [smul_smul]
  congr 1
  have hd := hψ a.toMul b.toMul c.toMul d.toMul
  rw [ha, hb, hc, hd'] at hd
  have hs :
      (ψ.val b.toMul c.toMul d.toMul)⁻¹ *
          (ψ.val a.toMul (b.toMul * c.toMul) d.toMul)⁻¹ *
          (ψ.val a.toMul b.toMul c.toMul)⁻¹ =
        (ω.val g0 g1 g2 g3)⁻¹ *
          (ψ.val a.toMul b.toMul (c.toMul * d.toMul))⁻¹ *
          (ψ.val (a.toMul * b.toMul) c.toMul d.toMul)⁻¹ := by
    apply Additive.ofMul.injective
    have he := congrArg Additive.ofMul hd
    simp only [dThree, ofMul_mul, ofMul_inv] at he
    simp only [ofMul_mul, ofMul_inv]
    apply sub_eq_zero.mp
    calc
      _ = -(Additive.ofMul (dThree ψ.val a.toMul b.toMul c.toMul d.toMul) -
          Additive.ofMul (ω.val g0 g1 g2 g3)) := by
        simp only [dThree, ofMul_mul, ofMul_inv]
        abel
      _ = 0 := by rw [hd]; simp
  simpa only [Units.val_mul, mul_comm, mul_left_comm,
    mul_assoc] using congrArg (fun z : ℂˣ => (z : ℂ)) hs

/-- Inversion reverses the actual scalar defect of actual isomorphisms. -/
lemma iso_hom_eq_smul_of_inv_eq {E : Type*} [Category E] [Preadditive E] [Linear ℂ E]
    {A B : E} (L R : A ≅ B) (s : ℂˣ)
    (h : L.inv = ((s⁻¹ : ℂˣ) : ℂ) • R.inv) : L.hom = (s : ℂ) • R.hom := by
  have hh := congrArg (fun f => L.hom ≫ f ≫ R.hom) h
  simp only [Iso.hom_inv_id_assoc, Linear.comp_smul, Linear.smul_comp,
    Iso.inv_hom_id, Category.comp_id] at hh
  have hs := congrArg (fun f => (s : ℂ) • f) hh
  simpa only [smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    one_smul] using hs.symm

/-- The actual positive convolution associators have precisely the
actual fourth-cocycle defect on their actual quotient-coset degrees. -/
lemma quasiAssociator_pentagon_on_support
    (hψ : ∀ a b c d, dThree ψ.val a b c d = ω.val (p a) (p b) (p c) (p d))
    {g0 g1 g2 g3 : G} (W X Y Z : V)
    (hW : Supported p g0 W) (hX : Supported p g1 X)
    (hY : Supported p g2 Y) (hZ : Supported p g3 Z) :
    (quasiAssociator ψ W X Y).hom ▷ Z ≫
      (quasiAssociator ψ W (X ⊗ Y) Z).hom ≫
        W ◁ (quasiAssociator ψ X Y Z).hom =
      (ω.val g0 g1 g2 g3 : ℂ) •
        ((quasiAssociator ψ (W ⊗ X) Y Z).hom ≫
          (quasiAssociator ψ W X (Y ⊗ Z)).hom) := by
  let L : ((W ⊗ X) ⊗ Y) ⊗ Z ≅ W ⊗ (X ⊗ (Y ⊗ Z)) :=
    whiskerRightIso (quasiAssociator ψ W X Y) Z ≪≫
      quasiAssociator ψ W (X ⊗ Y) Z ≪≫ whiskerLeftIso W (quasiAssociator ψ X Y Z)
  let R : ((W ⊗ X) ⊗ Y) ⊗ Z ≅ W ⊗ (X ⊗ (Y ⊗ Z)) :=
    quasiAssociator ψ (W ⊗ X) Y Z ≪≫ quasiAssociator ψ W X (Y ⊗ Z)
  exact iso_hom_eq_smul_of_inv_eq L R (ω.val g0 g1 g2 g3)
    (quasiAssociator_pentagon_inv_on_support p ψ ω hψ W X Y Z hW hX hY hZ)

/-- Every actual pentagon with a neutral-coset entry commutes. -/
lemma quasiAssociator_mixed_pentagon
    (hψ : ∀ a b c d, dThree ψ.val a b c d = ω.val (p a) (p b) (p c) (p d))
    {g0 g1 g2 g3 : G} (W X Y Z : V)
    (hW : Supported p g0 W) (hX : Supported p g1 X)
    (hY : Supported p g2 Y) (hZ : Supported p g3 Z)
    (hn : g0 = 1 ∨ g1 = 1 ∨ g2 = 1 ∨ g3 = 1) :
    (quasiAssociator ψ W X Y).hom ▷ Z ≫
      (quasiAssociator ψ W (X ⊗ Y) Z).hom ≫
        W ◁ (quasiAssociator ψ X Y Z).hom =
      (quasiAssociator ψ (W ⊗ X) Y Z).hom ≫
        (quasiAssociator ψ W X (Y ⊗ Z)).hom := by
  have hh := quasiAssociator_pentagon_on_support p ψ ω hψ W X Y Z hW hX hY hZ
  rcases hn with hn | hn | hn | hn <;> simpa only [hn, FourCocycle.one₁,
    FourCocycle.one₂, FourCocycle.one₃, FourCocycle.one₄, Units.val_one, one_smul] using hh

section ConstructedFinitePrimitive
variable [Fintype G]
local instance : Fintype (KillingExtension G) := killingExtensionFintype

set_option maxHeartbeats 2000000 in
/-- The constructed finite primitive supplies the actual defect equation
without a pentagon-defect or obstruction-sign premise. -/
lemma finitePrimitive_pentagon_on_support (ω : FourCocycle G ℂˣ)
    {g0 g1 g2 g3 : G} (W X Y Z : PointedVec (Additive (KillingExtension G)))
    (hW : Supported (UniversalExtension.projection (G := G) (R := ZMod (Fintype.card G))) g0 W)
    (hX : Supported (UniversalExtension.projection (G := G) (R := ZMod (Fintype.card G))) g1 X)
    (hY : Supported (UniversalExtension.projection (G := G) (R := ZMod (Fintype.card G))) g2 Y)
    (hZ : Supported (UniversalExtension.projection (G := G) (R := ZMod (Fintype.card G))) g3 Z) :
    (quasiAssociator ω.finitePrimitive W X Y).hom ▷ Z ≫
      (quasiAssociator ω.finitePrimitive W (X ⊗ Y) Z).hom ≫
        W ◁ (quasiAssociator ω.finitePrimitive X Y Z).hom =
      (ω.val g0 g1 g2 g3 : ℂ) •
        ((quasiAssociator ω.finitePrimitive (W ⊗ X) Y Z).hom ≫
          (quasiAssociator ω.finitePrimitive W X (Y ⊗ Z)).hom) :=
  quasiAssociator_pentagon_on_support
    (UniversalExtension.projection (G := G) (R := ZMod (Fintype.card G))) ω.finitePrimitive ω
    (fun a b c d => ω.finitePrimitive_spec a b c d) W X Y Z hW hX hY hZ
end ConstructedFinitePrimitive

end Paper18.Category.PointedRelativeCenterObstruction
