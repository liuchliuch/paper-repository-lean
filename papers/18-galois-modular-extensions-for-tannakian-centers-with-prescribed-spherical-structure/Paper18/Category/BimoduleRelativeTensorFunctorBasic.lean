import Paper18.Category.BimoduleRelativeTensorQuotient

/-! # Actual relative tensor functors on left internal modules -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u
namespace Paper18.Category.BimoduleRelativeTensor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
variable {S : D} [MonObj S]

/-- A left module has its actual right unit action, with no choice of
braiding or additional algebra structure. -/
def leftModuleBimod (N : Mod_ D S) : Bimod (Mon.mk S) (Mon.mk (𝟙_ D)) where
  X := N.X
  actLeft := γ[S,N.X]
  one_actLeft := ModObj.one_smul (M := S) N.X
  left_assoc := ModObj.mul_smul (M := S) N.X
  actRight := (ρ_ N.X).hom
  actRight_one := by change N.X ◁ 𝟙 _ ≫ (ρ_ N.X).hom = _; simp
  right_assoc := by
    change N.X ◁ (λ_ (𝟙_ D)).hom ≫ (ρ_ N.X).hom =
      (α_ N.X (𝟙_ D) (𝟙_ D)).inv ≫ (ρ_ N.X).hom ▷ _ ≫ (ρ_ N.X).hom
    monoidal
  middle_assoc := by monoidal

/-- Left modules are native bimodules with the trivial right unit action. -/
def moduleAsNative (N : Mod_ D S) : Native S (𝟙_ D) :=
  fromBimodObj S (𝟙_ D) (leftModuleBimod N)

def moduleAsNativeFunctor : Mod_ D S ⥤ Native S (𝟙_ D) where
  obj := moduleAsNative
  map f := (fromBimod S (𝟙_ D)).map
    { hom := f.hom
      left_act_hom := f.isMod_Hom.smul_hom
      right_act_hom := (rightUnitor_naturality f.hom).symm }
  map_id _ := by apply Mod_.Hom.ext; apply Mod_.Hom.ext; rfl
  map_comp _ _ := by apply Mod_.Hom.ext; apply Mod_.Hom.ext; rfl

variable [HasCoequalizers D] [LeftRigidCategory D] [RightRigidCategory D]
  {R : D} [MonObj R] (P : Native R S)

/-- The actual functor P tensor over S, obtained by the actual balancing
coequalizer and its actual inherited left R action. -/
def tensorFunctor : Mod_ D S ⥤ Mod_ D R where
  obj N := (tensor P (moduleAsNative N)).X
  map f := (whiskerLeft P (moduleAsNativeFunctor.map f)).hom
  map_id N := by
    apply Mod_.Hom.ext
    exact congrArg Bimod.Hom.hom (Bimod.whiskerLeft_id_bimod
      (M := toBimodObj R S P) (N := leftModuleBimod N))
  map_comp f g := by
    apply Mod_.Hom.ext
    exact congrArg Bimod.Hom.hom (Bimod.whiskerLeft_comp_bimod
      (toBimodObj R S P)
      ((toBimod S (𝟙_ D)).map (moduleAsNativeFunctor.map f))
      ((toBimod S (𝟙_ D)).map (moduleAsNativeFunctor.map g)))

/-- The actual ambient balancing quotient into the actual relative
tensor functor. -/
def moduleπ (N : Mod_ D S) : P.X.X ⊗ N.X ⟶ ((tensorFunctor P).obj N).X :=
  π P (moduleAsNative N)

instance moduleπ_epi (N : Mod_ D S) : Epi (moduleπ P N) := by
  unfold moduleπ
  infer_instance

@[reassoc (attr := simp)]
lemma moduleπ_map {N N' : Mod_ D S} (f : N ⟶ N') :
    moduleπ P N ≫ ((tensorFunctor P).map f).hom =
      P.X.X ◁ f.hom ≫ moduleπ P N' :=
  π_whiskerLeft P (moduleAsNativeFunctor.map f)

@[reassoc]
lemma moduleπ_condition (N : Mod_ D S) :
    γ[mop S,P.X].hom ▷ N.X ≫ moduleπ P N =
      (α_ P.X.X S N.X).hom ≫ P.X.X ◁ γ[S,N.X] ≫ moduleπ P N :=
  condition P (moduleAsNative N)

end Paper18.Category.BimoduleRelativeTensor
