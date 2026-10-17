import Paper18.Category.Semisimple
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # The actual category of families of component objects

The components may be different categories.  Equality transport is an
actual functor between the corresponding fibers, rather than an equality
of numerical grading labels.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe w v u
namespace Paper18.Category.PicardGradedAssembly
variable {G : Type w} (C : G → Type u) [∀ g, Category.{v} (C g)]

/-- Objects and morphisms of the assembled category are genuine families. -/
abbrev Total := ∀ g, C g

instance totalPreadditive [∀ g, Preadditive (C g)] : Preadditive (Total C) where
  homGroup X Y := inferInstanceAs (AddCommGroup (∀ g, X g ⟶ Y g))
  add_comp _ _ _ f f' t := by funext g; exact Preadditive.add_comp _ _ _ _ _ _
  comp_add _ _ _ f t t' := by funext g; exact Preadditive.comp_add _ _ _ _ _ _

instance totalLinear [∀ g, Preadditive (C g)] [∀ g, Linear ℂ (C g)] :
    Linear ℂ (Total C) where
  homModule X Y := inferInstanceAs (Module ℂ (∀ g, X g ⟶ Y g))
  smul_comp _ _ _ r f t := by funext g; exact Linear.smul_comp _ _ _ _ _ _
  comp_smul _ _ _ f r t := by funext g; exact Linear.comp_smul _ _ _ _ _ _

@[simp] lemma total_add_apply [∀ g, Preadditive (C g)] {X Y : Total C}
    (f t : X ⟶ Y) (g : G) : (f+t) g = f g + t g := rfl

@[simp] lemma total_smul_apply [∀ g, Preadditive (C g)] [∀ g, Linear ℂ (C g)]
    {X Y : Total C} (r : ℂ) (f : X ⟶ Y) (g : G) : (r • f) g = r • f g := rfl

instance evalAdditive [∀ g, Preadditive (C g)] (g : G) : (Pi.eval C g).Additive where
  map_add := rfl
instance evalLinear [∀ g, Preadditive (C g)] [∀ g, Linear ℂ (C g)] (g : G) :
    (Pi.eval C g).Linear ℂ where
  map_smul _ _ := rfl

/-- Actual equality transport between component categories. -/
def transport {g h : G} (e : g = h) : C g ⥤ C h := by
  subst h
  exact 𝟭 _

@[simp] lemma transport_refl (g : G) : transport C (rfl : g = g) = 𝟭 (C g) := rfl

instance transportAdditive [∀ g, Preadditive (C g)] {g h : G} (e : g = h) :
    (transport C e).Additive := by subst h; change (𝟭 (C g)).Additive; infer_instance
instance transportLinear [∀ g, Preadditive (C g)] [∀ g, Linear ℂ (C g)]
    {g h : G} (e : g = h) : (transport C e).Linear ℂ := by subst h; change (𝟭 (C g)).Linear ℂ; infer_instance

variable [∀ g, Preadditive (C g)] [∀ g, HasFiniteBiproducts (C g)]

/-- The finite biproduct bicone is assembled component by component. -/
def totalBicone {J : Type} [Finite J] (F : J → Total C) : Bicone F where
  pt g := ⨁ fun j => F j g
  π j g := biproduct.π (fun j => F j g) j
  ι j g := biproduct.ι (fun j => F j g) j
  ι_π i j := by
    funext g
    by_cases h : i = j
    · subst j; simp
    · simp only [dif_neg h]
      change biproduct.ι (fun j => F j g) i ≫ biproduct.π (fun j => F j g) j = 0
      exact biproduct.ι_π_ne _ h

/-- Both universal properties hold for the actual family bicone. -/
def totalBiconeIsBilimit {J : Type} [Finite J] (F : J → Total C) :
    (totalBicone C F).IsBilimit where
  isLimit :=
    { lift := fun s g => biproduct.lift (fun j => s.π.app ⟨j⟩ g)
      fac := fun s j => by funext g; exact biproduct.lift_π _ j.as
      uniq := fun s m h => by
        funext g
        apply biproduct.hom_ext
        intro j
        simpa using congrFun (h ⟨j⟩) g }
  isColimit :=
    { desc := fun s g => biproduct.desc (fun j => s.ι.app ⟨j⟩ g)
      fac := fun s j => by funext g; exact biproduct.ι_desc _ j.as
      uniq := fun s m h => by
        funext g
        apply biproduct.hom_ext'
        intro j
        simpa using congrFun (h ⟨j⟩) g }

instance totalHasFiniteBiproducts : HasFiniteBiproducts (Total C) where
  out _n := ⟨fun F => HasBiproduct.mk ⟨totalBicone C F, totalBiconeIsBilimit C F⟩⟩

instance totalFiniteHom [Fintype G] [∀ g, Linear ℂ (C g)]
    [∀ g (X Y : C g), FiniteDimensional ℂ (X ⟶ Y)] (X Y : Total C) : FiniteDimensional ℂ (X ⟶ Y) :=
  inferInstanceAs (FiniteDimensional ℂ (∀ g, X g ⟶ Y g))

end Paper18.Category.PicardGradedAssembly
