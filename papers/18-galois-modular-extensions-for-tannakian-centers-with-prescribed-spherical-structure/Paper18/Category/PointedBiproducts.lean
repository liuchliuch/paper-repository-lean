import Paper18.Category.PointedBasic
import Mathlib.CategoryTheory.Preadditive.Biproducts

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators
open Classical

namespace Paper18.Category.PointedVec

instance : HasFiniteBiproducts (FGModuleCat ℂ) :=
  HasFiniteBiproducts.of_hasFiniteCoproducts

variable {A J : Type} [Fintype J] (F : J → PointedVec A)

/-- Finite direct sums of actual graded vector spaces are formed in each degree. -/
def gradedBicone : Bicone F where
  pt a := ⨁ fun j => F j a
  π j a := biproduct.π (fun j => F j a) j
  ι j a := biproduct.ι (fun j => F j a) j
  ι_π j k := by
    by_cases hjk : j = k
    · subst k
      funext a
      simp only [eqToHom_refl, comp_apply]
      change biproduct.ι (fun j => F j a) j ≫ biproduct.π (fun j => F j a) j = 𝟙 _
      simp
    · funext a
      simp only [dif_neg hjk, comp_apply]
      change biproduct.ι (fun j => F j a) j ≫ biproduct.π (fun j => F j a) k = 0
      simp [hjk]

def gradedBiconeIsBilimit : (gradedBicone F).IsBilimit where
  isLimit :=
    { lift := fun s a => biproduct.lift (fun j => s.π.app ⟨j⟩ a)
      fac := fun s j => by
        cases j with | mk j =>
          funext a
          change biproduct.lift (fun j => s.π.app ⟨j⟩ a) ≫
            biproduct.π (fun j => F j a) j = s.π.app ⟨j⟩ a
          exact biproduct.lift_π _ _
      uniq := fun s m hm => by
        funext a
        apply biproduct.hom_ext
        intro j
        change m a ≫ biproduct.π (fun j => F j a) j =
          biproduct.lift (fun j => s.π.app ⟨j⟩ a) ≫ biproduct.π (fun j => F j a) j
        exact (congrFun (hm ⟨j⟩) a).trans
          (biproduct.lift_π (fun j => s.π.app ⟨j⟩ a) j).symm }
  isColimit :=
    { desc := fun s a => biproduct.desc (fun j => s.ι.app ⟨j⟩ a)
      fac := fun s j => by
        cases j with | mk j =>
          funext a
          change biproduct.ι (fun j => F j a) j ≫
            biproduct.desc (fun j => s.ι.app ⟨j⟩ a) = s.ι.app ⟨j⟩ a
          exact biproduct.ι_desc _ _
      uniq := fun s m hm => by
        funext a
        apply biproduct.hom_ext'
        intro j
        change biproduct.ι (fun j => F j a) j ≫ m a =
          biproduct.ι (fun j => F j a) j ≫ biproduct.desc (fun j => s.ι.app ⟨j⟩ a)
        exact (congrFun (hm ⟨j⟩) a).trans
          (biproduct.ι_desc (fun j => s.ι.app ⟨j⟩ a) j).symm }

instance hasBiproduct : HasBiproduct F :=
  HasBiproduct.mk ⟨gradedBicone F, gradedBiconeIsBilimit F⟩

instance hasFiniteBiproducts : HasFiniteBiproducts (PointedVec A) where
  out _ := ⟨fun _ => inferInstance⟩

end Paper18.Category.PointedVec
