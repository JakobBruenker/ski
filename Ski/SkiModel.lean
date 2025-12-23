/-
  SKI Calculus as a Computational Model

  Shows that SKI satisfies the ComputationalModel structure,
  making the generic Rice theorem applicable.
-/

import Ski.Model
import Ski.Basic
import Ski.Combinator
import Ski.Quote

namespace Term

/-! ## Convertibility properties -/

/-- Reduction implies convertibility -/
theorem steps_to_conv {a b : Term} (h : a ⟶* b) : a ≈ b :=
  ⟨b, h, Steps.refl⟩

/-- Application preserves convertibility on the left -/
theorem conv_appL {t t' u : Term} (h : t ≈ t') : (t ⬝ u) ≈ (t' ⬝ u) := by
  obtain ⟨c, htc, ht'c⟩ := h
  exact ⟨c ⬝ u, Steps.appL htc, Steps.appL ht'c⟩

/-- Application preserves convertibility on the right -/
theorem conv_appR {t u u' : Term} (h : u ≈ u') : (t ⬝ u) ≈ (t ⬝ u') := by
  obtain ⟨c, huc, hu'c⟩ := h
  exact ⟨t ⬝ c, Steps.appR huc, Steps.appR hu'c⟩

/-- tru x y ≈ x -/
theorem tru_conv (x y : Term) : (tru ⬝ x ⬝ y) ≈ x :=
  steps_to_conv (tru_red x y)

/-- fls x y ≈ y -/
theorem fls_conv (x y : Term) : (fls ⬝ x ⬝ y) ≈ y :=
  steps_to_conv (fls_red x y)

/-- S x y z ≈ (x z) (y z) -/
theorem s_conv (x y z : Term) : (S ⬝ x ⬝ y ⬝ z) ≈ ((x ⬝ z) ⬝ (y ⬝ z)) :=
  steps_to_conv (Steps.step Step.s Steps.refl)

/-- K x y ≈ x -/
theorem k_conv (x y : Term) : (K ⬝ x ⬝ y) ≈ x :=
  steps_to_conv (Steps.step Step.k Steps.refl)

/-! ## SKI as ComputationalModel -/

/-- SKI calculus as a computational model -/
def skiModel : ComputationalModel where
  Prog := Term
  equiv := Conv
  equiv_refl := fun _ => Conv.refl
  equiv_symm := fun _ _ => Conv.symm
  equiv_trans := fun _ _ _ => Conv.trans
  app := Term.app
  app_congr_left := fun _ _ _ h => conv_appL h
  app_congr_right := fun _ _ _ h => conv_appR h
  tru := tru
  fls := fls
  tru_select := tru_conv
  fls_select := fls_conv
  tru_ne_fls := tru_ne_fls
  encode := quote
  kleene := kleene
  S := S
  K := K
  S_red := s_conv
  K_red := k_conv

/-! ## Rice for SKI via the abstract theorem -/

/-- Rice's theorem for SKI, derived from the generic theorem -/
theorem ski_rice (P : Term → Prop)
    (hsem : skiModel.IsSemantic P)
    (hnt : skiModel.IsNontrivial P) :
    ¬skiModel.IsDecidable P :=
  ComputationalModel.rice skiModel P hsem hnt

end Term
