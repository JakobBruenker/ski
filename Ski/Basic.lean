/-- SKI Calculus terms -/
inductive Term where
  | S : Term
  | K : Term
  | I : Term
  | app : Term → Term → Term
  deriving Repr, DecidableEq

namespace Term

/-- Notation for application -/
infixl:100 " ⬝ " => app

/-- Single-step reduction relation for SKI calculus -/
inductive Step : Term → Term → Prop where
  | s : Step (S ⬝ x ⬝ y ⬝ z) ((x ⬝ z) ⬝ (y ⬝ z))
  | k : Step (K ⬝ x ⬝ y) x
  | i : Step (I ⬝ x) x
  | appL : Step t t' → Step (t ⬝ u) (t' ⬝ u)
  | appR : Step u u' → Step (t ⬝ u) (t ⬝ u')

notation:50 t " ⟶ " t' => Step t t'

/-- Multi-step reduction (reflexive transitive closure) -/
inductive Steps : Term → Term → Prop where
  | refl : Steps t t
  | step : Step t t' → Steps t' t'' → Steps t t''

notation:50 t " ⟶* " t' => Steps t t'

/-- A term is in normal form if no reduction applies -/
def IsNormal (t : Term) : Prop :=
  ∀ t', ¬ (t ⟶ t')

/-- I can be defined as S K K -/
theorem i_eq_skk : (S ⬝ K ⬝ K ⬝ x) ⟶ (I ⬝ x) := by
  have h1 : (S ⬝ K ⬝ K ⬝ x) ⟶ ((K ⬝ x) ⬝ (K ⬝ x)) := Step.s
  sorry -- Full proof would show (K ⬝ x) ⬝ (K ⬝ x) ⟶* x

end Term
