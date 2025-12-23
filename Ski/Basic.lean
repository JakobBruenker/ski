import Ski.Util

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

/-- Convertibility: terms that reduce to a common reduct -/
def Conv (a b : Term) : Prop := ∃ c, (a ⟶* c) ∧ (b ⟶* c)

notation:50 a " ≈ " b => Conv a b

/-- Convertibility is reflexive -/
lemma Conv.refl : a ≈ a := ⟨a, Steps.refl, Steps.refl⟩

/-- Convertibility is symmetric -/
lemma Conv.symm {a b : Term} : (a ≈ b) → (b ≈ a) := fun ⟨c, hac, hbc⟩ => ⟨c, hbc, hac⟩

/-- Steps is transitive -/
lemma Steps.trans {a b c : Term} : (a ⟶* b) → (b ⟶* c) → (a ⟶* c) := by
  intro r₁ r₂
  induction r₁ with
  | refl => exact r₂
  | step s rest ih => exact Steps.step s (ih r₂)

/-- Congruence: reduce left side of application -/
lemma Steps.appL {t t' u : Term} : (t ⟶* t') → (t ⬝ u ⟶* t' ⬝ u) := by
  intro r
  induction r with
  | refl => exact Steps.refl
  | step s rest ih => exact Steps.step (Step.appL s) ih

/-- Congruence: reduce right side of application -/
lemma Steps.appR {t u u' : Term} : (u ⟶* u') → (t ⬝ u ⟶* t ⬝ u') := by
  intro r
  induction r with
  | refl => exact Steps.refl
  | step s rest ih => exact Steps.step (Step.appR s) ih

/-- Congruence: reduce both sides of application -/
lemma Steps.app {t t' u u' : Term} : (t ⟶* t') → (u ⟶* u') → (t ⬝ u ⟶* t' ⬝ u') := by
  intro rt ru
  exact Steps.trans (Steps.appL rt) (Steps.appR ru)

/-- Parallel reduction: reduce all redexes at once -/
inductive Par : Term → Term → Prop where
  | S : Par S S
  | K : Par K K
  | I : Par I I
  | app : Par t t' → Par u u' → Par (t ⬝ u) (t' ⬝ u')
  | s : Par x x' → Par y y' → Par z z' → Par (S ⬝ x ⬝ y ⬝ z) ((x' ⬝ z') ⬝ (y' ⬝ z'))
  | k : Par x x' → Par y y' → Par (K ⬝ x ⬝ y) x'
  | i : Par x x' → Par (I ⬝ x) x'

notation:50 t " ⇒ " t' => Par t t'

/-- Parallel reduction is reflexive -/
lemma Par.refl : t ⇒ t := by
  induction t with
  | S => exact Par.S
  | K => exact Par.K
  | I => exact Par.I
  | app t u iht ihu => exact Par.app iht ihu

/-- Single step implies parallel step -/
lemma Step.toPar : (t ⟶ t') → (t ⇒ t') := by
  intro h
  induction h with
  | s => exact Par.s Par.refl Par.refl Par.refl
  | k => exact Par.k Par.refl Par.refl
  | i => exact Par.i Par.refl
  | appL _ ih => exact Par.app ih Par.refl
  | appR _ ih => exact Par.app Par.refl ih

/-- Parallel step implies multi-step -/
lemma Par.toSteps : (t ⇒ t') → (t ⟶* t') := by
  intro h
  induction h with
  | S => exact Steps.refl
  | K => exact Steps.refl
  | I => exact Steps.refl
  | app _ _ iht ihu => exact Steps.app iht ihu
  | s _ _ _ ihx ihy ihz =>
    -- S x y z ⟶ (x z) (y z) ⟶* (x' z') (y' z')
    refine Steps.step Step.s ?_
    exact Steps.app (Steps.app ihx ihz) (Steps.app ihy ihz)
  | k _ _ ihx _ihy => exact Steps.step Step.k ihx
  | i _ ihx => exact Steps.step Step.i ihx

/-- Maximum parallel reduct -/
def maxPar : Term → Term
  | S => S
  | K => K
  | I => I
  | S ⬝ x ⬝ y ⬝ z => (maxPar x ⬝ maxPar z) ⬝ (maxPar y ⬝ maxPar z)
  | K ⬝ x ⬝ _y => maxPar x
  | I ⬝ x => maxPar x
  | t ⬝ u => maxPar t ⬝ maxPar u

/-- Triangle property: any parallel reduct goes to maxPar -/
lemma Par.triangle : (t : Term) → (h : t ⇒ t') → (t' ⇒ maxPar t)
  | .S, .S => Par.S
  | .K, .K => Par.K
  | .I, .I => Par.I
  | .app (.app (.app .S x) y) z, .s px py pz =>
    Par.app (Par.app (triangle x px) (triangle z pz)) (Par.app (triangle y py) (triangle z pz))
  | .app (.app .K x) _, .k px _ => triangle x px
  | .app .I x, .i px => triangle x px
  -- App cases: match on shape of t to determine if t ⬝ u is a redex
  | .app .S u, .app .S pu => Par.app Par.S (triangle u pu)
  | .app .K u, .app .K pu => Par.app Par.K (triangle u pu)
  | .app .I u, .app .I pu => Par.i (triangle u pu)  -- I-redex!
  | .app (.app .S x) u, .app (.app .S px) pu =>
    Par.app (Par.app Par.S (triangle x px)) (triangle u pu)
  | .app (.app .K x) u, .app (.app .K px) pu =>
    Par.k (triangle x px) (triangle u pu)  -- K-redex!
  | .app (.app .I x) u, .app pt pu =>
    Par.app (triangle (.app .I x) pt) (triangle u pu)
  | .app (.app (.app .S x) y) u, .app (.app (.app .S px) py) pu =>  -- S-redex!
    Par.s (triangle x px) (triangle y py) (triangle u pu)
  | .app (.app (.app .K x) y) u, .app pt pu =>
    Par.app (triangle (.app (.app .K x) y) pt) (triangle u pu)
  | .app (.app (.app .I x) y) u, .app pt pu =>
    Par.app (triangle (.app (.app .I x) y) pt) (triangle u pu)
  | .app (.app (.app (.app a b) c) d) u, .app pt pu =>
    Par.app (triangle (.app (.app (.app a b) c) d) pt) (triangle u pu)

/-- Strong diamond: parallel reduction has diamond property -/
lemma Par.diamond {t a b : Term} : (t ⇒ a) → (t ⇒ b) → ∃ c, (a ⇒ c) ∧ (b ⇒ c) := by
  intro ha hb
  exact ⟨maxPar t, Par.triangle _ ha, Par.triangle _ hb⟩

/-- Multi-step parallel reduction -/
inductive Pars : Term → Term → Prop where
  | refl : Pars t t
  | step : Par t t' → Pars t' t'' → Pars t t''

notation:50 t " ⇒* " t' => Pars t t'

/-- Pars is transitive -/
lemma Pars.trans {a b c : Term} : (a ⇒* b) → (b ⇒* c) → (a ⇒* c) := by
  intro r₁ r₂
  induction r₁ with
  | refl => exact r₂
  | step p rest ih => exact Pars.step p (ih r₂)

/-- Strip lemma: single step commutes past multi-step -/
lemma Par.strip {t a b : Term} : (t ⇒ a) → (t ⇒* b) → ∃ c, (a ⇒* c) ∧ (b ⇒ c) := by
  intro p r
  induction r generalizing a with
  | refl => exact ⟨a, Pars.refl, p⟩
  | step q rest ih =>
    obtain ⟨c₁, hac₁, htc₁⟩ := Par.diamond p q
    obtain ⟨c₂, hc₁c₂, hbc₂⟩ := ih htc₁
    exact ⟨c₂, Pars.step hac₁ hc₁c₂, hbc₂⟩

/-- Confluence for parallel reduction -/
lemma Pars.confluence {t a b : Term} : (t ⇒* a) → (t ⇒* b) → ∃ c, (a ⇒* c) ∧ (b ⇒* c) := by
  intro r₁ r₂
  induction r₁ generalizing b with
  | refl => exact ⟨b, r₂, Pars.refl⟩
  | step p rest ih =>
    obtain ⟨c₁, htc₁, hbc₁⟩ := Par.strip p r₂
    obtain ⟨c₂, hac₂, hc₁c₂⟩ := ih htc₁
    exact ⟨c₂, hac₂, Pars.step hbc₁ hc₁c₂⟩

/-- Convert Steps to Pars -/
lemma Steps.toPars : (t ⟶* t') → (t ⇒* t') := by
  intro h
  induction h with
  | refl => exact Pars.refl
  | step s _ ih => exact Pars.step s.toPar ih

/-- Convert Pars to Steps -/
lemma Pars.toSteps : (t ⇒* t') → (t ⟶* t') := by
  intro h
  induction h with
  | refl => exact Steps.refl
  | step p _ ih => exact Steps.trans p.toSteps ih

/-- Confluence (Church-Rosser): if t reduces to both a and b, they are convertible -/
theorem confluence {t a b : Term} : (t ⟶* a) → (t ⟶* b) → a ≈ b := by
  intro ha hb
  obtain ⟨c, hac, hbc⟩ := Pars.confluence ha.toPars hb.toPars
  exact ⟨c, hac.toSteps, hbc.toSteps⟩

/-- Convertibility is transitive (requires confluence) -/
lemma Conv.trans {a b c : Term} : (a ≈ b) → (b ≈ c) → (a ≈ c) := by
  intro ⟨ab, hab, hbb⟩ ⟨bc, hbc, hcc⟩
  obtain ⟨d, hbd, hbcd⟩ := confluence hbb hbc
  exact ⟨d, Steps.trans hab hbd, Steps.trans hcc hbcd⟩

/-- Convertibility is an equivalence relation -/
theorem Conv.equivalence : Equivalence Conv :=
  ⟨fun _ => Conv.refl, Conv.symm, Conv.trans⟩

/-- SKK behaves like I: both reduce any argument to itself -/
lemma skk_conv_i (x : Term) : (S ⬝ K ⬝ K ⬝ x) ≈ (I ⬝ x) := by
  -- S K K x ⟶ (K x) (K x) ⟶ x
  -- I x ⟶ x
  refine ⟨x, ?_, ?_⟩
  · exact Steps.step Step.s (Steps.step Step.k Steps.refl)
  · exact Steps.step Step.i Steps.refl

/-- Normal forms are unique -/
lemma normal_unique {t n m : Term} : (t ⟶* n) → (t ⟶* m) → IsNormal n → IsNormal m → n = m := by
  intro hn hm nn nm
  obtain ⟨c, hnc, hmc⟩ : n ≈ m := confluence hn hm
  cases hnc with
  | refl =>
    cases hmc with
    | refl => rfl
    | step s _ => exact absurd s (nm _)
  | step s _ => exact absurd s (nn _)

end Term
