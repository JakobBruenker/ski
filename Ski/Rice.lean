import Ski.Basic
import Ski.Combinator

namespace Term

/-! ## Halting -/

/-- A term halts if it reduces to a normal form -/
def Halts (t : Term) : Prop := ∃ n, IsNormal n ∧ (t ⟶* n)

/-- I is in normal form -/
lemma i_normal : IsNormal I := by
  intro t' h
  cases h

/-- I halts (it's already in normal form) -/
lemma i_halts : Halts I := ⟨I, i_normal, Steps.refl⟩

/-- Ω does not halt -/
lemma omega_diverges : ¬Halts Ω := by
  intro ⟨n, hn, hred⟩
  -- n is reachable from Ω, so n is OmegaLike
  have hol : OmegaLike n := OmegaLike.reachable hred
  -- But OmegaLike terms are not normal
  exact hol.not_normal hn

/-! ## Semantic Properties -/

/-- A property is semantic if it respects convertibility -/
def IsSemantic (P : Term → Prop) : Prop :=
  ∀ t t', (t ≈ t') → (P t ↔ P t')

/-- Halts is a semantic property -/
lemma halts_semantic : IsSemantic Halts := by
  intro t t' hconv
  constructor
  · -- Halts t → Halts t'
    intro ⟨n, hn, htn⟩
    obtain ⟨c, htc, ht'c⟩ := hconv
    -- By confluence on t: t ⟶* n and t ⟶* c, so ∃d, n ⟶* d and c ⟶* d
    obtain ⟨d, hnd, hcd⟩ := confluence htn htc
    -- n is normal, so n ⟶* d means d = n
    cases hnd with
    | refl =>
      -- d = n, so c ⟶* n
      -- t' ⟶* c ⟶* n
      exact ⟨n, hn, Steps.trans ht'c hcd⟩
    | step s _ =>
      -- n ⟶ something, contradicts n being normal
      exact absurd s (hn _)
  · -- Halts t' → Halts t (symmetric)
    intro ⟨n, hn, ht'n⟩
    obtain ⟨c, htc, ht'c⟩ := hconv
    obtain ⟨d, hnd, hcd⟩ := confluence ht'n ht'c
    cases hnd with
    | refl => exact ⟨n, hn, Steps.trans htc hcd⟩
    | step s _ => exact absurd s (hn _)

/-! ## Decidability -/

/-- A term d decides property P if d t reduces to tru when P t, and fls otherwise -/
def Decides (d : Term) (P : Term → Prop) : Prop :=
  ∀ t, (P t → d ⬝ t ⟶* tru) ∧ (¬P t → d ⬝ t ⟶* fls)

/-- A property is decidable if some term decides it -/
def IsDecidable (P : Term → Prop) : Prop := ∃ d, Decides d P

/-! ## Rice's Theorem (Behavioral Version) -/

/-- Behavioral Rice's theorem: no non-trivial semantic property is decidable -/
theorem behavioral_rice (P : Term → Prop)
    (hsem : IsSemantic P)
    {t f : Term}
    (ht : P t)
    (hf : ¬P f) :
    ¬IsDecidable P := by
  intro ⟨d, hdec⟩
  -- Construct g = λx. (d x) f t
  -- In SKI: g = S (S d (K f)) (K t)
  let g := S ⬝ (S ⬝ d ⬝ (K ⬝ f)) ⬝ (K ⬝ t)
  -- Let x = Θ g (fixed point)
  let x := Θ ⬝ g
  -- Key: x ⟶* g x = (d x) f t
  have hxgx : x ⟶* g ⬝ x := theta_unfold g
  -- g x = S (S d (K f)) (K t) x ⟶* (d x) f t
  have hgx_red : g ⬝ x ⟶* (d ⬝ x) ⬝ f ⬝ t := by
    -- S (S d (K f)) (K t) x ⟶ ((S d (K f)) x) ((K t) x)
    -- = ((S d (K f)) x) t  [since (K t) x ⟶ t]
    -- (S d (K f)) x ⟶ (d x) ((K f) x) = (d x) f
    -- So g x ⟶* (d x) f t
    refine Steps.step Step.s ?_
    refine Steps.step (Step.appR Step.k) ?_
    refine Steps.step (Step.appL Step.s) ?_
    exact Steps.step (Step.appL (Step.appR Step.k)) Steps.refl
  -- Now case split on P x
  by_cases hPx : P x
  · -- Case P x
    -- Then d x ⟶* tru = K
    have hdx : d ⬝ x ⟶* tru := (hdec x).1 hPx
    -- So (d x) f t ⟶* K f t ⟶* f
    have hgx_f : g ⬝ x ⟶* f := by
      refine Steps.trans hgx_red ?_
      refine Steps.trans (Steps.appL (Steps.appL hdx)) ?_
      exact tru_red f t
    -- x ⟶* g x ⟶* f, so x ≈ f
    have hxf : x ≈ f := ⟨f, Steps.trans hxgx hgx_f, Steps.refl⟩
    -- By semanticity, P f ↔ P x, so P f
    have hPf : P f := (hsem x f hxf).1 hPx
    -- Contradiction with hf : ¬P f
    exact hf hPf
  · -- Case ¬P x
    -- Then d x ⟶* fls = K I
    have hdx : d ⬝ x ⟶* fls := (hdec x).2 hPx
    -- So (d x) f t ⟶* (K I) f t ⟶* t
    have hgx_t : g ⬝ x ⟶* t := by
      refine Steps.trans hgx_red ?_
      refine Steps.trans (Steps.appL (Steps.appL hdx)) ?_
      exact fls_red f t
    -- x ⟶* g x ⟶* t, so x ≈ t
    have hxt : x ≈ t := ⟨t, Steps.trans hxgx hgx_t, Steps.refl⟩
    -- By semanticity, P t ↔ P x, so P x (since P t)
    have hPx' : P x := (hsem t x (Conv.symm hxt)).1 ht
    -- Contradiction
    exact hPx hPx'

/-! ## Halting is Undecidable -/

/-- The halting problem is undecidable -/
theorem halting_undecidable : ¬IsDecidable Halts :=
  behavioral_rice Halts halts_semantic i_halts omega_diverges

/-! ## Equivalence is Undecidable -/

/-- K is in normal form -/
lemma k_normal : IsNormal K := by
  intro t' h
  cases h

/-- Normal forms can't reduce further -/
lemma normal_steps_eq {t t' : Term} (hn : IsNormal t) (h : t ⟶* t') : t = t' := by
  cases h with
  | refl => rfl
  | step s _ => exact absurd s (hn _)

/-- I and K are not convertible -/
lemma i_not_conv_k : ¬(I ≈ K) := by
  intro ⟨c, hic, hkc⟩
  have hi : I = c := normal_steps_eq i_normal hic
  have hk : K = c := normal_steps_eq k_normal hkc
  rw [← hi] at hk
  cases hk

/-- Convertibility to a fixed term is a semantic property -/
lemma conv_semantic (t : Term) : IsSemantic (· ≈ t) := by
  intro a b hab
  constructor
  · intro hat
    exact Conv.trans (Conv.symm hab) hat
  · intro hbt
    exact Conv.trans hab hbt

/-- Equivalence with any fixed term is undecidable -/
theorem equiv_undecidable (t : Term) : ¬IsDecidable (· ≈ t) := by
  by_cases h : t ≈ I
  · -- t ≈ I, so use K as negative witness
    have hneg : ¬(K ≈ t) := by
      intro hkt
      have : I ≈ K := Conv.trans (Conv.symm h) (Conv.symm hkt)
      exact i_not_conv_k this
    exact behavioral_rice (· ≈ t) (conv_semantic t) Conv.refl hneg
  · -- ¬(t ≈ I), so use I as negative witness
    have hneg : ¬(I ≈ t) := fun hit => h (Conv.symm hit)
    exact behavioral_rice (· ≈ t) (conv_semantic t) Conv.refl hneg

end Term
