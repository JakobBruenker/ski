import Ski.Basic
import Ski.Combinator
import Ski.Quote

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

/-- A semantic property can be proved by showing one direction (the other follows by symmetry) -/
lemma IsSemantic.of_forward {P : Term → Prop}
    (h : ∀ t t', (t ≈ t') → P t → P t') : IsSemantic P :=
  fun t t' hconv => ⟨h t t' hconv, h t' t hconv.symm⟩

/-- A property is non-trivial if some term has it and some term doesn't -/
def IsNontrivial (P : Term → Prop) : Prop :=
  ∃ t f, P t ∧ ¬P f

/-- Halts is non-trivial: I halts, Ω doesn't -/
lemma halts_nontrivial : IsNontrivial Halts := ⟨I, Ω, i_halts, omega_diverges⟩

/-- Halts is a semantic property -/
lemma halts_semantic : IsSemantic Halts := .of_forward fun t t' hconv ⟨n, hn, htn⟩ => by
  obtain ⟨c, htc, ht'c⟩ := hconv
  obtain ⟨d, hnd, hcd⟩ := confluence htn htc
  cases hnd with
  | refl => exact ⟨n, hn, Steps.trans ht'c hcd⟩
  | step s _ => exact absurd s (hn _)

/-! ## Decidability -/

/-- A term d decides property P if d ⌜t⌝ reduces to tru when P t, and fls otherwise -/
def Decides (d : Term) (P : Term → Prop) : Prop :=
  ∀ t, (P t → d ⬝ ⌜t⌝ ⟶* tru) ∧ (¬P t → d ⬝ ⌜t⌝ ⟶* fls)

/-- A property is decidable if some term decides it given the encoding -/
def IsDecidable (P : Term → Prop) : Prop := ∃ d, Decides d P

/-- A term d behaviorally decides P if d t reduces to tru when P t, and fls otherwise.
    Unlike standard decidability, this gives the decider the term itself, not its encoding. -/
def BehaviorallyDecides (d : Term) (P : Term → Prop) : Prop :=
  ∀ t, (P t → d ⬝ t ⟶* tru) ∧ (¬P t → d ⬝ t ⟶* fls)

/-- A property is behaviorally decidable if some term decides it given the term directly -/
def IsBehaviorallyDecidable (P : Term → Prop) : Prop := ∃ d, BehaviorallyDecides d P

/-- Behavioral decidability implies decidability (via eval).
    If d behaviorally decides P, then S (K d) eval decides P,
    since S (K d) eval ⌜t⌝ ⟶* d (eval ⌜t⌝) ⟶* d t. -/
theorem behavioral_decidable_implies_decidable (P : Term → Prop) :
    IsBehaviorallyDecidable P → IsDecidable P := by
  intro ⟨d, hdec⟩
  refine ⟨S ⬝ (K ⬝ d) ⬝ eval, fun t => ?_⟩
  have hred : (S ⬝ (K ⬝ d) ⬝ eval) ⬝ ⌜t⌝ ⟶* d ⬝ t := by
    refine Steps.step Step.s ?_
    refine Steps.step (Step.appL Step.k) ?_
    exact Steps.appR (eval_correct t)
  exact ⟨fun hPt => Steps.trans hred ((hdec t).1 hPt),
         fun hnPt => Steps.trans hred ((hdec t).2 hnPt)⟩

/-! ## Rice's Theorem -/

/-- Rice's theorem: no non-trivial semantic property is decidable.
    The decider has access to the term's syntax via its encoding ⌜t⌝. -/
theorem rice (P : Term → Prop)
    (hsem : IsSemantic P)
    (hnt : IsNontrivial P) :
    ¬IsDecidable P := by
  obtain ⟨t, f, ht, hf⟩ := hnt
  intro ⟨d, hdec⟩
  -- Construct g = λq. (d q) f t
  -- When d q = tru, returns f (which has ¬P)
  -- When d q = fls, returns t (which has P)
  -- In SKI: g = S (S d (K f)) (K t)
  let g := S ⬝ (S ⬝ d ⬝ (K ⬝ f)) ⬝ (K ⬝ t)
  -- By Kleene's theorem, there exists x such that x ≈ g ⌜x⌝
  obtain ⟨x, hconv⟩ := kleene g
  -- g ⌜x⌝ = S (S d (K f)) (K t) ⌜x⌝ ⟶* (d ⌜x⌝) f t
  have hgq_red : g ⬝ ⌜x⌝ ⟶* (d ⬝ ⌜x⌝) ⬝ f ⬝ t := by
    refine Steps.step Step.s ?_
    refine Steps.step (Step.appR Step.k) ?_
    refine Steps.step (Step.appL Step.s) ?_
    exact Steps.step (Step.appL (Step.appR Step.k)) Steps.refl
  -- Case split on P x
  by_cases hPx : P x
  · -- Case P x
    have hdx : d ⬝ ⌜x⌝ ⟶* tru := (hdec x).1 hPx
    -- (d ⌜x⌝) f t ⟶* tru f t ⟶* f
    have hgq_f : g ⬝ ⌜x⌝ ⟶* f := by
      refine Steps.trans hgq_red ?_
      refine Steps.trans (Steps.appL (Steps.appL hdx)) ?_
      exact tru_red f t
    -- x ≈ g ⌜x⌝ (from Kleene) and g ⌜x⌝ ⟶* f, so x ≈ f
    -- hconv gives us c such that x ⟶* c and g ⌜x⌝ ⟶* c
    -- By confluence on g ⌜x⌝: g ⌜x⌝ ⟶* c and g ⌜x⌝ ⟶* f, so ∃d, c ⟶* d and f ⟶* d
    obtain ⟨c, hxc, hgc⟩ := hconv
    obtain ⟨d, hcd, hfd⟩ := confluence hgc hgq_f
    -- x ⟶* c ⟶* d and f ⟶* d, so x ≈ f
    have hxf : x ≈ f := ⟨d, Steps.trans hxc hcd, hfd⟩
    -- By semanticity, P x ↔ P f, so P f
    have hPf : P f := (hsem x f hxf).1 hPx
    -- Contradiction with hf : ¬P f
    exact hf hPf
  · -- Case ¬P x
    have hdx : d ⬝ ⌜x⌝ ⟶* fls := (hdec x).2 hPx
    -- (d ⌜x⌝) f t ⟶* fls f t ⟶* t
    have hgq_t : g ⬝ ⌜x⌝ ⟶* t := by
      refine Steps.trans hgq_red ?_
      refine Steps.trans (Steps.appL (Steps.appL hdx)) ?_
      exact fls_red f t
    -- x ≈ g ⌜x⌝ (from Kleene) and g ⌜x⌝ ⟶* t, so x ≈ t
    obtain ⟨c, hxc, hgc⟩ := hconv
    obtain ⟨d, hcd, htd⟩ := confluence hgc hgq_t
    have hxt : x ≈ t := ⟨d, Steps.trans hxc hcd, htd⟩
    -- By semanticity, P t ↔ P x, so P x (since P t)
    have hPx' : P x := (hsem t x (Conv.symm hxt)).1 ht
    -- Contradiction
    exact hPx hPx'

/-- Behavioral Rice's theorem: no non-trivial semantic property is behaviorally decidable.
    Follows from Rice since behavioral decidability implies decidability (via eval). -/
theorem behavioral_rice (P : Term → Prop)
    (hsem : IsSemantic P)
    (hnt : IsNontrivial P) :
    ¬IsBehaviorallyDecidable P :=
  fun h => rice P hsem hnt (behavioral_decidable_implies_decidable P h)

/- NOTE: The implication only goes one way:
   - Behavioral decidability → Decidability (via eval)
   - Decidability does NOT imply behavioral decidability

   To go from decidability to behavioral, we would need a "quoting combinator"
   q such that q t ⟶* ⌜t⌝ for any term t. But no such combinator exists -
   you can't compute the syntax of a term from its behavior. -/

/-! ## Undecidability Results -/

/-- The halting problem is undecidable -/
theorem halting_undecidable : ¬IsDecidable Halts :=
  rice Halts halts_semantic halts_nontrivial

end Term
