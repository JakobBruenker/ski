/-
  Abstract Computational Model Framework

  Defines what properties a computational model needs to satisfy Rice's theorem,
  then proves Rice generically for any such model.
-/

/-! ## Abstract Computational Model -/

/-- A computational model supporting Rice's theorem -/
structure ComputationalModel where
  /-- Type of programs -/
  Prog : Type
  /-- Behavioral equivalence (e.g., same computed function) -/
  equiv : Prog → Prog → Prop
  /-- Equivalence is an equivalence relation -/
  equiv_refl : ∀ p, equiv p p
  equiv_symm : ∀ p q, equiv p q → equiv q p
  equiv_trans : ∀ p q r, equiv p q → equiv q r → equiv p r
  /-- Application of program to argument -/
  app : Prog → Prog → Prog
  /-- Application respects equivalence in first argument -/
  app_congr_left : ∀ p p' q, equiv p p' → equiv (app p q) (app p' q)
  /-- Application respects equivalence in second argument -/
  app_congr_right : ∀ p q q', equiv q q' → equiv (app p q) (app p q')
  /-- Boolean constants -/
  tru : Prog
  fls : Prog
  /-- tru selects first argument: tru x y ≈ x -/
  tru_select : ∀ x y, equiv (app (app tru x) y) x
  /-- fls selects second argument: fls x y ≈ y -/
  fls_select : ∀ x y, equiv (app (app fls x) y) y
  /-- tru and fls are distinguishable -/
  tru_ne_fls : ¬equiv tru fls
  /-- Self-encoding: programs as data -/
  encode : Prog → Prog
  /-- Kleene fixed-point property: for any g, there exists x equivalent to g applied to x's encoding -/
  kleene : ∀ g, ∃ x, equiv x (app g (encode x))
  /-- S combinator for program construction -/
  S : Prog
  /-- K combinator for program construction -/
  K : Prog
  /-- S reduction: S x y z ≈ (x z) (y z) -/
  S_red : ∀ x y z, equiv (app (app (app S x) y) z) (app (app x z) (app y z))
  /-- K reduction: K x y ≈ x -/
  K_red : ∀ x y, equiv (app (app K x) y) x

namespace ComputationalModel

/-! ## Semantic Properties -/

/-- A property is semantic if it respects equivalence -/
def IsSemantic (M : ComputationalModel) (P : M.Prog → Prop) : Prop :=
  ∀ p q, M.equiv p q → (P p ↔ P q)

/-- A property is non-trivial if some program has it and some doesn't -/
def IsNontrivial (M : ComputationalModel) (P : M.Prog → Prop) : Prop :=
  ∃ t f, P t ∧ ¬P f

/-- A program d decides property P if:
    - When P p, d applied to encoding of p is equivalent to tru
    - When ¬P p, d applied to encoding of p is equivalent to fls -/
def Decides (M : ComputationalModel) (d : M.Prog) (P : M.Prog → Prop) : Prop :=
  ∀ p, (P p → M.equiv (M.app d (M.encode p)) M.tru) ∧
       (¬P p → M.equiv (M.app d (M.encode p)) M.fls)

/-- A property is decidable if some program decides it -/
def IsDecidable (M : ComputationalModel) (P : M.Prog → Prop) : Prop :=
  ∃ d, M.Decides d P

/-! ## Generic Rice's Theorem -/

/-- Helper: application respects equivalence on both sides -/
theorem app_congr (M : ComputationalModel) {p p' q q' : M.Prog}
    (hp : M.equiv p p') (hq : M.equiv q q') :
    M.equiv (M.app p q) (M.app p' q') :=
  M.equiv_trans _ _ _ (M.app_congr_left _ _ _ hp) (M.app_congr_right _ _ _ hq)

/-- Rice's theorem for abstract computational models:
    No non-trivial semantic property is decidable. -/
theorem rice (M : ComputationalModel) (P : M.Prog → Prop)
    (hsem : M.IsSemantic P)
    (hnt : M.IsNontrivial P) :
    ¬M.IsDecidable P := by
  -- Get witnesses for non-triviality
  obtain ⟨t, f, hPt, hPf⟩ := hnt
  -- Assume there's a decider
  intro ⟨d, hdec⟩
  -- Construct g = S (S d (K f)) (K t)
  -- g q ≈ (d q) f t: when d q ≈ tru, returns f; when d q ≈ fls, returns t
  let g := M.app (M.app M.S (M.app (M.app M.S d) (M.app M.K f))) (M.app M.K t)
  -- By Kleene, there exists x such that x ≈ g ⌜x⌝
  obtain ⟨x, hxgx⟩ := M.kleene g
  -- Compute g q ≈ (d q) f t
  have g_red : ∀ q, M.equiv (M.app g q) (M.app (M.app (M.app d q) f) t) := by
    intro q
    -- g q = S (S d (K f)) (K t) q
    --     ≈ (S d (K f) q) (K t q)      by S
    --     ≈ (S d (K f) q) t            by K
    --     ≈ (d q) ((K f) q) t          by S
    --     ≈ (d q) f t                  by K
    have step1 := M.S_red (M.app (M.app M.S d) (M.app M.K f)) (M.app M.K t) q
    have step2 : M.equiv (M.app (M.app M.K t) q) t := M.K_red t q
    have step3 := M.S_red d (M.app M.K f) q
    have step4 : M.equiv (M.app (M.app M.K f) q) f := M.K_red f q
    -- Combine steps
    refine M.equiv_trans _ _ _ step1 ?_
    refine M.equiv_trans _ _ _ (M.app_congr_right _ _ _ step2) ?_
    refine M.equiv_trans _ _ _ (M.app_congr_left _ _ _ step3) ?_
    exact M.app_congr_left _ _ _ (M.app_congr_right _ _ _ step4)
  -- Case split on P x
  by_cases hPx : P x
  · -- Case: P x
    -- d ⌜x⌝ ≈ tru (since hdec says P x → d ⌜x⌝ ≈ tru)
    have hdx : M.equiv (M.app d (M.encode x)) M.tru := (hdec x).1 hPx
    -- g ⌜x⌝ ≈ (d ⌜x⌝) f t ≈ tru f t ≈ f
    have hgxf : M.equiv (M.app g (M.encode x)) f := by
      refine M.equiv_trans _ _ _ (g_red (M.encode x)) ?_
      refine M.equiv_trans _ _ _ (M.app_congr_left _ _ _ (M.app_congr_left _ _ _ hdx)) ?_
      exact M.tru_select f t
    -- x ≈ g ⌜x⌝ ≈ f
    have hxf : M.equiv x f := M.equiv_trans _ _ _ hxgx hgxf
    -- By semanticity, P x ↔ P f
    have : P f := (hsem x f hxf).1 hPx
    exact hPf this
  · -- Case: ¬P x
    -- d ⌜x⌝ ≈ fls
    have hdx : M.equiv (M.app d (M.encode x)) M.fls := (hdec x).2 hPx
    -- g ⌜x⌝ ≈ (d ⌜x⌝) f t ≈ fls f t ≈ t
    have hgxt : M.equiv (M.app g (M.encode x)) t := by
      refine M.equiv_trans _ _ _ (g_red (M.encode x)) ?_
      refine M.equiv_trans _ _ _ (M.app_congr_left _ _ _ (M.app_congr_left _ _ _ hdx)) ?_
      exact M.fls_select f t
    -- x ≈ g ⌜x⌝ ≈ t
    have hxt : M.equiv x t := M.equiv_trans _ _ _ hxgx hgxt
    -- By semanticity, P t ↔ P x, so P x (since P t)
    have : P x := (hsem t x (M.equiv_symm _ _ hxt)).1 hPt
    exact hPx this

end ComputationalModel
