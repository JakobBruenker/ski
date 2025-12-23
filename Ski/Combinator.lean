import Ski.Basic

namespace Term

/-! ## Church Booleans -/

/-- True: λxy.x (selects first argument) -/
def tru : Term := K

/-- False: λxy.y (selects second argument) -/
def fls : Term := K ⬝ I

/-- tru x y ⟶* x -/
lemma tru_red (x y : Term) : tru ⬝ x ⬝ y ⟶* x := by
  -- K x y ⟶ x
  exact Steps.step Step.k Steps.refl

/-- fls x y ⟶* y -/
lemma fls_red (x y : Term) : fls ⬝ x ⬝ y ⟶* y := by
  -- fls x y = (K I) x y
  -- (K I) x ⟶ I, so (K I) x y ⟶ I y
  -- I y ⟶ y
  unfold fls
  refine Steps.step (Step.appL Step.k) ?_
  exact Steps.step Step.i Steps.refl

/-! ## Omega (diverging term) -/

/-- ω = S I I -/
def ω : Term := S ⬝ I ⬝ I

/-- Ω = ω ω (the canonical diverging term) -/
def Ω : Term := ω ⬝ ω

/-- S I I x ⟶ (I x)(I x) -/
lemma omega_step1 (x : Term) : ω ⬝ x ⟶ (I ⬝ x) ⬝ (I ⬝ x) := Step.s

/-- ω x ⟶* x x -/
lemma omega_red (x : Term) : ω ⬝ x ⟶* x ⬝ x := by
  -- S I I x ⟶ (I x)(I x) ⟶ x (I x) ⟶ x x
  refine Steps.step Step.s ?_
  refine Steps.step (Step.appL Step.i) ?_
  exact Steps.step (Step.appR Step.i) Steps.refl

/-! ## Proving Ω diverges -/

/-- An Oterm is either ω or I applied to an Oterm -/
inductive Oterm : Term → Prop where
  | omega : Oterm ω
  | app : Oterm t → Oterm (I ⬝ t)

/-- An OmegaLike term is an application of two Oterms -/
inductive OmegaLike : Term → Prop where
  | mk : Oterm a → Oterm b → OmegaLike (a ⬝ b)

/-- ω is in normal form -/
lemma omega_normal : IsNormal ω := by
  intro t' h
  -- ω = S I I, check all possible reductions
  unfold ω at h
  cases h with
  | appL h' =>
    cases h' with
    | appL h'' => cases h''
    | appR h'' => cases h''
  | appR h' => cases h'

/-- Oterm is preserved by reduction -/
lemma Oterm.preserved : Oterm t → (t ⟶ t') → Oterm t' := by
  intro h hstep
  cases h with
  | omega =>
    -- ω is normal, contradiction
    exact absurd hstep (omega_normal _)
  | app hot =>
    -- t = I ⬝ c where Oterm c
    cases hstep with
    | i => exact hot  -- I c ⟶ c
    | appL hl => cases hl  -- I can't reduce
    | appR hc => exact Oterm.app (hot.preserved hc)  -- c ⟶ c'

/-- OmegaLike is preserved by reduction -/
lemma OmegaLike.preserved : OmegaLike t → (t ⟶ t') → OmegaLike t' := by
  intro h hstep
  cases h with
  | mk ha hb =>
    -- t = a ⬝ b with Oterm a, Oterm b
    cases hstep with
    | s =>
      -- S x y z ⟶ (x z)(y z)
      -- a = S x y, and Oterm a, so a = ω = S I I (the only Oterm starting with S)
      cases ha with
      | omega =>
        -- a = ω = S I I, so t = S I I b ⟶ (I b)(I b)
        exact OmegaLike.mk (Oterm.app hb) (Oterm.app hb)
    | k =>
      -- K x y ⟶ x, would need a = K ⬝ x
      -- But Oterm a means a = ω (starts with S) or a = I ⬝ _ (starts with I)
      -- Neither starts with K, so this is impossible
      cases ha
    | i =>
      -- I x ⟶ x, would need a = I (just I, no application)
      -- But Oterm a means a = ω = S I I or a = I ⬝ _, neither equals bare I
      cases ha
    | appL hl =>
      -- a ⟶ a'
      exact OmegaLike.mk (ha.preserved hl) hb
    | appR hr =>
      -- b ⟶ b'
      exact OmegaLike.mk ha (hb.preserved hr)

/-- OmegaLike terms are not normal (they always have a redex) -/
lemma OmegaLike.not_normal : OmegaLike t → ¬IsNormal t := by
  intro h hn
  cases h with
  | @mk a b ha hb =>
    cases ha with
    | omega =>
      -- a = ω = S I I, so t = S I I b is an S-redex
      -- S I I b ⟶ (I b)(I b)
      exact hn _ Step.s
    | @app c hc =>
      -- a = I ⬝ c, so t = (I c) b, which has an I-redex at the head
      -- (I c) b ⟶ c b via Step.appL Step.i
      exact hn _ (Step.appL Step.i)

/-- Ω is OmegaLike -/
lemma Omega_OmegaLike : OmegaLike Ω :=
  OmegaLike.mk Oterm.omega Oterm.omega

/-- OmegaLike is preserved by multi-step reduction -/
lemma OmegaLike.steps : OmegaLike t → (t ⟶* t') → OmegaLike t' := by
  intro h hsteps
  induction hsteps with
  | refl => exact h
  | step s _ ih => exact ih (h.preserved s)

/-- Any term reachable from Ω is OmegaLike -/
lemma OmegaLike.reachable : (Ω ⟶* t) → OmegaLike t :=
  Omega_OmegaLike.steps

/-! ## Fixed-Point Combinator -/

/-- A = λxf. f(xxf) in SKI
    Derivation:
    A = λx. λf. f(xxf)
    λf. f(xxf) = S I (S (K(xx)) I)  [since λf.f = I, λf.xxf = S(K(xx))I]
    A = λx. S I (S (K(xx)) I)
    = S (K(SI)) (S (S(KS)(S(KK)(SII))) (KI))
-/
def A : Term :=
  S ⬝ (K ⬝ (S ⬝ I)) ⬝ (S ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ I ⬝ I))) ⬝ (K ⬝ I))

/-- Turing's fixed-point combinator: Θ = A A -/
def Θ : Term := A ⬝ A

/-- Helper: (S I I) x ⟶* x x -/
lemma sii_red (x : Term) : (S ⬝ I ⬝ I) ⬝ x ⟶* x ⬝ x := omega_red x

-- Abbreviations for readability
private abbrev KSI : Term := K ⬝ (S ⬝ I)
private abbrev KS : Term := K ⬝ S
private abbrev KK : Term := K ⬝ K
private abbrev KI : Term := K ⬝ I
private abbrev SII : Term := S ⬝ I ⬝ I
private abbrev B1 : Term := S ⬝ KK ⬝ SII
private abbrev B2 : Term := S ⬝ KS ⬝ B1
private abbrev B : Term := S ⬝ B2 ⬝ KI

-- Verify A = S KSI B
private theorem A_eq : A = S ⬝ KSI ⬝ B := rfl

/-- A x ⟶* (S I) (B x) -/
private theorem A_red (x : Term) : A ⬝ x ⟶* (S ⬝ I) ⬝ (B ⬝ x) := by
  -- A x = S KSI B x ⟶ (KSI x)(B x) ⟶ (S I)(B x)
  calc A ⬝ x
    = S ⬝ KSI ⬝ B ⬝ x := rfl
    _ ⟶* (KSI ⬝ x) ⬝ (B ⬝ x) := Steps.step Step.s Steps.refl
    _ ⟶* (S ⬝ I) ⬝ (B ⬝ x) := Steps.step (Step.appL Step.k) Steps.refl

/-- A A ⟶* (S I)(B A) -/
private theorem AA_red : A ⬝ A ⟶* (S ⬝ I) ⬝ (B ⬝ A) := A_red A

/-- (S I) t f ⟶* f (t f) -/
private theorem SI_red (t f : Term) : (S ⬝ I) ⬝ t ⬝ f ⟶* f ⬝ (t ⬝ f) := by
  -- S I t f ⟶ (I f)(t f) ⟶ f (t f)
  calc (S ⬝ I) ⬝ t ⬝ f
    _ ⟶* (I ⬝ f) ⬝ (t ⬝ f) := Steps.step Step.s Steps.refl
    _ ⟶* f ⬝ (t ⬝ f) := Steps.step (Step.appL Step.i) Steps.refl

/-- B1 x ⟶* K (x x) -/
private theorem B1_red (x : Term) : B1 ⬝ x ⟶* K ⬝ (x ⬝ x) := by
  -- B1 x = S KK SII x ⟶ (KK x)(SII x) ⟶ K (SII x) ⟶* K (x x)
  calc B1 ⬝ x
    = S ⬝ KK ⬝ SII ⬝ x := rfl
    _ ⟶* (KK ⬝ x) ⬝ (SII ⬝ x) := Steps.step Step.s Steps.refl
    _ ⟶* K ⬝ (SII ⬝ x) := Steps.step (Step.appL Step.k) Steps.refl
    _ ⟶* K ⬝ (x ⬝ x) := Steps.appR (sii_red x)

/-- B2 x ⟶* S (K (x x)) -/
private theorem B2_red (x : Term) : B2 ⬝ x ⟶* S ⬝ (K ⬝ (x ⬝ x)) := by
  -- B2 x = S KS B1 x ⟶ (KS x)(B1 x) ⟶ S (B1 x) ⟶* S (K (x x))
  calc B2 ⬝ x
    = S ⬝ KS ⬝ B1 ⬝ x := rfl
    _ ⟶* (KS ⬝ x) ⬝ (B1 ⬝ x) := Steps.step Step.s Steps.refl
    _ ⟶* S ⬝ (B1 ⬝ x) := Steps.step (Step.appL Step.k) Steps.refl
    _ ⟶* S ⬝ (K ⬝ (x ⬝ x)) := Steps.appR (B1_red x)

/-- B x ⟶* S (K (x x)) I -/
private theorem B_red (x : Term) : B ⬝ x ⟶* S ⬝ (K ⬝ (x ⬝ x)) ⬝ I := by
  -- B x = S B2 KI x ⟶ (B2 x)(KI x) ⟶ (B2 x) I ⟶* S (K (x x)) I
  calc B ⬝ x
    = S ⬝ B2 ⬝ KI ⬝ x := rfl
    _ ⟶* (B2 ⬝ x) ⬝ (KI ⬝ x) := Steps.step Step.s Steps.refl
    _ ⟶* (B2 ⬝ x) ⬝ I := Steps.step (Step.appR Step.k) Steps.refl
    _ ⟶* S ⬝ (K ⬝ (x ⬝ x)) ⬝ I := Steps.appL (B2_red x)

/-- S (K t) I f ⟶* t (I f) -/
private theorem SKtI_red (t f : Term) : S ⬝ (K ⬝ t) ⬝ I ⬝ f ⟶* t ⬝ (I ⬝ f) := by
  -- S (K t) I f ⟶ (K t f)(I f) ⟶ t (I f)
  calc S ⬝ (K ⬝ t) ⬝ I ⬝ f
    _ ⟶* (K ⬝ t ⬝ f) ⬝ (I ⬝ f) := Steps.step Step.s Steps.refl
    _ ⟶* t ⬝ (I ⬝ f) := Steps.step (Step.appL Step.k) Steps.refl

/-- (B A) f ⟶* (A A) f -/
private theorem BA_red (f : Term) : (B ⬝ A) ⬝ f ⟶* (A ⬝ A) ⬝ f := by
  -- B A ⟶* S (K (A A)) I
  -- S (K (A A)) I f ⟶* (A A) (I f) ⟶ (A A) f
  calc (B ⬝ A) ⬝ f
    _ ⟶* S ⬝ (K ⬝ (A ⬝ A)) ⬝ I ⬝ f := Steps.appL (B_red A)
    _ ⟶* (A ⬝ A) ⬝ (I ⬝ f) := SKtI_red (A ⬝ A) f
    _ ⟶* (A ⬝ A) ⬝ f := Steps.step (Step.appR Step.i) Steps.refl

/-- Key property: Θ f ⟶* f (Θ f) -/
theorem theta_unfold (f : Term) : Θ ⬝ f ⟶* f ⬝ (Θ ⬝ f) := by
  -- Θ f = A A f ⟶* (S I)(B A) f ⟶* f ((B A) f) ⟶* f (Θ f)
  calc Θ ⬝ f
    = A ⬝ A ⬝ f := rfl
    _ ⟶* (S ⬝ I) ⬝ (B ⬝ A) ⬝ f := Steps.appL AA_red
    _ ⟶* f ⬝ ((B ⬝ A) ⬝ f) := SI_red (B ⬝ A) f
    _ ⟶* f ⬝ ((A ⬝ A) ⬝ f) := Steps.appR (BA_red f)
    _ = f ⬝ (Θ ⬝ f) := rfl

end Term
