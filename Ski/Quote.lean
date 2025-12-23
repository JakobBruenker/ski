import Ski.Basic
import Ski.Combinator

namespace Term

/-! ## Scott Encoding of Terms

We encode Term as SKI terms using a 4-way Scott encoding.
Each encoded term takes 4 handlers (s, k, i, a) and dispatches appropriately:
- ⌜S⌝ s k i a ⟶* s
- ⌜K⌝ s k i a ⟶* k
- ⌜I⌝ s k i a ⟶* i
- ⌜t ⬝ u⌝ s k i a ⟶* a ⌜t⌝ ⌜u⌝
-/

/-- Scott encoding of terms.
    ⌜S⌝ = λs k i a. s = S (K K) (S (K K) (S (K K) I))
    ⌜K⌝ = λs k i a. k = K (S (K K) (S (K K) I))
    ⌜I⌝ = λs k i a. i = K (K (S (K K) I))
    ⌜t ⬝ u⌝ = λs k i a. a ⌜t⌝ ⌜u⌝ = K (K (K (S (S I (K ⌜t⌝)) (K ⌜u⌝)))) -/
def quote : Term → Term
  | S => S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ K) ⬝ I))
  | K => K ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ K) ⬝ I))
  | I => K ⬝ (K ⬝ (S ⬝ (K ⬝ K) ⬝ I))
  | app t u => K ⬝ (K ⬝ (K ⬝ (S ⬝ (S ⬝ I ⬝ (K ⬝ quote t)) ⬝ (K ⬝ quote u))))

notation "⌜" t "⌝" => quote t

/-! ## Quote Reduction Lemmas -/

/-- ⌜S⌝ s k i a ⟶* s -/
theorem quote_S_red (s k i a : Term) : ⌜S⌝ ⬝ s ⬝ k ⬝ i ⬝ a ⟶* s := by
  unfold quote
  -- ((((S (K K) X) s) k) i) a where X = S (K K) (S (K K) I)
  -- First reduce the S at depth 3: S (K K) X s ⟶ (K K s) (X s)
  refine Steps.step (Step.appL (Step.appL (Step.appL Step.s))) ?_
  -- ((((K K s) (X s)) k) i) a
  -- Reduce K K s ⟶ K
  refine Steps.step (Step.appL (Step.appL (Step.appL (Step.appL Step.k)))) ?_
  -- (((K (X s)) k) i) a
  -- Reduce K (X s) k ⟶ X s
  refine Steps.step (Step.appL (Step.appL Step.k)) ?_
  -- ((X s) i) a where X s = S (K K) (S (K K) I) s
  -- Reduce S (K K) (S (K K) I) s ⟶ (K K s) ((S (K K) I) s)
  refine Steps.step (Step.appL (Step.appL Step.s)) ?_
  -- (((K K s) ((S (K K) I) s)) i) a
  -- Reduce K K s ⟶ K
  refine Steps.step (Step.appL (Step.appL (Step.appL Step.k))) ?_
  -- ((K ((S (K K) I) s)) i) a
  -- Reduce K _ i ⟶ _
  refine Steps.step (Step.appL Step.k) ?_
  -- ((S (K K) I) s) a
  -- Reduce S (K K) I s ⟶ (K K s) (I s)
  refine Steps.step (Step.appL Step.s) ?_
  -- ((K K s) (I s)) a
  -- Reduce K K s ⟶ K
  refine Steps.step (Step.appL (Step.appL Step.k)) ?_
  -- (K (I s)) a
  -- Reduce I s ⟶ s
  refine Steps.step (Step.appL (Step.appR Step.i)) ?_
  -- K s a ⟶ s
  exact Steps.step Step.k Steps.refl

/-- ⌜K⌝ s k i a ⟶* k -/
theorem quote_K_red (s k i a : Term) : ⌜K⌝ ⬝ s ⬝ k ⬝ i ⬝ a ⟶* k := by
  unfold quote
  -- ((((K X) s) k) i) a where X = S (K K) (S (K K) I)
  -- K X s ⟶ X
  refine Steps.step (Step.appL (Step.appL (Step.appL Step.k))) ?_
  -- (((X) k) i) a = ((X k) i) a
  -- X k = S (K K) (S (K K) I) k ⟶ (K K k) ((S (K K) I) k)
  refine Steps.step (Step.appL (Step.appL Step.s)) ?_
  -- ((((K K k) ((S (K K) I) k))) i) a
  -- K K k ⟶ K
  refine Steps.step (Step.appL (Step.appL (Step.appL Step.k))) ?_
  -- (((K ((S (K K) I) k))) i) a
  -- K _ i ⟶ _
  refine Steps.step (Step.appL Step.k) ?_
  -- ((S (K K) I) k) a
  -- S (K K) I k ⟶ (K K k) (I k)
  refine Steps.step (Step.appL Step.s) ?_
  -- (((K K k) (I k))) a
  -- K K k ⟶ K
  refine Steps.step (Step.appL (Step.appL Step.k)) ?_
  -- ((K (I k))) a
  -- I k ⟶ k
  refine Steps.step (Step.appL (Step.appR Step.i)) ?_
  -- K k a ⟶ k
  exact Steps.step Step.k Steps.refl

/-- ⌜I⌝ s k i a ⟶* i -/
theorem quote_I_red (s k i a : Term) : ⌜I⌝ ⬝ s ⬝ k ⬝ i ⬝ a ⟶* i := by
  unfold quote
  -- ((((K (K X)) s) k) i) a where X = S (K K) I
  -- K (K X) s ⟶ K X
  refine Steps.step (Step.appL (Step.appL (Step.appL Step.k))) ?_
  -- (((K X) k) i) a
  -- K X k ⟶ X
  refine Steps.step (Step.appL (Step.appL Step.k)) ?_
  -- ((X) i) a = (X i) a = (S (K K) I i) a
  -- S (K K) I i ⟶ (K K i) (I i)
  refine Steps.step (Step.appL Step.s) ?_
  -- (((K K i) (I i))) a
  -- K K i ⟶ K
  refine Steps.step (Step.appL (Step.appL Step.k)) ?_
  -- ((K (I i))) a
  -- I i ⟶ i
  refine Steps.step (Step.appL (Step.appR Step.i)) ?_
  -- (K i) a ⟶ i
  exact Steps.step Step.k Steps.refl

/-- ⌜t ⬝ u⌝ s k i a ⟶* a ⌜t⌝ ⌜u⌝ -/
theorem quote_app_red (t u s k i a : Term) : ⌜t ⬝ u⌝ ⬝ s ⬝ k ⬝ i ⬝ a ⟶* a ⬝ ⌜t⌝ ⬝ ⌜u⌝ := by
  simp only [quote]
  -- ((((K (K (K (S (S I (K ⌜t⌝)) (K ⌜u⌝))))) s) k) i) a
  -- K _ s ⟶ _
  refine Steps.step (Step.appL (Step.appL (Step.appL Step.k))) ?_
  -- (((K (K (S (S I (K ⌜t⌝)) (K ⌜u⌝)))) k) i) a
  -- K _ k ⟶ _
  refine Steps.step (Step.appL (Step.appL Step.k)) ?_
  -- ((K (S (S I (K ⌜t⌝)) (K ⌜u⌝))) i) a
  -- K _ i ⟶ _
  refine Steps.step (Step.appL Step.k) ?_
  -- (S (S I (K ⌜t⌝)) (K ⌜u⌝)) a
  -- S X Y a ⟶ (X a) (Y a)
  refine Steps.step Step.s ?_
  -- ((S I (K ⌜t⌝) a)) ((K ⌜u⌝) a)
  -- S I (K ⌜t⌝) a ⟶ (I a) ((K ⌜t⌝) a)
  refine Steps.step (Step.appL Step.s) ?_
  -- (((I a) ((K ⌜t⌝) a))) ((K ⌜u⌝) a)
  -- I a ⟶ a
  refine Steps.step (Step.appL (Step.appL Step.i)) ?_
  -- ((a ((K ⌜t⌝) a))) ((K ⌜u⌝) a)
  -- K ⌜t⌝ a ⟶ ⌜t⌝
  refine Steps.step (Step.appL (Step.appR Step.k)) ?_
  -- (a ⌜t⌝) ((K ⌜u⌝) a)
  -- K ⌜u⌝ a ⟶ ⌜u⌝
  refine Steps.step (Step.appR Step.k) ?_
  -- a ⌜t⌝ ⌜u⌝
  exact Steps.refl

/-! ## App Builder (needed for Kleene's theorem) -/

/-- Composition combinator: B f g x ⟶* f (g x) -/
private def B : Term := S ⬝ (K ⬝ S) ⬝ K

/-- B f g x ⟶* f (g x) -/
private theorem B_red (f g x : Term) : B ⬝ f ⬝ g ⬝ x ⟶* f ⬝ (g ⬝ x) := by
  unfold B
  -- ((((S ⬝ (K ⬝ S)) ⬝ K) ⬝ f) ⬝ g) ⬝ x
  -- The S-redex is at depth 2: ((S ⬝ (K ⬝ S)) ⬝ K) ⬝ f = S (K S) K f
  -- S (K S) K f ⟶ ((K S) f) (K f) = S (K f)
  refine Steps.step (Step.appL (Step.appL Step.s)) ?_
  -- (((((K ⬝ S) ⬝ f) ⬝ (K ⬝ f))) ⬝ g) ⬝ x
  -- (K S) f ⟶ S
  refine Steps.step (Step.appL (Step.appL (Step.appL Step.k))) ?_
  -- (((S ⬝ (K ⬝ f))) ⬝ g) ⬝ x
  -- S (K f) g x ⟶ (K f x) (g x)
  refine Steps.step Step.s ?_
  -- ((K ⬝ f ⬝ x) ⬝ (g ⬝ x))
  -- K f x ⟶ f
  exact Steps.step (Step.appL Step.k) Steps.refl

/-- wrap3 z = K (K (K z)) -- wraps a term in 3 K's
    This is the same as ⌜S⌝ = S (K K) (S (K K) (S (K K) I)) -/
private def wrap3 : Term := S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ K) ⬝ I))

/-- wrap3 z ⟶* K (K (K z)) -/
private theorem wrap3_red (z : Term) : wrap3 ⬝ z ⟶* K ⬝ (K ⬝ (K ⬝ z)) := by
  unfold wrap3
  -- S (K K) (S (K K) (S (K K) I)) z
  refine Steps.step Step.s ?_
  refine Steps.step (Step.appL Step.k) ?_
  -- K (S (K K) (S (K K) I) z)
  -- Need to reduce inner: S (K K) (S (K K) I) z ⟶* K (K z)
  refine Steps.step (Step.appR Step.s) ?_
  refine Steps.step (Step.appR (Step.appL Step.k)) ?_
  -- K (K (S (K K) I z))
  refine Steps.step (Step.appR (Step.appR Step.s)) ?_
  refine Steps.step (Step.appR (Step.appR (Step.appL Step.k))) ?_
  -- K (K (K (I z)))
  refine Steps.step (Step.appR (Step.appR (Step.appR Step.i))) ?_
  exact Steps.refl

/-- inner x y ⟶* S ((S I) (K x)) (K y)
    This is the bracket abstraction of λx. λy. S ((S I) (K x)) (K y)
    The derivation:
    [y](S ((S I) (K x)) (K y)) = S (K (S ((S I) (K x)))) (S (K K) I)
    [x] of that = S (S (K S) (S (K K) (S (K S) (S (K (S I)) (S (K K) I))))) (K (S (K K) I))
-/
private def inner : Term :=
  S ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ (S ⬝ (K ⬝ K) ⬝ I))))) ⬝
  (K ⬝ (S ⬝ (K ⬝ K) ⬝ I))

/-- inner x y ⟶* S ((S I) (K x)) (K y) -/
private theorem inner_red (x y : Term) : inner ⬝ x ⬝ y ⟶* S ⬝ (S ⬝ I ⬝ (K ⬝ x)) ⬝ (K ⬝ y) := by
  unfold inner
  -- inner = S A B where:
  -- A = S (K S) (S (K K) (S (K S) (S (K (S I)) (S (K K) I))))
  -- B = K (S (K K) I)
  -- inner x = S A B x ⟶ (A x) (B x)
  refine Steps.step (Step.appL Step.s) ?_
  -- B x = K (S (K K) I) x ⟶ S (K K) I
  refine Steps.step (Step.appL (Step.appR Step.k)) ?_
  -- A x = S (K S) C x where C = S (K K) (S (K S) (S (K (S I)) (S (K K) I)))
  -- ⟶ (K S x) (C x) = S (C x)
  refine Steps.step (Step.appL (Step.appL Step.s)) ?_
  refine Steps.step (Step.appL (Step.appL (Step.appL Step.k))) ?_
  -- (S (C x)) (S (K K) I) y where C x needs to be reduced
  -- C = S (K K) (S (K S) (S (K (S I)) (S (K K) I)))
  -- C x ⟶ (K K x) (D x) = K (D x) where D = S (K S) (S (K (S I)) (S (K K) I))
  refine Steps.step (Step.appL (Step.appL (Step.appR Step.s))) ?_
  refine Steps.step (Step.appL (Step.appL (Step.appR (Step.appL Step.k)))) ?_
  -- (S (K (D x))) (S (K K) I) y
  -- D = S (K S) (S (K (S I)) (S (K K) I))
  -- D x ⟶ (K S x) (E x) = S (E x) where E = S (K (S I)) (S (K K) I)
  refine Steps.step (Step.appL (Step.appL (Step.appR (Step.appR Step.s)))) ?_
  refine Steps.step (Step.appL (Step.appL (Step.appR (Step.appR (Step.appL Step.k))))) ?_
  -- (S (K (S (E x)))) (S (K K) I) y
  -- E x = S (K (S I)) (S (K K) I) x ⟶ (K (S I) x) ((S (K K) I) x)
  --     = (S I) ((S (K K) I) x)
  refine Steps.step (Step.appL (Step.appL (Step.appR (Step.appR (Step.appR Step.s))))) ?_
  refine Steps.step (Step.appL (Step.appL (Step.appR (Step.appR (Step.appR (Step.appL Step.k)))))) ?_
  -- (S (K (S ((S I) ((S (K K) I) x))))) (S (K K) I) y
  -- (S (K K) I) x ⟶ (K K x) (I x) = K x
  refine Steps.step (Step.appL (Step.appL (Step.appR (Step.appR (Step.appR (Step.appR Step.s)))))) ?_
  refine Steps.step (Step.appL (Step.appL (Step.appR (Step.appR (Step.appR (Step.appR (Step.appL Step.k))))))) ?_
  refine Steps.step (Step.appL (Step.appL (Step.appR (Step.appR (Step.appR (Step.appR (Step.appR Step.i))))))) ?_
  -- (S (K (S ((S I) (K x))))) (S (K K) I) y
  -- Now S (K (S ((S I) (K x)))) (S (K K) I) y ⟶ (K ... y) ((S (K K) I) y)
  refine Steps.step Step.s ?_
  -- (K (S ((S I) (K x))) y) ((S (K K) I) y)
  -- K (S ((S I) (K x))) y ⟶ S ((S I) (K x))
  refine Steps.step (Step.appL Step.k) ?_
  -- S ((S I) (K x)) ((S (K K) I) y)
  -- (S (K K) I) y ⟶ (K K y) (I y) = K y
  refine Steps.step (Step.appR Step.s) ?_
  refine Steps.step (Step.appR (Step.appL Step.k)) ?_
  refine Steps.step (Step.appR (Step.appR Step.i)) ?_
  -- S ((S I) (K x)) (K y)
  exact Steps.refl

/-- mkApp builds the app encoding from two quoted terms:
    mkApp ⌜t⌝ ⌜u⌝ ⟶* ⌜t ⬝ u⌝

    mkApp = S (K (B wrap3)) (S (K inner) I)
    mkApp x y = wrap3 (inner x y) = K (K (K (S (S I (K x)) (K y)))) -/
def mkApp : Term := S ⬝ (K ⬝ (B ⬝ wrap3)) ⬝ (S ⬝ (K ⬝ inner) ⬝ I)

theorem mkApp_correct (t u : Term) : mkApp ⬝ ⌜t⌝ ⬝ ⌜u⌝ ⟶* ⌜t ⬝ u⌝ := by
  unfold mkApp
  -- S (K (B wrap3)) (S (K inner) I) ⌜t⌝ ⌜u⌝
  -- First: S _ _ ⌜t⌝ ⟶ (K (B wrap3) ⌜t⌝) ((S (K inner) I) ⌜t⌝)
  refine Steps.step (Step.appL Step.s) ?_
  -- ((K (B wrap3) ⌜t⌝) ((S (K inner) I) ⌜t⌝)) ⌜u⌝
  -- K (B wrap3) ⌜t⌝ ⟶ B wrap3
  refine Steps.step (Step.appL (Step.appL Step.k)) ?_
  -- ((B wrap3) ((S (K inner) I) ⌜t⌝)) ⌜u⌝
  -- (S (K inner) I) ⌜t⌝ ⟶ (K inner ⌜t⌝) (I ⌜t⌝) ⟶ inner ⌜t⌝
  refine Steps.step (Step.appL (Step.appR Step.s)) ?_
  refine Steps.step (Step.appL (Step.appR (Step.appL Step.k))) ?_
  refine Steps.step (Step.appL (Step.appR (Step.appR Step.i))) ?_
  -- ((B wrap3) (inner ⌜t⌝)) ⌜u⌝
  -- B wrap3 (inner ⌜t⌝) ⌜u⌝ ⟶* wrap3 ((inner ⌜t⌝) ⌜u⌝) ⟶* wrap3 (inner ⌜t⌝ ⌜u⌝)
  refine Steps.trans (B_red wrap3 (inner ⬝ ⌜t⌝) ⌜u⌝) ?_
  -- wrap3 (inner ⌜t⌝ ⌜u⌝)
  -- inner ⌜t⌝ ⌜u⌝ ⟶* S (S I (K ⌜t⌝)) (K ⌜u⌝)
  refine Steps.trans (Steps.appR (inner_red ⌜t⌝ ⌜u⌝)) ?_
  -- wrap3 (S (S I (K ⌜t⌝)) (K ⌜u⌝))
  -- wrap3 z ⟶* K (K (K z))
  refine Steps.trans (wrap3_red (S ⬝ (S ⬝ I ⬝ (K ⬝ ⌜t⌝)) ⬝ (K ⬝ ⌜u⌝))) ?_
  -- K (K (K (S (S I (K ⌜t⌝)) (K ⌜u⌝)))) = ⌜t ⬝ u⌝
  simp only [quote]
  exact Steps.refl

/-! ## Self-Application Combinator -/

/-! ## quoteQuote combinator

quoteQuote takes a quoted term and returns its double-quotation:
quoteQuote ⌜t⌝ ⟶* ⌜⌜t⌝⌝

The construction uses Θ for recursion over the Scott encoding:
- For ⌜S⌝: returns ⌜⌜S⌝⌝ (constant)
- For ⌜K⌝: returns ⌜⌜K⌝⌝ (constant)
- For ⌜I⌝: returns ⌜⌜I⌝⌝ (constant)
- For ⌜t ⬝ u⌝: recursively gets ⌜⌜t⌝⌝ and ⌜⌜u⌝⌝, then builds ⌜⌜t ⬝ u⌝⌝
-/

-- Constants: quoted and double-quoted base terms
private def qS : Term := ⌜S⌝
private def qK : Term := ⌜K⌝
private def qI : Term := ⌜I⌝
private def qSI : Term := ⌜S ⬝ I⌝
private def qqS : Term := ⌜⌜S⌝⌝
private def qqK : Term := ⌜⌜K⌝⌝
private def qqI : Term := ⌜⌜I⌝⌝

-- Helpers: partial applications of mkApp to build specific patterns
private def mk_K : Term := mkApp ⬝ qK   -- mk_K x = ⌜K ⬝ x⌝
private def mk_S : Term := mkApp ⬝ qS   -- mk_S x = ⌜S ⬝ x⌝
private def mk_SI : Term := mkApp ⬝ qSI -- mk_SI x = ⌜(S ⬝ I) ⬝ x⌝

/-- Φ combinator: Φ h f g x y = h (f x) (g y)
    Φ h f g = S (S (K S) (S (K K) (S (K h) f))) (K g) -/
private def PhiComb (h f g : Term) : Term :=
  S ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ h) ⬝ f))) ⬝ (K ⬝ g)

/-- Φ h f g x y ⟶* h (f x) (g y) -/
private theorem PhiComb_red (h f g x y : Term) : PhiComb h f g ⬝ x ⬝ y ⟶* h ⬝ (f ⬝ x) ⬝ (g ⬝ y) := by
  unfold PhiComb
  -- S (S (K S) (S (K K) (S (K h) f))) (K g) x y
  -- First apply to x:
  refine Steps.step (Step.appL Step.s) ?_
  -- ((S (K S) (S (K K) (S (K h) f)) x) ((K g) x)) y
  refine Steps.step (Step.appL (Step.appR Step.k)) ?_
  -- ((S (K S) (S (K K) (S (K h) f)) x) g) y
  refine Steps.step (Step.appL (Step.appL Step.s)) ?_
  -- (((K S x) ((S (K K) (S (K h) f)) x)) g) y
  refine Steps.step (Step.appL (Step.appL (Step.appL Step.k))) ?_
  -- ((S ((S (K K) (S (K h) f)) x)) g) y
  refine Steps.step (Step.appL (Step.appL (Step.appR Step.s))) ?_
  -- ((S ((K K x) ((S (K h) f) x))) g) y
  refine Steps.step (Step.appL (Step.appL (Step.appR (Step.appL Step.k)))) ?_
  -- ((S (K ((S (K h) f) x))) g) y
  refine Steps.step (Step.appL (Step.appL (Step.appR (Step.appR Step.s)))) ?_
  -- ((S (K ((K h x) (f x)))) g) y
  refine Steps.step (Step.appL (Step.appL (Step.appR (Step.appR (Step.appL Step.k))))) ?_
  -- ((S (K (h (f x)))) g) y
  -- Now apply S (K (h (f x))) g y ⟶ (K (h (f x)) y) (g y)
  refine Steps.step Step.s ?_
  -- ((K (h (f x)) y) (g y))
  refine Steps.step (Step.appL Step.k) ?_
  -- (h (f x)) (g y)
  exact Steps.refl

/-- buildAppQuote builds ⌜⌜t ⬝ u⌝⌝ from ⌜⌜t⌝⌝ and ⌜⌜u⌝⌝.

Since ⌜t ⬝ u⌝ = K ⬝ (K ⬝ (K ⬝ (S ⬝ (S ⬝ I ⬝ (K ⬝ ⌜t⌝)) ⬝ (K ⬝ ⌜u⌝)))),
we need to build the encoding of this structure. The key structure is:
  (S ⬝ ((S ⬝ I) ⬝ (K ⬝ ⌜t⌝))) ⬝ (K ⬝ ⌜u⌝)

So ⌜⌜t ⬝ u⌝⌝ = mkApp qK (mkApp qK (mkApp qK (mkApp (mkApp qS (mkApp qSI (mkApp qK ⌜⌜t⌝⌝))) (mkApp qK ⌜⌜u⌝⌝))))

buildAppQuote = B (B wrap) inner where:
- inner x y = mkApp (mkApp qS (mkApp qSI (mkApp qK x))) (mkApp qK y)
- wrap z = mkApp qK (mkApp qK (mkApp qK z))
Note: B (B wrap) inner x y = (B wrap) (inner x) y = wrap (inner x y) -/
private def buildAppQuote : Term :=
  let wrap := B ⬝ mk_K ⬝ (B ⬝ mk_K ⬝ mk_K)
  let inner := PhiComb mkApp (B ⬝ mk_S ⬝ (B ⬝ mk_SI ⬝ mk_K)) mk_K
  B ⬝ (B ⬝ wrap) ⬝ inner

/-- Helper: wrap z ⟶* mk_K (mk_K (mk_K z))
    where wrap = B mk_K (B mk_K mk_K) -/
private theorem wrap_red (z : Term) :
    (B ⬝ mk_K ⬝ (B ⬝ mk_K ⬝ mk_K)) ⬝ z ⟶* mk_K ⬝ (mk_K ⬝ (mk_K ⬝ z)) := by
  refine Steps.trans (B_red mk_K (B ⬝ mk_K ⬝ mk_K) z) ?_
  exact Steps.appR (B_red mk_K mk_K z)

/-- buildAppQuote ⌜⌜t⌝⌝ ⌜⌜u⌝⌝ ⟶* ⌜⌜t ⬝ u⌝⌝ -/
private theorem buildAppQuote_correct (t u : Term) :
    buildAppQuote ⬝ ⌜⌜t⌝⌝ ⬝ ⌜⌜u⌝⌝ ⟶* ⌜⌜t ⬝ u⌝⌝ := by
  unfold buildAppQuote
  -- B (B wrap) inner ⌜⌜t⌝⌝ ⌜⌜u⌝⌝ where
  -- wrap = B mk_K (B mk_K mk_K)
  -- inner = PhiComb mkApp (B mk_S (B mk_SI mk_K)) mk_K
  -- First: B (B wrap) inner ⌜⌜t⌝⌝ ⟶* (B wrap) (inner ⌜⌜t⌝⌝)
  refine Steps.trans (Steps.appL (B_red (B ⬝ (B ⬝ mk_K ⬝ (B ⬝ mk_K ⬝ mk_K)))
    (PhiComb mkApp (B ⬝ mk_S ⬝ (B ⬝ mk_SI ⬝ mk_K)) mk_K) ⌜⌜t⌝⌝)) ?_
  -- ((B wrap) (inner ⌜⌜t⌝⌝)) ⌜⌜u⌝⌝
  -- (B wrap) (inner ⌜⌜t⌝⌝) ⌜⌜u⌝⌝ ⟶* wrap (inner ⌜⌜t⌝⌝ ⌜⌜u⌝⌝)
  refine Steps.trans (B_red (B ⬝ mk_K ⬝ (B ⬝ mk_K ⬝ mk_K))
    (PhiComb mkApp (B ⬝ mk_S ⬝ (B ⬝ mk_SI ⬝ mk_K)) mk_K ⬝ ⌜⌜t⌝⌝) ⌜⌜u⌝⌝) ?_
  -- wrap (inner ⌜⌜t⌝⌝ ⌜⌜u⌝⌝)
  -- inner ⌜⌜t⌝⌝ ⌜⌜u⌝⌝ ⟶* mkApp ((B mk_S (B mk_SI mk_K)) ⌜⌜t⌝⌝) (mk_K ⌜⌜u⌝⌝)
  refine Steps.trans (Steps.appR (PhiComb_red mkApp (B ⬝ mk_S ⬝ (B ⬝ mk_SI ⬝ mk_K)) mk_K ⌜⌜t⌝⌝ ⌜⌜u⌝⌝)) ?_
  -- wrap (mkApp ((B mk_S (B mk_SI mk_K)) ⌜⌜t⌝⌝) (mk_K ⌜⌜u⌝⌝))
  -- (B mk_S (B mk_SI mk_K)) ⌜⌜t⌝⌝ ⟶* mk_S ((B mk_SI mk_K) ⌜⌜t⌝⌝)
  refine Steps.trans (Steps.appR (Steps.appL (Steps.appR (B_red mk_S (B ⬝ mk_SI ⬝ mk_K) ⌜⌜t⌝⌝)))) ?_
  -- (B mk_SI mk_K) ⌜⌜t⌝⌝ ⟶* mk_SI (mk_K ⌜⌜t⌝⌝)
  refine Steps.trans (Steps.appR (Steps.appL (Steps.appR (Steps.appR (B_red mk_SI mk_K ⌜⌜t⌝⌝))))) ?_
  -- mk_K ⌜⌜t⌝⌝ ⟶* ⌜K ⬝ ⌜t⌝⌝
  have h_mk_K_t : mk_K ⬝ ⌜⌜t⌝⌝ ⟶* ⌜K ⬝ ⌜t⌝⌝ := mkApp_correct K ⌜t⌝
  have h_mk_K_u : mk_K ⬝ ⌜⌜u⌝⌝ ⟶* ⌜K ⬝ ⌜u⌝⌝ := mkApp_correct K ⌜u⌝
  -- mk_SI (mk_K ⌜⌜t⌝⌝) ⟶* ⌜(S ⬝ I) ⬝ (K ⬝ ⌜t⌝)⌝
  have h_mk_SI : mk_SI ⬝ (mk_K ⬝ ⌜⌜t⌝⌝) ⟶* ⌜(S ⬝ I) ⬝ (K ⬝ ⌜t⌝)⌝ := by
    refine Steps.trans (Steps.appR h_mk_K_t) ?_
    exact mkApp_correct (S ⬝ I) (K ⬝ ⌜t⌝)
  refine Steps.trans (Steps.appR (Steps.appL (Steps.appR (Steps.appR h_mk_SI)))) ?_
  -- mk_S (mk_SI (mk_K ⌜⌜t⌝⌝)) ⟶* ⌜S ⬝ ((S ⬝ I) ⬝ (K ⬝ ⌜t⌝))⌝
  have h_mk_S : mk_S ⬝ ⌜(S ⬝ I) ⬝ (K ⬝ ⌜t⌝)⌝ ⟶* ⌜S ⬝ ((S ⬝ I) ⬝ (K ⬝ ⌜t⌝))⌝ :=
    mkApp_correct S ((S ⬝ I) ⬝ (K ⬝ ⌜t⌝))
  refine Steps.trans (Steps.appR (Steps.appL (Steps.appR h_mk_S))) ?_
  refine Steps.trans (Steps.appR (Steps.appR h_mk_K_u)) ?_
  -- wrap (mkApp ⌜S ⬝ ((S ⬝ I) ⬝ (K ⬝ ⌜t⌝))⌝ ⌜K ⬝ ⌜u⌝⌝)
  have h_inner : mkApp ⬝ ⌜S ⬝ ((S ⬝ I) ⬝ (K ⬝ ⌜t⌝))⌝ ⬝ ⌜K ⬝ ⌜u⌝⌝ ⟶*
                 ⌜(S ⬝ ((S ⬝ I) ⬝ (K ⬝ ⌜t⌝))) ⬝ (K ⬝ ⌜u⌝)⌝ :=
    mkApp_correct (S ⬝ ((S ⬝ I) ⬝ (K ⬝ ⌜t⌝))) (K ⬝ ⌜u⌝)
  refine Steps.trans (Steps.appR h_inner) ?_
  -- wrap ⌜(S ⬝ ((S ⬝ I) ⬝ (K ⬝ ⌜t⌝))) ⬝ (K ⬝ ⌜u⌝)⌝
  refine Steps.trans (wrap_red _) ?_
  -- mk_K (mk_K (mk_K ⌜...⌝))
  have h1 : mk_K ⬝ ⌜(S ⬝ ((S ⬝ I) ⬝ (K ⬝ ⌜t⌝))) ⬝ (K ⬝ ⌜u⌝)⌝ ⟶*
            ⌜K ⬝ ((S ⬝ ((S ⬝ I) ⬝ (K ⬝ ⌜t⌝))) ⬝ (K ⬝ ⌜u⌝))⌝ := mkApp_correct K _
  refine Steps.trans (Steps.appR (Steps.appR h1)) ?_
  have h2 : mk_K ⬝ ⌜K ⬝ ((S ⬝ ((S ⬝ I) ⬝ (K ⬝ ⌜t⌝))) ⬝ (K ⬝ ⌜u⌝))⌝ ⟶*
            ⌜K ⬝ (K ⬝ ((S ⬝ ((S ⬝ I) ⬝ (K ⬝ ⌜t⌝))) ⬝ (K ⬝ ⌜u⌝)))⌝ := mkApp_correct K _
  refine Steps.trans (Steps.appR h2) ?_
  have h3 : mk_K ⬝ ⌜K ⬝ (K ⬝ ((S ⬝ ((S ⬝ I) ⬝ (K ⬝ ⌜t⌝))) ⬝ (K ⬝ ⌜u⌝)))⌝ ⟶*
            ⌜K ⬝ (K ⬝ (K ⬝ ((S ⬝ ((S ⬝ I) ⬝ (K ⬝ ⌜t⌝))) ⬝ (K ⬝ ⌜u⌝))))⌝ := mkApp_correct K _
  refine Steps.trans h3 ?_
  -- Now show ⌜K ⬝ (K ⬝ (K ⬝ ((S ⬝ ((S ⬝ I) ⬝ (K ⬝ ⌜t⌝))) ⬝ (K ⬝ ⌜u⌝))))⌝ = ⌜⌜t ⬝ u⌝⌝
  simp only [quote]
  exact Steps.refl

/-- P combinator: P r y ⟶* r y (equivalent to S (K r) I but computed via application)
    P = S (S (K S) (S (K K) I)) (K I)
    P r = S (K r) I
    P r y = (K r y) (I y) = r y -/
private def P : Term := S ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ K) ⬝ I)) ⬝ (K ⬝ I)

/-- P r y ⟶* r y -/
private theorem P_red (r y : Term) : P ⬝ r ⬝ y ⟶* r ⬝ y := by
  unfold P
  -- S (S (K S) (S (K K) I)) (K I) r y
  refine Steps.step (Step.appL Step.s) ?_
  -- ((S (K S) (S (K K) I) r) ((K I) r)) y
  refine Steps.step (Step.appL (Step.appR Step.k)) ?_
  -- ((S (K S) (S (K K) I) r) I) y
  refine Steps.step (Step.appL (Step.appL Step.s)) ?_
  -- (((K S r) ((S (K K) I) r)) I) y
  refine Steps.step (Step.appL (Step.appL (Step.appL Step.k))) ?_
  -- ((S ((S (K K) I) r)) I) y
  refine Steps.step (Step.appL (Step.appL (Step.appR Step.s))) ?_
  -- ((S ((K K r) (I r))) I) y
  refine Steps.step (Step.appL (Step.appL (Step.appR (Step.appL Step.k)))) ?_
  -- ((S (K (I r))) I) y
  refine Steps.step (Step.appL (Step.appL (Step.appR (Step.appR Step.i)))) ?_
  -- ((S (K r)) I) y
  refine Steps.step Step.s ?_
  -- ((K r y) (I y))
  refine Steps.step (Step.appL Step.k) ?_
  -- (r (I y))
  exact Steps.step (Step.appR Step.i) Steps.refl

/-- The handler for app case: λr x y. buildAppQuote (r x) (r y)
    = S (S (K S) (S (K (S (K B))) (S (K (S (K buildAppQuote))) P))) (S (K K) P)
    where P is defined above.

    The structure is:
    - P r = S (K r) I, which gives P r y ⟶* r y
    - Inner: S (K buildAppQuote) (P r) x ⟶* buildAppQuote ((P r) x) ⟶* buildAppQuote (r x)
    - Then: B (buildAppQuote (r x)) (P r) y ⟶* buildAppQuote (r x) (r y)
    - Full: S (B (buildAppQuote (r x))) (P r) is the x-abstracted form -/
private def handlerFor : Term :=
  S ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ B))) ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ buildAppQuote))) ⬝ P))) ⬝
  (S ⬝ (K ⬝ K) ⬝ P)

/-- handlerFor r x y ⟶* buildAppQuote (r x) (r y) -/
private theorem handlerFor_red (r x y : Term) :
    handlerFor ⬝ r ⬝ x ⬝ y ⟶* buildAppQuote ⬝ (r ⬝ x) ⬝ (r ⬝ y) := by
  unfold handlerFor
  -- S A C r x y where A = S (K S) (S (K (S (K B))) (S (K (S (K buildAppQuote))) P))
  --                and C = S (K K) P
  -- First S-reduction on the outermost S: S A C r → (A r) (C r)
  refine Steps.step (Step.appL (Step.appL Step.s)) ?_
  -- Now have ((A r) (C r)) x y
  -- Reduce C r = S (K K) P r → (K K r) (P r) → K (P r)
  refine Steps.step (Step.appL (Step.appL (Step.appR Step.s))) ?_
  refine Steps.step (Step.appL (Step.appL (Step.appR (Step.appL Step.k)))) ?_
  -- ((A r) (K (P r))) x y
  -- Now reduce A r where A = S (K S) (S (K (S (K B))) (S (K (S (K buildAppQuote))) P))
  -- S (K S) B' r → (K S r) (B' r) → S (B' r)
  refine Steps.step (Step.appL (Step.appL (Step.appL Step.s))) ?_
  refine Steps.step (Step.appL (Step.appL (Step.appL (Step.appL Step.k)))) ?_
  -- ((S (B' r)) (K (P r))) x y where B' = S (K (S (K B))) (S (K (S (K buildAppQuote))) P)
  -- Reduce B' r: S (K (S (K B))) D r → (K (S (K B)) r) (D r) → (S (K B)) (D r)
  -- where D = S (K (S (K buildAppQuote))) P
  refine Steps.step (Step.appL (Step.appL (Step.appL (Step.appR Step.s)))) ?_
  refine Steps.step (Step.appL (Step.appL (Step.appL (Step.appR (Step.appL Step.k))))) ?_
  -- ((S ((S (K B)) (D r))) (K (P r))) x y
  -- Reduce D r: S (K (S (K buildAppQuote))) P r → (K (S (K buildAppQuote)) r) (P r) → (S (K buildAppQuote)) (P r)
  refine Steps.step (Step.appL (Step.appL (Step.appL (Step.appR (Step.appR Step.s))))) ?_
  refine Steps.step (Step.appL (Step.appL (Step.appL (Step.appR (Step.appR (Step.appL Step.k)))))) ?_
  -- Now we have: ((S ((S (K B)) ((S (K buildAppQuote)) (P r)))) (K (P r))) x y
  -- This is ((S E F) x) y where E = (S (K B)) ((S (K buildAppQuote)) (P r)) and F = K (P r)
  -- Apply S E F x → (E x) (F x)
  refine Steps.step (Step.appL Step.s) ?_
  -- (((E x) (F x))) y where F x = K (P r) x → P r
  refine Steps.step (Step.appL (Step.appR Step.k)) ?_
  -- ((E x) (P r)) y where E = (S (K B)) ((S (K buildAppQuote)) (P r))
  -- E x = S (K B) G x → (K B x) (G x) → B (G x) where G = (S (K buildAppQuote)) (P r)
  refine Steps.step (Step.appL (Step.appL Step.s)) ?_
  refine Steps.step (Step.appL (Step.appL (Step.appL Step.k))) ?_
  -- ((B (G x)) (P r)) y where G x = (S (K buildAppQuote)) (P r) x
  -- G x = S (K buildAppQuote) (P r) x → (K buildAppQuote x) ((P r) x) → buildAppQuote ((P r) x)
  refine Steps.step (Step.appL (Step.appL (Step.appR Step.s))) ?_
  refine Steps.step (Step.appL (Step.appL (Step.appR (Step.appL Step.k)))) ?_
  -- ((B (buildAppQuote ((P r) x))) (P r)) y
  -- Now use P_red: (P r) x ⟶* r x
  -- Path: appL -> appL -> appR -> appR (to reach (P r) x inside buildAppQuote (P r x))
  refine Steps.trans (Steps.appL (Steps.appL (Steps.appR (Steps.appR (P_red r x))))) ?_
  -- ((B (buildAppQuote (r x))) (P r)) y
  -- B f g y → f (g y), so B (buildAppQuote (r x)) (P r) y → buildAppQuote (r x) ((P r) y)
  refine Steps.trans (B_red (buildAppQuote ⬝ (r ⬝ x)) (P ⬝ r) y) ?_
  -- buildAppQuote (r x) ((P r) y) ⟶* buildAppQuote (r x) (r y)
  exact Steps.appR (P_red r y)

/-- A_handler = λq. q qqS qqK qqI = S (S (S I (K qqS)) (K qqK)) (K qqI)
    When applied: A_handler q = q qqS qqK qqI -/
private def A_handler : Term := S ⬝ (S ⬝ (S ⬝ I ⬝ (K ⬝ qqS)) ⬝ (K ⬝ qqK)) ⬝ (K ⬝ qqI)

/-- A_handler q ⟶* q qqS qqK qqI -/
private theorem A_handler_red (q : Term) : A_handler ⬝ q ⟶* q ⬝ qqS ⬝ qqK ⬝ qqI := by
  unfold A_handler
  -- S (S (S I (K qqS)) (K qqK)) (K qqI) q
  refine Steps.step Step.s ?_
  -- (S (S I (K qqS)) (K qqK) q) ((K qqI) q)
  refine Steps.step (Step.appR Step.k) ?_
  -- (S (S I (K qqS)) (K qqK) q) qqI
  refine Steps.step (Step.appL Step.s) ?_
  -- ((S I (K qqS) q) ((K qqK) q)) qqI
  refine Steps.step (Step.appL (Step.appR Step.k)) ?_
  -- ((S I (K qqS) q) qqK) qqI
  refine Steps.step (Step.appL (Step.appL Step.s)) ?_
  -- (((I q) ((K qqS) q)) qqK) qqI
  refine Steps.step (Step.appL (Step.appL (Step.appL Step.i))) ?_
  -- ((q ((K qqS) q)) qqK) qqI
  refine Steps.step (Step.appL (Step.appL (Step.appR Step.k))) ?_
  -- ((q qqS) qqK) qqI
  exact Steps.refl

/-- quoteQuoteBody: body r q = q qqS qqK qqI (handlerFor r)
    = S A_handler (S (K K) handlerFor) applied to r q -/
private def quoteQuoteBody : Term :=
  S ⬝ (K ⬝ (S ⬝ A_handler)) ⬝ (S ⬝ (K ⬝ K) ⬝ handlerFor)

/-- The quoteQuote combinator using Θ -/
def quoteQuote : Term := Θ ⬝ quoteQuoteBody

/-- Helper: quoteQuoteBody r q ⟶* (q ⬝ qqS ⬝ qqK ⬝ qqI) ⬝ (handlerFor ⬝ r) -/
private theorem quoteQuoteBody_red (r q : Term) :
    quoteQuoteBody ⬝ r ⬝ q ⟶* (q ⬝ qqS ⬝ qqK ⬝ qqI) ⬝ (handlerFor ⬝ r) := by
  unfold quoteQuoteBody
  -- S (K (S A_handler)) (S (K K) handlerFor) r q
  refine Steps.step (Step.appL Step.s) ?_
  -- (K (S A_handler) r) ((S (K K) handlerFor) r) q
  refine Steps.step (Step.appL (Step.appL Step.k)) ?_
  -- (S A_handler) ((S (K K) handlerFor) r) q
  refine Steps.step (Step.appL (Step.appR Step.s)) ?_
  refine Steps.step (Step.appL (Step.appR (Step.appL Step.k))) ?_
  -- (S A_handler) (K (handlerFor r)) q
  -- S A_handler (K (handlerFor r)) q ⟶ (A_handler q) ((K (handlerFor r)) q)
  refine Steps.step Step.s ?_
  -- (A_handler q) ((K (handlerFor r)) q)
  refine Steps.step (Step.appR Step.k) ?_
  -- (A_handler q) (handlerFor r)
  -- A_handler q ⟶* q qqS qqK qqI
  exact Steps.appL (A_handler_red q)

/-- Common initial reduction: quoteQuote ⌜t⌝ ⟶* (⌜t⌝ qqS qqK qqI) (handlerFor quoteQuote) -/
private theorem quoteQuote_step (t : Term) :
    quoteQuote ⬝ ⌜t⌝ ⟶* (⌜t⌝ ⬝ qqS ⬝ qqK ⬝ qqI) ⬝ (handlerFor ⬝ quoteQuote) := by
  unfold quoteQuote
  refine Steps.trans (Steps.appL (theta_unfold quoteQuoteBody)) ?_
  exact quoteQuoteBody_red (Θ ⬝ quoteQuoteBody) ⌜t⌝

/-- quoteQuote ⌜t⌝ ⟶* ⌜⌜t⌝⌝ -/
theorem quoteQuote_correct : ∀ t, quoteQuote ⬝ ⌜t⌝ ⟶* ⌜⌜t⌝⌝
  | S => Steps.trans (quoteQuote_step S) (quote_S_red qqS qqK qqI (handlerFor ⬝ quoteQuote))
  | K => Steps.trans (quoteQuote_step K) (quote_K_red qqS qqK qqI (handlerFor ⬝ quoteQuote))
  | I => Steps.trans (quoteQuote_step I) (quote_I_red qqS qqK qqI (handlerFor ⬝ quoteQuote))
  | app t u => by
    refine Steps.trans (quoteQuote_step (t ⬝ u)) ?_
    refine Steps.trans (quote_app_red t u qqS qqK qqI (handlerFor ⬝ quoteQuote)) ?_
    refine Steps.trans (handlerFor_red quoteQuote ⌜t⌝ ⌜u⌝) ?_
    refine Steps.trans (Steps.appL (Steps.appR (quoteQuote_correct t))) ?_
    refine Steps.trans (Steps.appR (quoteQuote_correct u)) ?_
    exact buildAppQuote_correct t u

/-- Self-application combinator: selfApp ⌜t⌝ ⟶* ⌜t ⬝ ⌜t⌝⌝
    selfApp = λy. mkApp y (quoteQuote y) = S mkApp quoteQuote -/
def selfApp : Term := S ⬝ mkApp ⬝ quoteQuote

theorem selfApp_correct (t : Term) : selfApp ⬝ ⌜t⌝ ⟶* ⌜t ⬝ ⌜t⌝⌝ := by
  unfold selfApp
  -- S mkApp quoteQuote ⌜t⌝ ⟶ (mkApp ⌜t⌝) (quoteQuote ⌜t⌝)
  refine Steps.step Step.s ?_
  -- mkApp ⌜t⌝ (quoteQuote ⌜t⌝) ⟶* mkApp ⌜t⌝ ⌜⌜t⌝⌝
  refine Steps.trans (Steps.appR (quoteQuote_correct t)) ?_
  -- mkApp ⌜t⌝ ⌜⌜t⌝⌝ ⟶* ⌜t ⬝ ⌜t⌝⌝
  exact mkApp_correct t ⌜t⌝

/-! ## Kleene's Fixed-Point Theorem -/

/-- Helper: λy. g (selfApp y) in SKI = S (K g) selfApp -/
private def kleeneHelper (g : Term) : Term := S ⬝ (K ⬝ g) ⬝ selfApp

/-! ## Evaluator -/

/-- A_eval q = q S K I -/
private def A_eval : Term := S ⬝ (S ⬝ (S ⬝ I ⬝ (K ⬝ S)) ⬝ (K ⬝ K)) ⬝ (K ⬝ I)

/-- A_eval q ⟶* q S K I -/
private theorem A_eval_red (q : Term) : A_eval ⬝ q ⟶* q ⬝ S ⬝ K ⬝ I := by
  unfold A_eval
  -- S (S (S I (K S)) (K K)) (K I) q
  refine Steps.step Step.s ?_
  -- (S (S I (K S)) (K K) q) (K I q)
  refine Steps.step (Step.appR Step.k) ?_
  -- (S (S I (K S)) (K K) q) I
  refine Steps.step (Step.appL Step.s) ?_
  -- ((S I (K S) q) (K K q)) I
  refine Steps.step (Step.appL (Step.appR Step.k)) ?_
  -- ((S I (K S) q) K) I
  refine Steps.step (Step.appL (Step.appL Step.s)) ?_
  -- (((I q) (K S q)) K) I
  refine Steps.step (Step.appL (Step.appL (Step.appL Step.i))) ?_
  -- ((q (K S q)) K) I
  refine Steps.step (Step.appL (Step.appL (Step.appR Step.k))) ?_
  -- ((q S) K) I = q S K I
  exact Steps.refl

/-- appHandler r x y = (r x) (r y)
    = S (S (K S) (S (K (S (K S))) (S (K (S (K K))) I))) K -/
private def appHandler : Term :=
  S ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ S))) ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ K))) ⬝ I))) ⬝ K

/-- appHandler r x y ⟶* (r x) (r y) -/
private theorem appHandler_red (r x y : Term) : appHandler ⬝ r ⬝ x ⬝ y ⟶* (r ⬝ x) ⬝ (r ⬝ y) := by
  unfold appHandler
  -- S (S (K S) (S (K (S (K S))) (S (K (S (K K))) I))) K r x y
  -- First reduce the outermost S with r as argument
  refine Steps.step (Step.appL (Step.appL Step.s)) ?_
  -- ((S (K S) (S (K (S (K S))) (S (K (S (K K))) I)) r) (K r)) x y
  -- Reduce inner: S (K S) (S (...)) r
  refine Steps.step (Step.appL (Step.appL (Step.appL Step.s))) ?_
  -- (((K S r) ((S (K (S (K S))) (S (K (S (K K))) I)) r)) (K r)) x y
  refine Steps.step (Step.appL (Step.appL (Step.appL (Step.appL Step.k)))) ?_
  -- ((S ((S (K (S (K S))) (S (K (S (K K))) I)) r)) (K r)) x y
  refine Steps.step (Step.appL (Step.appL (Step.appL (Step.appR Step.s)))) ?_
  -- ((S ((K (S (K S)) r) ((S (K (S (K K))) I) r))) (K r)) x y
  refine Steps.step (Step.appL (Step.appL (Step.appL (Step.appR (Step.appL Step.k))))) ?_
  -- ((S ((S (K S)) ((S (K (S (K K))) I) r))) (K r)) x y
  refine Steps.step (Step.appL (Step.appL (Step.appL (Step.appR (Step.appR Step.s))))) ?_
  -- ((S ((S (K S)) ((K (S (K K)) r) (I r)))) (K r)) x y
  refine Steps.step (Step.appL (Step.appL (Step.appL (Step.appR (Step.appR (Step.appL Step.k)))))) ?_
  -- ((S ((S (K S)) ((S (K K)) (I r)))) (K r)) x y
  refine Steps.step (Step.appL (Step.appL (Step.appL (Step.appR (Step.appR (Step.appR Step.i)))))) ?_
  -- ((S (S (K S) (S (K K) r))) (K r)) x y
  -- Now apply x: S (S (K S) (S (K K) r)) (K r) x
  refine Steps.step (Step.appL Step.s) ?_
  -- ((S (K S) (S (K K) r) x) (K r x)) y
  refine Steps.step (Step.appL (Step.appR Step.k)) ?_
  -- ((S (K S) (S (K K) r) x) r) y
  refine Steps.step (Step.appL (Step.appL Step.s)) ?_
  -- (((K S x) ((S (K K) r) x)) r) y
  refine Steps.step (Step.appL (Step.appL (Step.appL Step.k))) ?_
  -- ((S ((S (K K) r) x)) r) y
  refine Steps.step (Step.appL (Step.appL (Step.appR Step.s))) ?_
  -- ((S ((K K x) (r x))) r) y
  refine Steps.step (Step.appL (Step.appL (Step.appR (Step.appL Step.k)))) ?_
  -- ((S (K (r x))) r) y
  -- Now S (K (r x)) r y = (K (r x) y) (r y) = (r x) (r y)
  refine Steps.step Step.s ?_
  -- (K (r x) y) (r y)
  refine Steps.step (Step.appL Step.k) ?_
  -- (r x) (r y)
  exact Steps.refl

/-- evalBody r q = q S K I (appHandler r)
    Using the same pattern as quoteQuoteBody -/
private def evalBody : Term := S ⬝ (K ⬝ (S ⬝ A_eval)) ⬝ (S ⬝ (K ⬝ K) ⬝ appHandler)

/-- evalBody r q ⟶* (q S K I) (appHandler r) -/
private theorem evalBody_red (r q : Term) :
    evalBody ⬝ r ⬝ q ⟶* (q ⬝ S ⬝ K ⬝ I) ⬝ (appHandler ⬝ r) := by
  unfold evalBody
  -- S (K (S A_eval)) (S (K K) appHandler) r q
  refine Steps.step (Step.appL Step.s) ?_
  -- (K (S A_eval) r) ((S (K K) appHandler) r) q
  refine Steps.step (Step.appL (Step.appL Step.k)) ?_
  -- (S A_eval) ((S (K K) appHandler) r) q
  refine Steps.step (Step.appL (Step.appR Step.s)) ?_
  -- (S A_eval) ((K K r) (appHandler r)) q
  refine Steps.step (Step.appL (Step.appR (Step.appL Step.k))) ?_
  -- (S A_eval) (K (appHandler r)) q
  refine Steps.step Step.s ?_
  -- (A_eval q) (K (appHandler r) q)
  refine Steps.step (Step.appR Step.k) ?_
  -- (A_eval q) (appHandler r)
  exact Steps.appL (A_eval_red q)

/-- The eval combinator: eval ⌜t⌝ ⟶* t -/
def eval : Term := Θ ⬝ evalBody

/-- Common initial reduction for eval -/
private theorem eval_step (t : Term) :
    eval ⬝ ⌜t⌝ ⟶* (⌜t⌝ ⬝ S ⬝ K ⬝ I) ⬝ (appHandler ⬝ eval) := by
  unfold eval
  refine Steps.trans (Steps.appL (theta_unfold evalBody)) ?_
  exact evalBody_red (Θ ⬝ evalBody) ⌜t⌝

/-- eval ⌜t⌝ ⟶* t -/
theorem eval_correct : ∀ t, eval ⬝ ⌜t⌝ ⟶* t
  | S => Steps.trans (eval_step S) (quote_S_red S K I (appHandler ⬝ eval))
  | K => Steps.trans (eval_step K) (quote_K_red S K I (appHandler ⬝ eval))
  | I => Steps.trans (eval_step I) (quote_I_red S K I (appHandler ⬝ eval))
  | app t u => by
    refine Steps.trans (eval_step (t ⬝ u)) ?_
    refine Steps.trans (quote_app_red t u S K I (appHandler ⬝ eval)) ?_
    refine Steps.trans (appHandler_red eval ⌜t⌝ ⌜u⌝) ?_
    exact Steps.app (eval_correct t) (eval_correct u)

/-! ## Kleene's Fixed Point Theorem -/

/-- kleeneHelper g y ⟶* g (selfApp y) -/
private theorem kleeneHelper_red (g y : Term) :
    kleeneHelper g ⬝ y ⟶* g ⬝ (selfApp ⬝ y) := by
  unfold kleeneHelper
  -- S (K g) selfApp y ⟶ (K g y) (selfApp y)
  refine Steps.step Step.s ?_
  -- (K g y) (selfApp y) ⟶ g (selfApp y)
  exact Steps.step (Step.appL Step.k) Steps.refl

/-- For any g, there exists x such that x ≈ g ⌜x⌝ -/
theorem kleene (g : Term) : ∃ x, x ≈ g ⬝ ⌜x⌝ :=
  -- Let e = kleeneHelper g, x = e ⌜e⌝
  -- Then x = e ⌜e⌝ ⟶* g (selfApp ⌜e⌝) ⟶* g ⌜e ⬝ ⌜e⌝⌝ = g ⌜x⌝
  let e := kleeneHelper g
  let x := e ⬝ ⌜e⌝
  ⟨x, g ⬝ ⌜x⌝,
    Steps.trans (kleeneHelper_red g ⌜e⌝) (Steps.appR (selfApp_correct e)),
    Steps.refl⟩

end Term
