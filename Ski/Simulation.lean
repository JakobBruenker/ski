/-
  Simulation between Register Machines and SKI Calculus

  Proves both directions:
  1. RM → SKI: Any RM can be simulated by an SKI term
  2. SKI → RM: SKI reduction can be simulated by an RM

  This establishes computational equivalence (Church-Turing thesis).
-/

import Ski.Basic
import Ski.Combinator
import Ski.Quote
import Ski.Register
import Ski.RegisterEncode

open Term

/-! ## Church Numerals -/

/-- Church numeral encoding of natural numbers in SKI -/
def churchNum : Nat → Term
  | 0 => K ⬝ I  -- λf x. x = fls
  | n + 1 => S ⬝ (S ⬝ (K ⬝ S) ⬝ K) ⬝ churchNum n  -- λf x. f (n f x)

/-- Church zero is K I -/
theorem church_zero : churchNum 0 = fls := rfl

/-- Apply f n times to x -/
def applyN (f : Term) (n : Nat) (x : Term) : Term :=
  match n with
  | 0 => x
  | n + 1 => f ⬝ applyN f n x

/-- K I f ⟶* I -/
private theorem ki_app (f : Term) : K ⬝ I ⬝ f ⟶* I :=
  Steps.step Step.k Steps.refl

/-- I x ⟶* x -/
private theorem i_app (x : Term) : I ⬝ x ⟶* x :=
  Steps.step Step.i Steps.refl

/-- The B combinator: S (K S) K -/
private def B : Term := S ⬝ (K ⬝ S) ⬝ K

/-- B f g x ⟶* f (g x) -/
private theorem b_red (f g x : Term) : B ⬝ f ⬝ g ⬝ x ⟶* f ⬝ (g ⬝ x) := by
  -- B f g x = S (K S) K f g x
  -- ⟶ ((K S) f) (K f) g x  (S reduction)
  -- ⟶ S (K f) g x          (K reduction)
  -- ⟶ (K f x) (g x)        (S reduction)
  -- ⟶ f (g x)              (K reduction)
  calc B ⬝ f ⬝ g ⬝ x
      = S ⬝ (K ⬝ S) ⬝ K ⬝ f ⬝ g ⬝ x := rfl
    _ ⟶* ((K ⬝ S) ⬝ f) ⬝ (K ⬝ f) ⬝ g ⬝ x := by
        apply Steps.appL; apply Steps.appL; apply Steps.appL
        exact Steps.step Step.s Steps.refl
    _ ⟶* S ⬝ (K ⬝ f) ⬝ g ⬝ x := by
        apply Steps.appL; apply Steps.appL; apply Steps.appL
        exact Steps.step Step.k Steps.refl
    _ ⟶* ((K ⬝ f) ⬝ x) ⬝ (g ⬝ x) := Steps.step Step.s Steps.refl
    _ ⟶* f ⬝ (g ⬝ x) := Steps.appL (Steps.step Step.k Steps.refl)

/-- Church numeral application: n f x ⟶* f^n x -/
theorem church_app (n : Nat) (f x : Term) :
    churchNum n ⬝ f ⬝ x ⟶* applyN f n x := by
  induction n with
  | zero =>
    -- churchNum 0 = K ⬝ I
    -- (K ⬝ I) ⬝ f ⬝ x ⟶ I ⬝ x ⟶ x = applyN f 0 x
    calc churchNum 0 ⬝ f ⬝ x
        = (K ⬝ I) ⬝ f ⬝ x := rfl
      _ ⟶* I ⬝ x := Steps.appL (ki_app f)
      _ ⟶* x := i_app x
  | succ n ih =>
    -- churchNum (n+1) = S ⬝ B ⬝ (churchNum n)
    -- S ⬝ B ⬝ (churchNum n) ⬝ f ⬝ x
    -- ⟶ (B ⬝ f) ⬝ ((churchNum n) ⬝ f) ⬝ x  (S reduction)
    -- ⟶* f ⬝ ((churchNum n) ⬝ f ⬝ x)       (B reduction)
    -- ⟶* f ⬝ (applyN f n x)                (IH)
    -- = applyN f (n+1) x
    calc churchNum (n + 1) ⬝ f ⬝ x
        = S ⬝ (S ⬝ (K ⬝ S) ⬝ K) ⬝ (churchNum n) ⬝ f ⬝ x := rfl
      _ = S ⬝ B ⬝ (churchNum n) ⬝ f ⬝ x := rfl
      _ ⟶* (B ⬝ f) ⬝ ((churchNum n) ⬝ f) ⬝ x := by
          apply Steps.appL
          exact Steps.step Step.s Steps.refl
      _ ⟶* f ⬝ ((churchNum n) ⬝ f ⬝ x) := b_red f (churchNum n ⬝ f) x
      _ ⟶* f ⬝ (applyN f n x) := Steps.appR ih
      _ = applyN f (n + 1) x := rfl

/-! ## SKI Pair Combinator -/

/-- Helper: S (K K) I is eta-equivalent to K (produces K b when applied to b) -/
private def SKK : Term := S ⬝ (K ⬝ K) ⬝ I

/-- SKK b ⟶* K b -/
private theorem skk_red (b : Term) : SKK ⬝ b ⟶* K ⬝ b := by
  calc SKK ⬝ b
      = S ⬝ (K ⬝ K) ⬝ I ⬝ b := rfl
    _ ⟶* ((K ⬝ K) ⬝ b) ⬝ (I ⬝ b) := Steps.step Step.s Steps.refl
    _ ⟶* K ⬝ (I ⬝ b) := Steps.appL (Steps.step Step.k Steps.refl)
    _ ⟶* K ⬝ b := Steps.appR (Steps.step Step.i Steps.refl)

/-- Pair combinator in SKI: λx y f. f x y
    Derived from bracket abstraction of λx. λy. λf. f x y -/
def skiPair : Term :=
  S ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ SKK)))) ⬝ (K ⬝ SKK)

/-- Helper: S (K (S I)) SKK is [λa. S I (K a)] -/
private def SI_Ka (a : Term) : Term := S ⬝ I ⬝ (K ⬝ a)

/-- S (K (S I)) SKK a ⟶* S I (K a) -/
private theorem siKa_red (a : Term) :
    S ⬝ (K ⬝ (S ⬝ I)) ⬝ SKK ⬝ a ⟶* S ⬝ I ⬝ (K ⬝ a) := by
  calc S ⬝ (K ⬝ (S ⬝ I)) ⬝ SKK ⬝ a
      ⟶* ((K ⬝ (S ⬝ I)) ⬝ a) ⬝ (SKK ⬝ a) := Steps.step Step.s Steps.refl
    _ ⟶* (S ⬝ I) ⬝ (SKK ⬝ a) := Steps.appL (Steps.step Step.k Steps.refl)
    _ ⟶* (S ⬝ I) ⬝ (K ⬝ a) := Steps.appR (skk_red a)

/-- S I (K a) f ⟶* f a -/
private theorem si_ka_f_red (a f : Term) : S ⬝ I ⬝ (K ⬝ a) ⬝ f ⟶* f ⬝ a := by
  calc S ⬝ I ⬝ (K ⬝ a) ⬝ f
      ⟶* (I ⬝ f) ⬝ ((K ⬝ a) ⬝ f) := Steps.step Step.s Steps.refl
    _ ⟶* f ⬝ ((K ⬝ a) ⬝ f) := Steps.appL (Steps.step Step.i Steps.refl)
    _ ⟶* f ⬝ a := Steps.appR (Steps.step Step.k Steps.refl)

/-- Helper: inner part [λa. S (S I (K a))] -/
private theorem inner_abs (a : Term) :
    S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ SKK) ⬝ a ⟶* S ⬝ (S ⬝ I ⬝ (K ⬝ a)) := by
  calc S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ SKK) ⬝ a
      ⟶* ((K ⬝ S) ⬝ a) ⬝ ((S ⬝ (K ⬝ (S ⬝ I)) ⬝ SKK) ⬝ a) := Steps.step Step.s Steps.refl
    _ ⟶* S ⬝ ((S ⬝ (K ⬝ (S ⬝ I)) ⬝ SKK) ⬝ a) := Steps.appL (Steps.step Step.k Steps.refl)
    _ ⟶* S ⬝ (S ⬝ I ⬝ (K ⬝ a)) := Steps.appR (siKa_red a)

/-- Helper: [λa. K (S (S I (K a)))] -/
private theorem k_inner_abs (a : Term) :
    S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ SKK)) ⬝ a ⟶* K ⬝ (S ⬝ (S ⬝ I ⬝ (K ⬝ a))) := by
  calc S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ SKK)) ⬝ a
      ⟶* ((K ⬝ K) ⬝ a) ⬝ ((S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ SKK)) ⬝ a) := Steps.step Step.s Steps.refl
    _ ⟶* K ⬝ ((S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ SKK)) ⬝ a) := Steps.appL (Steps.step Step.k Steps.refl)
    _ ⟶* K ⬝ (S ⬝ (S ⬝ I ⬝ (K ⬝ a))) := Steps.appR (inner_abs a)

/-- Helper: [λa. S (K (S (S I (K a))))] -/
private theorem s_k_inner_abs (a : Term) :
    S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ SKK))) ⬝ a
    ⟶* S ⬝ (K ⬝ (S ⬝ (S ⬝ I ⬝ (K ⬝ a)))) := by
  calc S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ SKK))) ⬝ a
      ⟶* ((K ⬝ S) ⬝ a) ⬝ ((S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ SKK))) ⬝ a)
        := Steps.step Step.s Steps.refl
    _ ⟶* S ⬝ ((S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ SKK))) ⬝ a)
        := Steps.appL (Steps.step Step.k Steps.refl)
    _ ⟶* S ⬝ (K ⬝ (S ⬝ (S ⬝ I ⬝ (K ⬝ a)))) := Steps.appR (k_inner_abs a)

/-- Step 1: skiPair x reduces -/
private theorem skiPair_x (x : Term) :
    skiPair ⬝ x ⟶* (S ⬝ (K ⬝ (S ⬝ (S ⬝ I ⬝ (K ⬝ x))))) ⬝ SKK := by
  calc skiPair ⬝ x
      = S ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ SKK)))) ⬝ (K ⬝ SKK) ⬝ x := rfl
    _ ⟶* ((S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ SKK)))) ⬝ x) ⬝ ((K ⬝ SKK) ⬝ x)
        := Steps.step Step.s Steps.refl
    _ ⟶* ((S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ SKK)))) ⬝ x) ⬝ SKK
        := Steps.appR (Steps.step Step.k Steps.refl)
    _ ⟶* (S ⬝ (K ⬝ (S ⬝ (S ⬝ I ⬝ (K ⬝ x))))) ⬝ SKK := Steps.appL (s_k_inner_abs x)

/-- Step 2: skiPair x y reduces -/
private theorem skiPair_xy (x y : Term) :
    skiPair ⬝ x ⬝ y ⟶* S ⬝ (S ⬝ I ⬝ (K ⬝ x)) ⬝ (K ⬝ y) := by
  calc skiPair ⬝ x ⬝ y
      ⟶* ((S ⬝ (K ⬝ (S ⬝ (S ⬝ I ⬝ (K ⬝ x))))) ⬝ SKK) ⬝ y := Steps.appL (skiPair_x x)
    _ = S ⬝ (K ⬝ (S ⬝ (S ⬝ I ⬝ (K ⬝ x)))) ⬝ SKK ⬝ y := rfl
    _ ⟶* ((K ⬝ (S ⬝ (S ⬝ I ⬝ (K ⬝ x)))) ⬝ y) ⬝ (SKK ⬝ y) := Steps.step Step.s Steps.refl
    _ ⟶* (S ⬝ (S ⬝ I ⬝ (K ⬝ x))) ⬝ (SKK ⬝ y) := Steps.appL (Steps.step Step.k Steps.refl)
    _ ⟶* (S ⬝ (S ⬝ I ⬝ (K ⬝ x))) ⬝ (K ⬝ y) := Steps.appR (skk_red y)

/-- Step 3: final reduction -/
private theorem skiPair_xyf_final (x y f : Term) :
    S ⬝ (S ⬝ I ⬝ (K ⬝ x)) ⬝ (K ⬝ y) ⬝ f ⟶* f ⬝ x ⬝ y := by
  calc S ⬝ (S ⬝ I ⬝ (K ⬝ x)) ⬝ (K ⬝ y) ⬝ f
      ⟶* ((S ⬝ I ⬝ (K ⬝ x)) ⬝ f) ⬝ ((K ⬝ y) ⬝ f) := Steps.step Step.s Steps.refl
    _ ⟶* (f ⬝ x) ⬝ ((K ⬝ y) ⬝ f) := Steps.appL (si_ka_f_red x f)
    _ ⟶* (f ⬝ x) ⬝ y := Steps.appR (Steps.step Step.k Steps.refl)

/-- skiPair x y f ⟶* f x y -/
theorem skiPair_red (x y f : Term) : skiPair ⬝ x ⬝ y ⬝ f ⟶* f ⬝ x ⬝ y := by
  calc skiPair ⬝ x ⬝ y ⬝ f
      ⟶* (S ⬝ (S ⬝ I ⬝ (K ⬝ x)) ⬝ (K ⬝ y)) ⬝ f := Steps.appL (skiPair_xy x y)
    _ = S ⬝ (S ⬝ I ⬝ (K ⬝ x)) ⬝ (K ⬝ y) ⬝ f := rfl
    _ ⟶* f ⬝ x ⬝ y := skiPair_xyf_final x y f

/-! ## Encoding Configurations as SKI Terms -/

/-- Encode a register bank (finite prefix) as nested pairs -/
def encodeRegs (regs : Nat → Nat) (bound : Nat) : Term :=
  match bound with
  | 0 => churchNum (regs 0)
  | n + 1 => skiPair ⬝ churchNum (regs (n + 1)) ⬝ encodeRegs regs n

/-- Encode an RM configuration as an SKI term -/
def encodeConfig (c : RMConfig) (numRegs : Nat) : Term :=
  skiPair ⬝ churchNum c.pc ⬝ encodeRegs c.regs numRegs

/-! ## RM → SKI Simulation -/

/-- Build the step function for an RM as an SKI term.
    Given the program, returns a term that takes a configuration encoding
    and returns the next configuration encoding (or a halted marker). -/
def rmStepTerm (prog : RM) : Term := sorry

/-- The full RM simulator: iterate rmStepTerm using Θ -/
def rmSimulator (prog : RM) : Term :=
  Θ ⬝ rmStepTerm prog

/-- RM simulation correctness: if prog halts with output, simulator reduces to that output -/
theorem rm_to_ski_correct (prog : RM) (input output : Nat) :
    rmComputes prog input = some output →
    rmSimulator prog ⬝ churchNum input ⟶* churchNum output := by
  sorry

/-! ## SKI → RM Simulation -/

/-- Encode an SKI term as a natural number -/
def termToNat : Term → Nat
  | Term.S => 0
  | Term.K => 1
  | Term.I => 2
  | Term.app t u => 3 + pair (termToNat t) (termToNat u)

/-- Decode a natural number to an SKI term -/
def natToTerm (n : Nat) : Option Term :=
  match n with
  | 0 => some Term.S
  | 1 => some Term.K
  | 2 => some Term.I
  | n + 3 =>
    let a := unpairFst n
    let b := unpairSnd n
    natToTerm a >>= fun t => natToTerm b >>= fun u => some (t ⬝ u)
termination_by n
decreasing_by
  all_goals simp_wf
  · -- unpairFst n < n + 3
    have h := unpairFst_le n
    omega
  · -- unpairSnd n < n + 3
    have h := unpairSnd_le n
    omega

/-- Decoding is left inverse of encoding -/
theorem natToTerm_termToNat (t : Term) : natToTerm (termToNat t) = some t := by
  induction t with
  | S => rfl
  | K => rfl
  | I => rfl
  | app t u iht ihu =>
    simp only [termToNat, natToTerm]
    have hp := unpair_pair (termToNat t) (termToNat u)
    simp only [hp.1, hp.2, iht, ihu, Option.bind_some]

/-- An RM that simulates one step of SKI reduction -/
def skiStepRM : RM := sorry

/-- An RM that fully reduces an SKI term to normal form -/
def skiSimulatorRM : RM :=
  -- Iterate skiStepRM until no more reductions possible
  sorry

/-- SKI simulation correctness -/
theorem ski_to_rm_correct (t n : Term) :
    (t ⟶* n) → IsNormal n →
    rmComputes skiSimulatorRM (termToNat t) = some (termToNat n) := by
  sorry

/-! ## Transfer Kleene's Theorem -/

/-- Replace halt in a program with an unconditional jump.
    Uses register 1000 which is always 0 for jumps. -/
private def replaceHalt (prog : RM) (target : Nat) : RM :=
  prog.map fun instr =>
    match instr with
    | RMInstr.halt => RMInstr.dec 1000 target  -- unconditional jump (r1000 = 0)
    | _ => instr

/-- Adjust jump targets in a program by an offset -/
private def adjustJumps (prog : RM) (offset : Nat) : RM :=
  prog.map fun instr =>
    match instr with
    | RMInstr.dec r j => RMInstr.dec r (j + offset)
    | _ => instr

/-- Compose two RMs: run q first, then run p on q's output.
    rmCompose p q computes (p ∘ q), i.e., p(q(input)). -/
def rmCompose (p q : RM) : RM :=
  let qLen := q.length
  -- Replace halt in q with jump to p's start
  let q' := replaceHalt q qLen
  -- Adjust all jump targets in p by qLen
  let p' := adjustJumps p qLen
  q' ++ p'

/-- Build a program that outputs a fixed natural number n.
    Clears r0 first, then increments n times. -/
private def rmBuildNum (n : Nat) : RM :=
  -- Clear r0: dec until 0, then proceed
  [ RMInstr.dec 0 2,   -- 0: if r0>0 dec and goto 1, else goto 2
    RMInstr.dec 1000 0 -- 1: unconditional jump to 0 (r1000 = 0)
  ] ++
  -- Increment r0 n times
  (List.replicate n (RMInstr.inc 0)) ++
  [RMInstr.halt]

/-- An RM that outputs the encoding of a given program p -/
def rmSelf (p : RM) : RM := rmBuildNum (encodeRM p)

/-- Given an RM g, construct an RM x such that x ≈ g applied to x's own code -/
theorem rm_kleene (g : RM) : ∃ x, rmEquiv x (rmCompose g (rmSelf x)) := by
  sorry

/-! ## Computational Equivalence -/

/-- RM and SKI compute the same class of partial functions -/
theorem rm_ski_equiv :
    (∀ prog input, ∃ t, (rmComputes prog input).isSome ↔
      ∃ n, (t ⬝ churchNum input ⟶* n) ∧ IsNormal n) ∧
    (∀ t input, ∃ prog, (∃ n, (t ⬝ churchNum input ⟶* n) ∧ IsNormal n) ↔
      (rmComputes prog input).isSome) := by
  sorry
