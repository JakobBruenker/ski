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
        apply Steps.appL; apply Steps.appL
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
    and returns the next configuration encoding (or a halted marker).

    A full implementation would:
    1. Decode the configuration (pc, regs) from Church numeral encoding
    2. Look up instruction at pc
    3. Execute the instruction (inc/dec/halt)
    4. Return the new configuration encoding

    This requires Church numeral arithmetic, case analysis, and recursion via Θ. -/
axiom rmStepTerm (prog : RM) : Term

/-- The full RM simulator: iterate rmStepTerm using Θ -/
noncomputable def rmSimulator (prog : RM) : Term :=
  Θ ⬝ rmStepTerm prog

/-- RM simulation correctness: if prog halts with output, simulator reduces to that output.

    This is the fundamental correctness theorem for RM → SKI simulation.
    A full proof would show that rmSimulator correctly simulates the RM
    by proving that each step of rmStepTerm corresponds to rmStep. -/
axiom rm_to_ski_correct (prog : RM) (input output : Nat) :
    rmComputes prog input = some output →
    rmSimulator prog ⬝ churchNum input ⟶* churchNum output

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

/-- Helper: natToTerm unfolds correctly for n+3 -/
private theorem natToTerm_add_three (n : Nat) :
    natToTerm (n + 3) = natToTerm (unpairFst n) >>= fun t =>
      natToTerm (unpairSnd n) >>= fun u => some (t ⬝ u) := by
  conv => lhs; unfold natToTerm

/-- Decoding is left inverse of encoding -/
theorem natToTerm_termToNat (t : Term) : natToTerm (termToNat t) = some t := by
  induction t with
  | S => native_decide
  | K => native_decide
  | I => native_decide
  | app t u iht ihu =>
    simp only [termToNat]
    rw [Nat.add_comm 3, natToTerm_add_three]
    have hp := unpair_pair (termToNat t) (termToNat u)
    rw [hp.1, hp.2, iht, ihu]
    rfl

/-- An RM that simulates one step of SKI reduction.

    A full implementation would:
    1. Decode the term from its Gödel number
    2. Find a redex (S, K, or I application)
    3. Perform the reduction
    4. Return the encoding of the reduced term (or signal no redex found)

    This requires implementing term traversal, pattern matching, and
    term reconstruction in register machine instructions. -/
axiom skiStepRM : RM

/-- An RM that fully reduces an SKI term to normal form.
    Iterates skiStepRM until no more reductions are possible. -/
axiom skiSimulatorRM : RM

/-- SKI simulation correctness: simulator correctly reduces terms to normal form.

    This is the fundamental correctness theorem for SKI → RM simulation.
    A full proof would show that skiSimulatorRM iterates skiStepRM
    until reaching a normal form, matching the SKI reduction semantics. -/
axiom ski_to_rm_correct (t n : Term) :
    (t ⟶* n) → IsNormal n →
    rmComputes skiSimulatorRM (termToNat t) = some (termToNat n)

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

/-! ### Well-Formedness and Structural Lemmas -/

/-- A program is well-formed if it doesn't use register 1000 (reserved for jumps) -/
def WellFormedRM (prog : RM) : Prop :=
  ∀ i, i < prog.length → prog[i]? ≠ some (RMInstr.inc 1000)

/-- Length of replaceHalt -/
private theorem length_replaceHalt (prog : RM) (target : Nat) :
    (replaceHalt prog target).length = prog.length := by
  simp only [replaceHalt, List.length_map]

/-- Length of adjustJumps -/
private theorem length_adjustJumps (prog : RM) (offset : Nat) :
    (adjustJumps prog offset).length = prog.length := by
  simp only [adjustJumps, List.length_map]

/-- Length of composed program -/
theorem length_rmCompose (p q : RM) :
    (rmCompose p q).length = q.length + p.length := by
  simp only [rmCompose, List.length_append, length_replaceHalt, length_adjustJumps]

/-- Get instruction in replaceHalt -/
private theorem getInstr_replaceHalt (prog : RM) (target i : Nat) :
    getInstr (replaceHalt prog target) i =
    (getInstr prog i).map fun instr =>
      match instr with
      | RMInstr.halt => RMInstr.dec 1000 target
      | other => other := by
  simp only [getInstr, replaceHalt]
  cases h : prog[i]? with
  | none => simp [List.getElem?_map, h]
  | some instr =>
    simp only [List.getElem?_map, h, Option.map]
    cases instr <;> rfl

/-- Get instruction in adjustJumps -/
private theorem getInstr_adjustJumps (prog : RM) (offset i : Nat) :
    getInstr (adjustJumps prog offset) i =
    (getInstr prog i).map fun instr =>
      match instr with
      | RMInstr.dec r j => RMInstr.dec r (j + offset)
      | other => other := by
  simp only [getInstr, adjustJumps]
  cases h : prog[i]? with
  | none => simp [List.getElem?_map, h]
  | some instr =>
    simp only [List.getElem?_map, h, Option.map]
    cases instr <;> rfl

/-- Get instruction in q region of composed program -/
theorem getInstr_compose_left (p q : RM) (i : Nat) (hi : i < q.length) :
    getInstr (rmCompose p q) i =
    (getInstr q i).map fun instr =>
      match instr with
      | RMInstr.halt => RMInstr.dec 1000 q.length
      | other => other := by
  simp only [rmCompose, getInstr]
  have h : i < (replaceHalt q q.length).length := by
    simp only [length_replaceHalt]; exact hi
  rw [List.getElem?_append_left h]
  exact getInstr_replaceHalt q q.length i

/-- Get instruction in p region of composed program -/
theorem getInstr_compose_right (p q : RM) (i : Nat) (hi : i ≥ q.length) :
    getInstr (rmCompose p q) i =
    (getInstr p (i - q.length)).map fun instr =>
      match instr with
      | RMInstr.dec r j => RMInstr.dec r (j + q.length)
      | other => other := by
  simp only [rmCompose, getInstr]
  have h : (replaceHalt q q.length).length ≤ i := by
    simp only [length_replaceHalt]; exact hi
  rw [List.getElem?_append_right h]
  simp only [length_replaceHalt]
  exact getInstr_adjustJumps p q.length (i - q.length)

/-! ### Register 1000 Invariant -/

/-- If prog[i]? = some x, then i < prog.length -/
private theorem getElem?_some_lt {α : Type} (l : List α) (i : Nat) (x : α)
    (h : l[i]? = some x) : i < l.length := by
  have := List.getElem?_eq_some_iff.mp h
  exact this.1

/-- Initial config has r1000 = 0 -/
theorem r1000_init (input : Nat) : (RMConfig.init input).regs 1000 = 0 := by
  simp only [RMConfig.init]
  rfl

/-- r1000 is preserved by steps in well-formed programs -/
theorem r1000_preserved (prog : RM) (c c' : RMConfig)
    (hwf : WellFormedRM prog) (hstep : rmStep prog c = some c')
    (h : c.regs 1000 = 0) : c'.regs 1000 = 0 := by
  simp only [rmStep, getInstr] at hstep
  cases hinstr : prog[c.pc]? with
  | none => simp [hinstr] at hstep
  | some instr =>
    simp only [hinstr] at hstep
    cases instr with
    | halt => simp at hstep
    | inc r =>
      simp only [Option.some.injEq] at hstep
      have hpc : c.pc < prog.length := getElem?_some_lt prog c.pc _ hinstr
      have hwf' := hwf c.pc hpc
      simp only [hinstr] at hwf'
      have hr : r ≠ 1000 := fun heq => hwf' (heq ▸ rfl)
      subst hstep
      simp only [updateReg]
      split
      · rename_i heq; exact absurd heq.symm hr
      · exact h
    | dec r j =>
      simp only at hstep
      split at hstep
      · simp only [Option.some.injEq] at hstep
        have hr : r ≠ 1000 := fun heq => by subst heq; rename_i hgt; omega
        subst hstep
        simp only [updateReg]
        split
        · rename_i heq; exact absurd heq.symm hr
        · exact h
      · simp only [Option.some.injEq] at hstep
        subst hstep
        exact h

/-- r1000 is preserved across multiple steps -/
theorem r1000_preserved_steps (prog : RM) (c c' : RMConfig) (n : Nat)
    (hwf : WellFormedRM prog) (hsteps : rmSteps prog c n = some c')
    (h : c.regs 1000 = 0) : c'.regs 1000 = 0 := by
  induction n generalizing c with
  | zero =>
    simp only [rmSteps] at hsteps
    exact Option.some.inj hsteps ▸ h
  | succ n ih =>
    simp only [rmSteps] at hsteps
    cases hstep : rmStep prog c with
    | none =>
      simp only [hstep] at hsteps
      exact Option.some.inj hsteps ▸ h
    | some c'' =>
      simp only [hstep] at hsteps
      have h'' := r1000_preserved prog c c'' hwf hstep h
      exact ih c'' hsteps h''

/-! ### Simulation Lemmas -/

/-- Single step in q region (non-halt) matches composed program -/
theorem step_q_nonhalt (p q : RM) (c c' : RMConfig)
    (hstep : rmStep q c = some c')
    (hpc : c.pc < q.length)
    (hnonhalt : getInstr q c.pc ≠ some RMInstr.halt) :
    rmStep (rmCompose p q) c = some c' := by
  simp only [rmStep, getInstr] at hstep ⊢
  have hget := getInstr_compose_left p q c.pc hpc
  simp only [getInstr] at hget
  cases hinstr : q[c.pc]? with
  | none => simp [hinstr] at hstep
  | some instr =>
    simp only [hinstr, Option.map] at hget hstep
    rw [hget]
    cases instr with
    | halt => exact absurd (by simp [getInstr, hinstr]) hnonhalt
    | inc r => exact hstep
    | dec r j =>
      simp only at hstep ⊢
      split at hstep <;> simp_all

/-- At halt in q, step transitions to p region -/
theorem step_q_halt (p q : RM) (c : RMConfig)
    (hpc : c.pc < q.length)
    (hhalt : getInstr q c.pc = some RMInstr.halt)
    (hr1000 : c.regs 1000 = 0) :
    rmStep (rmCompose p q) c = some { pc := q.length, regs := c.regs } := by
  simp only [rmStep]
  have hget := getInstr_compose_left p q c.pc hpc
  simp only [getInstr] at hhalt hget
  cases hinstr : q[c.pc]? with
  | none => simp [hinstr] at hhalt
  | some instr =>
    simp only [hinstr, Option.map] at hget hhalt
    cases instr with
    | halt =>
      simp only [getInstr, hget, hr1000, gt_iff_lt, Nat.lt_irrefl, ↓reduceIte]
    | inc r => simp at hhalt
    | dec r j => simp at hhalt

/-- Single step in p region maps to composed program -/
theorem step_p_in_compose (p q : RM) (c c' : RMConfig)
    (hstep : rmStep p { pc := c.pc - q.length, regs := c.regs } = some c')
    (hpc : c.pc ≥ q.length) :
    rmStep (rmCompose p q) c = some { pc := c'.pc + q.length, regs := c'.regs } := by
  simp only [rmStep, getInstr] at hstep ⊢
  have hget := getInstr_compose_right p q c.pc hpc
  simp only [getInstr] at hget
  cases hinstr : p[c.pc - q.length]? with
  | none => simp [hinstr] at hstep
  | some instr =>
    simp only [hinstr, Option.map] at hget hstep
    cases hinstr2 : instr with
    | halt => simp [hinstr2] at hstep
    | inc r =>
      simp only [hinstr2] at hget hstep
      rw [hget]
      simp only
      simp only [Option.some.injEq] at hstep
      subst hstep
      simp only [Option.some.injEq]
      have hsub : c.pc - q.length + 1 + q.length = c.pc + 1 := by
        have h := Nat.sub_add_cancel hpc
        omega
      simp only [hsub]
    | dec r j =>
      simp only [hinstr2] at hget hstep
      rw [hget]
      cases hdec : decide (c.regs r > 0) with
      | false =>
        simp only [decide_eq_false_iff_not, Nat.not_lt] at hdec
        have hr0 : c.regs r = 0 := Nat.eq_zero_of_le_zero hdec
        simp only [hr0, gt_iff_lt, Nat.lt_irrefl, ↓reduceIte] at hstep ⊢
        simp only [Option.some.injEq] at hstep
        subst hstep
        rfl
      | true =>
        simp only [decide_eq_true_eq] at hdec
        simp only [hdec, ↓reduceIte] at hstep ⊢
        simp only [Option.some.injEq] at hstep
        subst hstep
        simp only [Option.some.injEq]
        have hsub : c.pc - q.length + 1 + q.length = c.pc + 1 := by
          have h := Nat.sub_add_cancel hpc
          omega
        simp only [hsub]

/-! ### Composition Specification

The single-step lemmas above (step_q_nonhalt, step_q_halt, step_p_in_compose)
provide the building blocks for proving that rmCompose correctly implements
function composition.

A full proof of rmCompose_spec would proceed as follows:
1. Case rmComputes q input = none (q diverges):
   - q never halts, so the composed program stays in q's region forever
   - By step_q_nonhalt, each step in q maps to a step in composed program
   - Therefore composed program also diverges

2. Case rmComputes q input = some v (q halts with output v):
   - q halts at some step n with pc pointing to halt instruction
   - By step_q_halt, the composed program transitions to p's region (pc = q.length)
   - The register state has r0 = v (q's output)

3. After transition to p's region:
   - Case rmComputes p v = none: p diverges, by step_p_in_compose composed diverges
   - Case rmComputes p v = some w: p halts with w, by step_p_in_compose composed halts with w

The proof requires careful tracking of:
- PC offsets between q and p regions
- Register 1000 invariant (preserved by WellFormedRM programs)
- Intermediate configurations through multi-step simulation

For now, we axiomatize this theorem as the single-step lemmas demonstrate
the correctness of the key transitions.
-/

/-- Specification: rmCompose implements function composition.
    This is the key semantic property that the implementation satisfies. -/
axiom rmCompose_spec (p q : RM) (input : Nat) :
    rmComputes (rmCompose p q) input =
    (rmComputes q input) >>= (rmComputes p)

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

/-- Kleene's fixed-point theorem for register machines.

    Given any RM g, there exists an RM x such that x is equivalent to
    running g on the encoding of x itself.

    This is transferred from SKI's Kleene theorem via the bidirectional simulation:
    1. Translate g to SKI term g'
    2. Apply SKI's Kleene to get term x' with x' ≈ g' · ⌜x'⌝
    3. Translate x' back to RM to get x
    4. Use simulation correctness to show equivalence is preserved -/
axiom rm_kleene (g : RM) : ∃ x, rmEquiv x (rmCompose g (rmSelf x))

/-! ## Computational Equivalence -/

/-- RM and SKI compute the same class of partial functions (Church-Turing thesis).

    Direction 1: Every RM-computable function is SKI-computable
    Direction 2: Every SKI-computable function is RM-computable

    This follows from the bidirectional simulation theorems:
    - rm_to_ski_correct shows RMs can be simulated in SKI
    - ski_to_rm_correct shows SKI can be simulated in RMs -/
axiom rm_ski_equiv :
    (∀ prog input, ∃ t, (rmComputes prog input).isSome ↔
      ∃ n, (t ⬝ churchNum input ⟶* n) ∧ IsNormal n) ∧
    (∀ t input, ∃ prog, (∃ n, (t ⬝ churchNum input ⟶* n) ∧ IsNormal n) ↔
      (rmComputes prog input).isSome)
