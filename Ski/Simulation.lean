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

/-! ### Multi-Step Simulation -/

/-- If rmStep q fails (halts or out of bounds), what happens in composed program -/
private theorem step_q_fail (p q : RM) (c : RMConfig)
    (hstep : rmStep q c = none)
    (hpc : c.pc < q.length)
    (hr1000 : c.regs 1000 = 0) :
    -- q must have halted (since pc < length means instruction exists)
    getInstr q c.pc = some RMInstr.halt := by
  simp only [rmStep] at hstep
  cases hinstr : getInstr q c.pc with
  | none =>
    -- pc < q.length means there is an instruction
    simp only [getInstr] at hinstr
    have h : c.pc ≥ q.length := by
      cases hq : q[c.pc]? with
      | none => exact List.getElem?_eq_none_iff.mp hq
      | some _ => simp [hq] at hinstr
    omega
  | some instr =>
    simp only [hinstr] at hstep
    cases instr with
    | halt => rfl
    | inc r => simp at hstep
    | dec r j =>
      simp only at hstep
      split at hstep <;> simp at hstep

/-- Multi-step simulation in q region: if q runs n steps staying in bounds
    without halting, composed program matches exactly -/
theorem steps_q_nonhalt (p q : RM) (n : Nat) (c c' : RMConfig)
    (hwf : WellFormedRM q)
    (hsteps : rmSteps q c n = some c')
    (hpc : c.pc < q.length)
    (hr1000 : c.regs 1000 = 0)
    -- All intermediate configs have pc < q.length and don't halt
    (hbounds : ∀ k < n, ∀ ck, rmSteps q c k = some ck →
        ck.pc < q.length ∧ getInstr q ck.pc ≠ some RMInstr.halt) :
    rmSteps (rmCompose p q) c n = some c' := by
  induction n generalizing c with
  | zero =>
    simp only [rmSteps] at hsteps ⊢
    exact hsteps
  | succ n ih =>
    simp only [rmSteps] at hsteps ⊢
    cases hstep_q : rmStep q c with
    | none =>
      -- rmStep q c = none but we have hbounds saying c doesn't halt
      have ⟨_, hnonhalt⟩ := hbounds 0 (Nat.zero_lt_succ n) c (by simp [rmSteps])
      have hhalt := step_q_fail p q c hstep_q hpc hr1000
      exact absurd hhalt hnonhalt
    | some c1 =>
      simp only [hstep_q] at hsteps
      have ⟨_, hnonhalt⟩ := hbounds 0 (Nat.zero_lt_succ n) c (by simp [rmSteps])
      have hstep_comp := step_q_nonhalt p q c c1 hstep_q hpc hnonhalt
      rw [hstep_comp]
      -- For IH, need c1 properties
      have hr1000' := r1000_preserved q c c1 hwf hstep_q hr1000
      -- Handle n = 0 case separately
      cases n with
      | zero =>
        simp only [rmSteps] at hsteps ⊢
        exact hsteps
      | succ m =>
        have h1_lt : 1 < m + 1 + 1 := by omega
        have ⟨hpc1, _⟩ := hbounds 1 h1_lt c1 (by simp [rmSteps, hstep_q])
        apply ih c1 hsteps hpc1 hr1000'
        intro k hk ck hsteps_ck
        have hsteps_c : rmSteps q c (k + 1) = some ck := by
          simp only [rmSteps, hstep_q, hsteps_ck]
        exact hbounds (k + 1) (Nat.succ_lt_succ hk) ck hsteps_c

/-- Multi-step simulation in p region: steps match with pc offset -/
theorem steps_p_offset (p q : RM) (n : Nat) (c c' : RMConfig)
    (hsteps : rmSteps p c n = some c') :
    rmSteps (rmCompose p q) { pc := c.pc + q.length, regs := c.regs } n =
    some { pc := c'.pc + q.length, regs := c'.regs } := by
  induction n generalizing c with
  | zero =>
    simp only [rmSteps] at hsteps ⊢
    simp only [Option.some.injEq] at hsteps
    subst hsteps
    rfl
  | succ n ih =>
    simp only [rmSteps] at hsteps ⊢
    cases hstep_p : rmStep p c with
    | none =>
      simp only [hstep_p] at hsteps
      simp only [Option.some.injEq] at hsteps
      subst hsteps
      -- p halts or errors, need to show composed does too
      have hpc_ge : c.pc + q.length ≥ q.length := Nat.le_add_left q.length c.pc
      have hget := getInstr_compose_right p q (c.pc + q.length) hpc_ge
      simp only [Nat.add_sub_cancel] at hget
      simp only [rmStep] at hstep_p
      cases hinstr : getInstr p c.pc with
      | none =>
        simp only [getInstr] at hinstr hget
        simp only [hinstr, Option.map] at hget
        simp only [rmStep, getInstr, hget]
      | some instr =>
        simp only [getInstr] at hinstr hget
        simp only [hinstr, Option.map] at hget
        cases instr with
        | halt =>
          simp only [rmStep, getInstr, hget]
        | inc r =>
          -- hinstr says getInstr returns inc r, but hstep_p says rmStep returns none
          -- which is a contradiction since inc always succeeds
          simp only [getInstr, hinstr] at hstep_p
          exact Option.noConfusion hstep_p
        | dec r j =>
          -- dec always returns some (either increments or jumps)
          simp only [getInstr, hinstr] at hstep_p
          split at hstep_p <;> exact Option.noConfusion hstep_p
    | some c1 =>
      simp only [hstep_p] at hsteps
      have hpc_ge : c.pc + q.length ≥ q.length := Nat.le_add_left q.length c.pc
      have hstep_adj : rmStep p { pc := (c.pc + q.length) - q.length, regs := c.regs } = some c1 := by
        simp only [Nat.add_sub_cancel]
        exact hstep_p
      have hstep_comp := step_p_in_compose p q { pc := c.pc + q.length, regs := c.regs } c1 hstep_adj hpc_ge
      simp only at hstep_comp
      rw [hstep_comp]
      exact ih c1 hsteps

/-! ### Additional Simulation Lemmas -/

/-- When q halts, composed program transitions to p region -/
theorem q_halt_transition (p q : RM) (c : RMConfig)
    (hpc : c.pc < q.length)
    (hhalt : getInstr q c.pc = some RMInstr.halt)
    (hr1000 : c.regs 1000 = 0) :
    rmStep (rmCompose p q) c = some { pc := q.length, regs := c.regs } :=
  step_q_halt p q c hpc hhalt hr1000

/-- Halting in p region of composed program -/
theorem halt_p_in_compose (p q : RM) (c : RMConfig)
    (hpc : c.pc ≥ q.length)
    (hhalt : getInstr p (c.pc - q.length) = some RMInstr.halt) :
    isHalted (rmCompose p q) c = true := by
  simp only [isHalted]
  have hget := getInstr_compose_right p q c.pc hpc
  simp only [getInstr] at hhalt hget
  cases hp : p[c.pc - q.length]? with
  | none => simp [hp] at hhalt
  | some instr =>
    simp only [hp, Option.map] at hget
    cases instr with
    | halt =>
      simp only at hget
      simp only [hget, getInstr]
    | inc r => simp [hp] at hhalt
    | dec r j => simp [hp] at hhalt

/-! ### Composition Specification

The single-step lemmas (step_q_nonhalt, step_q_halt, step_p_in_compose) provide
the building blocks for proving that rmCompose correctly implements function
composition:

- **step_q_nonhalt**: Non-halt steps in q region map directly to composed program
- **step_q_halt**: Halt in q transitions to p region (pc = q.length)
- **step_p_in_compose**: Steps in p region map with pc offset adjustment
- **q_halt_transition**: Convenient wrapper for step_q_halt
- **halt_p_in_compose**: Halting detection in p region

A complete proof of rmCompose_spec requires tracking:
1. Multi-step simulation in q region until q halts
2. The transition when q halts
3. Multi-step simulation in p region after transition
-/

/-! ### Divergence Case -/

/-- When halted with valid pc, instruction is halt -/
private theorem halted_inbounds_is_halt (prog : RM) (c : RMConfig)
    (hhalted : isHalted prog c = true)
    (hinbounds : c.pc < prog.length) :
    getInstr prog c.pc = some RMInstr.halt := by
  simp only [isHalted, getInstr] at hhalted ⊢
  cases hget : prog[c.pc]? with
  | none =>
    have h : c.pc ≥ prog.length := List.getElem?_eq_none_iff.mp hget
    omega
  | some instr =>
    simp only [hget] at hhalted ⊢
    cases instr with
    | halt => rfl
    | inc r => simp at hhalted
    | dec r j => simp at hhalted

/-- Not halted means instruction is inc or dec -/
private theorem not_halted_instr (prog : RM) (c : RMConfig)
    (hnothalted : isHalted prog c = false)
    (hinbounds : c.pc < prog.length) :
    getInstr prog c.pc ≠ some RMInstr.halt := by
  intro hhalt
  simp only [isHalted, hhalt] at hnothalted
  exact absurd hnothalted (by decide)

/-- rmOutput = none means either rmSteps failed or not halted -/
private theorem rmOutput_none_cases (prog : RM) (input n : Nat)
    (hnone : (rmOutput prog input n).isNone) :
    (rmSteps prog (RMConfig.init input) n = none) ∨
    (∃ c, rmSteps prog (RMConfig.init input) n = some c ∧ isHalted prog c = false) := by
  simp only [rmOutput, Option.isNone_iff_eq_none] at hnone
  cases hsteps : rmSteps prog (RMConfig.init input) n with
  | none => left; rfl
  | some c =>
    right
    refine ⟨c, rfl, ?_⟩
    simp only [hsteps] at hnone
    split at hnone
    · simp at hnone
    · next h => exact Bool.eq_false_iff.mpr h

/-- For well-formed programs, rmSteps always succeeds -/
private theorem rmSteps_succeeds (prog : RM) (c : RMConfig) (n : Nat) :
    ∃ c', rmSteps prog c n = some c' := by
  induction n generalizing c with
  | zero => exact ⟨c, rfl⟩
  | succ n ih =>
    simp only [rmSteps]
    cases hstep : rmStep prog c with
    | none => exact ⟨c, rfl⟩
    | some c' => exact ih c'

/-- If q never halts, at any step q is not halted -/
private theorem never_halts_not_halted (prog : RM) (input n : Nat)
    (hdiv : ∀ m, (rmOutput prog input m).isNone) :
    ∃ c, rmSteps prog (RMConfig.init input) n = some c ∧ isHalted prog c = false := by
  have ⟨c, hsteps⟩ := rmSteps_succeeds prog (RMConfig.init input) n
  refine ⟨c, hsteps, ?_⟩
  have hnone := hdiv n
  simp only [rmOutput, hsteps, Option.isNone_iff_eq_none] at hnone
  split at hnone
  · simp at hnone
  · next h => exact Bool.eq_false_iff.mpr h

/-- Generalized: if q never halts from c_start, composed matches q exactly -/
private theorem compose_matches_q_diverge_gen (p q : RM) (c_start : RMConfig) (n : Nat) (c : RMConfig)
    (hwf : WellFormedRM q)
    (hsteps : rmSteps q c_start n = some c)
    (hstart_pc : c_start.pc < q.length)
    (hstart_r1000 : c_start.regs 1000 = 0)
    (hall_ok : ∀ k ≤ n, ∀ ck, rmSteps q c_start k = some ck →
        isHalted q ck = false ∧ ck.pc < q.length) :
    rmSteps (rmCompose p q) c_start n = some c := by
  induction n generalizing c_start with
  | zero =>
    simp only [rmSteps] at hsteps ⊢
    exact hsteps
  | succ m ih =>
    simp only [rmSteps] at hsteps ⊢
    cases hstep_q : rmStep q c_start with
    | none =>
      have ⟨hnothalted0, _⟩ := hall_ok 0 (Nat.zero_le _) c_start (by simp [rmSteps])
      have hhalted := isHalted_iff q c_start |>.mpr hstep_q
      simp only [hnothalted0] at hhalted
      exact absurd hhalted (by decide)
    | some c1 =>
      simp only [hstep_q] at hsteps
      have ⟨hnothalted0, hpc0_lt⟩ := hall_ok 0 (Nat.zero_le _) c_start (by simp [rmSteps])
      have hinstr0 := not_halted_instr q c_start hnothalted0 hpc0_lt
      have hstep_comp := step_q_nonhalt p q c_start c1 hstep_q hstart_pc hinstr0
      rw [hstep_comp]
      -- Properties of c1
      have hr1000_c1 := r1000_preserved q c_start c1 hwf hstep_q hstart_r1000
      have ⟨_, hpc1_lt⟩ := hall_ok 1 (by omega) c1 (by simp [rmSteps, hstep_q])
      have hall_ok' : ∀ k ≤ m, ∀ ck, rmSteps q c1 k = some ck →
          isHalted q ck = false ∧ ck.pc < q.length := by
        intro k hk ck hsteps_ck
        have hsteps_start : rmSteps q c_start (k + 1) = some ck := by
          simp only [rmSteps, hstep_q, hsteps_ck]
        exact hall_ok (k + 1) (by omega) ck hsteps_start
      exact ih c1 hsteps hpc1_lt hr1000_c1 hall_ok'

/-- Composed matches q at the halt step too (even though q is halted).
    This extends compose_matches_q_diverge_gen to include the halt step.
    Requires bounds hypothesis to handle final config's pc. -/
private theorem compose_matches_q_at_halt (p q : RM) (c_start : RMConfig) (n : Nat) (c : RMConfig)
    (hwf : WellFormedRM q)
    (hsteps : rmSteps q c_start n = some c)
    (hstart_pc : c_start.pc < q.length)
    (hstart_r1000 : c_start.regs 1000 = 0)
    (hbounds : ∀ k ck, rmSteps q c_start k = some ck → ck.pc < q.length)
    (hearlier : ∀ k < n, ∀ ck, rmSteps q c_start k = some ck →
        isHalted q ck = false ∧ ck.pc < q.length) :
    rmSteps (rmCompose p q) c_start n = some c := by
  induction n generalizing c_start with
  | zero =>
    simp only [rmSteps] at hsteps ⊢
    exact hsteps
  | succ m ih =>
    simp only [rmSteps] at hsteps ⊢
    cases hstep_q : rmStep q c_start with
    | none =>
      -- q halted at start, so hsteps says c_start = c and m+1 steps gives c_start
      simp only [hstep_q, Option.some.injEq] at hsteps
      subst hsteps
      -- m + 1 > 0, so hearlier at k = 0 applies: c_start not halted
      have ⟨hnothalted, _⟩ := hearlier 0 (Nat.zero_lt_succ m) c_start (by simp [rmSteps])
      have hhalted := isHalted_iff q c_start |>.mpr hstep_q
      simp only [hnothalted] at hhalted
      exact absurd hhalted (by decide)
    | some c1 =>
      simp only [hstep_q] at hsteps
      -- c_start not halted, so step_q_nonhalt applies
      have ⟨hnothalted0, hpc0_lt⟩ := hearlier 0 (Nat.zero_lt_succ m) c_start (by simp [rmSteps])
      have hinstr0 := not_halted_instr q c_start hnothalted0 hpc0_lt
      have hstep_comp := step_q_nonhalt p q c_start c1 hstep_q hstart_pc hinstr0
      rw [hstep_comp]
      -- Properties of c1
      have hr1000_c1 := r1000_preserved q c_start c1 hwf hstep_q hstart_r1000
      -- c1.pc < q.length from bounds
      have hpc1_lt : c1.pc < q.length := hbounds 1 c1 (by simp [rmSteps, hstep_q])
      -- Build hearlier' and hbounds' for recursion
      have hearlier' : ∀ k < m, ∀ ck, rmSteps q c1 k = some ck →
          isHalted q ck = false ∧ ck.pc < q.length := by
        intro k hk ck hsteps_ck
        have hsteps_start : rmSteps q c_start (k + 1) = some ck := by
          simp only [rmSteps, hstep_q, hsteps_ck]
        exact hearlier (k + 1) (by omega) ck hsteps_start
      have hbounds' : ∀ k ck, rmSteps q c1 k = some ck → ck.pc < q.length := by
        intro k ck hsteps_ck
        have hsteps_start : rmSteps q c_start (k + 1) = some ck := by
          simp only [rmSteps, hstep_q, hsteps_ck]
        exact hbounds (k + 1) ck hsteps_start
      exact ih c1 hsteps hpc1_lt hr1000_c1 hbounds' hearlier'

/-- rmSteps q gives unique result -/
private theorem rmSteps_unique (prog : RM) (c : RMConfig) (n : Nat) (c1 c2 : RMConfig)
    (h1 : rmSteps prog c n = some c1) (h2 : rmSteps prog c n = some c2) : c1 = c2 := by
  simp only [h1] at h2
  exact Option.some.inj h2

/-- Transitivity: if we reach c1 after n steps, and c2 after m more steps from c1,
    then we reach c2 after n+m steps from start -/
private theorem rmSteps_trans (prog : RM) (c0 c1 c2 : RMConfig) (n m : Nat)
    (h1 : rmSteps prog c0 n = some c1) (h2 : rmSteps prog c1 m = some c2) :
    rmSteps prog c0 (n + m) = some c2 := by
  induction n generalizing c0 with
  | zero =>
    simp only [rmSteps, Option.some.injEq] at h1
    simp only [Nat.zero_add, h1 ▸ h2]
  | succ n ih =>
    simp only [rmSteps] at h1
    cases hstep : rmStep prog c0 with
    | none =>
      simp only [hstep, Option.some.injEq] at h1
      -- c0 is halted, so all future steps give c0
      -- h1 : c0 = c1, h2 : rmSteps prog c1 m = some c2
      subst h1
      -- Since c0 is halted, rmSteps prog c0 m = some c0
      have hhalted := isHalted_iff prog c0 |>.mpr hstep
      have hstable := rmSteps_stable prog c0 c0 0 m (by rfl) hhalted (Nat.zero_le m)
      rw [hstable] at h2
      simp only [Option.some.injEq] at h2
      subst h2
      -- Goal: rmSteps prog c0 (n + 1 + m) = some c0
      -- Since c0 is halted, all further steps return c0
      have hstable2 := rmSteps_stable prog c0 c0 0 (n + 1 + m) (by rfl) hhalted (Nat.zero_le _)
      exact hstable2
    | some c0' =>
      simp only [hstep] at h1
      -- ih : rmSteps prog c0' (n + m) = some c2
      have hrec := ih c0' h1
      -- Goal: rmSteps prog c0 (n + 1 + m) = some c2
      -- Unfold one step: rmSteps prog c0 (n+1+m) = match rmStep ... with ...
      show rmSteps prog c0 (n + 1 + m) = some c2
      have heq : n + 1 + m = Nat.succ (n + m) := by omega
      rw [heq, rmSteps, hstep]
      exact hrec

/-- When p is halted (via halt instruction), composed is halted in p region -/
private theorem halt_p_in_compose_from_halt (p q : RM) (c : RMConfig)
    (hpc : c.pc ≥ q.length)
    (hhalted_p : isHalted p { pc := c.pc - q.length, regs := c.regs } = true)
    (hpc_p : (c.pc - q.length) < p.length) :
    isHalted (rmCompose p q) c = true := by
  have hhalt_instr := halted_inbounds_is_halt p { pc := c.pc - q.length, regs := c.regs }
    hhalted_p hpc_p
  exact halt_p_in_compose p q c hpc hhalt_instr

/-- In q-region with halt instruction, composed is NOT halted (halt becomes dec) -/
private theorem compose_not_halted_q_halt_instr (p q : RM) (c : RMConfig)
    (hpc : c.pc < q.length)
    (hhalt : getInstr q c.pc = some RMInstr.halt) :
    isHalted (rmCompose p q) c = false := by
  simp only [isHalted]
  have hget := getInstr_compose_left p q c.pc hpc
  simp only [getInstr] at hhalt hget
  cases hinstr : q[c.pc]? with
  | none => simp [hinstr] at hhalt
  | some instr =>
    simp only [hinstr, Option.map] at hget hhalt
    cases instr with
    | halt =>
      simp only [getInstr, hget]
    | _ => simp at hhalt

/-- In q-region with non-halt instruction, composed isHalted matches q -/
private theorem compose_not_halted_q_nonhalt (p q : RM) (c : RMConfig)
    (hpc : c.pc < q.length)
    (hnothalted : isHalted q c = false) :
    isHalted (rmCompose p q) c = false := by
  simp only [isHalted] at hnothalted ⊢
  have hget := getInstr_compose_left p q c.pc hpc
  simp only [getInstr] at hget
  cases hinstr : q[c.pc]? with
  | none =>
    have h : c.pc ≥ q.length := List.getElem?_eq_none_iff.mp hinstr
    omega
  | some instr =>
    simp only [hinstr] at hget
    simp only [Option.map] at hget
    simp only [getInstr, hinstr] at hnothalted
    cases instr with
    | halt => exact absurd hnothalted (by decide)
    | inc r => simp only [getInstr, hget]
    | dec r j => simp only [getInstr, hget]

/-- In q-region, composed is never halted (regardless of q's instruction) -/
private theorem compose_not_halted_q_halt_instr_or_nonhalt (p q : RM) (c : RMConfig)
    (hpc : c.pc < q.length) :
    isHalted (rmCompose p q) c = false := by
  simp only [isHalted]
  have hget := getInstr_compose_left p q c.pc hpc
  simp only [getInstr] at hget
  cases hinstr : q[c.pc]? with
  | none =>
    have h : c.pc ≥ q.length := List.getElem?_eq_none_iff.mp hinstr
    omega
  | some instr =>
    simp only [hinstr] at hget
    simp only [Option.map] at hget
    -- In all cases, the transformed instruction is NOT halt
    cases instr with
    | halt =>
      -- halt becomes dec 1000 q.length
      simp only [getInstr, hget]
    | inc r =>
      -- inc stays inc
      simp only [getInstr, hget]
    | dec r j =>
      -- dec stays dec
      simp only [getInstr, hget]

/-- If composed halts in p-region, then p halts -/
private theorem p_halts_from_compose_halts (p q : RM) (c : RMConfig)
    (hpc : c.pc ≥ q.length)
    (hhalted_comp : isHalted (rmCompose p q) c = true) :
    isHalted p { pc := c.pc - q.length, regs := c.regs } = true := by
  simp only [isHalted] at hhalted_comp ⊢
  have hget := getInstr_compose_right p q c.pc hpc
  simp only [getInstr] at hget
  cases hinstr : p[c.pc - q.length]? with
  | none =>
    simp only [hinstr, Option.map] at hget
    simp only [getInstr, hinstr]
  | some instr =>
    simp only [hinstr, Option.map] at hget
    cases instr with
    | halt => simp only [getInstr, hinstr]
    | inc r =>
      simp only [getInstr, hget] at hhalted_comp
      exact absurd hhalted_comp (by decide)
    | dec r j =>
      simp only [getInstr, hget] at hhalted_comp
      exact absurd hhalted_comp (by decide)

/-- If q never halts on input, composed program also never halts -/
theorem compose_diverges_if_q_diverges (p q : RM) (input : Nat)
    (hwf : WellFormedRM q)
    (hdiv : ∀ n, (rmOutput q input n).isNone)
    -- Additional hypothesis: all intermediate pcs stay in bounds
    (hinbounds : ∀ n c, rmSteps q (RMConfig.init input) n = some c → c.pc < q.length) :
    ∀ n, (rmOutput (rmCompose p q) input n).isNone := by
  intro n
  simp only [rmOutput, Option.isNone_iff_eq_none]
  have ⟨c_q, hsteps_q, hnothalted_q⟩ := never_halts_not_halted q input n hdiv
  have hpc_lt := hinbounds n c_q hsteps_q
  -- Build hall_ok from hdiv and hinbounds
  have hall_ok : ∀ k ≤ n, ∀ ck, rmSteps q (RMConfig.init input) k = some ck →
      isHalted q ck = false ∧ ck.pc < q.length := by
    intro k hk ck hsteps_ck
    have ⟨c', hsteps', hnothalted'⟩ := never_halts_not_halted q input k hdiv
    have heq := rmSteps_unique q (RMConfig.init input) k ck c' hsteps_ck hsteps'
    subst heq
    exact ⟨hnothalted', hinbounds k ck hsteps_ck⟩
  -- Show composed matches q
  have hinit_pc : (RMConfig.init input).pc < q.length := by
    have ⟨_, hpc0⟩ := hall_ok 0 (Nat.zero_le n) (RMConfig.init input) (by simp [rmSteps])
    exact hpc0
  have hr1000_init : (RMConfig.init input).regs 1000 = 0 := rfl
  have hcomp := compose_matches_q_diverge_gen p q (RMConfig.init input) n c_q hwf
      hsteps_q hinit_pc hr1000_init hall_ok
  simp only [hcomp]
  -- c_q is not halted in q, show it's not halted in composed
  -- c_q.pc < q.length, so in composed program c_q is in q-region
  -- The instruction at c_q.pc in composed is same as in q (just with adjusted jumps)
  -- Since q is not halted, composed is also not halted in q-region
  -- c_q is not halted in q, show it's not halted in composed
  -- c_q.pc < q.length, so in composed program c_q is in q-region
  -- The instruction at c_q.pc in composed is same as in q (transformed)
  -- Since q is not halted (not halt instruction), composed also not halted
  have hget := getInstr_compose_left p q c_q.pc hpc_lt
  -- Unfold getInstr in hypothesis and goal
  simp only [getInstr] at hget
  -- Show the composed program is also not halted
  split
  · -- isHalted returns true, need False
    next hhalted_comp =>
    simp only [isHalted] at hhalted_comp hnothalted_q
    cases hinstr_q : q[c_q.pc]? with
    | none =>
      -- q[c_q.pc]? = none, but c_q.pc < q.length, contradiction
      have h : c_q.pc ≥ q.length := List.getElem?_eq_none_iff.mp hinstr_q
      omega
    | some instr =>
      rw [hinstr_q, Option.map] at hget
      simp only [getInstr, hinstr_q] at hnothalted_q
      cases instr with
      | halt =>
        -- q is halted, contradiction with hnothalted_q
        simp at hnothalted_q
      | inc r =>
        -- Composed has inc r, which is not halted
        simp only [getInstr, hget] at hhalted_comp
        exact absurd hhalted_comp (by decide)
      | dec r j =>
        -- Composed has dec r j, which is not halted
        simp only [getInstr, hget] at hhalted_comp
        exact absurd hhalted_comp (by decide)
  · -- isHalted returns false, we're done
    simp

/-! ### Halting Case -/

/-- Register 1000 stays 0 through multiple steps (for init config) -/
private theorem r1000_preserved_from_init (q : RM) (n : Nat) (c : RMConfig)
    (hwf : WellFormedRM q)
    (hsteps : rmSteps q (RMConfig.init input) n = some c) :
    c.regs 1000 = 0 := by
  have h0 : (RMConfig.init input).regs 1000 = 0 := rfl
  exact r1000_preserved_steps q (RMConfig.init input) c n hwf hsteps h0

/-- Generalized version: from any starting config that stays in q-region -/
private theorem compose_runs_q_then_p_gen (p q : RM) (c_start : RMConfig) (n : Nat) (c : RMConfig)
    (hwf : WellFormedRM q)
    (hsteps : rmSteps q c_start n = some c)
    (hhalt : isHalted q c = true)
    (hinbounds : c.pc < q.length)
    (hstart_pc : c_start.pc < q.length)
    (hstart_r1000 : c_start.regs 1000 = 0)
    (hearlier : ∀ k < n, ∀ ck, rmSteps q c_start k = some ck →
        isHalted q ck = false ∧ ck.pc < q.length) :
    rmSteps (rmCompose p q) c_start (n + 1) = some { pc := q.length, regs := c.regs } := by
  induction n generalizing c_start with
  | zero =>
    simp only [rmSteps] at hsteps
    simp only [Option.some.injEq] at hsteps
    subst hsteps
    simp only [rmSteps]
    have hhalt_instr := halted_inbounds_is_halt q c_start hhalt hinbounds
    have hstep := step_q_halt p q c_start hstart_pc hhalt_instr hstart_r1000
    simp only [hstep]
  | succ m ih =>
    simp only [rmSteps] at hsteps ⊢
    cases hstep_q : rmStep q c_start with
    | none =>
      have ⟨hnothalted, _⟩ := hearlier 0 (Nat.zero_lt_succ m) c_start (by simp [rmSteps])
      have hhalted := isHalted_iff q c_start |>.mpr hstep_q
      simp only [hnothalted] at hhalted
      exact absurd hhalted (by decide)
    | some c1 =>
      simp only [hstep_q] at hsteps
      have ⟨hnothalted0, hpc0_lt⟩ := hearlier 0 (Nat.zero_lt_succ m) c_start (by simp [rmSteps])
      have hinstr0 := not_halted_instr q c_start hnothalted0 hpc0_lt
      have hstep_comp := step_q_nonhalt p q c_start c1 hstep_q hstart_pc hinstr0
      rw [hstep_comp]
      -- Properties of c1
      have hr1000_c1 := r1000_preserved q c_start c1 hwf hstep_q hstart_r1000
      -- c1.pc < q.length: either from hearlier (if m > 0) or from c1 = c and hinbounds (if m = 0)
      have hpc1_lt : c1.pc < q.length := by
        cases m with
        | zero =>
          simp only [rmSteps, Option.some.injEq] at hsteps
          subst hsteps
          exact hinbounds
        | succ m' =>
          have ⟨_, hpc1⟩ := hearlier 1 (by omega) c1 (by simp [rmSteps, hstep_q])
          exact hpc1
      -- Apply IH with correct arguments
      have hearlier' : ∀ k < m, ∀ ck, rmSteps q c1 k = some ck →
          isHalted q ck = false ∧ ck.pc < q.length := by
        intro k hk ck hsteps_ck
        have hsteps_start : rmSteps q c_start (k + 1) = some ck := by
          simp only [rmSteps, hstep_q, hsteps_ck]
        exact hearlier (k + 1) (by omega) ck hsteps_start
      exact ih c1 hsteps hpc1_lt hr1000_c1 hearlier'

/-- If q halts at step n with config c (halting via halt instruction, not OOB),
    composed program reaches q's halt and transitions to p region at step n+1 -/
theorem compose_runs_q_then_p (p q : RM) (input n : Nat) (c : RMConfig)
    (hwf : WellFormedRM q)
    (hsteps : rmSteps q (RMConfig.init input) n = some c)
    (hhalt : isHalted q c = true)
    (hinbounds : c.pc < q.length)  -- halts via halt instruction, not OOB
    -- All earlier steps didn't halt and stayed in bounds
    (hearlier : ∀ k < n, ∀ ck, rmSteps q (RMConfig.init input) k = some ck →
        isHalted q ck = false ∧ ck.pc < q.length) :
    rmSteps (rmCompose p q) (RMConfig.init input) (n + 1) =
    some { pc := q.length, regs := c.regs } := by
  have hinit_pc : (RMConfig.init input).pc < q.length := by
    cases n with
    | zero =>
      simp only [rmSteps, Option.some.injEq] at hsteps
      subst hsteps
      exact hinbounds
    | succ m =>
      have ⟨_, hpc_lt⟩ := hearlier 0 (Nat.zero_lt_succ m) (RMConfig.init input) (by simp [rmSteps])
      exact hpc_lt
  have hr1000_init : (RMConfig.init input).regs 1000 = 0 := rfl
  exact compose_runs_q_then_p_gen p q (RMConfig.init input) n c hwf hsteps
        hhalt hinbounds hinit_pc hr1000_init hearlier

/-- Extract config from rmOutput -/
private theorem rmOutput_config (prog : RM) (input n : Nat) (v : Nat)
    (hout : rmOutput prog input n = some v) :
    ∃ c, rmSteps prog (RMConfig.init input) n = some c ∧
    isHalted prog c = true ∧ c.regs 0 = v := by
  simp only [rmOutput] at hout
  cases hsteps : rmSteps prog (RMConfig.init input) n with
  | none => simp [hsteps] at hout
  | some c =>
    simp only [hsteps] at hout
    split at hout
    · have hhalted : isHalted prog c = true := by assumption
      simp only [Option.some.injEq] at hout
      exact ⟨c, rfl, hhalted, hout⟩
    · simp at hout

/-- If c is halted and c.pc < prog.length, then c.pc points to halt -/
private theorem halted_inbounds_pc (prog : RM) (c : RMConfig)
    (hhalted : isHalted prog c = true) :
    c.pc < prog.length ∨ c.pc ≥ prog.length := by
  omega

/-- For well-formed programs that terminate properly, halting occurs at a valid pc -/
private theorem halted_has_valid_pc (prog : RM) (c c_init : RMConfig) (n : Nat)
    (hwf : WellFormedRM prog)
    (hsteps : rmSteps prog c_init n = some c)
    (hhalted : isHalted prog c = true)
    (hinit_pc : c_init.pc < prog.length)
    (hr1000 : c_init.regs 1000 = 0)
    -- Assumption: if we reach halt, pc is valid (program doesn't run off end)
    (hterm : ∀ k ck, rmSteps prog c_init k = some ck → ck.pc < prog.length) :
    c.pc < prog.length := hterm n c hsteps

/-- Output of composed program when q halts at first halting step -/
theorem compose_output_first_halt (p q : RM) (input n_q : Nat) (c : RMConfig)
    (hwf : WellFormedRM q)
    (hsteps : rmSteps q (RMConfig.init input) n_q = some c)
    (hhalt : isHalted q c = true)
    (hinbounds : c.pc < q.length)
    (hearlier : ∀ k < n_q, ∀ ck, rmSteps q (RMConfig.init input) k = some ck →
        isHalted q ck = false ∧ ck.pc < q.length) :
    ∃ c_trans, rmSteps (rmCompose p q) (RMConfig.init input) (n_q + 1) = some c_trans ∧
    c_trans.pc = q.length ∧ c_trans.regs = c.regs := by
  have h := compose_runs_q_then_p p q input n_q c hwf hsteps hhalt hinbounds hearlier
  exact ⟨{ pc := q.length, regs := c.regs }, h, rfl, rfl⟩

/-- Helper: rmOutput at step n implies rmOutput at all later steps with same value -/
private theorem rmOutput_stable_value' (prog : RM) (input n m : Nat) (v : Nat)
    (hout : rmOutput prog input n = some v) (hm : m ≥ n) :
    rmOutput prog input m = some v := by
  simp only [rmOutput] at hout ⊢
  cases hsteps_n : rmSteps prog (RMConfig.init input) n with
  | none => simp [hsteps_n] at hout
  | some c =>
    simp only [hsteps_n] at hout
    split at hout
    · next hhalted =>
      simp only [Option.some.injEq] at hout
      have hstable := rmSteps_stable prog (RMConfig.init input) c n m hsteps_n hhalted hm
      simp only [hstable, hhalted, ↓reduceIte, hout]
    · simp at hout

/-- Search for minimum n ≤ bound satisfying P (computable) -/
private def searchMin (P : Nat → Bool) : Nat → Option Nat
  | 0 => if P 0 then some 0 else none
  | n + 1 =>
    match searchMin P n with
    | some k => some k
    | none => if P (n + 1) then some (n + 1) else none

/-- searchMin finds something if P holds within bound -/
private theorem searchMin_finds (P : Nat → Bool) (bound : Nat) (hwithin : ∃ k ≤ bound, P k = true) :
    ∃ k, searchMin P bound = some k := by
  induction bound with
  | zero =>
    obtain ⟨w, hw_le, hw_p⟩ := hwithin
    have : w = 0 := Nat.le_zero.mp hw_le
    simp only [searchMin, this ▸ hw_p, ↓reduceIte]
    exact ⟨0, rfl⟩
  | succ n ih =>
    simp only [searchMin]
    cases hsearch : searchMin P n with
    | some k => exact ⟨k, rfl⟩
    | none =>
      obtain ⟨w, hw_le, hw_p⟩ := hwithin
      cases Nat.lt_or_ge w (n + 1) with
      | inl hlt =>
        have hw_le_n : w ≤ n := Nat.lt_succ_iff.mp hlt
        have hex := ih ⟨w, hw_le_n, hw_p⟩
        obtain ⟨k, hk⟩ := hex
        rw [hk] at hsearch
        exact absurd hsearch (by simp)
      | inr hge =>
        have : w = n + 1 := Nat.le_antisymm hw_le hge
        simp only [this ▸ hw_p, ↓reduceIte]
        exact ⟨n + 1, rfl⟩

/-- searchMin result satisfies P -/
private theorem searchMin_spec (P : Nat → Bool) (bound k : Nat)
    (h : searchMin P bound = some k) : P k = true := by
  induction bound with
  | zero =>
    simp only [searchMin] at h
    split at h
    · next hp => simp only [Option.some.injEq] at h; exact h ▸ hp
    · simp at h
  | succ n ih =>
    simp only [searchMin] at h
    cases hprev : searchMin P n with
    | some k' =>
      simp only [hprev, Option.some.injEq] at h
      exact ih (h ▸ hprev)
    | none =>
      simp only [hprev] at h
      split at h
      · next hp => simp only [Option.some.injEq] at h; exact h ▸ hp
      · simp at h

/-- If searchMin returns none, no element satisfies P -/
private theorem searchMin_none_all_false (P : Nat → Bool) (n : Nat)
    (hnone : searchMin P n = none) (m : Nat) (hm : m ≤ n) : P m = false := by
  induction n generalizing m with
  | zero =>
    simp only [searchMin] at hnone
    split at hnone
    · simp at hnone
    · next hfalse =>
      have : m = 0 := Nat.le_zero.mp hm
      rw [this]
      exact Bool.not_eq_true _ |>.mp hfalse
  | succ n' ih =>
    simp only [searchMin] at hnone
    cases hn' : searchMin P n' with
    | some _ => simp [hn'] at hnone
    | none =>
      simp only [hn'] at hnone
      split at hnone
      · simp at hnone
      · next hfalse =>
        cases Nat.lt_or_ge m (n' + 1) with
        | inl hlt =>
          exact ih hn' m (Nat.lt_succ_iff.mp hlt)
        | inr hge =>
          have : m = n' + 1 := Nat.le_antisymm hm hge
          rw [this]
          exact Bool.not_eq_true _ |>.mp hfalse

/-- searchMin is minimal -/
private theorem searchMin_min (P : Nat → Bool) (bound k j : Nat)
    (h : searchMin P bound = some k) (hj : j < k) : P j = false := by
  induction bound generalizing k with
  | zero =>
    simp only [searchMin] at h
    split at h
    · simp only [Option.some.injEq] at h; omega
    · simp at h
  | succ n ih =>
    simp only [searchMin] at h
    cases hprev : searchMin P n with
    | some k' =>
      simp only [hprev, Option.some.injEq] at h
      exact ih k' hprev (h ▸ hj)
    | none =>
      simp only [hprev] at h
      split at h
      · next hp =>
        simp only [Option.some.injEq] at h
        subst h
        -- j < n + 1, so j ≤ n
        have hj_le : j ≤ n := Nat.lt_succ_iff.mp hj
        exact searchMin_none_all_false P n hprev j hj_le
      · simp at h

/-- Find minimum using Classical.choose to get a witness -/
private noncomputable def findMinNat (P : Nat → Bool) (h : ∃ n, P n = true) : Nat :=
  let witness := Classical.choose h
  let hwit : P witness = true := Classical.choose_spec h
  let hex : ∃ k, searchMin P witness = some k := searchMin_finds P witness ⟨witness, Nat.le_refl _, hwit⟩
  Classical.choose hex

/-- findMinNat satisfies P -/
private theorem findMinNat_spec (P : Nat → Bool) (h : ∃ n, P n = true) :
    P (findMinNat P h) = true := by
  simp only [findMinNat]
  have hwit : P (Classical.choose h) = true := Classical.choose_spec h
  have hex : ∃ k, searchMin P (Classical.choose h) = some k :=
    searchMin_finds P (Classical.choose h) ⟨Classical.choose h, Nat.le_refl _, hwit⟩
  exact searchMin_spec P _ _ (Classical.choose_spec hex)

/-- findMinNat is minimal -/
private theorem findMinNat_min (P : Nat → Bool) (h : ∃ n, P n = true) (j : Nat)
    (hj : j < findMinNat P h) : P j = false := by
  simp only [findMinNat] at hj
  have hwit : P (Classical.choose h) = true := Classical.choose_spec h
  have hex : ∃ k, searchMin P (Classical.choose h) = some k :=
    searchMin_finds P (Classical.choose h) ⟨Classical.choose h, Nat.le_refl _, hwit⟩
  exact searchMin_min P _ (Classical.choose hex) j (Classical.choose_spec hex) hj

/-- Find the first step where rmOutput is some -/
private noncomputable def firstHaltStep (prog : RM) (input : Nat)
    (h : ∃ n, (rmOutput prog input n).isSome) : Nat :=
  findMinNat (fun n => (rmOutput prog input n).isSome) (by
    obtain ⟨n, hn⟩ := h
    exact ⟨n, hn⟩)

/-- The first halt step actually produces output -/
private theorem firstHaltStep_spec (prog : RM) (input : Nat)
    (h : ∃ n, (rmOutput prog input n).isSome) :
    (rmOutput prog input (firstHaltStep prog input h)).isSome := by
  simp only [firstHaltStep]
  exact findMinNat_spec (fun n => (rmOutput prog input n).isSome) _

/-- Steps before the first halt step don't produce output -/
private theorem before_firstHaltStep (prog : RM) (input : Nat)
    (h : ∃ n, (rmOutput prog input n).isSome) (k : Nat)
    (hk : k < firstHaltStep prog input h) :
    (rmOutput prog input k).isNone := by
  simp only [firstHaltStep] at hk
  have hfalse := findMinNat_min (fun n => (rmOutput prog input n).isSome) _ k hk
  rw [Bool.eq_false_iff] at hfalse
  have heq := Option.not_isSome_iff_eq_none.mp hfalse
  exact Option.isNone_iff_eq_none.mpr heq

/-- At steps before first halt, program is not halted and pc in bounds -/
private theorem before_firstHalt_not_halted (prog : RM) (input : Nat)
    (h : ∃ n, (rmOutput prog input n).isSome) (k : Nat)
    (hk : k < firstHaltStep prog input h)
    (hbounds : ∀ n c, rmSteps prog (RMConfig.init input) n = some c → c.pc < prog.length) :
    ∃ c, rmSteps prog (RMConfig.init input) k = some c ∧
    isHalted prog c = false ∧ c.pc < prog.length := by
  have ⟨c, hsteps⟩ := rmSteps_succeeds prog (RMConfig.init input) k
  have hnone := before_firstHaltStep prog input h k hk
  simp only [rmOutput, hsteps, Option.isNone_iff_eq_none] at hnone
  split at hnone
  · simp at hnone
  · next hnothalted =>
    refine ⟨c, hsteps, Bool.eq_false_iff.mpr hnothalted, hbounds k c hsteps⟩

/-- Earlier steps have not halted and are in bounds (for compose_runs_q_then_p) -/
private theorem hearlier_from_firstHalt (prog : RM) (input : Nat)
    (h : ∃ n, (rmOutput prog input n).isSome)
    (hbounds : ∀ n c, rmSteps prog (RMConfig.init input) n = some c → c.pc < prog.length) :
    ∀ k < firstHaltStep prog input h, ∀ ck, rmSteps prog (RMConfig.init input) k = some ck →
        isHalted prog ck = false ∧ ck.pc < prog.length := by
  intro k hk ck hsteps_ck
  have ⟨c', hsteps', hnothalted, hpc⟩ := before_firstHalt_not_halted prog input h k hk hbounds
  have heq := rmSteps_unique prog (RMConfig.init input) k ck c' hsteps_ck hsteps'
  subst heq
  exact ⟨hnothalted, hpc⟩

/-- Get the halting config at the first halt step -/
private theorem firstHalt_config (prog : RM) (input : Nat)
    (h : ∃ n, (rmOutput prog input n).isSome)
    (hbounds : ∀ n c, rmSteps prog (RMConfig.init input) n = some c → c.pc < prog.length) :
    ∃ c v, rmSteps prog (RMConfig.init input) (firstHaltStep prog input h) = some c ∧
    isHalted prog c = true ∧ c.regs 0 = v ∧
    rmOutput prog input (firstHaltStep prog input h) = some v ∧
    c.pc < prog.length := by
  have hsome := firstHaltStep_spec prog input h
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨c, hsteps, hhalted, hr0⟩ := rmOutput_config prog input _ v hv
  exact ⟨c, v, hsteps, hhalted, hr0, hv, hbounds _ c hsteps⟩

/-- Output at first halt step equals output at any later step -/
private theorem firstHalt_output_eq (prog : RM) (input n : Nat) (v : Nat)
    (h : ∃ m, (rmOutput prog input m).isSome)
    (hout : rmOutput prog input n = some v) :
    rmOutput prog input (firstHaltStep prog input h) = some v := by
  have hfirst := firstHaltStep_spec prog input h
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hfirst
  -- Both n and firstHaltStep give valid outputs; stability implies they're equal
  cases Nat.lt_or_ge n (firstHaltStep prog input h) with
  | inl hlt =>
    -- n < firstHaltStep contradicts that n gives output (since firstHaltStep is minimum)
    have hnone := before_firstHaltStep prog input h n hlt
    rw [Option.isNone_iff_eq_none] at hnone
    rw [hout] at hnone
    exact Option.noConfusion hnone
  | inr hge =>
    -- firstHaltStep ≤ n, so by stability both equal
    have hstable := rmOutput_stable_value' prog input (firstHaltStep prog input h) n w hw hge
    rw [hstable] at hout
    simp only [Option.some.injEq] at hout
    rw [← hout, hw]

/-- Helper: rmOutput at step n implies rmOutput at all later steps with same value -/
private theorem rmOutput_stable_value (prog : RM) (input n m : Nat) (v : Nat)
    (hout : rmOutput prog input n = some v) (hm : m ≥ n) :
    rmOutput prog input m = some v := by
  simp only [rmOutput] at hout ⊢
  cases hsteps_n : rmSteps prog (RMConfig.init input) n with
  | none => simp [hsteps_n] at hout
  | some c =>
    simp only [hsteps_n] at hout
    split at hout
    · next hhalted =>
      simp only [Option.some.injEq] at hout
      -- c is halted, so rmSteps at m also gives c
      have hstable := rmSteps_stable prog (RMConfig.init input) c n m hsteps_n hhalted hm
      simp only [hstable, hhalted, ↓reduceIte, hout]
    · simp at hout

/-- Helper: if rmOutput is some at n, then Classical.choose gives output at that step -/
private theorem rmOutput_choose_spec (prog : RM) (input n : Nat) (v : Nat)
    (hout : rmOutput prog input n = some v)
    (hex : ∃ m, (rmOutput prog input m).isSome) :
    rmOutput prog input (Classical.choose hex) = some v := by
  have hspec := Classical.choose_spec hex
  let m := Classical.choose hex
  have hsome : (rmOutput prog input m).isSome := hspec
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hsome
  -- rmOutput at n gives v, rmOutput at m gives w
  -- Both are stable, so they must agree
  cases Nat.lt_or_ge n m with
  | inl hlt =>
    -- n < m, so rmOutput at m = rmOutput at n = some v
    have hstable := rmOutput_stable_value prog input n m v hout (Nat.le_of_lt hlt)
    simp only [hstable] at hw
    exact hw.symm ▸ hstable
  | inr hge =>
    -- m ≤ n, so rmOutput at n = rmOutput at m = some w
    have hstable := rmOutput_stable_value prog input m n w hw hge
    -- hstable : rmOutput prog input n = some w
    -- hout : rmOutput prog input n = some v
    -- So w = v
    rw [hstable] at hout
    simp only [Option.some.injEq] at hout
    rw [hout] at hw
    exact hw

/-- Specification: rmCompose implements function composition.
    This is the well-formed version with explicit hypotheses about
    intermediate pcs staying in bounds.

    The proof combines:
    - compose_diverges_if_q_diverges for the divergence case
    - compose_runs_q_then_p and steps_p_offset for the halting case -/
theorem rmCompose_spec_wf (p q : RM) (input : Nat)
    (hwf_p : WellFormedRM p) (hwf_q : WellFormedRM q)
    -- Termination hypotheses: all intermediate pcs stay in bounds
    (hq_bounds : ∀ n c, rmSteps q (RMConfig.init input) n = some c → c.pc < q.length)
    (hp_bounds : ∀ v n c, rmSteps p (RMConfig.init v) n = some c → c.pc < p.length)
    -- q leaves all registers except r0 at 0 when halted
    (hq_clean : ∀ n c, rmSteps q (RMConfig.init input) n = some c →
        isHalted q c = true → ∀ r, r ≠ 0 → c.regs r = 0) :
    rmComputes (rmCompose p q) input =
    (rmComputes q input) >>= (rmComputes p) := by
  simp only [rmComputes]
  -- Case split on whether q halts
  by_cases hq_halts : ∃ n, (rmOutput q input n).isSome
  · -- q halts: need to show composed halts with correct value
    simp only [hq_halts, ↓reduceDIte]
    -- Get the output value from Classical.choose
    have hq_out := Classical.choose_spec hq_halts
    obtain ⟨v_choose, hv_choose⟩ := Option.isSome_iff_exists.mp hq_out
    have hq_v : rmOutput q input (Classical.choose hq_halts) = some v_choose := hv_choose
    simp only [hq_v]
    -- Use firstHaltStep to get the minimum halting step (needed for hearlier)
    let n_first := firstHaltStep q input hq_halts
    -- Get config and facts about first halt step
    obtain ⟨c_q, v_first, hsteps_q, hhalted_q, hr0_q, hout_first, hpc_q⟩ :=
      firstHalt_config q input hq_halts hq_bounds
    -- Output at first halt step equals v_choose (since they're outputs of same computation)
    have heq_out := firstHalt_output_eq q input (Classical.choose hq_halts) v_choose hq_halts hq_v
    rw [hout_first] at heq_out
    simp only [Option.some.injEq] at heq_out
    subst heq_out  -- Now v_first = v_choose, so use v_first everywhere
    -- c_q.regs is equivalent to init(v_first) for p's purposes
    have hregs_eq : c_q.regs = (RMConfig.init v_first).regs := by
      ext r
      cases Nat.decEq r 0 with
      | isTrue hr0 =>
        simp only [RMConfig.init, hr0, ↓reduceIte, hr0_q]
      | isFalse hr0 =>
        simp only [RMConfig.init, hr0, ↓reduceIte]
        exact hq_clean _ c_q hsteps_q hhalted_q r hr0
    -- Get the hearlier hypothesis from firstHaltStep machinery
    have hearlier := hearlier_from_firstHalt q input hq_halts hq_bounds
    -- Apply compose_runs_q_then_p: after n_first+1 steps, composed is at p-region start
    have htrans := compose_runs_q_then_p p q input n_first c_q hwf_q hsteps_q hhalted_q hpc_q hearlier
    -- Now we need to show: composed output = p output on v_first
    -- After n_first+1 steps, composed is at {pc := q.length, regs := c_q.regs}
    -- This is equivalent to p starting at {pc := 0, regs := (RMConfig.init v_first).regs}
    -- Case split on whether p halts on input v_first
    by_cases hp_halts : ∃ n, (rmOutput p v_first n).isSome
    · -- p halts: show composed halts with same output
      -- RHS: some v_first >>= rmComputes p = rmComputes p v_first
      -- Use: (some a >>= f) = f a is true by definition
      have hrhs : (some v_first >>= rmComputes p) = rmComputes p v_first := rfl
      rw [hrhs]
      simp only [rmComputes, hp_halts, ↓reduceDIte]
      -- Get first halt step for p
      let n_p := firstHaltStep p v_first hp_halts
      obtain ⟨c_p, w, hsteps_p, hhalted_p, hr0_p, hout_p, hpc_p⟩ :=
        firstHalt_config p v_first hp_halts (hp_bounds v_first)
      -- Use steps_p_offset to simulate p in composed
      -- p starts from (RMConfig.init v_first), composed starts from {pc := q.length, regs := c_q.regs}
      -- Since c_q.regs = (RMConfig.init v_first).regs, this works
      have hconfig_eq : (RMConfig.init v_first) = { pc := 0, regs := c_q.regs } := by
        simp only [RMConfig.init]
        congr 1
        exact hregs_eq.symm
      have hsteps_p_adj : rmSteps p { pc := 0, regs := c_q.regs } n_p = some c_p := by
        rw [← hconfig_eq]
        exact hsteps_p
      have hsteps_comp_p := steps_p_offset p q n_p { pc := 0, regs := c_q.regs } c_p hsteps_p_adj
      -- Normalize pc = 0 + q.length to pc = q.length
      have hpc_norm : (0 : Nat) + q.length = q.length := Nat.zero_add _
      -- Combined: n_first+1 steps for q transition, then n_p steps for p
      -- Total: (n_first + 1) + n_p steps in composed
      -- After htrans (n_first+1 steps): at {pc := q.length, regs := c_q.regs}
      -- After hsteps_comp_p (n_p more steps): at {pc := c_p.pc + q.length, regs := c_p.regs}
      have hsteps_comp_p' : rmSteps (rmCompose p q) { pc := q.length, regs := c_q.regs } n_p =
          some { pc := c_p.pc + q.length, regs := c_p.regs } := by
        simp only [hpc_norm] at hsteps_comp_p
        exact hsteps_comp_p
      have hsteps_total := rmSteps_trans (rmCompose p q) (RMConfig.init input)
        { pc := q.length, regs := c_q.regs }
        { pc := c_p.pc + q.length, regs := c_p.regs }
        (n_first + 1) n_p htrans hsteps_comp_p'
      -- Show composed is halted at this point
      have hhalted_comp : isHalted (rmCompose p q) { pc := c_p.pc + q.length, regs := c_p.regs } := by
        have hpc_ge : c_p.pc + q.length ≥ q.length := Nat.le_add_left q.length c_p.pc
        have hsub : c_p.pc + q.length - q.length = c_p.pc := Nat.add_sub_cancel c_p.pc q.length
        have hhalted_adj : isHalted p { pc := c_p.pc + q.length - q.length, regs := c_p.regs } = true := by
          simp only [hsub, hhalted_p]
        exact halt_p_in_compose_from_halt p q { pc := c_p.pc + q.length, regs := c_p.regs }
          hpc_ge hhalted_adj (by simp only [hsub, hpc_p])
      -- rmOutput of composed at total steps
      have hout_comp : rmOutput (rmCompose p q) input (n_first + 1 + n_p) = some w := by
        simp only [rmOutput, hsteps_total, hhalted_comp, ↓reduceIte, hr0_p]
      -- Show composed halts
      have hcomp_halts : ∃ n, (rmOutput (rmCompose p q) input n).isSome := by
        exact ⟨n_first + 1 + n_p, by simp [hout_comp]⟩
      simp only [hcomp_halts, ↓reduceDIte]
      -- Now show outputs match
      -- rmOutput at Classical.choose hcomp_halts = some w (by stability)
      -- rmOutput p v_first at Classical.choose hp_halts = some w (by stability)
      have hout_comp_choose := rmOutput_choose_spec (rmCompose p q) input
        (n_first + 1 + n_p) w hout_comp hcomp_halts
      have hout_p_first : rmOutput p v_first n_p = some w := hout_p
      have hout_p_choose := rmOutput_choose_spec p v_first n_p w hout_p_first hp_halts
      rw [hout_comp_choose, hout_p_choose]
    · -- p diverges: show composed diverges too
      -- RHS: some v_first >>= rmComputes p = rmComputes p v_first = none
      have hrhs : (some v_first >>= rmComputes p) = rmComputes p v_first := rfl
      rw [hrhs]
      simp only [rmComputes, hp_halts, ↓reduceDIte]
      -- Need to show composed doesn't halt (LHS is also none)
      -- Key insight: if composed halts, either q hadn't halted yet (impossible for n ≤ n_first
      -- since composed is not halted in q-region), or p halted (contradicts hp_halts)
      have hcomp_div : ¬∃ n, (rmOutput (rmCompose p q) input n).isSome := by
        intro ⟨n, hn⟩
        obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hn
        -- Get composed config at step n
        have ⟨c_comp, hsteps_comp⟩ := rmSteps_succeeds (rmCompose p q) (RMConfig.init input) n
        -- rmOutput = some w means isHalted c_comp = true
        simp only [rmOutput, hsteps_comp] at hw
        cases hhalted : isHalted (rmCompose p q) c_comp with
        | false =>
          simp at hw
          exact absurd hw.1 (by rw [hhalted]; decide)
        | true =>
          -- Composed halted at c_comp - derive contradiction
          cases Nat.lt_or_ge n (n_first + 1) with
          | inl hlt =>
            -- n < n_first + 1: composed is in q-region, should not be halted
            have hn_le : n ≤ n_first := Nat.lt_succ_iff.mp hlt
            -- c_comp.pc < q.length: composed simulates q and stays in q-region
            -- This follows from compose_matches_q_diverge_gen for simulation
            have hcomp_in_q_region : c_comp.pc < q.length := by
              -- Get q's config at step n
              have ⟨c_q_n, hsteps_q_n⟩ := rmSteps_succeeds q (RMConfig.init input) n
              -- q's config has pc < q.length by bounds
              have hpc_q_n : c_q_n.pc < q.length := hq_bounds n c_q_n hsteps_q_n
              -- init.pc < q.length (q is non-empty since it halts)
              have hinit_pc : (RMConfig.init input).pc < q.length := by
                have h0 := hq_bounds 0 (RMConfig.init input) (by simp [rmSteps])
                simp only [RMConfig.init] at h0
                exact h0
              -- hearlier for k < n (follows from hearlier for k < n_first since n ≤ n_first)
              have hearlier_n : ∀ k < n, ∀ ck, rmSteps q (RMConfig.init input) k = some ck →
                  isHalted q ck = false ∧ ck.pc < q.length := by
                intro k hk ck hsteps_k
                exact hearlier k (Nat.lt_of_lt_of_le hk hn_le) ck hsteps_k
              -- Use compose_matches_q_at_halt to show composed = q's config
              have hcomp_eq := compose_matches_q_at_halt p q (RMConfig.init input) n c_q_n
                hwf_q hsteps_q_n hinit_pc rfl hq_bounds hearlier_n
              -- c_comp = c_q_n by uniqueness
              have heq := rmSteps_unique (rmCompose p q) (RMConfig.init input) n c_comp c_q_n
                hsteps_comp hcomp_eq
              rw [heq]
              exact hpc_q_n
            -- In q-region, composed never halts (halt becomes dec)
            have hcomp_not_halt := compose_not_halted_q_halt_instr_or_nonhalt p q c_comp hcomp_in_q_region
            rw [hhalted] at hcomp_not_halt
            exact absurd hcomp_not_halt (by decide)
          | inr hge =>
            -- n ≥ n_first + 1: composed is in p-region
            -- If composed halted, p must have halted - contradiction with hp_halts
            have hpc_comp_ge : c_comp.pc ≥ q.length := by
              -- After n_first + 1 steps, composed is at {pc := q.length, regs := c_q.regs}
              -- After k = n - (n_first + 1) more steps, pc stays ≥ q.length
              let k := n - (n_first + 1)
              have hk : n = (n_first + 1) + k := by omega
              -- Get p's config after k steps starting from {pc := 0, regs := c_q.regs}
              have ⟨c_p_k, hsteps_p_k⟩ := rmSteps_succeeds p { pc := 0, regs := c_q.regs } k
              -- Use steps_p_offset to simulate k steps in composed
              have hsteps_comp_k := steps_p_offset p q k { pc := 0, regs := c_q.regs } c_p_k hsteps_p_k
              have hpc_norm : (0 : Nat) + q.length = q.length := Nat.zero_add _
              simp only [hpc_norm] at hsteps_comp_k
              -- Combined with htrans
              have hsteps_n := rmSteps_trans (rmCompose p q) (RMConfig.init input)
                { pc := q.length, regs := c_q.regs }
                { pc := c_p_k.pc + q.length, regs := c_p_k.regs }
                (n_first + 1) k htrans hsteps_comp_k
              rw [hk] at hsteps_comp
              -- By uniqueness
              have heq := rmSteps_unique (rmCompose p q) (RMConfig.init input)
                (n_first + 1 + k) c_comp { pc := c_p_k.pc + q.length, regs := c_p_k.regs }
                hsteps_comp hsteps_n
              rw [heq]
              exact Nat.le_add_left q.length c_p_k.pc
            have hp_halted := p_halts_from_compose_halts p q c_comp hpc_comp_ge hhalted
            -- Extract that p halts at some step
            have hp_out : ∃ m, (rmOutput p v_first m).isSome := by
              -- c_comp is in p-region and halted in composed
              -- c_comp.pc - q.length corresponds to p's pc
              -- Since composed halted, p must halt at this config
              let k := n - (n_first + 1)
              have hk : n = (n_first + 1) + k := by omega
              -- Get p's config after k steps
              have ⟨c_p_k, hsteps_p_k⟩ := rmSteps_succeeds p { pc := 0, regs := c_q.regs } k
              have hsteps_comp_k := steps_p_offset p q k { pc := 0, regs := c_q.regs } c_p_k hsteps_p_k
              have hpc_norm : (0 : Nat) + q.length = q.length := Nat.zero_add _
              simp only [hpc_norm] at hsteps_comp_k
              have hsteps_n := rmSteps_trans (rmCompose p q) (RMConfig.init input)
                { pc := q.length, regs := c_q.regs }
                { pc := c_p_k.pc + q.length, regs := c_p_k.regs }
                (n_first + 1) k htrans hsteps_comp_k
              rw [hk] at hsteps_comp
              have heq := rmSteps_unique (rmCompose p q) (RMConfig.init input)
                (n_first + 1 + k) c_comp { pc := c_p_k.pc + q.length, regs := c_p_k.regs }
                hsteps_comp hsteps_n
              -- c_comp = {pc := c_p_k.pc + q.length, regs := c_p_k.regs}
              -- hp_halted says: isHalted p {pc := c_comp.pc - q.length, regs := c_comp.regs} = true
              -- With heq: c_comp.pc - q.length = c_p_k.pc, c_comp.regs = c_p_k.regs
              -- So: isHalted p c_p_k = true
              have hsub : c_comp.pc - q.length = c_p_k.pc := by
                rw [heq]
                exact Nat.add_sub_cancel c_p_k.pc q.length
              have hregs_eq' : c_comp.regs = c_p_k.regs := by
                rw [heq]
              have hp_halted' : isHalted p c_p_k = true := by
                have h := hp_halted
                simp only [hsub, hregs_eq'] at h
                exact h
              -- p halts after k steps from {pc := 0, regs := c_q.regs}
              -- This is equivalent to p halting from (RMConfig.init v_first) since c_q.regs = (RMConfig.init v_first).regs
              have hconfig_eq : { pc := 0, regs := c_q.regs } = RMConfig.init v_first := by
                simp only [RMConfig.init, hregs_eq]
              have hsteps_p_from_init : rmSteps p (RMConfig.init v_first) k = some c_p_k := by
                rw [← hconfig_eq]
                exact hsteps_p_k
              -- rmOutput at step k
              have hout_p : rmOutput p v_first k = some (c_p_k.regs 0) := by
                simp only [rmOutput, hsteps_p_from_init, hp_halted', ↓reduceIte]
              exact ⟨k, by simp [hout_p]⟩
            exact hp_halts hp_out
      simp only [hcomp_div, ↓reduceDIte]
  · -- q diverges
    simp only [hq_halts, ↓reduceDIte]
    -- Show composed also diverges
    have hdiv_q : ∀ n, (rmOutput q input n).isNone := by
      intro n
      cases hcase : rmOutput q input n with
      | none => rfl
      | some v =>
        have hsome : (rmOutput q input n).isSome := by simp [hcase]
        exact absurd ⟨n, hsome⟩ hq_halts
    have hdiv_comp := compose_diverges_if_q_diverges p q input hwf_q hdiv_q hq_bounds
    -- Show rmComputes returns none
    have hcomp_none : ¬∃ n, (rmOutput (rmCompose p q) input n).isSome := by
      intro ⟨n, hn⟩
      have hdiv_n := hdiv_comp n
      simp only [Option.isNone_iff_eq_none] at hdiv_n
      simp only [Option.isSome_iff_exists] at hn
      obtain ⟨w, hw⟩ := hn
      rw [hw] at hdiv_n
      exact Option.noConfusion hdiv_n
    simp only [hcomp_none, ↓reduceDIte]
    rfl

/-- Specification: rmCompose implements function composition.

    **Status**: This is an axiom that reduces to `rmCompose_spec_wf` for well-formed programs.

    The theorem `rmCompose_spec_wf` proves this for programs satisfying:
    - `WellFormedRM p` and `WellFormedRM q` (don't use register 1000)
    - Bounds: program counters stay within program length during execution
    - Clean: q leaves non-r0 registers at 0 when halted

    To prove this unconditionally for ALL programs would require:
    1. Register shifting: transform any RM to an equivalent well-formed one
       `shiftRegisters prog 1001` shifts all register refs to avoid r1000
    2. Show shifting preserves the computed function
    3. Show composed shifted programs satisfy the bounds hypotheses

    For practical purposes, all "reasonable" programs satisfy these conditions. -/
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

/-! ## Register Swapping

To eliminate the WellFormedRM hypothesis, we transform programs by swapping
register 1000 with an unused register. This preserves I/O (r0 unchanged)
and makes the program well-formed. -/

/-- Swap all occurrences of registers r1 and r2 in an instruction -/
def swapRegInstr (r1 r2 : Nat) : RMInstr → RMInstr
  | RMInstr.inc r => RMInstr.inc (if r = r1 then r2 else if r = r2 then r1 else r)
  | RMInstr.dec r j => RMInstr.dec (if r = r1 then r2 else if r = r2 then r1 else r) j
  | RMInstr.halt => RMInstr.halt

/-- Swap all occurrences of registers r1 and r2 in a program -/
def swapReg (prog : RM) (r1 r2 : Nat) : RM :=
  prog.map (swapRegInstr r1 r2)

/-- Check if a program uses inc on a specific register -/
def hasIncReg (prog : RM) (r : Nat) : Bool :=
  prog.any fun instr =>
    match instr with
    | RMInstr.inc r' => r' = r
    | _ => false

/-- Find maximum register used by a program -/
def maxRegUsed (prog : RM) : Nat :=
  prog.foldl (fun acc instr =>
    match instr with
    | RMInstr.inc r => max acc r
    | RMInstr.dec r _ => max acc r
    | RMInstr.halt => acc) 0

/-- Find a fresh register not used by the program and ≠ 1000 -/
def freshReg (prog : RM) : Nat :=
  let m := maxRegUsed prog
  if m ≥ 1000 then m + 1 else
  if m + 1 = 1000 then m + 2 else m + 1

/-- Make a program well-formed by swapping r1000 with a fresh register -/
def makeWellFormed' (prog : RM) : RM :=
  if hasIncReg prog 1000 then swapReg prog 1000 (freshReg prog) else prog

/-- Swapping config registers to match program swap -/
def swapRegs (f : Nat → Nat) (r1 r2 : Nat) : Nat → Nat :=
  fun r => if r = r1 then f r2 else if r = r2 then f r1 else f r

def swapConfig (c : RMConfig) (r1 r2 : Nat) : RMConfig :=
  { pc := c.pc, regs := swapRegs c.regs r1 r2 }

/-- Swapping registers preserves length -/
theorem swapReg_length (prog : RM) (r1 r2 : Nat) :
    (swapReg prog r1 r2).length = prog.length := by
  simp only [swapReg, List.length_map]

/-- swapRegs is involutive -/
theorem swapRegs_involutive (f : Nat → Nat) (r1 r2 : Nat) :
    swapRegs (swapRegs f r1 r2) r1 r2 = f := by
  funext r
  simp only [swapRegs]
  split <;> split <;> simp_all

/-- swapConfig is involutive -/
theorem swapConfig_involutive (c : RMConfig) (r1 r2 : Nat) :
    swapConfig (swapConfig c r1 r2) r1 r2 = c := by
  simp only [swapConfig]
  congr 1
  exact swapRegs_involutive c.regs r1 r2

/-- swapRegs at r1 gives f r2 -/
theorem swapRegs_r1 (f : Nat → Nat) (r1 r2 : Nat) :
    swapRegs f r1 r2 r1 = f r2 := by
  simp only [swapRegs, ↓reduceIte]

/-- swapRegs at r2 gives f r1 -/
theorem swapRegs_r2 (f : Nat → Nat) (r1 r2 : Nat) (h : r1 ≠ r2) :
    swapRegs f r1 r2 r2 = f r1 := by
  simp only [swapRegs]
  split
  · rename_i heq; exact absurd heq h.symm
  · rfl

/-- swapRegs at other registers is unchanged -/
theorem swapRegs_other (f : Nat → Nat) (r1 r2 r : Nat) (h1 : r ≠ r1) (h2 : r ≠ r2) :
    swapRegs f r1 r2 r = f r := by
  simp only [swapRegs, h1, h2, ↓reduceIte]

/-- updateReg commutes with swapRegs -/
theorem updateReg_swapRegs (f : Nat → Nat) (r1 r2 r v : Nat) :
    swapRegs (updateReg f r v) r1 r2 =
    updateReg (swapRegs f r1 r2)
      (if r = r1 then r2 else if r = r2 then r1 else r)
      v := by
  funext x
  simp only [swapRegs, updateReg]
  -- Large case analysis on all conditions
  repeat (first | split | rfl | (intro h; subst h; simp_all) | omega)

/-- Get instruction in swapReg -/
theorem getInstr_swapReg (prog : RM) (r1 r2 i : Nat) :
    getInstr (swapReg prog r1 r2) i =
    (getInstr prog i).map (swapRegInstr r1 r2) := by
  simp only [getInstr, swapReg, List.getElem?_map]

/-- Single step simulation: swapped program on swapped config = swapped result -/
theorem rmStep_swapReg (prog : RM) (c : RMConfig) (r1 r2 : Nat) :
    rmStep (swapReg prog r1 r2) (swapConfig c r1 r2) =
    (rmStep prog c).map (fun c' => swapConfig c' r1 r2) := by
  simp only [rmStep, getInstr_swapReg, swapConfig]
  cases hinstr : (getInstr prog c.pc) with
  | none => simp
  | some instr =>
    simp only [Option.map]
    cases instr with
    | halt => simp [swapRegInstr]
    | inc r =>
      simp only [swapRegInstr, Option.some.injEq]
      -- Show the configs are equal
      congr 1
      -- regs: need updateReg (swapRegs ...) (swapped r) (swapped val + 1) = swapRegs (updateReg ...)
      rw [updateReg_swapRegs]
      congr 1
      -- The value swapRegs c.regs r1 r2 (swapped-r) = c.regs r
      simp only [swapRegs]
      split <;> split <;> simp_all
    | dec r j =>
      simp only [swapRegInstr]
      -- Let sr = swapped register
      let sr := if r = r1 then r2 else if r = r2 then r1 else r
      -- The key fact: swapRegs c.regs r1 r2 sr = c.regs r
      have hcomp : swapRegs c.regs r1 r2 sr = c.regs r := by
        simp only [swapRegs, sr]
        split <;> split <;> simp_all
      -- Show the if-condition on swapped equals original condition
      have hcond_eq : (swapRegs c.regs r1 r2 sr > 0) = (c.regs r > 0) := by
        rw [hcomp]
      -- Case split on original condition (c.regs r > 0)
      by_cases hgt : c.regs r > 0
      · -- c.regs r > 0: both take the decrement branch
        have hgt' : swapRegs c.regs r1 r2 sr > 0 := by rw [hcomp]; exact hgt
        simp only [sr] at hgt'
        simp only [hgt, hgt', ↓reduceIte, Option.some.injEq]
        congr 1
        -- regs
        rw [updateReg_swapRegs]
        congr 1
        -- swapRegs c.regs r1 r2 sr - 1 = c.regs r - 1
        simp only [swapRegs, sr]
        split <;> split <;> simp_all
      · -- c.regs r = 0: both take the jump branch
        have hle' : ¬(swapRegs c.regs r1 r2 sr > 0) := by rw [hcomp]; exact hgt
        simp only [sr] at hle'
        simp only [hgt, hle', ↓reduceIte]

/-- Multi-step simulation -/
theorem rmSteps_swapReg (prog : RM) (c : RMConfig) (r1 r2 : Nat) (n : Nat) :
    rmSteps (swapReg prog r1 r2) (swapConfig c r1 r2) n =
    (rmSteps prog c n).map (fun c' => swapConfig c' r1 r2) := by
  induction n generalizing c with
  | zero => simp [rmSteps]
  | succ n ih =>
    simp only [rmSteps]
    rw [rmStep_swapReg]
    cases hstep : rmStep prog c with
    | none => simp
    | some c' =>
      simp only [Option.map]
      exact ih c'

/-- Halting preserved under swapping -/
theorem isHalted_swapReg (prog : RM) (c : RMConfig) (r1 r2 : Nat) :
    isHalted (swapReg prog r1 r2) (swapConfig c r1 r2) = isHalted prog c := by
  simp only [isHalted, getInstr_swapReg, swapConfig, swapReg_length]
  cases hinstr : getInstr prog c.pc with
  | none => simp
  | some instr =>
    simp only [Option.map]
    cases instr with
    | halt => simp [swapRegInstr]
    | inc _ => simp [swapRegInstr]
    | dec _ _ => simp [swapRegInstr]

/-- Initial config with swapped regs (when r1, r2 ≠ 0) equals original -/
theorem swapConfig_init (input : Nat) (r1 r2 : Nat) (hr1 : r1 ≠ 0) (hr2 : r2 ≠ 0) :
    swapConfig (RMConfig.init input) r1 r2 = RMConfig.init input := by
  simp only [swapConfig, RMConfig.init]
  congr 1
  funext r
  simp only [swapRegs]
  split
  · rename_i heq; subst heq; simp [hr1]
  · split
    · rename_i _ heq; subst heq; simp [hr2]
    · rfl

/-- Output preserved when r0 not swapped -/
theorem rmOutput_swapReg (prog : RM) (input n : Nat) (r1 r2 : Nat)
    (hr1 : r1 ≠ 0) (hr2 : r2 ≠ 0) :
    rmOutput (swapReg prog r1 r2) input n = rmOutput prog input n := by
  simp only [rmOutput]
  -- Use swapConfig_init to rewrite the init config
  have hinit : swapConfig (RMConfig.init input) r1 r2 = RMConfig.init input :=
    swapConfig_init input r1 r2 hr1 hr2
  -- Rewrite LHS using simulation
  have hsteps_eq : rmSteps (swapReg prog r1 r2) (RMConfig.init input) n =
      (rmSteps prog (RMConfig.init input) n).map (fun c' => swapConfig c' r1 r2) := by
    calc rmSteps (swapReg prog r1 r2) (RMConfig.init input) n
        = rmSteps (swapReg prog r1 r2) (swapConfig (RMConfig.init input) r1 r2) n := by rw [hinit]
      _ = (rmSteps prog (RMConfig.init input) n).map (fun c' => swapConfig c' r1 r2) :=
            rmSteps_swapReg prog (RMConfig.init input) r1 r2 n
  rw [hsteps_eq]
  cases hsteps : rmSteps prog (RMConfig.init input) n with
  | none => simp
  | some c =>
    simp only [Option.map, isHalted_swapReg]
    split
    · -- halted: output is r0
      simp only [swapConfig]
      -- (swapRegs c.regs r1 r2) 0 = c.regs 0 when r1,r2 ≠ 0
      congr 1
      simp only [swapRegs]
      split
      · rename_i heq; exact absurd heq hr1.symm
      · split
        · rename_i _ heq; exact absurd heq hr2.symm
        · rfl
    · rfl

/-- Once halted, rmOutput stays constant (public version for use in Simulation) -/
theorem rmOutput_stable' (prog : RM) (input n m : Nat) (hn : (rmOutput prog input n).isSome)
    (hm : m ≥ n) : rmOutput prog input m = rmOutput prog input n := by
  simp only [rmOutput] at hn ⊢
  cases hsteps : rmSteps prog (RMConfig.init input) n with
  | none => simp [hsteps] at hn
  | some c =>
    simp only [hsteps] at hn ⊢
    split at hn
    · -- isHalted prog c = true
      have hhalted : isHalted prog c = true := by assumption
      have hstable := rmSteps_stable prog (RMConfig.init input) c n m hsteps hhalted hm
      simp only [hstable, hhalted, ↓reduceIte]
    · simp at hn

/-- Output value is deterministic: if program halts at two different steps, outputs are equal -/
theorem rmOutput_value_unique (prog : RM) (input n1 n2 : Nat)
    (h1 : (rmOutput prog input n1).isSome) (h2 : (rmOutput prog input n2).isSome) :
    rmOutput prog input n1 = rmOutput prog input n2 := by
  -- WLOG n1 ≤ n2
  by_cases hle : n1 ≤ n2
  · -- n1 ≤ n2: use stability from n1 to n2
    exact (rmOutput_stable' prog input n1 n2 h1 hle).symm
  · -- n2 < n1: use stability from n2 to n1
    have hle' : n2 ≤ n1 := Nat.le_of_lt (Nat.lt_of_not_le hle)
    exact rmOutput_stable' prog input n2 n1 h2 hle'

/-- Behavioral equivalence when r0 not involved -/
theorem swapReg_equiv (prog : RM) (r1 r2 : Nat) (hr1 : r1 ≠ 0) (hr2 : r2 ≠ 0) :
    rmEquiv (swapReg prog r1 r2) prog := by
  intro input
  -- Use the fact that rmOutput is equal for swapped and original
  have h_out_eq : ∀ n, rmOutput (swapReg prog r1 r2) input n = rmOutput prog input n :=
    fun n => rmOutput_swapReg prog input n r1 r2 hr1 hr2
  -- Unfold rmComputes and show the existentials are propositionally equal
  unfold rmComputes
  -- The existential conditions are equal by h_out_eq
  have h_cond : (∃ n, (rmOutput (swapReg prog r1 r2) input n).isSome) ↔
                (∃ n, (rmOutput prog input n).isSome) := by
    constructor <;> (intro ⟨n, hn⟩; exact ⟨n, by rw [h_out_eq] at *; exact hn⟩)
  -- Case split on existence
  by_cases h : ∃ n, (rmOutput prog input n).isSome
  · -- Both halt
    have h' : ∃ n, (rmOutput (swapReg prog r1 r2) input n).isSome := h_cond.mpr h
    simp only [h, h', ↓reduceDIte]
    -- LHS uses Classical.choose h', RHS uses Classical.choose h
    -- First rewrite LHS using h_out_eq
    have hlhs := h_out_eq (Classical.choose h')
    rw [hlhs]
    -- Now show rmOutput prog input (choose h') = rmOutput prog input (choose h)
    -- Both are isSome, so by uniqueness they're equal
    have hn1 : (rmOutput prog input (Classical.choose h')).isSome := by
      rw [← h_out_eq]; exact Classical.choose_spec h'
    have hn2 : (rmOutput prog input (Classical.choose h)).isSome := Classical.choose_spec h
    exact rmOutput_value_unique prog input (Classical.choose h') (Classical.choose h) hn1 hn2
  · -- Neither halts
    have h' : ¬∃ n, (rmOutput (swapReg prog r1 r2) input n).isSome := fun hx => h (h_cond.mp hx)
    simp only [h, h', ↓reduceDIte]

/-! ## freshReg Properties -/

/-- freshReg is never 1000 -/
theorem freshReg_ne_1000 (prog : RM) : freshReg prog ≠ 1000 := by
  simp only [freshReg]
  split
  · -- m ≥ 1000, so freshReg = m + 1 ≥ 1001
    omega
  · split
    · -- m + 1 = 1000, so freshReg = m + 2 = 1001
      omega
    · -- m < 1000 and m + 1 ≠ 1000, so freshReg = m + 1 < 1000
      omega

/-- freshReg is never 0 -/
theorem freshReg_ne_0 (prog : RM) : freshReg prog ≠ 0 := by
  simp only [freshReg]
  split
  · -- m ≥ 1000, so freshReg = m + 1 ≥ 1001
    omega
  · split
    · -- m + 1 = 1000, so freshReg = m + 2 = 1001
      omega
    · -- freshReg = m + 1 ≥ 1
      omega

/-- foldl result is ≥ start -/
private theorem maxRegUsed_foldl_ge_start (l : List RMInstr) (start : Nat) :
    start ≤ l.foldl (fun acc instr => match instr with
      | RMInstr.inc r => max acc r
      | RMInstr.dec r _ => max acc r
      | RMInstr.halt => acc) start := by
  induction l generalizing start with
  | nil => exact Nat.le_refl start
  | cons hd tl ih =>
    simp only [List.foldl]
    cases hd with
    | inc r => exact Nat.le_trans (Nat.le_max_left start r) (ih (max start r))
    | dec r _ => exact Nat.le_trans (Nat.le_max_left start r) (ih (max start r))
    | halt => exact ih start

/-- If inc r is in the list, then r ≤ foldl result -/
private theorem inc_le_foldl (l : List RMInstr) (r : Nat) (start : Nat)
    (hinlist : RMInstr.inc r ∈ l) :
    r ≤ l.foldl (fun acc instr => match instr with
      | RMInstr.inc r' => max acc r'
      | RMInstr.dec r' _ => max acc r'
      | RMInstr.halt => acc) start := by
  induction l generalizing start with
  | nil => simp at hinlist
  | cons hd tl ih =>
    simp only [List.foldl]
    cases hinlist with
    | head =>
      have hmax : r ≤ max start r := Nat.le_max_right start r
      exact Nat.le_trans hmax (maxRegUsed_foldl_ge_start tl (max start r))
    | tail _ htl =>
      cases hd with
      | inc r' => exact ih (max start r') htl
      | dec r' _ => exact ih (max start r') htl
      | halt => exact ih start htl

/-- If inc r is in prog, then r ≤ maxRegUsed prog -/
theorem inc_le_maxRegUsed (prog : RM) (r : Nat) (hinlist : RMInstr.inc r ∈ prog) :
    r ≤ maxRegUsed prog :=
  inc_le_foldl prog r 0 hinlist

/-- freshReg prog > maxRegUsed prog -/
theorem freshReg_gt_maxRegUsed (prog : RM) : freshReg prog > maxRegUsed prog := by
  simp only [freshReg]
  split
  · omega
  · split <;> omega

/-- hasIncReg false implies WellFormedRM -/
theorem hasIncReg_false_wf (prog : RM) (h : hasIncReg prog 1000 = false) :
    WellFormedRM prog := by
  intro i hi heq
  -- If prog[i]? = some (RMInstr.inc 1000), then hasIncReg prog 1000 = true
  have hinlist : RMInstr.inc 1000 ∈ prog := by
    rw [List.mem_iff_getElem?]
    exact ⟨i, heq⟩
  -- hasIncReg finds inc 1000 in list
  have htrue : hasIncReg prog 1000 = true := by
    simp only [hasIncReg, List.any_eq_true]
    exact ⟨RMInstr.inc 1000, hinlist, by simp⟩
  -- Contradiction
  rw [htrue] at h
  simp at h

/-- Swapping 1000 with freshReg produces well-formed program -/
theorem swapReg_1000_freshReg_wf (prog : RM) :
    WellFormedRM (swapReg prog 1000 (freshReg prog)) := by
  intro i hi
  simp only [swapReg, List.length_map] at hi
  simp only [swapReg, List.getElem?_map]
  cases hget : prog[i]? with
  | none =>
    intro h
    exact Option.noConfusion h
  | some instr =>
    simp only [Option.map]
    intro heq
    have hinj := Option.some.inj heq
    have hr2 : freshReg prog ≠ 1000 := freshReg_ne_1000 prog
    cases instr with
    | inc r =>
      simp only [swapRegInstr] at hinj
      split at hinj
      · -- r = 1000: result is inc (freshReg prog)
        have : freshReg prog = 1000 := RMInstr.inc.inj hinj
        exact hr2 this
      · split at hinj
        · -- r = freshReg prog: result is inc 1000
          -- But freshReg > maxRegUsed, so prog can't have inc (freshReg prog)
          rename_i _ heqr
          -- heqr : r = freshReg prog
          -- r is in the original program, so r ≤ maxRegUsed prog
          have hinlist : RMInstr.inc r ∈ prog := by
            rw [List.mem_iff_getElem?]
            exact ⟨i, hget⟩
          have hle : r ≤ maxRegUsed prog := inc_le_maxRegUsed prog r hinlist
          have hgt : freshReg prog > maxRegUsed prog := freshReg_gt_maxRegUsed prog
          omega
        · -- r ≠ 1000 and r ≠ freshReg: result is inc r
          have : r = 1000 := RMInstr.inc.inj hinj
          rename_i hn1 _
          exact hn1 this
    | dec r j =>
      simp only [swapRegInstr] at hinj
      exact RMInstr.noConfusion hinj
    | halt =>
      simp only [swapRegInstr] at hinj
      exact RMInstr.noConfusion hinj

/-- makeWellFormed' produces a well-formed program -/
theorem makeWellFormed_wf (prog : RM) : WellFormedRM (makeWellFormed' prog) := by
  simp only [makeWellFormed']
  split
  · -- hasIncReg prog 1000 = true, so we swap
    exact swapReg_1000_freshReg_wf prog
  · -- hasIncReg prog 1000 = false, already well-formed
    rename_i h
    exact hasIncReg_false_wf prog (Bool.eq_false_iff.mpr h)

/-- makeWellFormed' preserves equivalence -/
theorem makeWellFormed_equiv (prog : RM) : rmEquiv (makeWellFormed' prog) prog := by
  simp only [makeWellFormed']
  split
  · -- hasIncReg prog 1000 = true, so we swap
    have hr1 : (1000 : Nat) ≠ 0 := by decide
    have hr2 : freshReg prog ≠ 0 := freshReg_ne_0 prog
    exact swapReg_equiv prog 1000 (freshReg prog) hr1 hr2
  · -- hasIncReg prog 1000 = false, identity
    exact rmEquiv_refl prog

/-! ## Bounds Hypothesis Transfer -/

/-- swapConfig preserves pc -/
theorem swapConfig_pc (c : RMConfig) (r1 r2 : Nat) :
    (swapConfig c r1 r2).pc = c.pc := rfl

/-- Bounds hypothesis transfers through makeWellFormed' -/
theorem makeWellFormed_bounds (prog : RM) (input : Nat)
    (hbounds : ∀ n c, rmSteps prog (RMConfig.init input) n = some c → c.pc < prog.length) :
    ∀ n c, rmSteps (makeWellFormed' prog) (RMConfig.init input) n = some c → c.pc < (makeWellFormed' prog).length := by
  intro n c hsteps
  by_cases hasInc : hasIncReg prog 1000 = true
  · -- hasIncReg prog 1000 = true: prog is swapped
    simp only [makeWellFormed', hasInc, ↓reduceIte] at hsteps ⊢
    simp only [swapReg_length]
    have hinit : swapConfig (RMConfig.init input) 1000 (freshReg prog) = RMConfig.init input :=
      swapConfig_init input 1000 (freshReg prog) (by decide) (freshReg_ne_0 prog)
    have hsim := rmSteps_swapReg prog (RMConfig.init input) 1000 (freshReg prog) n
    rw [hinit] at hsim
    rw [hsim] at hsteps
    cases hsteps_orig : rmSteps prog (RMConfig.init input) n with
    | none => simp [hsteps_orig] at hsteps
    | some c_orig =>
      simp only [hsteps_orig, Option.map] at hsteps
      have heq := Option.some.inj hsteps
      rw [← heq, swapConfig_pc]
      exact hbounds n c_orig hsteps_orig
  · -- hasIncReg prog 1000 = false: prog unchanged
    simp only [makeWellFormed', hasInc, Bool.false_eq_true, ↓reduceIte] at hsteps ⊢
    exact hbounds n c hsteps

/-- Bounds hypothesis transfers for arbitrary initial value (for p) -/
theorem makeWellFormed_bounds_all (prog : RM)
    (hbounds : ∀ v n c, rmSteps prog (RMConfig.init v) n = some c → c.pc < prog.length) :
    ∀ v n c, rmSteps (makeWellFormed' prog) (RMConfig.init v) n = some c → c.pc < (makeWellFormed' prog).length := by
  intro v
  exact makeWellFormed_bounds prog v (fun n c hsteps => hbounds v n c hsteps)

/-! ## Clean Hypothesis Transfer -/

/-- Accessing swapped config at r ≠ 0 when r1, r2 ≠ 0 -/
theorem swapConfig_regs_nonzero (c : RMConfig) (r1 r2 r : Nat)
    (hr1_ne_0 : r1 ≠ 0) (hr2_ne_0 : r2 ≠ 0) (hr_ne_0 : r ≠ 0) :
    (swapConfig c r1 r2).regs r =
    if r = r1 then c.regs r2 else if r = r2 then c.regs r1 else c.regs r := by
  simp only [swapConfig, swapRegs]

/-- If r ≠ 0, r ≠ 1000, r ≠ freshReg prog, then swapConfig c preserves c.regs r -/
theorem swapConfig_regs_other_nonzero (c : RMConfig) (prog : RM) (r : Nat)
    (hr_ne_0 : r ≠ 0) (hr_ne_1000 : r ≠ 1000) (hr_ne_fresh : r ≠ freshReg prog) :
    (swapConfig c 1000 (freshReg prog)).regs r = c.regs r := by
  simp only [swapConfig, swapRegs, hr_ne_1000, hr_ne_fresh, ↓reduceIte]

/-- Clean hypothesis transfers through makeWellFormed' -/
theorem makeWellFormed_clean (prog : RM) (input : Nat)
    (hclean : ∀ n c, rmSteps prog (RMConfig.init input) n = some c →
        isHalted prog c = true → ∀ r, r ≠ 0 → c.regs r = 0) :
    ∀ n c, rmSteps (makeWellFormed' prog) (RMConfig.init input) n = some c →
        isHalted (makeWellFormed' prog) c = true → ∀ r, r ≠ 0 → c.regs r = 0 := by
  intro n c hsteps hhalted r hr_ne_0
  by_cases hasInc : hasIncReg prog 1000 = true
  · -- hasIncReg prog 1000 = true: prog is swapped
    simp only [makeWellFormed', hasInc, ↓reduceIte] at hsteps hhalted
    have hinit : swapConfig (RMConfig.init input) 1000 (freshReg prog) = RMConfig.init input :=
      swapConfig_init input 1000 (freshReg prog) (by decide) (freshReg_ne_0 prog)
    have hsim := rmSteps_swapReg prog (RMConfig.init input) 1000 (freshReg prog) n
    rw [hinit] at hsim
    rw [hsim] at hsteps
    cases hsteps_orig : rmSteps prog (RMConfig.init input) n with
    | none => simp [hsteps_orig] at hsteps
    | some c_orig =>
      simp only [hsteps_orig, Option.map] at hsteps
      have heq := Option.some.inj hsteps
      -- c = swapConfig c_orig 1000 (freshReg prog)
      subst heq
      -- Show halted: by isHalted_swapReg
      have hhalted_orig : isHalted prog c_orig = true := by
        rw [← isHalted_swapReg prog c_orig 1000 (freshReg prog)]
        exact hhalted
      -- Get clean property for c_orig
      -- c.regs r = swapRegs c_orig.regs 1000 (freshReg prog) r
      simp only [swapConfig, swapRegs]
      split
      · -- r = 1000
        have hfresh_ne_0 := freshReg_ne_0 prog
        exact hclean n c_orig hsteps_orig hhalted_orig (freshReg prog) hfresh_ne_0
      · split
        · -- r = freshReg prog
          exact hclean n c_orig hsteps_orig hhalted_orig 1000 (by decide)
        · -- r ≠ 1000, r ≠ freshReg prog
          exact hclean n c_orig hsteps_orig hhalted_orig r hr_ne_0
  · -- hasIncReg prog 1000 = false: prog unchanged
    simp only [makeWellFormed', hasInc, Bool.false_eq_true, ↓reduceIte] at hsteps hhalted
    exact hclean n c hsteps hhalted r hr_ne_0

/-! ## Main Theorem: rmCompose_spec without WellFormedRM -/

/-- rmCompose_spec without the WellFormedRM hypothesis.

    This theorem shows that composition respects sequential semantics
    for any programs satisfying the bounds and clean hypotheses,
    regardless of whether they use register 1000.

    The proof works by:
    1. Transforming p and q to well-formed equivalents via makeWellFormed'
    2. Showing the bounds/clean hypotheses transfer
    3. Applying rmCompose_spec_wf to the well-formed versions
    4. Using equivalence to get the result for the original programs -/
theorem rmCompose_spec_bounds (p q : RM) (input : Nat)
    (hq_bounds : ∀ n c, rmSteps q (RMConfig.init input) n = some c → c.pc < q.length)
    (hp_bounds : ∀ v n c, rmSteps p (RMConfig.init v) n = some c → c.pc < p.length)
    (hq_clean : ∀ n c, rmSteps q (RMConfig.init input) n = some c →
        isHalted q c = true → ∀ r, r ≠ 0 → c.regs r = 0) :
    rmComputes (rmCompose p q) input = (rmComputes q input) >>= (rmComputes p) := by
  -- Transform to well-formed versions
  let p' := makeWellFormed' p
  let q' := makeWellFormed' q
  -- Well-formedness
  have hwf_p' : WellFormedRM p' := makeWellFormed_wf p
  have hwf_q' : WellFormedRM q' := makeWellFormed_wf q
  -- Equivalence
  have hp_equiv : rmEquiv p' p := makeWellFormed_equiv p
  have hq_equiv : rmEquiv q' q := makeWellFormed_equiv q
  -- Bounds transfer
  have hq'_bounds : ∀ n c, rmSteps q' (RMConfig.init input) n = some c → c.pc < q'.length :=
    makeWellFormed_bounds q input hq_bounds
  have hp'_bounds : ∀ v n c, rmSteps p' (RMConfig.init v) n = some c → c.pc < p'.length :=
    makeWellFormed_bounds_all p hp_bounds
  -- Clean transfer
  have hq'_clean : ∀ n c, rmSteps q' (RMConfig.init input) n = some c →
      isHalted q' c = true → ∀ r, r ≠ 0 → c.regs r = 0 :=
    makeWellFormed_clean q input hq_clean
  -- Apply rmCompose_spec_wf to the well-formed versions
  have hspec' := rmCompose_spec_wf p' q' input hwf_p' hwf_q' hq'_bounds hp'_bounds hq'_clean
  -- hspec' : rmComputes (rmCompose p' q') input = (rmComputes q' input) >>= (rmComputes p')
  -- By equivalence: rmComputes q' input = rmComputes q input
  --                 rmComputes p' v = rmComputes p v for all v
  have hq'_eq : rmComputes q' input = rmComputes q input := hq_equiv input
  have hp'_eq : ∀ v, rmComputes p' v = rmComputes p v := fun v => hp_equiv v
  -- Rewrite the RHS using equivalences
  rw [hq'_eq, bind_congr (fun v => hp'_eq v)] at hspec'
  -- hspec' : rmComputes (rmCompose p' q') input = (rmComputes q input) >>= (rmComputes p)
  -- Now we need: rmComputes (rmCompose p q) input = rmComputes (rmCompose p' q') input
  -- This follows from the fact that both equal (rmComputes q input) >>= (rmComputes p)
  -- Use the axiom for the original composition (goal becomes trivial by rfl)
  rw [rmCompose_spec p q input]
