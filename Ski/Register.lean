/-
  Register Machines

  A simple Turing-complete computational model consisting of:
  - Unbounded registers holding natural numbers
  - Three instructions: increment, decrement-or-jump, halt
-/

/-! ## Register Machine Instructions -/

/-- Register machine instructions -/
inductive RMInstr where
  /-- Increment register r, then go to next instruction -/
  | inc : Nat → RMInstr
  /-- If register r > 0, decrement and go to next; else jump to line j -/
  | dec : Nat → Nat → RMInstr
  /-- Halt execution -/
  | halt : RMInstr
  deriving Repr, DecidableEq

/-- A register machine is a list of instructions -/
abbrev RM := List RMInstr

instance : DecidableEq RM := inferInstanceAs (DecidableEq (List RMInstr))

/-! ## Configuration and Execution -/

/-- Configuration: program counter + register values -/
structure RMConfig where
  /-- Current instruction index (0-based) -/
  pc : Nat
  /-- Register values (infinite registers, indexed by Nat) -/
  regs : Nat → Nat

/-- Initial configuration with input in register 0 -/
def RMConfig.init (input : Nat) : RMConfig :=
  { pc := 0, regs := fun r => if r = 0 then input else 0 }

/-- Update a register value -/
def updateReg (regs : Nat → Nat) (r : Nat) (v : Nat) : Nat → Nat :=
  fun r' => if r' = r then v else regs r'

/-- Get instruction at index, if valid -/
def getInstr (prog : RM) (i : Nat) : Option RMInstr := prog[i]?

/-- Single step of execution. Returns None if halted or PC out of bounds. -/
def rmStep (prog : RM) (c : RMConfig) : Option RMConfig :=
  match getInstr prog c.pc with
  | none => none  -- PC out of bounds, halt
  | some RMInstr.halt => none  -- Explicit halt
  | some (RMInstr.inc r) =>
    some { pc := c.pc + 1, regs := updateReg c.regs r (c.regs r + 1) }
  | some (RMInstr.dec r j) =>
    if c.regs r > 0 then
      some { pc := c.pc + 1, regs := updateReg c.regs r (c.regs r - 1) }
    else
      some { pc := j, regs := c.regs }

/-- Execute n steps from configuration c -/
def rmSteps (prog : RM) (c : RMConfig) : Nat → Option RMConfig
  | 0 => some c
  | n + 1 => match rmStep prog c with
    | none => some c  -- Halted
    | some c' => rmSteps prog c' n

/-- Check if configuration is halted (computable) -/
def isHalted (prog : RM) (c : RMConfig) : Bool :=
  match getInstr prog c.pc with
  | none => true
  | some RMInstr.halt => true
  | some _ => false

/-- isHalted is equivalent to rmStep returning none -/
theorem isHalted_iff (prog : RM) (c : RMConfig) :
    isHalted prog c = true ↔ rmStep prog c = none := by
  simp only [isHalted, rmStep, getInstr]
  cases prog[c.pc]? with
  | none => simp
  | some instr =>
    cases instr with
    | halt => simp
    | inc r => simp
    | dec r j => simp; split <;> simp

/-! ## Partial Function Semantics -/

/-- Result of running a program: either halts with output or diverges -/
inductive RMResult where
  | halts : Nat → RMResult  -- Halted with output (register 0)
  | diverges : RMResult
  deriving Repr, DecidableEq

/-- A program halts from initial config with given input if it reaches a halted state -/
def rmHalts (prog : RM) (input : Nat) : Prop :=
  ∃ n c, rmSteps prog (RMConfig.init input) n = some c ∧ isHalted prog c

/-- Get the output (register 0) when halted after n steps -/
def rmOutput (prog : RM) (input : Nat) (n : Nat) : Option Nat :=
  match rmSteps prog (RMConfig.init input) n with
  | none => none
  | some c => if isHalted prog c then some (c.regs 0) else none

/-- The partial function computed by a register machine.
    Uses classical logic to find a halting step if one exists. -/
noncomputable def rmComputes (prog : RM) (input : Nat) : Option Nat :=
  open Classical in
  if h : ∃ n, (rmOutput prog input n).isSome then
    rmOutput prog input (Classical.choose h)
  else
    none

/-! ## Stability Lemmas -/

/-- One more step from a halted config stays at the same config -/
theorem rmSteps_halted_succ (prog : RM) (c c' : RMConfig) (n : Nat)
    (hsteps : rmSteps prog c n = some c') (hhalted : isHalted prog c') :
    rmSteps prog c (n + 1) = some c' := by
  induction n generalizing c with
  | zero =>
    -- rmSteps prog c 0 = some c, so c = c'
    simp only [rmSteps] at hsteps
    have heq : c = c' := Option.some.inj hsteps
    subst heq
    -- Now show rmSteps prog c 1 = some c (where c = c')
    simp only [rmSteps]
    have hstep : rmStep prog c = none := isHalted_iff prog c |>.mp hhalted
    simp only [hstep]
  | succ n ih =>
    simp only [rmSteps] at hsteps ⊢
    cases hstep : rmStep prog c with
    | none =>
      -- c is halted, so rmSteps prog c (n+1) = some c = some c'
      simp only [hstep] at hsteps
      have heq : c = c' := Option.some.inj hsteps
      subst heq
      rfl
    | some c'' =>
      simp only [hstep] at hsteps ⊢
      exact ih c'' hsteps

/-- rmSteps is stable after halting: more steps give the same result -/
theorem rmSteps_stable (prog : RM) (c c' : RMConfig) (n m : Nat)
    (hsteps : rmSteps prog c n = some c') (hhalted : isHalted prog c') (hm : m ≥ n) :
    rmSteps prog c m = some c' := by
  induction m with
  | zero =>
    have : n = 0 := Nat.eq_zero_of_le_zero hm
    subst this
    exact hsteps
  | succ m ih =>
    cases Nat.lt_or_ge n (m + 1) with
    | inl hlt =>
      have hle : n ≤ m := Nat.lt_succ_iff.mp hlt
      have hprev := ih hle
      exact rmSteps_halted_succ prog c c' m hprev hhalted
    | inr hge =>
      have heq : n = m + 1 := Nat.le_antisymm hm hge
      subst heq
      exact hsteps

/-! ## Behavioral Equivalence -/

/-- Two programs are equivalent if they compute the same partial function -/
def rmEquiv (p q : RM) : Prop :=
  ∀ input, rmComputes p input = rmComputes q input

/-- Equivalence is reflexive -/
theorem rmEquiv_refl : ∀ p, rmEquiv p p := fun _ _ => rfl

/-- Equivalence is symmetric -/
theorem rmEquiv_symm : ∀ p q, rmEquiv p q → rmEquiv q p :=
  fun _ _ h input => (h input).symm

/-- Equivalence is transitive -/
theorem rmEquiv_trans : ∀ p q r, rmEquiv p q → rmEquiv q r → rmEquiv p r :=
  fun _ _ _ hpq hqr input => (hpq input).trans (hqr input)

/-! ## Example Programs -/

/-- Identity program: outputs input unchanged -/
def rmId : RM := [RMInstr.halt]

/-- Successor program: outputs input + 1 -/
def rmSucc : RM :=
  [ RMInstr.inc 0,
    RMInstr.halt ]

/-- Program that always outputs 1 (clears r0, then increments).
    Uses r1 (known to be 0 initially) for unconditional jumps via dec r1 target. -/
def rmTru : RM :=
  [ RMInstr.dec 0 2,   -- 0: if r0>0 then {dec r0; goto 1} else goto 2
    RMInstr.dec 1 0,   -- 1: r1=0, so goto 0 (loop back to clear)
    RMInstr.inc 0,     -- 2: r0 = 0 here, set to 1
    RMInstr.halt ]     -- 3: halt

/-- Program that always outputs 0 (clears r0 then halts) -/
def rmFls : RM :=
  [ RMInstr.dec 0 2,   -- 0: if r0>0 then {dec r0; goto 1} else goto 2
    RMInstr.dec 1 0,   -- 1: r1=0, so goto 0 (loop back to clear)
    RMInstr.halt ]     -- 2: r0 = 0, halt
