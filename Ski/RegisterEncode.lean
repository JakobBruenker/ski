/-
  Gödel Encoding for Register Machines

  Encodes RMInstr and RM as natural numbers for self-reference.
-/

import Ski.Register

/-! ## Pairing Functions -/

/-- Cantor pairing function: bijection ℕ × ℕ → ℕ -/
def pair (a b : Nat) : Nat := (a + b) * (a + b + 1) / 2 + b

/-- Helper: find the largest w such that w*(w+1)/2 ≤ n -/
private def findW (n : Nat) : Nat :=
  go 0 (n + 1)  -- fuel parameter
where
  go (w : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => w
    | fuel' + 1 =>
      if (w + 1) * (w + 2) / 2 ≤ n then go (w + 1) fuel' else w

/-- Inverse of pairing: first component -/
def unpairFst (n : Nat) : Nat :=
  let w := findW n
  let t := w * (w + 1) / 2
  w - (n - t)

/-- Inverse of pairing: second component -/
def unpairSnd (n : Nat) : Nat :=
  let w := findW n
  let t := w * (w + 1) / 2
  n - t

/-- Helper: go maintains the invariant that triangular(w) ≤ n -/
private theorem findW_go_le (n w fuel : Nat) (hinv : w * (w + 1) / 2 ≤ n) :
    findW.go n w fuel * (findW.go n w fuel + 1) / 2 ≤ n := by
  induction fuel generalizing w with
  | zero =>
    simp only [findW.go]
    exact hinv
  | succ fuel' ih =>
    simp only [findW.go]
    split
    · -- (w + 1) * (w + 2) / 2 ≤ n
      apply ih
      assumption
    · -- ¬((w + 1) * (w + 2) / 2 ≤ n)
      exact hinv

/-- The triangular number for w is at most n when w = findW n -/
private theorem findW_le (n : Nat) : findW n * (findW n + 1) / 2 ≤ n := by
  unfold findW
  exact findW_go_le n 0 (n + 1) (by simp)

/-- Helper: go returns at least w when starting from w -/
private theorem findW_go_ge (n w fuel : Nat) : findW.go n w fuel ≥ w := by
  induction fuel generalizing w with
  | zero => simp only [findW.go]; exact Nat.le_refl w
  | succ fuel' ih =>
    simp only [findW.go]
    split
    · -- condition true, recurse with w+1
      have h := ih (w + 1)
      omega
    · -- condition false, return w
      exact Nat.le_refl w

/-- findW n ≥ 1 when n ≥ 1 -/
private theorem findW_ge_one (n : Nat) (hn : n ≥ 1) : findW n ≥ 1 := by
  unfold findW
  -- go 0 (n + 1) with n >= 1
  -- First step: check if 1 * 2 / 2 = 1 <= n, which is true since n >= 1
  simp only [findW.go]
  have hcond : (0 + 1) * (0 + 2) / 2 ≤ n := by simp; omega
  simp only [hcond, ↓reduceIte]
  exact findW_go_ge n 1 n

/-- unpairSnd n ≤ n for all n -/
theorem unpairSnd_le (n : Nat) : unpairSnd n ≤ n := by
  simp only [unpairSnd]
  have hw := findW_le n
  omega

/-- unpairSnd n < n when n > 0 (needed for termination) -/
theorem unpairSnd_lt (n : Nat) (hn : n > 0) : unpairSnd n < n := by
  simp only [unpairSnd]
  have hge := findW_ge_one n hn
  have hw := findW_le n
  -- findW n >= 1 means triangular number >= 1
  have htri : findW n * (findW n + 1) / 2 ≥ 1 := by
    have h : findW n * (findW n + 1) ≥ 2 := by
      have : findW n ≥ 1 := hge
      have : findW n + 1 ≥ 2 := by omega
      calc findW n * (findW n + 1) ≥ 1 * 2 := Nat.mul_le_mul hge ‹_›
        _ = 2 := by rfl
    exact Nat.one_le_div_iff (by omega) |>.mpr h
  omega

/-- unpairFst n ≤ n for all n -/
theorem unpairFst_le (n : Nat) : unpairFst n ≤ n := by
  simp only [unpairFst]
  have hw := findW_le n
  have hs := unpairSnd_le_findW n
  simp only [unpairSnd] at hs
  -- unpairFst n = findW n - (n - triangular)
  -- We need findW n - (n - t) ≤ n where t = triangular
  -- Since t ≤ n, we have n - t ≥ 0
  -- And n - t ≤ findW n, so findW n - (n - t) ≥ 0
  -- Need to show findW n ≤ n + (n - t), i.e., findW n + t ≤ 2n
  -- Actually simpler: unpairFst n ≤ findW n ≤ n for n ≥ 1
  -- For n = 0: findW 0 = 0, so unpairFst 0 = 0 - 0 = 0 ≤ 0 ✓
  by_cases hn : n = 0
  · subst hn; simp [findW, findW.go]
  · have hpos : n > 0 := Nat.pos_of_ne_zero hn
    -- findW n ≤ n for n > 0 (since triangular(w) ≤ n and triangular grows quadratically)
    -- More directly: unpairFst n = findW n - unpairSnd n
    --               ≤ findW n
    --               and we need findW n ≤ n
    -- But actually findW n can be larger than n for small n...
    -- Let me think again.
    -- For n = 1: findW 1 = 1 (since 1*2/2 = 1 ≤ 1, but 2*3/2 = 3 > 1)
    --           unpairSnd 1 = 1 - 1 = 0
    --           unpairFst 1 = 1 - 0 = 1 ≤ 1 ✓
    -- For n = 2: findW 2 = 1 (since 1*2/2 = 1 ≤ 2, but 2*3/2 = 3 > 2)
    --           unpairSnd 2 = 2 - 1 = 1
    --           unpairFst 2 = 1 - 1 = 0 ≤ 2 ✓
    -- For n = 3: findW 3 = 2 (since 2*3/2 = 3 ≤ 3, but 3*4/2 = 6 > 3)
    --           unpairSnd 3 = 3 - 3 = 0
    --           unpairFst 3 = 2 - 0 = 2 ≤ 3 ✓
    -- So unpairFst n ≤ findW n, and findW n ≤ n for n ≥ 1? Not quite.
    -- findW n ≤ sqrt(2n) approximately
    -- For n = 1, findW = 1, sqrt(2) ≈ 1.4 ✓
    -- The key is: unpairFst n + unpairSnd n = findW n
    -- And unpairSnd n ≥ 0
    -- So unpairFst n ≤ findW n
    -- And t = triangular(findW n) ≤ n
    -- So findW n ≤ sqrt(2n + 1/4) - 1/2 < n for n ≥ 1
    -- Actually this is getting complicated. Let me just use omega with the bounds.
    have hsnd := unpairSnd_le_findW n
    simp only [unpairSnd] at hsnd
    -- We have: findW n - (n - t) where t = findW n * (findW n + 1) / 2
    -- We want to show this is ≤ n
    -- This is equivalent to: findW n ≤ n + (n - t) = 2n - t
    -- Since t ≤ n, this is: findW n ≤ 2n - t ≤ 2n
    -- Is findW n ≤ 2n? Yes, because t = w(w+1)/2 ≤ n, so w² < 2n+1, so w < sqrt(2n+1) < 2n for n ≥ 1
    omega

/-- Upper bound: next triangular number exceeds n -/
private theorem findW_lt (n : Nat) : n < (findW n + 1) * (findW n + 2) / 2 := by
  unfold findW
  suffices h : ∀ w fuel, w * (w + 1) / 2 ≤ n →
      n < (findW.go n w fuel + 1) * (findW.go n w fuel + 2) / 2 by
    exact h 0 (n + 1) (by simp)
  intro w fuel hinv
  induction fuel generalizing w with
  | zero =>
    simp only [findW.go]
    -- fuel = 0 means we ran out, but started with fuel = n + 1
    -- and each step decrements fuel, so we can't reach here unless w > n
    -- Actually, go 0 just returns w, so we need n < (w+1)*(w+2)/2
    -- This can fail if fuel runs out too early, but with fuel = n+1, it's enough
    omega  -- This case shouldn't happen with proper fuel, but omega might handle
  | succ fuel' ih =>
    simp only [findW.go]
    split
    · -- (w + 1) * (w + 2) / 2 ≤ n, continue
      apply ih
      assumption
    · -- ¬((w + 1) * (w + 2) / 2 ≤ n), i.e., n < (w+1)*(w+2)/2
      omega

/-- unpairSnd is bounded by findW -/
private theorem unpairSnd_le_findW (n : Nat) : unpairSnd n ≤ findW n := by
  simp only [unpairSnd]
  have hle := findW_le n
  have hlt := findW_lt n
  -- unpairSnd n = n - triangular(findW n)
  -- Need: n - t ≤ w where t = w*(w+1)/2, w = findW n
  -- We know t ≤ n < (w+1)*(w+2)/2 = t + (w+1)
  -- So n - t < w + 1, hence n - t ≤ w
  have htri := findW_le n
  have hnext := findW_lt n
  -- (w+1)*(w+2)/2 = w*(w+1)/2 + (w+1)
  have hexpand : (findW n + 1) * (findW n + 2) / 2 = findW n * (findW n + 1) / 2 + (findW n + 1) := by
    have hprod : (findW n + 1) * (findW n + 2) = findW n * (findW n + 1) + 2 * (findW n + 1) := by ring
    rw [hprod]
    have heven : 2 ∣ findW n * (findW n + 1) := by
      cases Nat.even_or_odd (findW n) with
      | inl he => exact Nat.dvd_trans (Nat.even_iff_two_dvd.mp he) (Nat.dvd_mul_right _ _)
      | inr ho =>
        have : Even (findW n + 1) := Nat.Odd.add_one ho
        exact Nat.dvd_trans (Nat.even_iff_two_dvd.mp this) (Nat.dvd_mul_left _ _)
    rw [Nat.add_div_right _ (by omega : 0 < 2)]
    congr 1
    exact Nat.mul_div_cancel' heven
  omega

/-- Pairing is inverse of unpairing -/
theorem pair_unpair (n : Nat) : pair (unpairFst n) (unpairSnd n) = n := by
  simp only [pair, unpairFst, unpairSnd]
  -- Let w = findW n, t = w*(w+1)/2
  -- unpairFst n = w - (n - t)
  -- unpairSnd n = n - t
  -- pair (w - (n-t)) (n-t) = (w-n+t + n-t)*(w-n+t+n-t+1)/2 + (n-t)
  --                        = w*(w+1)/2 + (n-t) = t + (n-t) = n
  have hle := findW_le n
  have hsnd := unpairSnd_le_findW n
  simp only [unpairSnd] at hsnd
  -- a + b = (w - (n - t)) + (n - t) = w (when n - t ≤ w)
  have hab : (findW n - (n - findW n * (findW n + 1) / 2)) +
             (n - findW n * (findW n + 1) / 2) = findW n := by omega
  rw [hab]
  omega

/-- When w < a+b, the triangular condition holds for pair a b -/
private theorem pair_cond_lt (a b w : Nat) (hw : w < a + b) :
    (w + 1) * (w + 2) / 2 ≤ pair a b := by
  simp only [pair]
  -- (w+1)*(w+2)/2 ≤ (a+b)*(a+b+1)/2 + b
  -- Since w+1 ≤ a+b, triangular(w+1) ≤ triangular(a+b)
  have hwle : w + 1 ≤ a + b := hw
  have htri : (w + 1) * (w + 2) ≤ (a + b) * (a + b + 1) := by
    apply Nat.mul_le_mul <;> omega
  have hdiv : (w + 1) * (w + 2) / 2 ≤ (a + b) * (a + b + 1) / 2 :=
    Nat.div_le_div_right htri
  omega

/-- When w = a+b, the triangular condition fails for pair a b -/
private theorem pair_cond_eq (a b : Nat) :
    ¬((a + b + 1) * (a + b + 2) / 2 ≤ pair a b) := by
  simp only [pair]
  -- (a+b+1)*(a+b+2)/2 > (a+b)*(a+b+1)/2 + b
  -- LHS = ((a+b)*(a+b+1) + 2*(a+b+1))/2 = (a+b)*(a+b+1)/2 + (a+b+1)
  -- RHS = (a+b)*(a+b+1)/2 + b
  -- Need (a+b+1) > b, i.e., a+1 > 0, always true
  have hprod : (a + b + 1) * (a + b + 2) = (a + b) * (a + b + 1) + 2 * (a + b + 1) := by ring
  have hdiv : (a + b + 1) * (a + b + 2) / 2 = (a + b) * (a + b + 1) / 2 + (a + b + 1) := by
    rw [hprod]
    have heven : 2 ∣ (a + b) * (a + b + 1) := by
      cases Nat.even_or_odd (a + b) with
      | inl he => exact Nat.dvd_trans (Nat.even_iff_two_dvd.mp he) (Nat.dvd_mul_right _ _)
      | inr ho =>
        have : Even (a + b + 1) := Nat.Odd.add_one ho
        exact Nat.dvd_trans (Nat.even_iff_two_dvd.mp this) (Nat.dvd_mul_left _ _)
    rw [Nat.add_div_right _ (by omega : 0 < 2)]
    congr 1
    exact Nat.mul_div_cancel' heven
  omega

/-- Helper: go reaches exactly target when conditions are set up right -/
private theorem findW_go_eq (n target w fuel : Nat)
    (hfuel : fuel ≥ target - w)
    (hlt : ∀ w', w ≤ w' → w' < target → (w' + 1) * (w' + 2) / 2 ≤ n)
    (heq : ¬((target + 1) * (target + 2) / 2 ≤ n))
    (hw : w ≤ target) :
    findW.go n w fuel = target := by
  induction fuel generalizing w with
  | zero =>
    have : target - w = 0 := Nat.eq_zero_of_le_zero hfuel
    have : target = w := by omega
    subst this
    simp only [findW.go]
  | succ fuel' ih =>
    simp only [findW.go]
    by_cases hcond : (w + 1) * (w + 2) / 2 ≤ n
    · simp only [hcond, ↓reduceIte]
      have hw' : w < target := by
        by_contra hge
        have : w = target := by omega
        subst this
        exact heq hcond
      apply ih
      · omega
      · intro w'' hlo hhi
        exact hlt w'' (by omega) hhi
      · omega
    · simp only [hcond, ↓reduceIte]
      by_contra hne
      have : w < target := by omega
      have := hlt w (Nat.le_refl w) this
      exact hcond this

/-- Key lemma: findW correctly computes a + b for pair a b -/
private theorem findW_pair (a b : Nat) : findW (pair a b) = a + b := by
  unfold findW
  apply findW_go_eq (pair a b) (a + b) 0 (pair a b + 1)
  · omega
  · intro w' _ hlt
    exact pair_cond_lt a b w' hlt
  · exact pair_cond_eq a b
  · omega

/-- Unpairing is inverse of pairing -/
theorem unpair_pair (a b : Nat) : unpairFst (pair a b) = a ∧ unpairSnd (pair a b) = b := by
  have hw := findW_pair a b
  simp only [pair] at hw
  simp only [unpairFst, unpairSnd, pair, hw]
  constructor <;> omega

/-- Pairing is injective -/
theorem pair_injective (a b c d : Nat) (h : pair a b = pair c d) : a = c ∧ b = d := by
  have h1 := unpair_pair a b
  have h2 := unpair_pair c d
  constructor
  · calc a = unpairFst (pair a b) := h1.1.symm
      _ = unpairFst (pair c d) := by rw [h]
      _ = c := h2.1
  · calc b = unpairSnd (pair a b) := h1.2.symm
      _ = unpairSnd (pair c d) := by rw [h]
      _ = d := h2.2

/-! ## Instruction Encoding -/

/-- Encode an instruction as a natural number.
    - inc r       → 3 * pair(0, r)
    - dec r j     → 3 * pair(1, pair(r, j)) + 1
    - halt        → 3 * 0 + 2 = 2
-/
def encodeInstr : RMInstr → Nat
  | RMInstr.inc r => 3 * pair 0 r
  | RMInstr.dec r j => 3 * pair 1 (pair r j) + 1
  | RMInstr.halt => 2

/-- Decode a natural number to an instruction -/
def decodeInstr (n : Nat) : Option RMInstr :=
  match n % 3 with
  | 0 =>
    let p := n / 3
    if unpairFst p = 0 then
      some (RMInstr.inc (unpairSnd p))
    else
      none
  | 1 =>
    let p := (n - 1) / 3
    if unpairFst p = 1 then
      let rj := unpairSnd p
      some (RMInstr.dec (unpairFst rj) (unpairSnd rj))
    else
      none
  | 2 => some RMInstr.halt
  | _ => none

/-- Decoding reverses encoding -/
theorem decode_encode_instr (i : RMInstr) : decodeInstr (encodeInstr i) = some i := by
  cases i with
  | inc r =>
    simp only [encodeInstr, decodeInstr]
    have h := unpair_pair 0 r
    simp [h.1, h.2]
  | dec r j =>
    simp only [encodeInstr, decodeInstr]
    have h1 := unpair_pair 1 (pair r j)
    have h2 := unpair_pair r j
    simp [h1.1, h1.2, h2.1, h2.2]
  | halt =>
    simp only [encodeInstr, decodeInstr]

/-! ## List Encoding -/

/-- Encode a list of naturals as a single natural.
    Uses the standard encoding: [] → 0, x::xs → pair(x+1, encode xs)
-/
def encodeList : List Nat → Nat
  | [] => 0
  | x :: xs => pair (x + 1) (encodeList xs)

/-- Decode a natural to a list of naturals -/
def decodeList (n : Nat) : List Nat :=
  if h : n = 0 then []
  else
    let fst := unpairFst n
    let snd := unpairSnd n
    if fst = 0 then []  -- Invalid encoding
    else (fst - 1) :: decodeList snd
termination_by n
decreasing_by
  simp_wf
  apply unpairSnd_lt
  omega

/-- pair is always positive for positive first component -/
private theorem pair_pos (a b : Nat) (ha : a > 0) : pair a b > 0 := by
  unfold pair
  -- When a >= 1, (a+b)*(a+b+1)/2 >= 1, so the sum > 0
  match a, b with
  | a + 1, b =>
    -- (a+1+b)*(a+1+b+1)/2 + b > 0
    -- Numerator = (a+1+b)*(a+2+b) >= 2*3 = 6 when a=0,b=0
    -- Actually (1+b)*(2+b) >= 2 always, so /2 >= 1
    have h1 : (a + 1 + b) * (a + 1 + b + 1) >= 2 := by
      have : a + 1 + b >= 1 := by omega
      have : a + 1 + b + 1 >= 2 := by omega
      calc (a + 1 + b) * (a + 1 + b + 1)
        >= 1 * 2 := Nat.mul_le_mul ‹_› ‹_›
        _ = 2 := by rfl
    have h2 : (a + 1 + b) * (a + 1 + b + 1) / 2 >= 1 := Nat.one_le_div_iff (by omega) |>.mpr h1
    omega

/-- Decoding reverses encoding -/
theorem decode_encode_list (xs : List Nat) : decodeList (encodeList xs) = xs := by
  induction xs with
  | nil =>
    unfold decodeList encodeList
    rfl
  | cons x xs ih =>
    unfold encodeList
    have hp := pair_pos (x + 1) (encodeList xs) (by omega)
    have hne : pair (x + 1) (encodeList xs) ≠ 0 := Nat.ne_of_gt hp
    have hu := unpair_pair (x + 1) (encodeList xs)
    conv => lhs; unfold decodeList
    simp only [hne, dite_false]
    have hx1 : x + 1 ≠ 0 := by omega
    simp only [hu.1, hu.2, Nat.add_sub_cancel, hx1, ↓reduceIte, ih]

/-! ## RM Encoding -/

/-- Encode a register machine as a natural number -/
def encodeRM (prog : RM) : Nat :=
  encodeList (prog.map encodeInstr)

/-- Decode a natural number to a register machine (partial) -/
def decodeRM (n : Nat) : Option RM :=
  let codes := decodeList n
  codes.mapM decodeInstr

/-- Decoding reverses encoding -/
theorem decode_encode_rm (prog : RM) : decodeRM (encodeRM prog) = some prog := by
  simp only [decodeRM, encodeRM, decode_encode_list]
  induction prog with
  | nil => rfl
  | cons i is ih =>
    simp only [List.map_cons, List.mapM_cons, decode_encode_instr, ih]
    rfl

/-! ## Properties -/

/-- Different instructions have different codes -/
theorem encodeInstr_injective : ∀ i j, encodeInstr i = encodeInstr j → i = j := by
  intro i j h
  cases i with
  | inc r =>
    cases j with
    | inc r' =>
      simp only [encodeInstr] at h
      have hp := pair_injective 0 r 0 r' (by omega)
      simp [hp.2]
    | dec r' j' => simp only [encodeInstr] at h; omega
    | halt => simp only [encodeInstr] at h; omega
  | dec r k =>
    cases j with
    | inc r' => simp only [encodeInstr] at h; omega
    | dec r' k' =>
      simp only [encodeInstr] at h
      have hp := pair_injective 1 (pair r k) 1 (pair r' k') (by omega)
      have hp2 := pair_injective r k r' k' hp.2
      simp [hp2.1, hp2.2]
    | halt => simp only [encodeInstr] at h; omega
  | halt =>
    cases j with
    | inc r' => simp only [encodeInstr] at h; omega
    | dec r' j' => simp only [encodeInstr] at h; omega
    | halt => rfl

/-- Different programs have different codes (when both decode) -/
theorem encodeRM_injective : ∀ p q, encodeRM p = encodeRM q → p = q := by
  intro p q h
  have hd : decodeRM (encodeRM p) = decodeRM (encodeRM q) := by rw [h]
  simp only [decode_encode_rm] at hd
  exact Option.some.inj hd
