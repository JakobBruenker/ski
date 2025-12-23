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

/-- Product of consecutive naturals is even -/
private theorem two_dvd_mul_succ (n : Nat) : 2 ∣ n * (n + 1) := by
  match hn : n % 2 with
  | 0 =>
    have hdvd : 2 ∣ n := Nat.dvd_of_mod_eq_zero hn
    exact Nat.dvd_trans hdvd (Nat.dvd_mul_right n (n + 1))
  | 1 =>
    have hdvd : 2 ∣ (n + 1) := by
      have h : (n + 1) % 2 = 0 := by omega
      exact Nat.dvd_of_mod_eq_zero h
    exact Nat.dvd_trans hdvd (Nat.dvd_mul_left (n + 1) n)
  | k + 2 => omega

/-- Helper: go also satisfies upper bound when it terminates by not satisfying condition -/
private theorem findW_go_lt (n w fuel : Nat)
    (hcont : ∀ w', w ≤ w' → (w' + 1) * (w' + 2) / 2 ≤ n → w' + 1 < w + fuel) :
    n < (findW.go n w fuel + 1) * (findW.go n w fuel + 2) / 2 := by
  induction fuel generalizing w with
  | zero =>
    simp only [findW.go]
    match hcond : decide ((w + 1) * (w + 2) / 2 ≤ n) with
    | true =>
      have hle : (w + 1) * (w + 2) / 2 ≤ n := of_decide_eq_true hcond
      have := hcont w (Nat.le_refl w) hle
      omega
    | false =>
      have hgt : ¬((w + 1) * (w + 2) / 2 ≤ n) := of_decide_eq_false hcond
      omega
  | succ fuel' ih =>
    simp only [findW.go]
    split
    · apply ih
      intro w' hw' hcond'
      have := hcont w' (Nat.le_trans (Nat.le_succ w) hw') hcond'
      omega
    · omega

/-- Upper bound: next triangular number exceeds n -/
private theorem findW_lt (n : Nat) : n < (findW n + 1) * (findW n + 2) / 2 := by
  unfold findW
  apply findW_go_lt
  intro w' _ hcond
  -- From hcond: (w'+1)*(w'+2)/2 ≤ n
  -- Since (w'+1)*(w'+2) ≥ 2*(w'+1), we have (w'+1)*(w'+2)/2 ≥ w'+1
  have hprod : (w' + 1) * (w' + 2) ≥ 2 * (w' + 1) := by
    have : w' + 2 ≥ 2 := by omega
    calc (w' + 1) * (w' + 2) ≥ (w' + 1) * 2 := Nat.mul_le_mul_left _ this
      _ = 2 * (w' + 1) := Nat.mul_comm _ _
  have hdvd := two_dvd_mul_succ (w' + 1)
  have hdiv : (w' + 1) * (w' + 2) / 2 ≥ w' + 1 := by
    have ⟨k, hk⟩ := hdvd
    rw [hk, Nat.mul_div_cancel_left k (by omega : 0 < 2)]
    have h : 2 * k ≥ 2 * (w' + 1) := by rw [← hk]; exact hprod
    omega
  omega

/-- Triangular division subtraction -/
private theorem tri_div_sub (w : Nat) :
    (w + 1) * (w + 2) / 2 - w * (w + 1) / 2 = w + 1 := by
  have heven1 := two_dvd_mul_succ w
  have heven2 := two_dvd_mul_succ (w + 1)
  have ⟨k1, hk1⟩ := heven1
  have ⟨k2, hk2⟩ := heven2
  rw [hk1, hk2, Nat.mul_div_cancel_left k1 (by omega : 0 < 2),
      Nat.mul_div_cancel_left k2 (by omega : 0 < 2)]
  have hdiff : (w + 1) * (w + 2) - w * (w + 1) = 2 * (w + 1) := by
    have h1 : (w + 1) * (w + 2) = (w + 1) * w + (w + 1) * 2 := Nat.mul_add (w + 1) w 2
    have h2 : (w + 1) * w = w * (w + 1) := Nat.mul_comm (w + 1) w
    have h3 : (w + 1) * 2 = 2 * (w + 1) := Nat.mul_comm (w + 1) 2
    omega
  have h : 2 * k2 - 2 * k1 = 2 * (w + 1) := by
    rw [← hk1, ← hk2]
    exact hdiff
  omega

/-- unpairSnd is bounded by findW -/
private theorem unpairSnd_le_findW (n : Nat) : unpairSnd n ≤ findW n := by
  simp only [unpairSnd]
  have hle := findW_le n
  have hlt := findW_lt n
  -- We need: n - (findW n * (findW n + 1) / 2) ≤ findW n
  -- Use divisibility to simplify
  have heven := two_dvd_mul_succ (findW n)
  have ⟨k, hk⟩ := heven
  -- findW n * (findW n + 1) / 2 = k
  have ht_eq : findW n * (findW n + 1) / 2 = k := by
    rw [hk, Nat.mul_div_cancel_left k (by omega : 0 < 2)]
  -- (findW n + 1)*(findW n + 2)/2 = k + (findW n + 1) from tri_div_sub
  have heven2 := two_dvd_mul_succ (findW n + 1)
  have ⟨k2, hk2⟩ := heven2
  have ht2_eq : (findW n + 1) * (findW n + 2) / 2 = k2 := by
    rw [hk2, Nat.mul_div_cancel_left k2 (by omega : 0 < 2)]
  have hdiff : k2 - k = findW n + 1 := by
    have h1 : (findW n + 1) * (findW n + 2) - findW n * (findW n + 1) = 2 * (findW n + 1) := by
      have step1 : (findW n + 1) * (findW n + 2) = (findW n + 1) * (findW n) + (findW n + 1) * 2 :=
        Nat.mul_add (findW n + 1) (findW n) 2
      have step2 : (findW n + 1) * (findW n) = (findW n) * (findW n + 1) :=
        Nat.mul_comm (findW n + 1) (findW n)
      have step3 : (findW n + 1) * 2 = 2 * (findW n + 1) := Nat.mul_comm (findW n + 1) 2
      omega
    have h2 : 2 * k2 - 2 * k = 2 * (findW n + 1) := by
      rw [← hk, ← hk2]
      exact h1
    omega
  -- hle says findW n * (findW n + 1) / 2 ≤ n, i.e., k ≤ n
  have hle' : k ≤ n := by rw [← ht_eq]; exact hle
  -- hlt says n < (findW n + 1) * (findW n + 2) / 2, i.e., n < k2
  have hlt' : n < k2 := by rw [← ht2_eq]; exact hlt
  -- k2 = k + (findW n + 1)
  have hk2_eq : k2 = k + (findW n + 1) := by omega
  -- Goal: n - k ≤ findW n (after substituting ht_eq)
  rw [ht_eq]
  -- n < k + (findW n + 1), n ≥ k, so n - k < findW n + 1
  omega

/-- unpairFst n ≤ n for all n -/
theorem unpairFst_le (n : Nat) : unpairFst n ≤ n := by
  simp only [unpairFst]
  have hw := findW_le n
  have hsnd := unpairSnd_le_findW n
  simp only [unpairSnd] at hsnd
  -- unpairFst n = findW n - (n - t) where t = findW n * (findW n + 1) / 2
  -- We need to show findW n - (n - t) ≤ n
  -- First, use divisibility
  have heven := two_dvd_mul_succ (findW n)
  have ⟨k, hk⟩ := heven
  have ht_eq : findW n * (findW n + 1) / 2 = k := by
    rw [hk, Nat.mul_div_cancel_left k (by omega : 0 < 2)]
  -- hw says k ≤ n
  have hk_le : k ≤ n := by rw [← ht_eq]; exact hw
  -- hsnd says n - k ≤ findW n
  have hsnd' : n - k ≤ findW n := by rw [← ht_eq]; exact hsnd
  -- Goal: findW n - (n - k) ≤ n
  rw [ht_eq]
  -- findW n - (n - k) ≤ findW n ≤ n + k (we need to bound findW n)
  -- Actually simpler: findW n - (n - k) ≤ k + (n - k) - (n - k) = k ≤ n
  -- We have: findW n = (n - k) + (findW n - (n - k)) ≤ (n - k) + (findW n - (n - k))
  -- The key observation: unpairFst n + unpairSnd n = findW n
  -- So unpairFst n = findW n - unpairSnd n ≤ findW n
  -- And we need findW n ≤ n + (n - t) = n + (n - k)
  -- We know t = k ≤ n, so findW n - (n - k) + (n - k) = findW n
  -- We want findW n - (n - k) ≤ n
  -- Equivalently, findW n ≤ n + (n - k) = 2n - k
  -- Since k ≤ n, we have 2n - k ≥ n
  -- We need findW n ≤ n, i.e., w ≤ n where w*(w+1)/2 ≤ n
  -- For w ≥ 2, w*(w+1)/2 ≥ 3, so if n < 3 we have w ≤ 1 ≤ n (for n ≥ 1)
  -- For w ≥ n+1, w*(w+1)/2 ≥ (n+1)(n+2)/2 > n for n ≥ 0, contradiction
  -- So w ≤ n always. Thus findW n ≤ n
  have hfindW_le_n : findW n ≤ n := by
    -- Key insight: k2 = k + (findW n + 1), n < k2, k ≤ n
    -- So n < k + findW n + 1 ≤ n + findW n + 1
    -- This gives n - k < findW n + 1, i.e., n - k ≤ findW n
    -- Combined with hsnd': n - k ≤ findW n, this confirms the bound
    -- Now: findW n ≤ n iff n - k ≤ n - 0 when k = findW n * (findW n + 1) / 2
    -- Actually simpler: from hlt and hk_le, we can derive findW n ≤ n directly
    -- hlt: n < (findW n + 1) * (findW n + 2) / 2
    -- hk_le: k ≤ n, where 2k = findW n * (findW n + 1)
    -- If findW n > n, then findW n ≥ n + 1
    -- So 2k = findW n * (findW n + 1) ≥ (n+1) * (n+2) > 2n
    -- Thus k > n, contradicting k ≤ n
    have hlt := findW_lt n
    have heven2 := two_dvd_mul_succ (findW n + 1)
    have ⟨k2, hk2⟩ := heven2
    have ht2_eq : (findW n + 1) * (findW n + 2) / 2 = k2 := by
      rw [hk2, Nat.mul_div_cancel_left k2 (by omega : 0 < 2)]
    have hlt' : n < k2 := by rw [← ht2_eq]; exact hlt
    -- From 2k2 = (findW n + 1) * (findW n + 2) and 2k = findW n * (findW n + 1)
    -- 2k2 - 2k = 2 * (findW n + 1), so k2 - k = findW n + 1
    -- k2 = k + findW n + 1
    -- Since n < k2 and k ≤ n: n < k + findW n + 1
    -- So findW n + 1 > n - k ≥ 0 (since k ≤ n)
    -- Actually just use: if findW n > n then k > n (contradiction)
    -- Suppose findW n ≥ n + 1. Then:
    -- 2k = findW n * (findW n + 1) ≥ (n + 1) * (n + 2)
    -- (n + 1) * (n + 2) ≥ (n + 1) * 2 = 2 * (n + 1) > 2n
    -- So 2k > 2n, meaning k > n, contradicting k ≤ n
    if h : findW n ≤ n then exact h
    else
      have hge : findW n ≥ n + 1 := Nat.not_le.mp h
      have hprod : findW n * (findW n + 1) ≥ (n + 1) * (n + 2) := by
        apply Nat.mul_le_mul <;> omega
      have hprod_gt : (n + 1) * (n + 2) > 2 * n := by
        have h1 : n + 2 ≥ 2 := by omega
        have h2 : (n + 1) * (n + 2) ≥ (n + 1) * 2 := Nat.mul_le_mul_left _ h1
        have h3 : (n + 1) * 2 = 2 * (n + 1) := Nat.mul_comm _ _
        have h4 : 2 * (n + 1) > 2 * n := by omega
        omega
      have h2k_gt : 2 * k > 2 * n := by
        rw [← hk]
        have h : findW n * (findW n + 1) ≥ (n + 1) * (n + 2) := hprod
        omega
      have : k > n := by omega
      omega
  -- Now use hfindW_le_n
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
  -- LHS = (a+b)*(a+b+1)/2 + (a+b+1)
  -- RHS = (a+b)*(a+b+1)/2 + b
  -- Need (a+b+1) > b, i.e., a+1 > 0, always true
  have heven := two_dvd_mul_succ (a + b)
  have heven2 := two_dvd_mul_succ (a + b + 1)
  have ⟨k, hk⟩ := heven
  have ⟨k2, hk2⟩ := heven2
  -- (a+b)*(a+b+1)/2 = k
  have heq1 : (a + b) * (a + b + 1) / 2 = k := by
    rw [hk, Nat.mul_div_cancel_left k (by omega : 0 < 2)]
  -- (a+b+1)*(a+b+2)/2 = k2
  have heq2 : (a + b + 1) * (a + b + 2) / 2 = k2 := by
    rw [hk2, Nat.mul_div_cancel_left k2 (by omega : 0 < 2)]
  -- k2 = k + (a+b+1), so k2 > k + b
  have hdiff : (a + b + 1) * (a + b + 2) - (a + b) * (a + b + 1) = 2 * (a + b + 1) := by
    have h1 : (a + b + 1) * (a + b + 2) = (a + b + 1) * (a + b) + (a + b + 1) * 2 :=
      Nat.mul_add (a + b + 1) (a + b) 2
    have h2 : (a + b + 1) * (a + b) = (a + b) * (a + b + 1) :=
      Nat.mul_comm (a + b + 1) (a + b)
    have h3 : (a + b + 1) * 2 = 2 * (a + b + 1) := Nat.mul_comm (a + b + 1) 2
    omega
  have hk2_eq : 2 * k2 - 2 * k = 2 * (a + b + 1) := by
    rw [← hk, ← hk2]
    exact hdiff
  have hk2_val : k2 = k + (a + b + 1) := by omega
  rw [heq1, heq2]
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
    split
    case isTrue hcond =>
      have hw' : w < target := by
        -- If w ≥ target, then w = target (since hw : w ≤ target)
        -- Then hcond contradicts heq
        if h : w < target then exact h
        else
          have hge : w ≥ target := Nat.not_lt.mp h
          have heq' : w = target := by omega
          subst heq'
          exact absurd hcond heq
      apply ih
      · omega
      · intro w'' hlo hhi
        exact hlt w'' (by omega) hhi
      · omega
    case isFalse hcond =>
      -- Need to show w = target
      -- If w < target, then hlt gives (w+1)*(w+2)/2 ≤ n, contradicting hcond
      if h : w = target then exact h
      else
        have hne : w ≠ target := h
        have hwlt : w < target := by omega
        have hcond' := hlt w (Nat.le_refl w) hwlt
        exact absurd hcond' hcond

/-- pair a b ≥ b -/
private theorem pair_ge_snd (a b : Nat) : pair a b ≥ b := by
  simp only [pair]
  omega

/-- pair a b ≥ a + b -/
private theorem pair_ge_sum (a b : Nat) : pair a b ≥ a + b := by
  simp only [pair]
  -- (a+b)*(a+b+1)/2 + b ≥ a + b
  -- (a+b)*(a+b+1)/2 ≥ a
  -- (a+b)*(a+b+1) ≥ 2a when a+b ≥ 1
  -- For a = 0: 0 ≥ 0 ✓
  -- For a ≥ 1, a + b ≥ 1: (a+b)*(a+b+1) ≥ 1*2 = 2 ≥ 2*1 = 2a only when a ≤ 1
  -- Actually need: (a+b)*(a+b+1)/2 ≥ a
  -- When a = 0: 0 ≥ 0 ✓
  -- When a ≥ 1: (a+b)*(a+b+1) ≥ a*(a+1) ≥ a*2 = 2a, so /2 ≥ a
  have hdvd := two_dvd_mul_succ (a + b)
  have ⟨k, hk⟩ := hdvd
  rw [hk, Nat.mul_div_cancel_left k (by omega : 0 < 2)]
  -- Need: k + b ≥ a + b, i.e., k ≥ a
  -- 2k = (a+b)*(a+b+1), and we need k ≥ a
  -- (a+b)*(a+b+1) ≥ 2a when (a+b) ≥ 1 or a = 0
  -- For a = 0: 2k = b*(b+1) ≥ 0 = 2*0 ✓
  -- For a ≥ 1: (a+b)*(a+b+1) ≥ a*(a+1) ≥ 2a, so k ≥ a
  have hprod : (a + b) * (a + b + 1) ≥ 2 * a := by
    match a with
    | 0 => simp
    | a' + 1 =>
      have h1 : a' + 1 + b ≥ a' + 1 := by omega
      have h2 : a' + 1 + b + 1 ≥ 2 := by omega
      calc (a' + 1 + b) * (a' + 1 + b + 1)
        ≥ (a' + 1) * 2 := Nat.mul_le_mul h1 h2
        _ = 2 * (a' + 1) := Nat.mul_comm _ _
  have : 2 * k ≥ 2 * a := by rw [← hk]; exact hprod
  omega

/-- Key lemma: findW correctly computes a + b for pair a b -/
private theorem findW_pair (a b : Nat) : findW (pair a b) = a + b := by
  unfold findW
  have hge := pair_ge_sum a b
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
