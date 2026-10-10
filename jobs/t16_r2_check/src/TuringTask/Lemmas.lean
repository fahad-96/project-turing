import Mathlib

/-!
# Auxiliary development for the five Fibonacci/Lucas Diophantine theorems

This file develops:
* the Lucas numbers `luc` and their relation to `Nat.fib`;
* Cassini's identity and the basic quadratic identities;
* the "ladder" (anti-periodicity) congruences
  `fib (m + 2 * k * s) ≡ (-1)^s * fib m  (mod luc k)` for even `k`;
* arithmetic facts about `luc (2 ^ j)` modulo `24`;
* Jacobi symbol computations used to obtain contradictions.
-/

namespace TuringTask

/-! ## Lucas numbers -/

/-- The Lucas numbers. -/
def luc : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | (n + 2) => luc n + luc (n + 1)

@[simp] theorem luc_zero : luc 0 = 2 := rfl
@[simp] theorem luc_one : luc 1 = 1 := rfl
theorem luc_add_two (n : ℕ) : luc (n + 2) = luc n + luc (n + 1) := rfl

/-- `L_{n+1} = F_n + F_{n+2}`, matching the statement form `Nat.fib (n-1) + Nat.fib (n+1)`. -/
theorem luc_succ_eq (n : ℕ) : luc (n + 1) = Nat.fib n + Nat.fib (n + 2) := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih1 ih2 =>
      have h : luc (n + 3) = luc (n + 1) + luc (n + 2) := luc_add_two (n + 1)
      have e1 : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := Nat.fib_add_two
      have e2 : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
      have e3 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
      have ih1' : luc (n + 1) = Nat.fib n + Nat.fib (n + 2) := ih1
      have ih2' : luc (n + 2) = Nat.fib (n + 1) + Nat.fib (n + 3) := ih2
      show luc (n + 3) = Nat.fib (n + 2) + Nat.fib (n + 4)
      omega

theorem luc_pos (n : ℕ) : 0 < luc n := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n ih1 ih2 => rw [luc_add_two]; omega

/-- The basic cast identity `L n = 2 * F (n+1) - F n` over `ℤ`. -/
theorem luc_cast (n : ℕ) : (luc n : ℤ) = 2 * Nat.fib (n + 1) - Nat.fib n := by
  cases n with
  | zero => simp
  | succ m =>
      rw [luc_succ_eq]
      have e : Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
      push_cast [e]
      ring

/-! ## Cassini's identity -/

theorem cassini (n : ℕ) :
    (Nat.fib (n + 1) : ℤ) ^ 2 - (Nat.fib (n + 1) : ℤ) * (Nat.fib n : ℤ)
      - (Nat.fib n : ℤ) ^ 2 = (-1) ^ n := by
  induction n with
  | zero => simp
  | succ m ih =>
      have e : Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
      have e' : ((Nat.fib (m + 1 + 1) : ℕ) : ℤ) = (Nat.fib m : ℤ) + (Nat.fib (m + 1) : ℤ) := by
        rw [show m + 1 + 1 = m + 2 from rfl, e]; push_cast; ring
      rw [e']
      linear_combination -ih

/-- `L n ^ 2 = 5 * F n ^ 2 + 4 * (-1)^n`. -/
theorem luc_sq (n : ℕ) : (luc n : ℤ) ^ 2 = 5 * (Nat.fib n : ℤ) ^ 2 + 4 * (-1) ^ n := by
  rw [luc_cast]
  linear_combination 4 * cassini n

/-! ## Doubling identities -/

theorem fib_two_mul' (n : ℕ) : (Nat.fib (2 * n) : ℤ) = (Nat.fib n : ℤ) * (luc n : ℤ) := by
  have h : Nat.fib n ≤ 2 * Nat.fib (n + 1) := le_trans Nat.fib_le_fib_succ (by omega)
  rw [Nat.fib_two_mul, luc_cast]
  push_cast [Nat.cast_sub h]
  ring

theorem fib_two_mul_add_one' (k : ℕ) (hk : Even k) :
    (Nat.fib (2 * k + 1) : ℤ) + 1 = (luc k : ℤ) * (Nat.fib (k + 1) : ℤ) := by
  have hc := cassini k
  rw [hk.neg_one_pow] at hc
  rw [Nat.fib_two_mul_add_one, luc_cast]
  push_cast
  linear_combination -hc

/-- Doubling for Lucas numbers: `L (2n) = L n ^ 2 - 2 * (-1)^n`. -/
theorem luc_two_mul (n : ℕ) : (luc (2 * n) : ℤ) = (luc n : ℤ) ^ 2 - 2 * (-1) ^ n := by
  rcases Nat.even_or_odd n with hn | hn
  · -- `2*n + 1 = 2*n+1`, use the two identities above
    have h1 : (Nat.fib (2 * n + 1) : ℤ) + 1 = (luc n : ℤ) * (Nat.fib (n + 1) : ℤ) :=
      fib_two_mul_add_one' n hn
    have h2 : (Nat.fib (2 * n) : ℤ) = (Nat.fib n : ℤ) * (luc n : ℤ) := fib_two_mul' n
    have h3 : (luc (2 * n) : ℤ) = 2 * (Nat.fib (2 * n + 1) : ℤ) - (Nat.fib (2 * n) : ℤ) := by
      have := luc_cast (2 * n); simpa using this
    have h4 : (luc n : ℤ) = 2 * (Nat.fib (n + 1) : ℤ) - (Nat.fib n : ℤ) := luc_cast n
    rw [hn.neg_one_pow, h3, h2]
    linear_combination 2 * h1 - (luc n : ℤ) * h4
  · -- odd case
    have hc := cassini n
    rw [hn.neg_one_pow] at hc
    have h2 : (Nat.fib (2 * n) : ℤ) = (Nat.fib n : ℤ) * (luc n : ℤ) := fib_two_mul' n
    have h3 : (luc (2 * n) : ℤ) = 2 * (Nat.fib (2 * n + 1) : ℤ) - (Nat.fib (2 * n) : ℤ) := by
      have := luc_cast (2 * n); simpa using this
    have h5 : (Nat.fib (2 * n + 1) : ℤ) = (Nat.fib (n + 1) : ℤ) ^ 2 + (Nat.fib n : ℤ) ^ 2 := by
      rw [Nat.fib_two_mul_add_one]; push_cast; ring
    have h4 : (luc n : ℤ) = 2 * (Nat.fib (n + 1) : ℤ) - (Nat.fib n : ℤ) := luc_cast n
    rw [hn.neg_one_pow, h3, h5, h2, h4]
    linear_combination (-2 : ℤ) * hc

/-! ## Addition formulas -/

/-- `F (m + 2k) + (-1)^k * F m = F (m + k) * L k`. -/
theorem fib_add_two_mul (m k : ℕ) :
    (Nat.fib (m + 2 * k) : ℤ) + (-1) ^ k * (Nat.fib m : ℤ)
      = (Nat.fib (m + k) : ℤ) * (luc k : ℤ) := by
  cases k with
  | zero =>
    simp only [Nat.mul_zero, Nat.add_zero, pow_zero, one_mul, luc_zero]
    push_cast
    ring
  | succ p =>
    have hA : Nat.fib (m + p + 1 + p + 1) =
        Nat.fib (m + p + 1) * Nat.fib p + Nat.fib (m + p + 2) * Nat.fib (p + 1) :=
      Nat.fib_add (m + p + 1) p
    have hB : Nat.fib (m + p + 1) = Nat.fib m * Nat.fib p + Nat.fib (m + 1) * Nat.fib (p + 1) :=
      Nat.fib_add m p
    have hC : Nat.fib (m + p + 2) =
        Nat.fib (m + 1) * Nat.fib p + Nat.fib (m + 2) * Nat.fib (p + 1) := by
      have := Nat.fib_add (m + 1) p
      rw [show m + 1 + p + 1 = m + p + 2 by omega] at this
      exact this
    have hD : Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
    have hL : (luc (p + 1) : ℤ) = 2 * (Nat.fib p : ℤ) + (Nat.fib (p + 1) : ℤ) := by
      rw [luc_succ_eq]
      have : Nat.fib (p + 2) = Nat.fib p + Nat.fib (p + 1) := Nat.fib_add_two
      push_cast [this]; ring
    have hc := cassini p
    rw [show m + 2 * (p + 1) = m + p + 1 + p + 1 by omega,
        show m + (p + 1) = m + p + 1 by omega, hA, hL]
    push_cast [hB, hC, hD]
    linear_combination ((Nat.fib m : ℤ)) * hc

/-- `L (m + 2k) + (-1)^k * L m = L (m + k) * L k`. -/
theorem luc_add_two_mul (m k : ℕ) :
    (luc (m + 2 * k) : ℤ) + (-1) ^ k * (luc m : ℤ)
      = (luc (m + k) : ℤ) * (luc k : ℤ) := by
  have h1 := fib_add_two_mul m k
  have h2 := fib_add_two_mul (m + 1) k
  rw [show m + 1 + 2 * k = m + 2 * k + 1 by omega, show m + 1 + k = m + k + 1 by omega] at h2
  rw [luc_cast (m + 2 * k), luc_cast m, luc_cast (m + k)]
  linear_combination 2 * h2 - h1

/-! ## Ladder congruences

For `k` even, `F (m + 2 k s) ≡ (-1)^s * F m [ZMOD luc k]`, and similarly for `luc`.
-/

theorem fib_ladder (k : ℕ) (hk : Even k) (m s : ℕ) :
    (Nat.fib (m + 2 * k * s) : ℤ) ≡ (-1) ^ s * (Nat.fib m : ℤ) [ZMOD (luc k : ℤ)] := by
  induction s with
  | zero => simp [Int.ModEq.refl]
  | succ t ih =>
    have key : (Nat.fib (m + 2 * k * t + 2 * k) : ℤ) + (Nat.fib (m + 2 * k * t) : ℤ)
        = (Nat.fib (m + 2 * k * t + k) : ℤ) * (luc k : ℤ) := by
      have := fib_add_two_mul (m + 2 * k * t) k
      rwa [hk.neg_one_pow, one_mul] at this
    have h1 : (Nat.fib (m + 2 * k * (t + 1)) : ℤ) ≡ -(Nat.fib (m + 2 * k * t) : ℤ)
        [ZMOD (luc k : ℤ)] := by
      have hd : (luc k : ℤ) ∣ (Nat.fib (m + 2 * k * (t+1)) : ℤ) - (-(Nat.fib (m + 2*k*t) : ℤ)) := by
        refine ⟨(Nat.fib (m + 2 * k * t + k) : ℤ), ?_⟩
        rw [show m + 2 * k * (t + 1) = m + 2 * k * t + 2 * k by ring]
        linarith [key]
      exact Int.ModEq.symm (Int.modEq_iff_dvd.mpr (by simpa using hd))
    calc (Nat.fib (m + 2 * k * (t + 1)) : ℤ)
        ≡ -(Nat.fib (m + 2 * k * t) : ℤ) [ZMOD (luc k : ℤ)] := h1
      _ ≡ -((-1) ^ t * (Nat.fib m : ℤ)) [ZMOD (luc k : ℤ)] := ih.neg
      _ = (-1) ^ (t + 1) * (Nat.fib m : ℤ) := by ring

theorem luc_ladder (k : ℕ) (hk : Even k) (m s : ℕ) :
    (luc (m + 2 * k * s) : ℤ) ≡ (-1) ^ s * (luc m : ℤ) [ZMOD (luc k : ℤ)] := by
  induction s with
  | zero => simp [Int.ModEq.refl]
  | succ t ih =>
    have key : (luc (m + 2 * k * t + 2 * k) : ℤ) + (luc (m + 2 * k * t) : ℤ)
        = (luc (m + 2 * k * t + k) : ℤ) * (luc k : ℤ) := by
      have := luc_add_two_mul (m + 2 * k * t) k
      rwa [hk.neg_one_pow, one_mul] at this
    have h1 : (luc (m + 2 * k * (t + 1)) : ℤ) ≡ -(luc (m + 2 * k * t) : ℤ)
        [ZMOD (luc k : ℤ)] := by
      have hd : (luc k : ℤ) ∣ (luc (m + 2 * k * (t+1)) : ℤ) - (-(luc (m + 2*k*t) : ℤ)) := by
        refine ⟨(luc (m + 2 * k * t + k) : ℤ), ?_⟩
        rw [show m + 2 * k * (t + 1) = m + 2 * k * t + 2 * k by ring]
        linarith [key]
      exact Int.ModEq.symm (Int.modEq_iff_dvd.mpr (by simpa using hd))
    calc (luc (m + 2 * k * (t + 1)) : ℤ)
        ≡ -(luc (m + 2 * k * t) : ℤ) [ZMOD (luc k : ℤ)] := h1
      _ ≡ -((-1) ^ t * (luc m : ℤ)) [ZMOD (luc k : ℤ)] := ih.neg
      _ = (-1) ^ (t + 1) * (luc m : ℤ) := by ring

/-! ## Arithmetic of `luc (2 ^ j)` -/

/-- For `j ≥ 1`, `luc (2^j) ≡ 3 [MOD 4]`; for `j ≥ 2` in fact `luc (2^j) ≡ 7 [MOD 8]`.
We record the value mod 24, which is `7` for `j = 2` and `23` for `j ≥ 3`. -/
theorem luc_two_pow_mod_four (j : ℕ) (hj : 1 ≤ j) : luc (2 ^ j) % 4 = 3 := by
  induction j with
  | zero => omega
  | succ p ih =>
    rcases Nat.eq_or_lt_of_le hj with h | h
    · -- p + 1 = 1, i.e. p = 0
      have : p = 0 := by omega
      subst this; decide
    · have hp : 1 ≤ p := by omega
      have ihp := ih hp
      -- luc (2^(p+1)) = luc (2^p)^2 - 2 * (-1)^(2^p) = luc(2^p)^2 - 2 (since 2^p even)
      have hev : Even (2 ^ p) := by
        refine (Nat.even_pow' (by omega)).mpr even_two
      have hd : (luc (2 ^ (p + 1)) : ℤ) = (luc (2 ^ p) : ℤ) ^ 2 - 2 := by
        have := luc_two_mul (2 ^ p)
        rw [hev.neg_one_pow] at this
        rw [show 2 ^ (p + 1) = 2 * 2 ^ p by ring]
        linarith [this]
      -- now reduce mod 4
      have h2 : luc (2 ^ p) ^ 2 % 4 = 1 := by
        rw [Nat.pow_mod, ihp]
      have hge : 2 ≤ luc (2 ^ p) ^ 2 := by
        have h3 : 3 ≤ luc (2 ^ p) := by omega
        calc 2 ≤ 3 * 3 := by norm_num
        _ ≤ luc (2 ^ p) * luc (2 ^ p) := Nat.mul_le_mul h3 h3
        _ = luc (2 ^ p) ^ 2 := by ring
      have hnat : luc (2 ^ (p + 1)) = luc (2 ^ p) ^ 2 - 2 := by
        have := hd
        zify [hge]
        linarith [this]
      omega

/-- For `j ≥ 2`, `luc (2^j) % 8 = 7`. -/
theorem luc_two_pow_mod_eight (j : ℕ) (hj : 2 ≤ j) : luc (2 ^ j) % 8 = 7 := by
  obtain ⟨p, rfl⟩ : ∃ p, j = p + 1 := ⟨j - 1, by omega⟩
  have hp : 1 ≤ p := by omega
  have ihp : luc (2 ^ p) % 4 = 3 := luc_two_pow_mod_four p hp
  have hev : Even (2 ^ p) := (Nat.even_pow' (by omega)).mpr even_two
  have hd : (luc (2 ^ (p + 1)) : ℤ) = (luc (2 ^ p) : ℤ) ^ 2 - 2 := by
    have := luc_two_mul (2 ^ p)
    rw [hev.neg_one_pow] at this
    rw [show 2 ^ (p + 1) = 2 * 2 ^ p by ring]
    linarith [this]
  have h2 : luc (2 ^ p) ^ 2 % 8 = 1 := by
    have h4 : luc (2 ^ p) % 4 = 3 := ihp
    have : luc (2 ^ p) % 8 = 3 ∨ luc (2 ^ p) % 8 = 7 := by omega
    rcases this with h | h <;> · rw [Nat.pow_mod, h]
  have hge : 2 ≤ luc (2 ^ p) ^ 2 := by
    have h3 : 3 ≤ luc (2 ^ p) := by omega
    calc 2 ≤ 3 * 3 := by norm_num
    _ ≤ luc (2 ^ p) * luc (2 ^ p) := Nat.mul_le_mul h3 h3
    _ = luc (2 ^ p) ^ 2 := by ring
  have hnat : luc (2 ^ (p + 1)) = luc (2 ^ p) ^ 2 - 2 := by
    zify [hge]; linarith [hd]
  omega

/-- For `j ≥ 2`, `3` does not divide `luc (2^j)`. -/
theorem luc_two_pow_mod_three (j : ℕ) (hj : 2 ≤ j) :
    luc (2 ^ j) % 3 = 1 ∨ luc (2 ^ j) % 3 = 2 := by
  induction j with
  | zero => omega
  | succ p ih =>
    rcases Nat.lt_or_ge p 2 with hp | hp
    · interval_cases p
      · omega
      · decide
    · have ihp := ih hp
      have hev : Even (2 ^ p) := (Nat.even_pow' (by omega)).mpr even_two
      have hd : (luc (2 ^ (p + 1)) : ℤ) = (luc (2 ^ p) : ℤ) ^ 2 - 2 := by
        have := luc_two_mul (2 ^ p)
        rw [hev.neg_one_pow] at this
        rw [show 2 ^ (p + 1) = 2 * 2 ^ p by ring]
        linarith [this]
      have h2 : luc (2 ^ p) ^ 2 % 3 = 1 := by
        rcases ihp with h | h <;> · rw [Nat.pow_mod, h]
      have hge : 2 ≤ luc (2 ^ p) ^ 2 := by
        have h3 : luc (2 ^ p) % 4 = 3 := luc_two_pow_mod_four p (by omega)
        have h4 : 2 ≤ luc (2 ^ p) := by omega
        calc 2 ≤ 2 * 2 := by norm_num
        _ ≤ luc (2 ^ p) * luc (2 ^ p) := Nat.mul_le_mul h4 h4
        _ = luc (2 ^ p) ^ 2 := by ring
      have hnat : luc (2 ^ (p + 1)) = luc (2 ^ p) ^ 2 - 2 := by
        zify [hge]; linarith [hd]
      omega

/-! ## The Jacobi symbol contradiction engine -/

theorem jacobi_neg_one_of_mod_four {N : ℕ} (h : N % 4 = 3) : jacobiSym (-1) N = -1 := by
  rw [jacobiSym.at_neg_one (Nat.odd_iff.mpr (by omega)), ZMod.χ₄_nat_eq_if_mod_four]
  simp only [h]
  norm_num
  omega

theorem jacobi_two_of_mod_eight {N : ℕ} (h : N % 8 = 7) : jacobiSym 2 N = 1 := by
  rw [jacobiSym.at_two (Nat.odd_iff.mpr (by omega)), ZMod.χ₈_nat_eq_if_mod_eight]
  simp only [h]
  norm_num
  omega

/-- If `a ≡ x^2 [ZMOD N]` with `x` coprime to `N`, then `J(a | N) = 1`. -/
theorem jacobi_eq_one_of_sq {N : ℕ} {a x : ℤ} (h : a ≡ x ^ 2 [ZMOD (N : ℤ)])
    (hx : Int.gcd x N = 1) : jacobiSym a N = 1 := by
  rw [jacobiSym.mod_left' h, jacobiSym.sq_one' hx]

/-! ## Reflection: `F (2k - i) ≡ (-1)^i F i  [ZMOD luc k]` for `k` even -/

theorem fib_two_mul_dvd (k : ℕ) : (luc k : ℤ) ∣ (Nat.fib (2 * k) : ℤ) :=
  ⟨(Nat.fib k : ℤ), by rw [fib_two_mul']; ring⟩

theorem fib_two_mul_add_one_mod (k : ℕ) (hk : Even k) :
    (Nat.fib (2 * k + 1) : ℤ) ≡ -1 [ZMOD (luc k : ℤ)] := by
  have h := fib_two_mul_add_one' k hk
  refine Int.ModEq.symm (Int.modEq_iff_dvd.mpr ⟨(Nat.fib (k + 1) : ℤ), ?_⟩)
  linarith [h]

/-- The reflection formula, in paired form. -/
theorem fib_reflect (k : ℕ) (hk : Even k) (hk0 : 0 < k) :
    ∀ i b : ℕ, b + i + 1 = 2 * k →
      ((Nat.fib (b + 1) : ℤ) ≡ (-1) ^ i * (Nat.fib i : ℤ) [ZMOD (luc k : ℤ)]) ∧
      ((Nat.fib b : ℤ) ≡ (-1) ^ (i + 1) * (Nat.fib (i + 1) : ℤ) [ZMOD (luc k : ℤ)]) := by
  intro i
  induction i with
  | zero =>
    intro b hb
    have hb' : b = 2 * k - 1 := by omega
    have hb1 : b + 1 = 2 * k := by omega
    constructor
    · rw [hb1]
      simpa using (Int.modEq_zero_iff_dvd.mpr (fib_two_mul_dvd k))
    · -- fib b ≡ -1
      have h1 : (Nat.fib (2 * k) : ℤ) ≡ 0 [ZMOD (luc k : ℤ)] :=
        Int.modEq_zero_iff_dvd.mpr (fib_two_mul_dvd k)
      have h2 : (Nat.fib (2 * k + 1) : ℤ) ≡ -1 [ZMOD (luc k : ℤ)] :=
        fib_two_mul_add_one_mod k hk
      have h3 : Nat.fib (b + 2) = Nat.fib b + Nat.fib (b + 1) := Nat.fib_add_two
      have h3' : (Nat.fib (2 * k + 1) : ℤ) = (Nat.fib b : ℤ) + (Nat.fib (2 * k) : ℤ) := by
        rw [← hb1, show b + 1 + 1 = b + 2 by ring, h3]; push_cast; ring
      have : (Nat.fib b : ℤ) ≡ -1 - 0 [ZMOD (luc k : ℤ)] := by
        calc (Nat.fib b : ℤ) = (Nat.fib (2 * k + 1) : ℤ) - (Nat.fib (2 * k) : ℤ) := by
              rw [h3']; ring
        _ ≡ -1 - 0 [ZMOD (luc k : ℤ)] := h2.sub h1
      simpa using this
  | succ p ih =>
    intro b hb
    have hb' : (b + 1) + p + 1 = 2 * k := by omega
    obtain ⟨ih1, ih2⟩ := ih (b + 1) hb'
    refine ⟨ih2, ?_⟩
    -- fib b = fib (b+2) - fib (b+1)
    have h3 : Nat.fib (b + 2) = Nat.fib b + Nat.fib (b + 1) := Nat.fib_add_two
    have hfb : (Nat.fib b : ℤ) = (Nat.fib (b + 1 + 1) : ℤ) - (Nat.fib (b + 1) : ℤ) := by
      rw [show b + 1 + 1 = b + 2 by ring, h3]; push_cast; ring
    have hpp : Nat.fib (p + 2) = Nat.fib p + Nat.fib (p + 1) := Nat.fib_add_two
    have : (Nat.fib b : ℤ)
        ≡ (-1) ^ p * (Nat.fib p : ℤ) - (-1) ^ (p + 1) * (Nat.fib (p + 1) : ℤ)
        [ZMOD (luc k : ℤ)] := by rw [hfb]; exact ih1.sub ih2
    have heq : (-1 : ℤ) ^ p * (Nat.fib p : ℤ) - (-1) ^ (p + 1) * (Nat.fib (p + 1) : ℤ)
        = (-1) ^ (p + 1 + 1) * (Nat.fib (p + 1 + 1) : ℤ) := by
      rw [show p + 1 + 1 = p + 2 by ring]
      push_cast [hpp]
      ring
    rwa [heq] at this

/-- Clean form of reflection: for even `k > 0` and `i < 2*k`,
`F (2k - i) ≡ (-1)^i * F i [ZMOD luc k]`. -/
theorem fib_reflect' (k : ℕ) (hk : Even k) (hk0 : 0 < k) (i : ℕ) (hi : i < 2 * k) :
    (Nat.fib (2 * k - i) : ℤ) ≡ (-1) ^ i * (Nat.fib i : ℤ) [ZMOD (luc k : ℤ)] := by
  have hb : (2 * k - i - 1) + i + 1 = 2 * k := by omega
  have h1 := (fib_reflect k hk hk0 i (2 * k - i - 1) hb).1
  rwa [show 2 * k - i - 1 + 1 = 2 * k - i by omega] at h1

/-- Lucas reflection: for even `k > 0` and `i < 2*k`,
`L (2k - i) ≡ (-1)^(i+1) * L i [ZMOD luc k]`. -/
theorem luc_reflect' (k : ℕ) (hk : Even k) (hk0 : 0 < k) (i : ℕ) (hi : i + 1 < 2 * k) :
    (luc (2 * k - i) : ℤ) ≡ (-1) ^ (i + 1) * (luc i : ℤ) [ZMOD (luc k : ℤ)] := by
  -- L m = F (m-1) + F (m+1); use `luc_cast` : L m = 2 F (m+1) - F m
  have h1 : (Nat.fib (2 * k - i) : ℤ) ≡ (-1) ^ i * (Nat.fib i : ℤ) [ZMOD (luc k : ℤ)] :=
    fib_reflect' k hk hk0 i (by omega)
  have h2 : (Nat.fib (2 * k - (i + 1)) : ℤ) ≡ (-1) ^ (i + 1) * (Nat.fib (i + 1) : ℤ)
      [ZMOD (luc k : ℤ)] := fib_reflect' k hk hk0 (i + 1) (by omega)
  -- L (2k - i) = F (2k-i-1) + F (2k-i+1) = 2 F(2k-i+1) - F(2k-i) -- use the other direction:
  -- Instead: L m = F (m+1) + F (m-1).  With m = 2k - i,  m - 1 = 2k - (i+1), m + 1 = 2k - (i-1).
  -- Simpler: L m = 2 F (m - 1) + F m  for m ≥ 1.
  have hm : 1 ≤ 2 * k - i := by omega
  obtain ⟨m, hm'⟩ : ∃ m, 2 * k - i = m + 1 := ⟨2 * k - i - 1, by omega⟩
  have hmm : m = 2 * k - (i + 1) := by omega
  have hL : (luc (2 * k - i) : ℤ) = (Nat.fib m : ℤ) + (Nat.fib (m + 2) : ℤ) := by
    rw [hm', luc_succ_eq]; push_cast; ring
  have hfib2 : Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
  have hL' : (luc (2 * k - i) : ℤ) = 2 * (Nat.fib m : ℤ) + (Nat.fib (m + 1) : ℤ) := by
    rw [hL]; push_cast [hfib2]; ring
  have hfm1 : m + 1 = 2 * k - i := hm'.symm
  rw [hL']
  have key : (2 : ℤ) * (Nat.fib m : ℤ) + (Nat.fib (m + 1) : ℤ)
      ≡ 2 * ((-1) ^ (i + 1) * (Nat.fib (i + 1) : ℤ)) + (-1) ^ i * (Nat.fib i : ℤ)
      [ZMOD (luc k : ℤ)] := by
    refine Int.ModEq.add (Int.ModEq.mul_left 2 ?_) ?_
    · rw [hmm]; exact h2
    · rw [hfm1]; exact h1
  refine key.trans (Int.ModEq.symm (Int.modEq_iff_dvd.mpr ⟨0, ?_⟩))
  have hlucI : (luc i : ℤ) = 2 * (Nat.fib (i + 1) : ℤ) - (Nat.fib i : ℤ) := luc_cast i
  rw [hlucI]
  ring

/-! ## The two master tools

Write `n = c + 2^(j+1) * t` with `t` odd, `k = 2^j`, `N = luc k`.
Then `n = c + 2 * k * t` with `t` odd, so by the ladder
`F n ≡ (-1)^t F c = - F c  [ZMOD N]`.  Similarly for `luc`.
-/

theorem fib_toolA {n c j t : ℕ} (ht : Odd t) (hn : n = c + 2 * 2 ^ j * t) :
    (Nat.fib n : ℤ) ≡ -(Nat.fib c : ℤ) [ZMOD (luc (2 ^ j) : ℤ)] := by
  have hk : Even (2 ^ j) ∨ 2 ^ j = 1 := by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · right; norm_num
    · left; exact (Nat.even_pow' (by omega)).mpr even_two
  subst hn
  rcases hk with hk | hk
  · have := fib_ladder (2 ^ j) hk c t
    rwa [ht.neg_one_pow, neg_one_mul] at this
  · rw [hk]
    have : Even (1 : ℕ) ∨ True := Or.inr trivial
    -- `j = 0`: luc 1 = 1, everything is ≡ mod 1
    have h1 : (luc 1 : ℤ) = 1 := by norm_num
    rw [h1]
    exact Int.modEq_one

theorem luc_toolA {n c j t : ℕ} (ht : Odd t) (hn : n = c + 2 * 2 ^ j * t) :
    (luc n : ℤ) ≡ -(luc c : ℤ) [ZMOD (luc (2 ^ j) : ℤ)] := by
  have hk : Even (2 ^ j) ∨ 2 ^ j = 1 := by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · right; norm_num
    · left; exact (Nat.even_pow' (by omega)).mpr even_two
  subst hn
  rcases hk with hk | hk
  · have := luc_ladder (2 ^ j) hk c t
    rwa [ht.neg_one_pow, neg_one_mul] at this
  · rw [hk]
    have h1 : (luc 1 : ℤ) = 1 := by norm_num
    rw [h1]
    exact Int.modEq_one

/-- Tool B: if `n + c = 2 * 2^j * t` with `t` odd and `c < 2 * 2^j`, `j ≥ 1`, then
`F n ≡ (-1)^c * F c [ZMOD luc (2^j)]`. -/
theorem fib_toolB {n c j t : ℕ} (hj : 1 ≤ j) (ht : Odd t) (hc : c < 2 * 2 ^ j)
    (hn : n + c = 2 * 2 ^ j * t) :
    (Nat.fib n : ℤ) ≡ (-1) ^ c * (Nat.fib c : ℤ) [ZMOD (luc (2 ^ j) : ℤ)] := by
  set k := 2 ^ j with hkdef
  have hke : Even k := (Nat.even_pow' (by omega)).mpr even_two
  have hk0 : 0 < k := Nat.two_pow_pos j
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by rcases ht with ⟨u, hu⟩; omega⟩
  -- n = 2*k*(s+1) - c = (2*k - c) + 2*k*s
  have hmul : 2 * k * (s + 1) = 2 * k * s + 2 * k := by ring
  have hn' : n = (2 * k - c) + 2 * k * s := by omega
  have h1 : (Nat.fib n : ℤ) ≡ (-1) ^ s * (Nat.fib (2 * k - c) : ℤ) [ZMOD (luc k : ℤ)] := by
    rw [hn']; exact fib_ladder k hke _ s
  have h2 : (Nat.fib (2 * k - c) : ℤ) ≡ (-1) ^ c * (Nat.fib c : ℤ) [ZMOD (luc k : ℤ)] :=
    fib_reflect' k hke hk0 c hc
  have hs : Even s := by
    have h := Nat.odd_iff.mp ht
    exact Nat.even_iff.mpr (by omega)
  calc (Nat.fib n : ℤ)
      ≡ (-1) ^ s * (Nat.fib (2 * k - c) : ℤ) [ZMOD (luc k : ℤ)] := h1
    _ ≡ (-1) ^ s * ((-1) ^ c * (Nat.fib c : ℤ)) [ZMOD (luc k : ℤ)] := h2.mul_left _
    _ = (-1) ^ c * (Nat.fib c : ℤ) := by rw [hs.neg_one_pow, one_mul]

/-- Tool B for Lucas: if `n + c = 2 * 2^j * t` with `t` odd and `c + 1 < 2 * 2^j`, `j ≥ 1`, then
`L n ≡ (-1)^(c+1) * L c [ZMOD luc (2^j)]`. -/
theorem luc_toolB {n c j t : ℕ} (hj : 1 ≤ j) (ht : Odd t) (hc : c + 1 < 2 * 2 ^ j)
    (hn : n + c = 2 * 2 ^ j * t) :
    (luc n : ℤ) ≡ (-1) ^ (c + 1) * (luc c : ℤ) [ZMOD (luc (2 ^ j) : ℤ)] := by
  set k := 2 ^ j with hkdef
  have hke : Even k := (Nat.even_pow' (by omega)).mpr even_two
  have hk0 : 0 < k := Nat.two_pow_pos j
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by rcases ht with ⟨u, hu⟩; omega⟩
  have hmul : 2 * k * (s + 1) = 2 * k * s + 2 * k := by ring
  have hn' : n = (2 * k - c) + 2 * k * s := by omega
  have h1 : (luc n : ℤ) ≡ (-1) ^ s * (luc (2 * k - c) : ℤ) [ZMOD (luc k : ℤ)] := by
    rw [hn']; exact luc_ladder k hke _ s
  have h2 : (luc (2 * k - c) : ℤ) ≡ (-1) ^ (c + 1) * (luc c : ℤ) [ZMOD (luc k : ℤ)] :=
    luc_reflect' k hke hk0 c hc
  have hs : Even s := by
    have h := Nat.odd_iff.mp ht
    exact Nat.even_iff.mpr (by omega)
  calc (luc n : ℤ)
      ≡ (-1) ^ s * (luc (2 * k - c) : ℤ) [ZMOD (luc k : ℤ)] := h1
    _ ≡ (-1) ^ s * ((-1) ^ (c + 1) * (luc c : ℤ)) [ZMOD (luc k : ℤ)] := h2.mul_left _
    _ = (-1) ^ (c + 1) * (luc c : ℤ) := by rw [hs.neg_one_pow, one_mul]

/-! ## Jacobi values -/

theorem jacobiSym_sq_mem {N : ℕ} {a x : ℤ} (h : a ≡ x ^ 2 [ZMOD (N : ℤ)]) :
    jacobiSym a N = 0 ∨ jacobiSym a N = 1 := by
  rw [jacobiSym.mod_left' h, jacobiSym.pow_left]
  rcases Int.even_or_odd (jacobiSym x N) with _ | _ <;>
    rcases jacobiSym.trichotomy x N with h' | h' | h' <;> rw [h'] <;> norm_num

theorem jacobiSym_two_sq_mem {N : ℕ} {a x : ℤ} (hN : N % 8 = 7)
    (h : a ≡ 2 * x ^ 2 [ZMOD (N : ℤ)]) :
    jacobiSym a N = 0 ∨ jacobiSym a N = 1 := by
  rw [jacobiSym.mod_left' h, jacobiSym.mul_left, jacobi_two_of_mod_eight hN, one_mul,
    jacobiSym.pow_left]
  rcases jacobiSym.trichotomy x N with h' | h' | h' <;> rw [h'] <;> norm_num

/-! ## Coprime splitting -/

theorem nat_sq_of_coprime {a b c : ℕ} (h : Nat.Coprime a b) (h2 : a * b = c ^ 2) :
    ∃ d, a = d ^ 2 := by
  refine exists_eq_pow_of_mul_eq_pow (a := a) (b := b) ?_ h2
  rw [Nat.isUnit_iff]; exact h

/-- `gcd (fib n) (luc n)` divides 2. -/
theorem gcd_fib_luc_dvd_two (n : ℕ) : Nat.gcd (Nat.fib n) (luc n) ∣ 2 := by
  obtain ⟨g, hg⟩ : ∃ g, g = Nat.gcd (Nat.fib n) (luc n) := ⟨_, rfl⟩
  rw [← hg]
  have hgl : g ∣ Nat.fib n := hg ▸ Nat.gcd_dvd_left _ _
  have hgr : g ∣ luc n := hg ▸ Nat.gcd_dvd_right _ _
  clear hg
  have h1 : (g : ℤ) ∣ (Nat.fib n : ℤ) := Int.natCast_dvd_natCast.mpr hgl
  have h2 : (g : ℤ) ∣ (luc n : ℤ) := Int.natCast_dvd_natCast.mpr hgr
  have hsq := luc_sq n
  have hd : (g : ℤ) ∣ 4 * (-1) ^ n := by
    have he : (4 : ℤ) * (-1) ^ n = (luc n : ℤ) * (luc n : ℤ)
        - 5 * (Nat.fib n : ℤ) * (Nat.fib n : ℤ) := by nlinarith [hsq]
    rw [he]
    exact dvd_sub (h2.mul_left _) ((h1.mul_left _).mul_right _)
  have hd4 : (g : ℤ) ∣ 4 := by
    rcases Nat.even_or_odd n with h | h
    · rwa [h.neg_one_pow, mul_one] at hd
    · rw [h.neg_one_pow] at hd
      simpa using hd.neg_right
  have hd4' : g ∣ 4 := by exact_mod_cast hd4
  -- rule out g = 4:  if 4 ∣ fib n and 4 ∣ luc n, contradiction with coprimality of consecutive fibs
  have hcop : Nat.Coprime (Nat.fib n) (Nat.fib (n + 1)) := Nat.fib_coprime_fib_succ n
  -- the divisors of 4 are 1,2,4; rule out 4
  have hmem : g = 1 ∨ g = 2 ∨ g = 4 := by
    have := Nat.le_of_dvd (by norm_num) hd4'
    interval_cases g <;> revert hd4' <;> decide
  rcases hmem with rfl | rfl | rfl
  · norm_num
  · norm_num
  · -- g = 4 : then 4 ∣ fib n and 4 ∣ luc n = 2 fib (n+1) - fib n, so 4 ∣ 2 fib (n+1)
    exfalso
    have hf : (4 : ℕ) ∣ Nat.fib n := hgl
    have hl : (4 : ℕ) ∣ luc n := hgr
    have hz : (4 : ℤ) ∣ 2 * (Nat.fib (n + 1) : ℤ) := by
      have h1' : (4 : ℤ) ∣ (Nat.fib n : ℤ) := Int.natCast_dvd_natCast.mpr hf
      have h2' : (4 : ℤ) ∣ (luc n : ℤ) := Int.natCast_dvd_natCast.mpr hl
      rw [luc_cast] at h2'
      have := dvd_add h2' h1'
      simpa using this
    have hev : (2 : ℕ) ∣ Nat.fib (n + 1) := by
      have : (2 : ℤ) ∣ (Nat.fib (n + 1) : ℤ) := by
        rcases hz with ⟨c, hc⟩; exact ⟨c, by linarith [hc]⟩
      exact_mod_cast this
    have hev2 : (2 : ℕ) ∣ Nat.fib n := dvd_trans (by norm_num) hf
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hev2
      (Nat.Coprime.coprime_dvd_right hev hcop)) dvd_rfl
    omega

/-! ## 2-adic splitting -/

/-- If `4 ∣ d` and `d ≠ 0`, then `d = 2 * 2^j * t` with `j ≥ 1` and `t` odd. -/
theorem split_two_adic {d : ℕ} (hd : d ≠ 0) (h4 : 4 ∣ d) :
    ∃ j t, 1 ≤ j ∧ Odd t ∧ d = 2 * 2 ^ j * t := by
  obtain ⟨e, t, ht, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hd
  have hto : t % 2 = 1 := Nat.odd_iff.mp ht
  have he : 2 ≤ e := by
    by_contra hc
    interval_cases e
    · simp at h4; omega
    · rw [pow_one] at h4
      obtain ⟨c, hc'⟩ := h4
      omega
  refine ⟨e - 1, t, by omega, ht, ?_⟩
  rw [show 2 * 2 ^ (e - 1) = 2 ^ (e - 1 + 1) by ring, show e - 1 + 1 = e by omega]

/-! ## `luc` mod 4 -/

theorem luc_add_six (n : ℕ) : luc (n + 6) = 5 * luc n + 8 * luc (n + 1) := by
  have e0 : luc (n + 2) = luc n + luc (n + 1) := luc_add_two n
  have e1 : luc (n + 3) = luc (n + 1) + luc (n + 2) := luc_add_two (n + 1)
  have e2 : luc (n + 4) = luc (n + 2) + luc (n + 3) := luc_add_two (n + 2)
  have e3 : luc (n + 5) = luc (n + 3) + luc (n + 4) := luc_add_two (n + 3)
  have e4 : luc (n + 6) = luc (n + 4) + luc (n + 5) := luc_add_two (n + 4)
  omega

theorem luc_mod_four_periodic (n : ℕ) : luc (n + 6) % 4 = luc n % 4 := by
  rw [luc_add_six]; omega

/-- For even `n`, `luc n % 4 ∈ {2, 3}`; in particular `luc n` is never a square. -/
theorem luc_even_mod_four : ∀ n : ℕ, n % 2 = 0 → luc n % 4 = 2 ∨ luc n % 4 = 3 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 6 with h | h
    · interval_cases n <;> simp_all <;> decide
    · have := ih (n - 6) (by omega) (by omega)
      rw [show n = (n - 6) + 6 by omega, luc_mod_four_periodic]
      exact this

/-! ## Statement bridge: `Nat.fib (n-1) + Nat.fib (n+1) = luc n` for `n ≥ 1` -/

theorem fib_pred_add_fib_succ (n : ℕ) (hn : 1 ≤ n) :
    Nat.fib (n - 1) + Nat.fib (n + 1) = luc n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [luc_succ_eq, Nat.add_sub_cancel]

/-! ## Killing lemma for `luc n = square` -/

theorem luc_toolA_jacobi {n c j t : ℕ} (_hj : 1 ≤ j) (ht : Odd t) (hn : n = c + 2 * 2 ^ j * t)
    {x : ℤ} (hx : (luc n : ℤ) ≡ x ^ 2 [ZMOD (luc (2 ^ j) : ℤ)]) :
    jacobiSym (-(luc c : ℤ)) (luc (2 ^ j)) = 0 ∨
      jacobiSym (-(luc c : ℤ)) (luc (2 ^ j)) = 1 := by
  have h1 : (-(luc c : ℤ)) ≡ x ^ 2 [ZMOD (luc (2 ^ j) : ℤ)] :=
    ((luc_toolA ht hn).symm).trans hx
  exact jacobiSym_sq_mem h1

/-- `2` is coprime to any odd number, as an `Int.gcd` statement. -/
theorem int_gcd_two_of_odd {N : ℕ} (h : N % 2 = 1) : Int.gcd 2 N = 1 := by
  have h2 : Nat.Coprime 2 N := by
    have hp : Nat.Prime 2 := Nat.prime_two
    rcases (Nat.coprime_or_dvd_of_prime hp N) with hco | hdvd
    · exact hco
    · omega
  simpa [Int.gcd] using h2

/-! ## Periodicity -/

theorem luc_periodic {M p : ℕ} (h0 : luc p ≡ luc 0 [MOD M]) (h1 : luc (p + 1) ≡ luc 1 [MOD M]) :
    ∀ n, luc (n + p) ≡ luc n [MOD M] ∧ luc (n + 1 + p) ≡ luc (n + 1) [MOD M] := by
  intro n
  induction n with
  | zero =>
    refine ⟨by simpa using h0, ?_⟩
    rw [show 0 + 1 + p = p + 1 by ring]
    exact h1
  | succ m ih =>
    obtain ⟨iha, ihb⟩ := ih
    refine ⟨ihb, ?_⟩
    have e1 : luc (m + 1 + 1 + p) = luc (m + p) + luc (m + 1 + p) := by
      rw [show m + 1 + 1 + p = (m + p) + 2 by ring, luc_add_two,
        show m + p + 1 = m + 1 + p by ring]
    have e2 : luc (m + 1 + 1) = luc m + luc (m + 1) := by
      rw [show m + 1 + 1 = m + 2 by ring, luc_add_two]
    rw [e1, e2]
    exact Nat.ModEq.add iha ihb

theorem fib_periodic {M p : ℕ} (h0 : Nat.fib p ≡ Nat.fib 0 [MOD M])
    (h1 : Nat.fib (p + 1) ≡ Nat.fib 1 [MOD M]) :
    ∀ n, Nat.fib (n + p) ≡ Nat.fib n [MOD M] ∧
      Nat.fib (n + 1 + p) ≡ Nat.fib (n + 1) [MOD M] := by
  intro n
  induction n with
  | zero =>
    refine ⟨by simpa using h0, ?_⟩
    rw [show 0 + 1 + p = p + 1 by ring]
    exact h1
  | succ m ih =>
    obtain ⟨iha, ihb⟩ := ih
    refine ⟨ihb, ?_⟩
    have e1 : Nat.fib (m + 1 + 1 + p) = Nat.fib (m + p) + Nat.fib (m + 1 + p) := by
      rw [show m + 1 + 1 + p = (m + p) + 2 by ring, Nat.fib_add_two,
        show m + p + 1 = m + 1 + p by ring]
    have e2 : Nat.fib (m + 1 + 1) = Nat.fib m + Nat.fib (m + 1) := by
      rw [show m + 1 + 1 = m + 2 by ring, Nat.fib_add_two]
    rw [e1, e2]
    exact Nat.ModEq.add iha ihb

theorem luc_mod_eq {M p : ℕ} (hp : 0 < p) (h0 : luc p ≡ luc 0 [MOD M])
    (h1 : luc (p + 1) ≡ luc 1 [MOD M]) (n : ℕ) : luc n % M = luc (n % p) % M := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n p with h | h
    · rw [Nat.mod_eq_of_lt h]
    · have hrec := ih (n - p) (by omega)
      have hmod : (n - p) % p = n % p := by
        conv_rhs => rw [show n = (n - p) + p by omega]
        exact (Nat.add_mod_right _ _).symm
      rw [← hmod, ← hrec]
      conv_lhs => rw [show n = (n - p) + p by omega]
      exact (luc_periodic h0 h1 (n - p)).1

theorem fib_mod_eq {M p : ℕ} (hp : 0 < p) (h0 : Nat.fib p ≡ Nat.fib 0 [MOD M])
    (h1 : Nat.fib (p + 1) ≡ Nat.fib 1 [MOD M]) (n : ℕ) :
    Nat.fib n % M = Nat.fib (n % p) % M := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n p with h | h
    · rw [Nat.mod_eq_of_lt h]
    · have hrec := ih (n - p) (by omega)
      have hmod : (n - p) % p = n % p := by
        conv_rhs => rw [show n = (n - p) + p by omega]
        exact (Nat.add_mod_right _ _).symm
      rw [← hmod, ← hrec]
      conv_lhs => rw [show n = (n - p) + p by omega]
      exact (fib_periodic h0 h1 (n - p)).1

/-! ## Concrete base-case reductions -/

/-- `Nat.fib` has period 24 mod 16. -/
theorem fib_mod16 (n : ℕ) : Nat.fib n % 16 = Nat.fib (n % 24) % 16 :=
  fib_mod_eq (by norm_num) (by decide) (by decide) n

/-- `luc` has period 24 mod 16. -/
theorem luc_mod16 (n : ℕ) : luc n % 16 = luc (n % 24) % 16 :=
  luc_mod_eq (by norm_num) (by decide) (by decide) n

/-- `Nat.fib` has period 16 mod 21. -/
theorem fib_mod21 (n : ℕ) : Nat.fib n % 21 = Nat.fib (n % 16) % 21 :=
  fib_mod_eq (by norm_num) (by decide) (by decide) n

/-- `luc` has period 16 mod 21. -/
theorem luc_mod21 (n : ℕ) : luc n % 21 = luc (n % 16) % 21 :=
  luc_mod_eq (by norm_num) (by decide) (by decide) n

/-- Squares mod `M`: reduce `x^2 % M` to a bounded search. -/
theorem sq_mod (M : ℕ) (_hM : 0 < M) (x : ℕ) : x ^ 2 % M = (x % M) ^ 2 % M := by
  conv_lhs => rw [Nat.pow_mod]

/-- If `luc n = x^2` then `n % 12 = 1 ∨ n % 12 = 3`. -/
theorem luc_sq_mod12 {n x : ℕ} (h : luc n = x ^ 2) : n % 12 = 1 ∨ n % 12 = 3 := by
  have h1 : luc (n % 24) % 16 = (x % 16) ^ 2 % 16 := by
    rw [← luc_mod16, h, ← sq_mod 16 (by norm_num)]
  have h2 : n % 24 < 24 := Nat.mod_lt _ (by norm_num)
  have h3 : x % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have key : ∀ a < 24, ∀ b < 16, luc a % 16 = b ^ 2 % 16 → a % 12 = 1 ∨ a % 12 = 3 := by decide
  have h4 := key (n % 24) h2 (x % 16) h3 h1
  omega

/-- Twice-a-square version of `sq_mod`. -/
theorem two_sq_mod (M : ℕ) (x : ℕ) : 2 * x ^ 2 % M = 2 * (x % M) ^ 2 % M := by
  conv_lhs => rw [Nat.mul_mod, Nat.pow_mod]
  conv_rhs => rw [Nat.mul_mod, Nat.pow_mod, Nat.mod_mod]

/-- If `luc n = 2 * x^2` then `n % 6 = 0`. -/
theorem luc_two_sq_mod6 {n x : ℕ} (h : luc n = 2 * x ^ 2) : n % 6 = 0 := by
  have h1 : luc (n % 24) % 16 = 2 * (x % 16) ^ 2 % 16 := by
    rw [← luc_mod16, h, ← two_sq_mod 16]
  have h2 : n % 24 < 24 := Nat.mod_lt _ (by norm_num)
  have h3 : x % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have key : ∀ a < 24, ∀ b < 16, luc a % 16 = 2 * b ^ 2 % 16 → a % 6 = 0 := by decide
  have h4 := key (n % 24) h2 (x % 16) h3 h1
  omega

/-- If `luc n = 2 * x^2` and `n` is even then `n % 16 ∈ {0, 6, 10}`. -/
theorem luc_two_sq_mod16 {n x : ℕ} (h : luc n = 2 * x ^ 2) :
    n % 16 = 0 ∨ n % 16 = 6 ∨ n % 16 = 10 ∨ n % 2 = 1 := by
  have h1 : luc (n % 16) % 21 = 2 * (x % 21) ^ 2 % 21 := by
    rw [← luc_mod21, h, ← two_sq_mod 21]
  have h2 : n % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have h3 : x % 21 < 21 := Nat.mod_lt _ (by norm_num)
  have key : ∀ a < 16, ∀ b < 21, luc a % 21 = 2 * b ^ 2 % 21 →
      a = 0 ∨ a = 6 ∨ a = 10 ∨ a % 2 = 1 := by decide
  have h4 := key (n % 16) h2 (x % 21) h3 h1
  rcases h4 with h5 | h5 | h5 | h5
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (by omega)))

/-- If `Nat.fib n = 2 * x^2` and `n` is odd then `n % 16 ∈ {3, 13}`. -/
theorem fib_two_sq_mod16 {n x : ℕ} (h : Nat.fib n = 2 * x ^ 2) :
    n % 16 = 3 ∨ n % 16 = 13 ∨ n % 2 = 0 := by
  have h1 : Nat.fib (n % 16) % 21 = 2 * (x % 21) ^ 2 % 21 := by
    rw [← fib_mod21, h, ← two_sq_mod 21]
  have h2 : n % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have h3 : x % 21 < 21 := Nat.mod_lt _ (by norm_num)
  have key : ∀ a < 16, ∀ b < 21, Nat.fib a % 21 = 2 * b ^ 2 % 21 →
      a = 3 ∨ a = 13 ∨ a % 2 = 0 := by decide
  have h4 := key (n % 16) h2 (x % 21) h3 h1
  rcases h4 with h5 | h5 | h5
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (by omega))

/-! ## Splitting `d = 2 * 2^j * t` with `j ≥ 3` -/

/-- If `16 ∣ d` and `d ≠ 0`, then `d = 2 * 2^j * t` with `j ≥ 3` and `t` odd. -/
theorem split_two_adic16 {d : ℕ} (hd : d ≠ 0) (h16 : 16 ∣ d) :
    ∃ j t, 3 ≤ j ∧ Odd t ∧ d = 2 * 2 ^ j * t := by
  obtain ⟨e, t, ht, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hd
  have hto : t % 2 = 1 := Nat.odd_iff.mp ht
  have he : 4 ≤ e := by
    by_contra hc
    interval_cases e
    · obtain ⟨c, hc'⟩ := h16; simp only [pow_zero, one_mul] at hc'; omega
    · obtain ⟨c, hc'⟩ := h16; simp only [pow_one] at hc'; omega
    · obtain ⟨c, hc'⟩ := h16; norm_num at hc'; omega
    · obtain ⟨c, hc'⟩ := h16; norm_num at hc'; omega
  refine ⟨e - 1, t, by omega, ht, ?_⟩
  rw [show 2 * 2 ^ (e - 1) = 2 ^ (e - 1 + 1) by ring, show e - 1 + 1 = e by omega]

/-- `J(-2 | N) = -1` when `N % 8 = 7`. -/
theorem jacobi_neg_two {N : ℕ} (h : N % 8 = 7) : jacobiSym (-2) N = -1 := by
  have h4 : N % 4 = 3 := by omega
  have : (-2 : ℤ) = (-1) * 2 := by norm_num
  rw [this, jacobiSym.mul_left, jacobi_neg_one_of_mod_four h4, jacobi_two_of_mod_eight h]
  norm_num

/-- `J(-18 | N) = -1` when `N % 8 = 7` and `3 ∤ N`. -/
theorem jacobi_neg_eighteen {N : ℕ} (h : N % 8 = 7) (h3 : N % 3 = 1 ∨ N % 3 = 2) :
    jacobiSym (-18) N = -1 := by
  have hcop3 : Int.gcd 3 (N : ℤ) = 1 := by
    have hc : Nat.Coprime 3 N := by
      rcases (Nat.coprime_or_dvd_of_prime Nat.prime_three N) with hco | hdvd
      · exact hco
      · omega
    simpa [Int.gcd] using hc
  have hfac : (-18 : ℤ) = (-2) * 3 ^ 2 := by norm_num
  rw [hfac, jacobiSym.mul_left, jacobiSym.sq_one' hcop3, jacobi_neg_two h]
  norm_num

/-- Packaged contradiction for `luc n = 2 * x ^ 2` via Tool A. -/
theorem luc_two_sq_killA {n c j t x : ℕ} (hj : 3 ≤ j) (ht : Odd t) (hn : n = c + 2 * 2 ^ j * t)
    (h : luc n = 2 * x ^ 2)
    (hval : jacobiSym (-(luc c : ℤ)) (luc (2 ^ j)) = -1) : False := by
  have hN8 : luc (2 ^ j) % 8 = 7 := luc_two_pow_mod_eight j (by omega)
  have hmod : (-(luc c : ℤ)) ≡ 2 * ((x : ℤ)) ^ 2 [ZMOD (luc (2 ^ j) : ℤ)] := by
    refine ((luc_toolA ht hn).symm).trans ?_
    have he : (luc n : ℤ) = 2 * ((x : ℤ)) ^ 2 := by
      exact_mod_cast congrArg (fun m : ℕ => (m : ℤ)) h
    rw [he]
  have := jacobiSym_two_sq_mem hN8 hmod
  rw [hval] at this
  norm_num at this

/-- Packaged contradiction for `luc n = 2 * x ^ 2` via Tool B. -/
theorem luc_two_sq_killB {n c j t x : ℕ} (hj : 3 ≤ j) (ht : Odd t) (hc : c + 1 < 2 * 2 ^ j)
    (hn : n + c = 2 * 2 ^ j * t) (h : luc n = 2 * x ^ 2)
    (hval : jacobiSym ((-1) ^ (c + 1) * (luc c : ℤ)) (luc (2 ^ j)) = -1) : False := by
  have hN8 : luc (2 ^ j) % 8 = 7 := luc_two_pow_mod_eight j (by omega)
  have hmod : ((-1) ^ (c + 1) * (luc c : ℤ)) ≡ 2 * ((x : ℤ)) ^ 2 [ZMOD (luc (2 ^ j) : ℤ)] := by
    refine ((luc_toolB (by omega) ht hc hn).symm).trans ?_
    have he : (luc n : ℤ) = 2 * ((x : ℤ)) ^ 2 := by
      exact_mod_cast congrArg (fun m : ℕ => (m : ℤ)) h
    rw [he]
  have := jacobiSym_two_sq_mem hN8 hmod
  rw [hval] at this
  norm_num at this

/-! ## Odd-index Fibonacci squares -/

/-- Packaged contradiction for `Nat.fib n = x ^ 2` via Tool A / Tool B, when the relevant
residue is `-1` or `+1` times `F c` with `c = 1`. -/
theorem fib_sq_killA {n c j t x : ℕ} (_hj : 1 ≤ j) (ht : Odd t) (hn : n = c + 2 * 2 ^ j * t)
    (h : Nat.fib n = x ^ 2)
    (hval : jacobiSym (-(Nat.fib c : ℤ)) (luc (2 ^ j)) = -1) : False := by
  have hmod : (-(Nat.fib c : ℤ)) ≡ ((x : ℤ)) ^ 2 [ZMOD (luc (2 ^ j) : ℤ)] := by
    refine ((fib_toolA ht hn).symm).trans ?_
    have he : (Nat.fib n : ℤ) = ((x : ℤ)) ^ 2 := by
      exact_mod_cast congrArg (fun m : ℕ => (m : ℤ)) h
    rw [he]
  have := jacobiSym_sq_mem hmod
  rw [hval] at this
  norm_num at this

theorem fib_sq_killB {n c j t x : ℕ} (hj : 1 ≤ j) (ht : Odd t) (hc : c < 2 * 2 ^ j)
    (hn : n + c = 2 * 2 ^ j * t) (h : Nat.fib n = x ^ 2)
    (hval : jacobiSym ((-1) ^ c * (Nat.fib c : ℤ)) (luc (2 ^ j)) = -1) : False := by
  have hmod : ((-1) ^ c * (Nat.fib c : ℤ)) ≡ ((x : ℤ)) ^ 2 [ZMOD (luc (2 ^ j) : ℤ)] := by
    refine ((fib_toolB hj ht hc hn).symm).trans ?_
    have he : (Nat.fib n : ℤ) = ((x : ℤ)) ^ 2 := by
      exact_mod_cast congrArg (fun m : ℕ => (m : ℤ)) h
    rw [he]
  have := jacobiSym_sq_mem hmod
  rw [hval] at this
  norm_num at this

/-- If `Nat.fib n = x ^ 2` with `n` odd, then `n = 1`. -/
theorem fib_sq_odd {n x : ℕ} (hodd : n % 2 = 1) (h : Nat.fib n = x ^ 2) : n = 1 := by
  by_contra hne
  have hn1 : 1 < n := by omega
  rcases (by omega : n % 4 = 1 ∨ n % 4 = 3) with hc | hc
  · obtain ⟨j, t, hj, ht, hdt⟩ := split_two_adic (d := n - 1) (by omega) (by omega)
    refine fib_sq_killA hj ht (c := 1) (by omega) h ?_
    rw [Nat.fib_one]
    have hcast : (-((1 : ℕ) : ℤ)) = -1 := by norm_num
    rw [hcast]
    exact jacobi_neg_one_of_mod_four (luc_two_pow_mod_four j hj)
  · obtain ⟨j, t, hj, ht, hdt⟩ := split_two_adic (d := n + 1) (by omega) (by omega)
    have hcj : (1 : ℕ) < 2 * 2 ^ j := by
      have : (2 : ℕ) ≤ 2 ^ j := by
        calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
      omega
    refine fib_sq_killB hj ht hcj (by omega) h ?_
    rw [Nat.fib_one]
    have hcast : ((-1 : ℤ)) ^ 1 * ((1 : ℕ) : ℤ) = -1 := by norm_num
    rw [hcast]
    exact jacobi_neg_one_of_mod_four (luc_two_pow_mod_four j hj)

/-! ## Splitting `F(2m) = F(m) * L(m)` -/

theorem fib_two_mul_nat (m : ℕ) : Nat.fib (2 * m) = Nat.fib m * luc m := by
  have h := fib_two_mul' m
  have h2 : ((Nat.fib (2 * m) : ℕ) : ℤ) = ((Nat.fib m * luc m : ℕ) : ℤ) := by push_cast; exact h
  exact_mod_cast h2

/-- `3 ∣ m ↔ 2 ∣ Nat.fib m`.  We only need the forward/backward facts about parity of `fib`. -/
theorem fib_even_iff (m : ℕ) : Nat.fib m % 2 = 0 ↔ m % 3 = 0 := by
  constructor
  · intro hm
    have h1 : Nat.fib (m % 3) % 2 = 0 := by
      rw [← fib_mod_eq (M := 2) (p := 3) (by norm_num) (by decide) (by decide) m]
      exact hm
    have h2 : m % 3 < 3 := Nat.mod_lt _ (by norm_num)
    by_contra hc
    interval_cases h : (m % 3)
    · exact hc rfl
    · revert h1; decide
    · revert h1; decide
  · intro hm
    have := fib_mod_eq (M := 2) (p := 3) (by norm_num) (by decide) (by decide) m
    rw [this, hm]
    decide

/-- If `gcd (fib m) (luc m) = 1` and `fib m * luc m = x^2`, both factors are squares. -/
theorem split_coprime_sq {m x : ℕ} (hcop : Nat.Coprime (Nat.fib m) (luc m))
    (h : Nat.fib m * luc m = x ^ 2) : (∃ a, Nat.fib m = a ^ 2) ∧ (∃ b, luc m = b ^ 2) := by
  constructor
  · exact nat_sq_of_coprime (c := x) hcop h
  · refine nat_sq_of_coprime (c := x) hcop.symm ?_
    rw [mul_comm]; exact h

/-- `luc m` is even iff `3 ∣ m`. -/
theorem luc_even_iff (m : ℕ) : luc m % 2 = 0 ↔ m % 3 = 0 := by
  have hper := luc_mod_eq (M := 2) (p := 3) (by norm_num) (by decide) (by decide) m
  have h2 : m % 3 < 3 := Nat.mod_lt _ (by norm_num)
  constructor
  · intro hm
    rw [hper] at hm
    by_contra hc
    interval_cases h : (m % 3)
    · exact hc rfl
    · revert hm; decide
    · revert hm; decide
  · intro hm
    rw [hper, hm]
    decide

/-- The exact gcd of `fib m` and `luc m`. -/
theorem gcd_fib_luc (m : ℕ) :
    Nat.gcd (Nat.fib m) (luc m) = if m % 3 = 0 then 2 else 1 := by
  have hd := gcd_fib_luc_dvd_two m
  have hle : Nat.gcd (Nat.fib m) (luc m) ≤ 2 := Nat.le_of_dvd (by norm_num) hd
  have hmem : Nat.gcd (Nat.fib m) (luc m) = 1 ∨ Nat.gcd (Nat.fib m) (luc m) = 2 := by
    interval_cases h : (Nat.gcd (Nat.fib m) (luc m))
    · exfalso
      have := Nat.eq_zero_of_gcd_eq_zero_right h
      have := luc_pos m
      omega
    · exact Or.inl rfl
    · exact Or.inr rfl
  by_cases hm : m % 3 = 0
  · rw [if_pos hm]
    rcases hmem with h | h
    · exfalso
      have hfe : Nat.fib m % 2 = 0 := (fib_even_iff m).mpr hm
      have hle : luc m % 2 = 0 := (luc_even_iff m).mpr hm
      have h2f : 2 ∣ Nat.fib m := by omega
      have h2l : 2 ∣ luc m := by omega
      have : (2 : ℕ) ∣ Nat.gcd (Nat.fib m) (luc m) := Nat.dvd_gcd h2f h2l
      omega
    · exact h
  · rw [if_neg hm]
    rcases hmem with h | h
    · exact h
    · exfalso
      have h2f : 2 ∣ Nat.fib m := h ▸ Nat.gcd_dvd_left _ _
      have : Nat.fib m % 2 = 0 := by omega
      have := (fib_even_iff m).mp this
      omega

/-- When `3 ∣ m`, write `fib m = 2 * a`, `luc m = 2 * b` with `a, b` coprime. -/
theorem split_gcd_two {m : ℕ} (hm : m % 3 = 0) :
    ∃ a b, Nat.fib m = 2 * a ∧ luc m = 2 * b ∧ Nat.Coprime a b := by
  have hfe : Nat.fib m % 2 = 0 := (fib_even_iff m).mpr hm
  have hle : luc m % 2 = 0 := (luc_even_iff m).mpr hm
  obtain ⟨a, ha⟩ : ∃ a, Nat.fib m = 2 * a := ⟨Nat.fib m / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, luc m = 2 * b := ⟨luc m / 2, by omega⟩
  refine ⟨a, b, ha, hb, ?_⟩
  have hg := gcd_fib_luc m
  rw [if_pos hm, ha, hb] at hg
  have : 2 * Nat.gcd a b = 2 := by
    rw [← Nat.gcd_mul_left]; exact hg
  omega

/-! ## Odd-index `fib = 2 * square` -/

theorem fib_two_sq_killA {n c j t x : ℕ} (hj : 3 ≤ j) (ht : Odd t) (hn : n = c + 2 * 2 ^ j * t)
    (h : Nat.fib n = 2 * x ^ 2)
    (hval : jacobiSym (-(Nat.fib c : ℤ)) (luc (2 ^ j)) = -1) : False := by
  have hN8 : luc (2 ^ j) % 8 = 7 := luc_two_pow_mod_eight j (by omega)
  have hmod : (-(Nat.fib c : ℤ)) ≡ 2 * ((x : ℤ)) ^ 2 [ZMOD (luc (2 ^ j) : ℤ)] := by
    refine ((fib_toolA ht hn).symm).trans ?_
    have he : (Nat.fib n : ℤ) = 2 * ((x : ℤ)) ^ 2 := by
      exact_mod_cast congrArg (fun m : ℕ => (m : ℤ)) h
    rw [he]
  have := jacobiSym_two_sq_mem hN8 hmod
  rw [hval] at this
  norm_num at this

theorem fib_two_sq_killB {n c j t x : ℕ} (hj : 3 ≤ j) (ht : Odd t) (hc : c < 2 * 2 ^ j)
    (hn : n + c = 2 * 2 ^ j * t) (h : Nat.fib n = 2 * x ^ 2)
    (hval : jacobiSym ((-1) ^ c * (Nat.fib c : ℤ)) (luc (2 ^ j)) = -1) : False := by
  have hN8 : luc (2 ^ j) % 8 = 7 := luc_two_pow_mod_eight j (by omega)
  have hmod : ((-1) ^ c * (Nat.fib c : ℤ)) ≡ 2 * ((x : ℤ)) ^ 2 [ZMOD (luc (2 ^ j) : ℤ)] := by
    refine ((fib_toolB (by omega) ht hc hn).symm).trans ?_
    have he : (Nat.fib n : ℤ) = 2 * ((x : ℤ)) ^ 2 := by
      exact_mod_cast congrArg (fun m : ℕ => (m : ℤ)) h
    rw [he]
  have := jacobiSym_two_sq_mem hN8 hmod
  rw [hval] at this
  norm_num at this

/-- If `Nat.fib n = 2 * x ^ 2` with `n` odd, then `n = 3`. -/
theorem fib_two_sq_odd {n x : ℕ} (hodd : n % 2 = 1) (h : Nat.fib n = 2 * x ^ 2) : n = 3 := by
  have hb := fib_two_sq_mod16 h
  have hb' : n % 16 = 3 ∨ n % 16 = 13 := by omega
  by_contra hne
  have hpow : (8 : ℕ) ≤ 2 ^ 3 := by norm_num
  rcases hb' with hc | hc
  · have hn3 : 3 < n := by omega
    obtain ⟨j, t, hj, ht, hdt⟩ := split_two_adic16 (d := n - 3) (by omega) (by omega)
    refine fib_two_sq_killA hj ht (c := 3) (by omega) h ?_
    have hf3 : (Nat.fib 3 : ℤ) = 2 := by norm_num
    rw [hf3]
    exact jacobi_neg_two (luc_two_pow_mod_eight j (by omega))
  · obtain ⟨j, t, hj, ht, hdt⟩ := split_two_adic16 (d := n + 3) (by omega) (by omega)
    have hcj : (3 : ℕ) < 2 * 2 ^ j := by
      have : (8 : ℕ) ≤ 2 ^ j := by
        calc (8 : ℕ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
      omega
    refine fib_two_sq_killB hj ht hcj (by omega) h ?_
    have hf3 : ((-1 : ℤ)) ^ 3 * (Nat.fib 3 : ℤ) = -2 := by norm_num
    rw [hf3]
    exact jacobi_neg_two (luc_two_pow_mod_eight j (by omega))

/-- `luc 12 = 322` and `161` is not a perfect square; used to exclude `m = 12`. -/
theorem not_sq_161 (q : ℕ) : q ^ 2 ≠ 161 := by
  intro hq
  have h1 : q ≤ 13 := by
    by_contra hc
    have : 14 * 14 ≤ q * q := Nat.mul_le_mul (by omega) (by omega)
    have h2 : q ^ 2 = q * q := by ring
    omega
  interval_cases q <;> omega

theorem luc_twelve : luc 12 = 322 := by norm_num [luc]

/-! ## Growth bounds -/

theorem luc_ge_eight {m : ℕ} (hm : 5 ≤ m) : 8 ≤ luc m := by
  induction m using Nat.twoStepInduction with
  | zero => omega
  | one => omega
  | more p ih1 ih2 =>
    rcases Nat.lt_or_ge p 3 with hp | hp
    · interval_cases p
      · omega
      · omega
      · have h4 : luc 4 = 7 := by norm_num [luc]
        have h5 : luc 3 = 4 := by norm_num [luc]
        have h6 : luc (2 + 2) = luc 2 + luc 3 := luc_add_two 2
        omega
    · rcases Nat.eq_or_lt_of_le hp with h | h
      · -- `p = 3`, goal is `8 ≤ luc 5 = 11`
        have hp4 : p = 3 := h.symm
        subst hp4
        have h5 : luc 5 = 11 := by norm_num [luc]
        have : luc (3 + 2) = luc 5 := by norm_num
        omega
      · have h1 : 8 ≤ luc (p + 1) := ih2 (by omega)
        have h2 : luc (p + 2) = luc p + luc (p + 1) := luc_add_two p
        have h3 : 0 < luc p := luc_pos p
        omega

theorem fib_ge_five {n : ℕ} (hn : 5 ≤ n) : 5 ≤ Nat.fib n := by
  have h : Nat.fib 5 ≤ Nat.fib n := Nat.fib_mono hn
  have h5 : Nat.fib 5 = 5 := by norm_num
  omega

/-! ## Lucas numbers that are powers of two -/

/-- `luc m % 8 ≠ 0` for every `m`: use the period `12` of `luc` modulo `8`. -/
theorem luc_not_dvd_eight (m : ℕ) : luc m % 8 ≠ 0 := by
  have hper := luc_mod_eq (M := 8) (p := 12) (by norm_num) (by decide) (by decide) m
  have h2 : m % 12 < 12 := Nat.mod_lt _ (by norm_num)
  rw [hper]
  revert h2
  generalize m % 12 = r
  intro h2
  interval_cases r <;> decide

/-- If `luc m` is a power of two, then `m ∈ {0, 1, 3}`. -/
theorem luc_eq_two_pow {m s : ℕ} (h : luc m = 2 ^ s) : m = 0 ∨ m = 1 ∨ m = 3 := by
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨h0, h1, h3⟩ := hcon
  rcases Nat.lt_or_ge m 5 with hm | hm
  · -- `m ∈ {2, 4}`: `luc 2 = 3`, `luc 4 = 7`
    interval_cases m
    · exact h0 rfl
    · exact h1 rfl
    · -- `luc 2 = 3 = 2 ^ s` impossible
      have h2 : luc 2 = 3 := by norm_num [luc]
      rw [h2] at h
      rcases Nat.lt_or_ge s 2 with hs | hs
      · interval_cases s <;> omega
      · have : (4 : ℕ) ≤ 2 ^ s := by
          calc (4 : ℕ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
        omega
    · exact h3 rfl
    · -- `luc 4 = 7 = 2 ^ s` impossible
      have h2 : luc 4 = 7 := by norm_num [luc]
      rw [h2] at h
      rcases Nat.lt_or_ge s 3 with hs | hs
      · interval_cases s <;> omega
      · have : (8 : ℕ) ≤ 2 ^ s := by
          calc (8 : ℕ) = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
        omega
  · -- `m ≥ 5`: then `luc m ≥ 8`, so `8 ∣ luc m`, contradicting `luc_not_dvd_eight`
    have h8 : 8 ≤ luc m := luc_ge_eight hm
    have hs3 : 3 ≤ s := by
      by_contra hc
      have : 2 ^ s ≤ 4 := by
        interval_cases s <;> norm_num
      omega
    have hdvd : (8 : ℕ) ∣ luc m := by
      rw [h, show (8 : ℕ) = 2 ^ 3 by norm_num]
      exact pow_dvd_pow 2 hs3
    refine luc_not_dvd_eight m ?_
    omega

/-- `4 ∣ Nat.fib n ↔ 6 ∣ n`; we need only that `fib n` odd forces `3 ∤ n` etc.
Here: if `Nat.fib n = 1` then `n = 1 ∨ n = 2`. -/
theorem fib_eq_one {n : ℕ} (h : Nat.fib n = 1) : n = 1 ∨ n = 2 := by
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n
    · simp at h
    · exact h1 rfl
    · exact h2 rfl
  · have : Nat.fib 3 ≤ Nat.fib n := Nat.fib_mono hn
    have h3 : Nat.fib 3 = 2 := by norm_num
    omega
