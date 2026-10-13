import Mathlib

/-!
# Lucas numbers with integer indices and the shift congruences

`lucZ n = F(n - 1) + F(n + 1)` for `n : Int`, with Mathlib's `Int.fib`.  For an even `k`:
* `fib_add_add_fib_sub`: `F(a + k) + F(a - k) = F(a) L(k)`;
* `lucZ_add_add_lucZ_sub`: `L(a + k) + L(a - k) = L(a) L(k)`;
* `lucZ_dvd_fib_shift`, `lucZ_dvd_lucZ_shift`: for odd `t`,
  `L(k)` divides `F(m + 2 k t) + F(m)` and `L(m + 2 k t) + L(m)`.
-/

namespace TuringTask

/-- Lucas numbers with integer index. -/
def lucZ (n : ℤ) : ℤ := Int.fib (n - 1) + Int.fib (n + 1)

lemma fib_neg_of_even {k : ℤ} (hk : Even k) : Int.fib (-k) = -Int.fib k := by
  rw [Int.fib_neg, if_pos hk]

lemma fib_one_sub_of_even {k : ℤ} (hk : Even k) : Int.fib (1 - k) = Int.fib (k - 1) := by
  have hodd : ¬ Even (k - 1) := by
    rw [Int.even_sub_one]
    exact not_not.mpr hk
  rw [show (1 : ℤ) - k = -(k - 1) by ring, Int.fib_neg, if_neg hodd]

/-- `F(a + k) + F(a - k) = F(a) L(k)` for even `k`. -/
lemma fib_add_add_fib_sub (a : ℤ) {k : ℤ} (hk : Even k) :
    Int.fib (a + k) + Int.fib (a - k) = Int.fib a * lucZ k := by
  have h1 := Int.fib_add a k
  have h2 := Int.fib_add a (-k)
  rw [fib_neg_of_even hk, show -k + 1 = 1 - k by ring, fib_one_sub_of_even hk] at h2
  rw [sub_eq_add_neg, h1, h2, lucZ]
  ring

/-- `L(a + k) + L(a - k) = L(a) L(k)` for even `k`. -/
lemma lucZ_add_add_lucZ_sub (a : ℤ) {k : ℤ} (hk : Even k) :
    lucZ (a + k) + lucZ (a - k) = lucZ a * lucZ k := by
  have h1 := fib_add_add_fib_sub (a - 1) hk
  have h2 := fib_add_add_fib_sub (a + 1) hk
  unfold lucZ at *
  rw [show a + k - 1 = a - 1 + k by ring, show a + k + 1 = a + 1 + k by ring,
    show a - k - 1 = a - 1 - k by ring, show a - k + 1 = a + 1 - k by ring]
  linear_combination h1 + h2

/-- Shifting the index by `2 k` changes the sign of `F` modulo `L(k)` (`k` even). -/
lemma lucZ_dvd_fib_shift_pow (k : ℤ) (hk : Even k) (m : ℤ) (t : ℕ) :
    lucZ k ∣ Int.fib (m + 2 * k * t) - (-1) ^ t * Int.fib m := by
  induction t with
  | zero => simp
  | succ t ih =>
    have e := fib_add_add_fib_sub (m + 2 * k * t + k) hk
    rw [show m + 2 * k * t + k + k = m + 2 * k * ((t + 1 : ℕ) : ℤ) by push_cast; ring,
      show m + 2 * k * t + k - k = m + 2 * k * t by ring] at e
    have : Int.fib (m + 2 * k * ((t + 1 : ℕ) : ℤ)) - (-1) ^ (t + 1) * Int.fib m
        = Int.fib (m + 2 * k * t + k) * lucZ k
          - (Int.fib (m + 2 * k * t) - (-1) ^ t * Int.fib m) := by
      rw [pow_succ]
      linear_combination e
    rw [this]
    exact dvd_sub (dvd_mul_left _ _) ih

lemma lucZ_dvd_lucZ_shift_pow (k : ℤ) (hk : Even k) (m : ℤ) (t : ℕ) :
    lucZ k ∣ lucZ (m + 2 * k * t) - (-1) ^ t * lucZ m := by
  induction t with
  | zero => simp
  | succ t ih =>
    have e := lucZ_add_add_lucZ_sub (m + 2 * k * t + k) hk
    rw [show m + 2 * k * t + k + k = m + 2 * k * ((t + 1 : ℕ) : ℤ) by push_cast; ring,
      show m + 2 * k * t + k - k = m + 2 * k * t by ring] at e
    have : lucZ (m + 2 * k * ((t + 1 : ℕ) : ℤ)) - (-1) ^ (t + 1) * lucZ m
        = lucZ (m + 2 * k * t + k) * lucZ k
          - (lucZ (m + 2 * k * t) - (-1) ^ t * lucZ m) := by
      rw [pow_succ]
      linear_combination e
    rw [this]
    exact dvd_sub (dvd_mul_left _ _) ih

lemma lucZ_dvd_fib_shift (k : ℤ) (hk : Even k) (m : ℤ) (t : ℕ) (ht : Odd t) :
    lucZ k ∣ Int.fib (m + 2 * k * t) + Int.fib m := by
  have := lucZ_dvd_fib_shift_pow k hk m t
  rwa [ht.neg_one_pow, neg_one_mul, sub_neg_eq_add] at this

lemma lucZ_dvd_lucZ_shift (k : ℤ) (hk : Even k) (m : ℤ) (t : ℕ) (ht : Odd t) :
    lucZ k ∣ lucZ (m + 2 * k * t) + lucZ m := by
  have := lucZ_dvd_lucZ_shift_pow k hk m t
  rwa [ht.neg_one_pow, neg_one_mul, sub_neg_eq_add] at this

/-- The Lucas number of the prompt, `F(n - 1) + F(n + 1)` with natural `n >= 1`. -/
lemma lucZ_natCast (n : ℕ) (hn : 1 ≤ n) :
    lucZ n = ((Nat.fib (n - 1) + Nat.fib (n + 1) : ℕ) : ℤ) := by
  unfold lucZ
  rw [show (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) by push_cast [Nat.cast_sub hn]; ring,
    show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring, Int.fib_natCast, Int.fib_natCast]
  push_cast
  ring

end TuringTask
