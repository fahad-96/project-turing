import Mathlib
import TuringTask.Knopp

/-!
# The five statements

Each statement is about a function `s` with the hypothesis `hs`, which makes `s` the Dedekind sum
`dsum` (`dsum_eq`).
-/

namespace TuringTask

open Finset

/-- Knopp's identity. -/
theorem main_knopp (s : ℕ → ℕ → ℚ)
    (hs : ∀ x y : ℕ, s x y = ∑ r ∈ range y, ((r : ℚ) / y - 1 / 2) *
      (if x * r % y = 0 then 0 else ((x * r % y : ℕ) : ℚ) / y - 1 / 2)) (h k n : ℕ) :
    ∑ d ∈ Nat.divisors n, ∑ b ∈ range d, s (n / d * h + b * k) (d * k) =
      (ArithmeticFunction.sigma 1 n : ℚ) * s h k := by
  simp only [dsum_eq s hs]
  exact knopp h k n

/-- `2 gcd(3, k) k s(h, k)` is an integer. -/
theorem main_integral (s : ℕ → ℕ → ℚ)
    (hs : ∀ x y : ℕ, s x y = ∑ r ∈ range y, ((r : ℚ) / y - 1 / 2) *
      (if x * r % y = 0 then 0 else ((x * r % y : ℕ) : ℚ) / y - 1 / 2)) (h k : ℕ) :
    ∃ m : ℤ, ((2 * Nat.gcd 3 k * k : ℕ) : ℚ) * s h k = m := by
  rw [dsum_eq s hs]
  exact integral h k

/-- `12 k s(h, k) ≡ k + 1 - 2 J(h | k) (mod 8)` for odd `k`. -/
theorem main_mod_eight (s : ℕ → ℕ → ℚ)
    (hs : ∀ x y : ℕ, s x y = ∑ r ∈ range y, ((r : ℚ) / y - 1 / 2) *
      (if x * r % y = 0 then 0 else ((x * r % y : ℕ) : ℚ) / y - 1 / 2))
    (h k : ℕ) (hk : k % 2 = 1) (hhk : Nat.Coprime h k) :
    ∃ m : ℤ, (12 * k : ℚ) * s h k = k + 1 - 2 * jacobiSym h k + 8 * m := by
  rw [dsum_eq s hs]
  exact mod_eight k hk h hhk

/-- `s(h, k) = 0` iff `k ∣ h² + 1`. -/
theorem main_eq_zero (s : ℕ → ℕ → ℚ)
    (hs : ∀ x y : ℕ, s x y = ∑ r ∈ range y, ((r : ℚ) / y - 1 / 2) *
      (if x * r % y = 0 then 0 else ((x * r % y : ℕ) : ℚ) / y - 1 / 2))
    (h k : ℕ) (hk : 0 < k) (hhk : Nat.Coprime h k) :
    s h k = 0 ↔ (h ^ 2 + 1) % k = 0 := by
  rw [dsum_eq s hs]
  exact dsum_eq_zero_iff h k hk hhk

/-- For a prime `k`, `s(a, k) = s(b, k)` iff `a ≡ b` or `a b ≡ 1 (mod k)`. -/
theorem main_eq (s : ℕ → ℕ → ℚ)
    (hs : ∀ x y : ℕ, s x y = ∑ r ∈ range y, ((r : ℚ) / y - 1 / 2) *
      (if x * r % y = 0 then 0 else ((x * r % y : ℕ) : ℚ) / y - 1 / 2))
    (a b k : ℕ) (hk : k.Prime) (ha : Nat.Coprime a k) (hb : Nat.Coprime b k) :
    s a k = s b k ↔ (a % k = b % k ∨ a * b % k = 1) := by
  rw [dsum_eq s hs, dsum_eq s hs]
  exact dsum_eq_iff a b k hk ha hb

end TuringTask
