import Mathlib
import TuringTask.Curves

/-!
# `x ^ 3 - 2 y ^ 3 = ±1` and triangular numbers that are cubes

* `cube_sub_two_cube`: `x ^ 3 - 2 y ^ 3 = 1` is `x ^ 3 + (-1) ^ 3 = 2 y ^ 3`, and
  `x ^ 3 - 2 y ^ 3 = -1` is `x ^ 3 + 1 ^ 3 = 2 y ^ 3`, so `two_cubes` gives `x = ±1`.
* `triangular_cube`: `n` and `n + 1` are coprime, so `n (n + 1) = 2 m ^ 3` makes one of them a
  cube and the other twice a cube, which is an equation `b ^ 3 - 2 a ^ 3 = ±1` in natural
  numbers.
-/

namespace TuringTask

lemma cube_eq_zero {y : ℤ} (h : y ^ 3 = 0) : y = 0 := pow_eq_zero_iff (by norm_num) |>.mp h

/-- The integer solutions of `x ^ 3 - 2 y ^ 3 = ±1`. -/
theorem cube_sub_two_cube {x y : ℤ} (h : x ^ 3 - 2 * y ^ 3 = 1 ∨ x ^ 3 - 2 * y ^ 3 = -1) :
    (x = 1 ∧ y = 0) ∨ (x = -1 ∧ y = -1) ∨ (x = -1 ∧ y = 0) ∨ (x = 1 ∧ y = 1) := by
  rcases h with h | h
  · rcases two_cubes (x := x) (y := -1) (z := y) (by linear_combination h) with h1 | h1
    · subst h1
      right; left
      exact ⟨rfl, cube_inj (by linarith [show ((-1 : ℤ)) ^ 3 = -1 by norm_num])⟩
    · have hx : x = 1 := by linarith
      subst hx
      left
      exact ⟨rfl, cube_eq_zero (by linarith)⟩
  · rcases two_cubes (x := x) (y := 1) (z := y) (by linear_combination h) with h1 | h1
    · subst h1
      right; right; right
      exact ⟨rfl, cube_inj (by linarith [show ((1 : ℤ)) ^ 3 = 1 by norm_num])⟩
    · have hx : x = -1 := by linarith
      subst hx
      right; right; left
      exact ⟨rfl, cube_eq_zero (by linarith)⟩

lemma nat_cubes_of_mul {a b c : ℕ} (hab : IsCoprime (a : ℤ) b) (h : a * b = c ^ 3) :
    (∃ s : ℕ, a = s ^ 3) ∧ ∃ t : ℕ, b = t ^ 3 := by
  have hc : Nat.Coprime a b := Nat.isCoprime_iff_coprime.mp hab
  refine ⟨exists_eq_pow_of_mul_eq_pow (by rw [Nat.isUnit_iff]; exact hc) h,
    exists_eq_pow_of_mul_eq_pow (c := c) (by rw [Nat.isUnit_iff]; exact hc.symm)
      (by rw [mul_comm]; exact h)⟩

/-- `n (n + 1) = 2 m ^ 3` only for `n = 0, 1`. -/
theorem triangular_cube {n m : ℕ} (h : n * (n + 1) = 2 * m ^ 3) : n = 0 ∨ n = 1 := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- `n = 2 k`: `k (2 k + 1) = m ^ 3`
    have hm : k * (2 * k + 1) = m ^ 3 := by
      have : 2 * (k * (2 * k + 1)) = 2 * m ^ 3 := by rw [← h, hk]; ring
      omega
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ :=
      nat_cubes_of_mul (a := k) (b := 2 * k + 1) ⟨-2, 1, by push_cast; ring⟩ hm
    have hz : (b : ℤ) ^ 3 - 2 * (a : ℤ) ^ 3 = 1 := by
      have e : b ^ 3 = 2 * a ^ 3 + 1 := by rw [← hb, ← ha]
      have e' : (b : ℤ) ^ 3 = 2 * (a : ℤ) ^ 3 + 1 := by exact_mod_cast e
      linarith
    rcases cube_sub_two_cube (Or.inl hz) with ⟨-, h2⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h2⟩
    · left
      have : a = 0 := by exact_mod_cast h2
      subst this
      omega
    · omega
    · omega
    · exfalso
      have : a = 1 := by exact_mod_cast h2
      subst this
      have h1 : (b : ℤ) ^ 3 = 3 := by linarith
      have h1' : b ^ 3 = 3 := by exact_mod_cast h1
      have hb1 : b ≤ 1 := by
        by_contra hc; push Not at hc
        have : 2 ^ 3 ≤ b ^ 3 := Nat.pow_le_pow_left hc 3
        omega
      interval_cases b <;> norm_num at h1'
  · -- `n = 2 k + 1`: `(2 k + 1) (k + 1) = m ^ 3`
    have hm : (2 * k + 1) * (k + 1) = m ^ 3 := by
      have : 2 * ((2 * k + 1) * (k + 1)) = 2 * m ^ 3 := by rw [← h, hk]; ring
      omega
    obtain ⟨⟨b, hb⟩, ⟨a, ha⟩⟩ :=
      nat_cubes_of_mul (a := 2 * k + 1) (b := k + 1) ⟨-1, 2, by push_cast; ring⟩ hm
    have hz : (b : ℤ) ^ 3 - 2 * (a : ℤ) ^ 3 = -1 := by
      have e : b ^ 3 + 1 = 2 * a ^ 3 := by rw [← ha, ← hb]; ring
      have e' : (b : ℤ) ^ 3 + 1 = 2 * (a : ℤ) ^ 3 := by exact_mod_cast e
      linarith
    rcases cube_sub_two_cube (Or.inr hz) with ⟨-, h2⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h2⟩
    · exfalso
      have : a = 0 := by exact_mod_cast h2
      subst this
      simp at ha
    · omega
    · omega
    · right
      have : a = 1 := by exact_mod_cast h2
      subst this
      omega

end TuringTask
