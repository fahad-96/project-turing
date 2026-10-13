import Mathlib
import TuringTask.Descent

/-!
# Rational points of `y ^ 2 = x ^ 3 - 27` and `y ^ 2 = x ^ 3 + 1`

* `rat_two_cubes`: the rational form of `two_cubes`, by clearing denominators.
* `minus27_points`: on `y ^ 2 = x ^ 3 - 27` put `u = 3 / x + y / (3 x)` and
  `v = 3 / x - y / (3 x)`. Then `u ^ 3 + v ^ 3 = 2`, so `u = v` (as `u + v = 6 / x ≠ 0`), which
  gives `y = 0` and `x = 3`.
* `plus1_points`: for `x ≠ 0` the point `((x ^ 3 + 4) / x ^ 2, y (x ^ 3 - 8) / x ^ 3)` lies on
  `Y ^ 2 = X ^ 3 - 27`, by `(t + 4) ^ 3 - 27 t ^ 2 = (t + 1) (t - 8) ^ 2` with `t = x ^ 3`.
  Hence `x ^ 3 + 4 = 3 x ^ 2`, that is `(x + 1) (x - 2) ^ 2 = 0`.
-/

namespace TuringTask

/-- `two_cubes` over `ℚ`. -/
lemma rat_two_cubes {u v w : ℚ} (h : u ^ 3 + v ^ 3 = 2 * w ^ 3) : u = v ∨ u + v = 0 := by
  have hD : ((u.den : ℚ) * v.den * w.den) ≠ 0 := by positivity
  have eU : u * ((u.den : ℚ) * v.den * w.den) = ((u.num * v.den * w.den : ℤ) : ℚ) := by
    push_cast; rw [← Rat.mul_den_eq_num]; ring
  have eV : v * ((u.den : ℚ) * v.den * w.den) = ((v.num * u.den * w.den : ℤ) : ℚ) := by
    push_cast; rw [← Rat.mul_den_eq_num]; ring
  have eW : w * ((u.den : ℚ) * v.den * w.den) = ((w.num * u.den * v.den : ℤ) : ℚ) := by
    push_cast; rw [← Rat.mul_den_eq_num]; ring
  have hZ : ((u.num * v.den * w.den : ℤ) : ℚ) ^ 3 + ((v.num * u.den * w.den : ℤ) : ℚ) ^ 3 =
      2 * ((w.num * u.den * v.den : ℤ) : ℚ) ^ 3 := by
    rw [← eU, ← eV, ← eW]
    linear_combination ((u.den : ℚ) * v.den * w.den) ^ 3 * h
  have hZ' : (u.num * v.den * w.den) ^ 3 + (v.num * u.den * w.den) ^ 3 =
      2 * (w.num * u.den * v.den) ^ 3 := by exact_mod_cast hZ
  rcases two_cubes hZ' with h1 | h1
  · left
    have : u * ((u.den : ℚ) * v.den * w.den) = v * ((u.den : ℚ) * v.den * w.den) := by
      rw [eU, eV, h1]
    exact mul_right_cancel₀ hD this
  · right
    have : (u + v) * ((u.den : ℚ) * v.den * w.den) = 0 := by
      rw [add_mul, eU, eV, ← Int.cast_add, h1, Int.cast_zero]
    rcases mul_eq_zero.mp this with h2 | h2
    · exact h2
    · exact absurd h2 hD

/-- The only rational point of `y ^ 2 = x ^ 3 - 27` is `(3, 0)`. -/
theorem minus27_points {x y : ℚ} (h : y ^ 2 = x ^ 3 - 27) : x = 3 ∧ y = 0 := by
  have hx : x ≠ 0 := by
    rintro rfl
    nlinarith [sq_nonneg y]
  have key : (3 / x + y / (3 * x)) ^ 3 + (3 / x - y / (3 * x)) ^ 3 = 2 * 1 ^ 3 := by
    have e : (3 / x + y / (3 * x)) ^ 3 + (3 / x - y / (3 * x)) ^ 3 =
        (54 + 2 * y ^ 2) / x ^ 3 := by
      field_simp; ring
    rw [e, h]
    field_simp; ring
  rcases rat_two_cubes key with h1 | h1
  · have hy : y = 0 := by
      have : y / (3 * x) = 0 := by linarith
      rcases div_eq_zero_iff.mp this with h2 | h2
      · exact h2
      · exact absurd h2 (mul_ne_zero (by norm_num) hx)
    refine ⟨?_, hy⟩
    rw [hy] at h
    exact (Odd.pow_inj (by decide)).mp (by linarith : x ^ 3 = 3 ^ 3)
  · exfalso
    have : 6 / x = 0 := by linear_combination h1
    rcases div_eq_zero_iff.mp this with h2 | h2
    · norm_num at h2
    · exact hx h2

/-- The rational points of `y ^ 2 = x ^ 3 + 1`. -/
theorem plus1_points {x y : ℚ} (h : y ^ 2 = x ^ 3 + 1) :
    (x = -1 ∧ y = 0) ∨ (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = -1) ∨ (x = 2 ∧ y = 3) ∨
      (x = 2 ∧ y = -3) := by
  by_cases hx : x = 0
  · subst hx
    have : (y - 1) * (y + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h1 | h1
    · right; left; exact ⟨rfl, by linarith⟩
    · right; right; left; exact ⟨rfl, by linarith⟩
  have hmap : (y * (x ^ 3 - 8) / x ^ 3) ^ 2 = ((x ^ 3 + 4) / x ^ 2) ^ 3 - 27 := by
    rw [div_pow, mul_pow, h, div_pow]
    field_simp
    ring
  have h3 := (minus27_points hmap).1
  have hx3 : x ^ 3 + 4 = 3 * x ^ 2 := by
    field_simp at h3
    linarith
  have hfac : (x + 1) * (x - 2) ^ 2 = 0 := by linear_combination hx3
  rcases mul_eq_zero.mp hfac with h1 | h1
  · have hx1 : x = -1 := by linarith
    subst hx1
    left; exact ⟨rfl, by nlinarith [sq_nonneg y]⟩
  · have hx2 : x = 2 := by nlinarith [sq_nonneg (x - 2)]
    subst hx2
    have : (y - 3) * (y + 3) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h2 | h2
    · right; right; right; left; exact ⟨rfl, by linarith⟩
    · right; right; right; right; exact ⟨rfl, by linarith⟩

end TuringTask
