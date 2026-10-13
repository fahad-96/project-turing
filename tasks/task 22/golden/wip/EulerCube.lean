import Mathlib
import TuringTask.Eisenstein

/-!
# Cubes of the form `u ^ 2 + 3 v ^ 2`

`euler_cube`: if `u ^ 2 + 3 v ^ 2 = s ^ 3` and `u`, `3 v` are coprime, then
`u = a ^ 3 - 9 a b ^ 2` and `v = 3 a ^ 2 b - 3 b ^ 3`, that is `u + v √-3 = (a + b √-3) ^ 3`.

In `Eis` put `α = (u + v) + 2 v ω = u + v √-3`. Then `α * star α = s ^ 3`, the two factors are
coprime (`2` and the odd number `s ^ 3` lie in the ideal they generate), so `α` is a unit
times a cube. The units `±ω`, `±ω ^ 2` give an odd `ω`-coordinate, while that of `α` is `2 v`.
Multiplying the cube root by a power of `ω` makes its `ω`-coordinate even.
-/

namespace TuringTask

open QuadraticAlgebra

namespace Eis

lemma re_cube (d : Eis) : (d ^ 3).re = d.re ^ 3 - 3 * d.re * d.im ^ 2 + d.im ^ 3 := by
  simp [pow_succ]; ring

lemma im_cube (d : Eis) : (d ^ 3).im = 3 * d.re ^ 2 * d.im - 3 * d.re * d.im ^ 2 := by
  simp [pow_succ]; ring

lemma omega_cube : (⟨0, 1⟩ : Eis) ^ 3 = 1 := by
  ext <;> simp [pow_succ]

/-- Multiplying by a power of `ω` (which does not change the cube) makes the `ω`-coordinate
even. -/
lemma exists_cube_eq_even_im (g : Eis) : ∃ d : Eis, d ^ 3 = g ^ 3 ∧ Even d.im := by
  rcases Int.even_or_odd g.im with he | he
  · exact ⟨g, rfl, he⟩
  rcases Int.even_or_odd g.re with hc | hc
  · refine ⟨⟨-1, -1⟩ * g, ?_, ?_⟩
    · rw [mul_pow, show (⟨-1, -1⟩ : Eis) = ⟨0, 1⟩ ^ 2 by ext <;> simp [pow_succ],
        ← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, omega_cube, one_pow, one_mul]
    · simpa using hc.neg
  · refine ⟨⟨0, 1⟩ * g, ?_, ?_⟩
    · rw [mul_pow, omega_cube, one_mul]
    · simpa [sub_eq_add_neg] using hc.sub_odd he

lemma odd_polys {c e : ℤ} (h : Odd (c ^ 2 - c * e + e ^ 2)) :
    Odd (c ^ 3 - 3 * c ^ 2 * e + e ^ 3) ∧ Odd (c ^ 3 - 3 * c * e ^ 2 + e ^ 3) := by
  have key : ∀ x y : ZMod 2, x ^ 2 - x * y + y ^ 2 = 1 →
      x ^ 3 - 3 * x ^ 2 * y + y ^ 3 = 1 ∧ x ^ 3 - 3 * x * y ^ 2 + y ^ 3 = 1 := by decide
  rw [← ZMod.intCast_eq_one_iff_odd] at h
  push_cast at h
  obtain ⟨h1, h2⟩ := key _ _ h
  refine ⟨?_, ?_⟩ <;> rw [← ZMod.intCast_eq_one_iff_odd] <;> push_cast <;> assumption

lemma not_dvd_of_sq_add_three_sq {u v s : ℤ} (hc : IsCoprime u (3 * v))
    (h : u ^ 2 + 3 * v ^ 2 = s ^ 3) : Odd s := by
  rcases Int.even_or_odd s with ⟨t, ht⟩ | hs
  · exfalso
    have h8 : ((u ^ 2 + 3 * v ^ 2 : ℤ) : ZMod 8) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mpr ⟨t ^ 3, by rw [h, ht]; ring⟩
    push_cast at h8
    have key : ∀ x y : ZMod 8, x ^ 2 + 3 * y ^ 2 = 0 → 4 * x = 0 ∧ 4 * y = 0 := by decide
    obtain ⟨hu, hv⟩ := key _ _ h8
    have hu' : ((8 : ℕ) : ℤ) ∣ 4 * u :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp (by push_cast; exact hu)
    have hv' : ((8 : ℕ) : ℤ) ∣ 4 * v :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp (by push_cast; exact hv)
    have h2u : (2 : ℤ) ∣ u := by omega
    have h2v : (2 : ℤ) ∣ 3 * v := by omega
    rcases Int.isUnit_iff.mp (hc.isUnit_of_dvd' h2u h2v) with h2 | h2 <;> omega
  · exact hs

/-- Euler's lemma: a cube `u ^ 2 + 3 v ^ 2` with `u` prime to `3 v` comes from a cube in
`ℤ[√-3]`. -/
theorem euler_cube {u v s : ℤ} (hc : IsCoprime u (3 * v)) (h : u ^ 2 + 3 * v ^ 2 = s ^ 3) :
    ∃ a b : ℤ, u = a ^ 3 - 9 * a * b ^ 2 ∧ v = 3 * a ^ 2 * b - 3 * b ^ 3 := by
  have hs := not_dvd_of_sq_add_three_sq hc h
  obtain ⟨k, hk⟩ : Odd (s ^ 3) := hs.pow
  obtain ⟨p, q, hpq⟩ := hc
  have hprod : (⟨u + v, 2 * v⟩ : Eis) * star ⟨u + v, 2 * v⟩ = (s : Eis) ^ 3 := by
    rw [← Int.cast_pow, ← h]
    ext <;> simp only [re_mul, im_mul, re_star, im_star, re_intCast, im_intCast, Int.cast_id] <;>
      ring
  have hcop : IsCoprime (⟨u + v, 2 * v⟩ : Eis) (star ⟨u + v, 2 * v⟩) := by
    refine ⟨star ⟨u + v, 2 * v⟩ - ((k * p : ℤ) : Eis) + ((k * q : ℤ) : Eis) * ⟨1, 2⟩,
      -((k * p : ℤ) : Eis) - ((k * q : ℤ) : Eis) * ⟨1, 2⟩, ?_⟩
    ext <;> simp only [re_mul, im_mul, re_star, im_star, re_intCast, im_intCast, Int.cast_id,
      re_add, im_add, re_sub, im_sub, re_neg, im_neg, re_one, im_one]
    · linear_combination h + hk - 2 * k * hpq
    · ring
  obtain ⟨d, w, hdw⟩ := exists_assoc_cube hcop hprod
  have hnorm : norm d ^ 3 = s ^ 3 := by
    have h1 := congrArg QuadraticAlgebra.norm hdw
    rw [map_mul, map_pow, norm_eq_one_of_isUnit w.isUnit, mul_one] at h1
    rw [h1, norm_eq, ← h]; ring
  have hNd : Odd (norm d) := by
    rcases Int.even_or_odd (norm d) with he | ho
    · exfalso
      have := Int.even_pow.mpr ⟨he, (by norm_num : (3 : ℕ) ≠ 0)⟩
      rw [hnorm] at this
      exact (Int.not_even_iff_odd.mpr hs.pow) this
    · exact ho
  rw [norm_eq] at hNd
  obtain ⟨o1, o2⟩ := odd_polys hNd
  have him := congrArg QuadraticAlgebra.im hdw
  have hev : Even (2 * v) := even_two_mul v
  -- the cube root `g` with `g ^ 3 = ⟨u + v, 2 v⟩`
  obtain ⟨g, hg⟩ : ∃ g : Eis, g ^ 3 = ⟨u + v, 2 * v⟩ := by
    rcases eq_of_isUnit w.isUnit with hw | hw | hw | hw | hw | hw <;> rw [hw] at hdw him
    · exact ⟨d, by rw [← hdw]; ext <;> simp⟩
    · exact ⟨-d, by rw [← hdw]; ext <;> simp [Odd.neg_pow (by decide : Odd 3)]⟩
    all_goals
      exfalso
      simp only [im_mul, re_cube, im_cube] at him
      rw [← him] at hev
      refine Int.not_even_iff_odd.mpr ?_ hev
    · obtain ⟨r, hr⟩ := o1; exact ⟨r, by linear_combination hr⟩
    · obtain ⟨r, hr⟩ := o1.neg; exact ⟨r, by linear_combination hr⟩
    · obtain ⟨r, hr⟩ := o2.neg; exact ⟨r, by linear_combination hr⟩
    · obtain ⟨r, hr⟩ := o2; exact ⟨r, by linear_combination hr⟩
  obtain ⟨d', hd', ⟨b, hb⟩⟩ := exists_cube_eq_even_im g
  rw [hg] at hd'
  have hre := congrArg QuadraticAlgebra.re hd'
  have him' := congrArg QuadraticAlgebra.im hd'
  rw [re_cube] at hre
  rw [im_cube] at him'
  simp only at hre him'
  refine ⟨d'.re - b, b, ?_, ?_⟩
  · rw [hb] at hre him'
    have h2 : 2 * v = 2 * (3 * (d'.re - b) ^ 2 * b - 3 * b ^ 3) := by
      rw [← him']; ring
    have hv := mul_left_cancel₀ (two_ne_zero) h2
    linear_combination -hre - hv
  · rw [hb] at him'
    have h2 : 2 * v = 2 * (3 * (d'.re - b) ^ 2 * b - 3 * b ^ 3) := by
      rw [← him']; ring
    exact mul_left_cancel₀ (two_ne_zero) h2

end Eis

end TuringTask
