import Mathlib
import TuringTask.Blocks65

/-!
# Smooth values: the five statements

* `sq_sub_one_smooth`: if every prime factor of `x ^ 2 - 1` is at most `7`, write
  `x ^ 2 - 1 = D y ^ 2` with `D` squarefree. Then `D ∣ 210`, `D ≠ 1`, and `(x, y)` solves
  `x ^ 2 - D y ^ 2 = 1` with `y` smooth, so the lemmas `blk210_D` list `x`.
* `mul_succ_smooth`: `x = 2 n + 1` gives `x ^ 2 - 1 = 4 n (n + 1)`.
* `three_smooth`: `n (n + 1)` and `(n + 1) (n + 2)` are both smooth.
* `sq_add_one_smooth`: `3`, `7`, `11` and `4` never divide `x ^ 2 + 1`, so
  `x ^ 2 + 1 = D y ^ 2` with `D ∣ 130` and `y` odd and smooth for `65`; then `blk65_D`.
* `pell_smooth`: `blk30030_2`.
-/

namespace TuringTask

lemma smooth_210_of {N : ℕ} (h : ∀ p : ℕ, p.Prime → N % p = 0 → p ≤ 7) : Smooth 210 N := by
  intro q hq hd
  have := h q hq (Nat.mod_eq_zero_of_dvd hd)
  interval_cases q <;> first | omega | (exfalso; norm_num at hq)

lemma smooth_30030_of {N : ℕ} (h : ∀ p : ℕ, p.Prime → N % p = 0 → p ≤ 13) :
    Smooth 30030 N := by
  intro q hq hd
  have := h q hq (Nat.mod_eq_zero_of_dvd hd)
  interval_cases q <;> first | omega | (exfalso; norm_num at hq)

/-- If every prime factor of `x ^ 2 - 1` is at most `7`, then `x` is one of 29 values. -/
theorem sq_sub_one_smooth {x : ℕ} (h : ∀ p : ℕ, p.Prime → (x ^ 2 - 1) % p = 0 → p ≤ 7) :
    x ∈ ({2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 15, 17, 19, 26, 29, 31, 41, 49, 55, 71, 97,
      99, 127, 161, 244, 251, 449, 4801, 8749} : Finset ℕ) := by
  have hN : x ^ 2 - 1 ≠ 0 := by
    intro h0
    have := h 11 (by norm_num) (by rw [h0])
    omega
  have hx1 : 1 ≤ x ^ 2 := by
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp at hN
    · exact Nat.one_le_pow _ _ hx
  have hs := smooth_210_of h
  obtain ⟨D, y, hDy, hsq⟩ := Nat.sq_mul_squarefree (x ^ 2 - 1)
  have hD : D ∣ 210 := squarefree_dvd hsq (hs.of_dvd (Dvd.intro_left _ hDy))
  have hy : 0 < y := by
    rcases Nat.eq_zero_or_pos y with rfl | hy
    · simp at hDy; exact absurd hDy.symm hN
    · exact hy
  have hys : Smooth 210 y :=
    hs.of_dvd (hDy ▸ Dvd.dvd.mul_right (dvd_pow_self y two_ne_zero) D)
  have heq : (x : ℤ) ^ 2 - D * y ^ 2 = 1 := by
    have e : y ^ 2 * D + 1 = x ^ 2 := by rw [hDy, Nat.sub_add_cancel hx1]
    have e' : (y : ℤ) ^ 2 * D + 1 = x ^ 2 := by exact_mod_cast e
    linarith
  have hD' : D ∈ Nat.divisors 210 := Nat.mem_divisors.mpr ⟨hD, by norm_num⟩
  rw [show Nat.divisors 210 = {1, 2, 3, 5, 6, 7, 10, 14, 15, 21, 30, 35, 42, 70, 105, 210} by
    decide] at hD'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hD'
  rcases hD' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exfalso
    norm_num at heq
    have hxy : (y : ℤ) < x := by nlinarith
    have hxy' : (y : ℤ) + 1 ≤ x := by omega
    nlinarith
  · exact Finset.mem_of_subset (by decide) (blk210_2 (by exact_mod_cast heq) hy hys)
  · exact Finset.mem_of_subset (by decide) (blk210_3 (by exact_mod_cast heq) hy hys)
  · exact Finset.mem_of_subset (by decide) (blk210_5 (by exact_mod_cast heq) hy hys)
  · exact Finset.mem_of_subset (by decide) (blk210_6 (by exact_mod_cast heq) hy hys)
  · exact Finset.mem_of_subset (by decide) (blk210_7 (by exact_mod_cast heq) hy hys)
  · exact Finset.mem_of_subset (by decide) (blk210_10 (by exact_mod_cast heq) hy hys)
  · exact Finset.mem_of_subset (by decide) (blk210_14 (by exact_mod_cast heq) hy hys)
  · exact Finset.mem_of_subset (by decide) (blk210_15 (by exact_mod_cast heq) hy hys)
  · exact Finset.mem_of_subset (by decide) (blk210_21 (by exact_mod_cast heq) hy hys)
  · exact Finset.mem_of_subset (by decide) (blk210_30 (by exact_mod_cast heq) hy hys)
  · exact Finset.mem_of_subset (by decide) (blk210_35 (by exact_mod_cast heq) hy hys)
  · exact Finset.mem_of_subset (by decide) (blk210_42 (by exact_mod_cast heq) hy hys)
  · exact Finset.mem_of_subset (by decide) (blk210_70 (by exact_mod_cast heq) hy hys)
  · exact Finset.mem_of_subset (by decide) (blk210_105 (by exact_mod_cast heq) hy hys)
  · exact Finset.mem_of_subset (by decide) (blk210_210 (by exact_mod_cast heq) hy hys)

/-- If every prime factor of `n (n + 1)` is at most `7`, then `n` is one of 23 values. -/
theorem mul_succ_smooth {n : ℕ} (h : ∀ p : ℕ, p.Prime → n * (n + 1) % p = 0 → p ≤ 7) :
    n ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 9, 14, 15, 20, 24, 27, 35, 48, 49, 63, 80, 125, 224,
      2400, 4374} : Finset ℕ) := by
  have e : (2 * n + 1) ^ 2 - 1 = 4 * (n * (n + 1)) := by
    have : (2 * n + 1) ^ 2 = 4 * (n * (n + 1)) + 1 := by ring
    omega
  have hx := sq_sub_one_smooth (x := 2 * n + 1) (by
    intro p hp hd
    rw [e] at hd
    rcases (Nat.Prime.dvd_mul hp).mp (Nat.dvd_of_mod_eq_zero hd) with h4 | h4
    · have := Nat.le_of_dvd (by norm_num) h4
      omega
    · exact h p hp (Nat.mod_eq_zero_of_dvd h4))
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  omega

/-- If every prime factor of `n (n + 1) (n + 2)` is at most `7`, then `n` is one of 10
values. -/
theorem three_smooth {n : ℕ}
    (h : ∀ p : ℕ, p.Prime → n * (n + 1) * (n + 2) % p = 0 → p ≤ 7) :
    n ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 14, 48} : Finset ℕ) := by
  have h1 := mul_succ_smooth (n := n) (by
    intro p hp hd
    exact h p hp (Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero hd) _)))
  have h2 := mul_succ_smooth (n := n + 1) (by
    intro p hp hd
    refine h p hp (Nat.mod_eq_zero_of_dvd ?_)
    rw [mul_assoc]
    exact Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero hd) _)
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2 ⊢
  omega

lemma sq_add_one_mod {x m : ℕ} (hm : m = 3 ∨ m = 4 ∨ m = 7 ∨ m = 11) : (x ^ 2 + 1) % m ≠ 0 := by
  have hr : (x ^ 2 + 1) % m = ((x % m) ^ 2 + 1) % m := by simp [Nat.pow_mod, Nat.add_mod]
  rw [hr]
  rcases hm with rfl | rfl | rfl | rfl
  · have := Nat.mod_lt x (by norm_num : 3 > 0)
    generalize x % 3 = r at this
    interval_cases r <;> norm_num
  · have := Nat.mod_lt x (by norm_num : 4 > 0)
    generalize x % 4 = r at this
    interval_cases r <;> norm_num
  · have := Nat.mod_lt x (by norm_num : 7 > 0)
    generalize x % 7 = r at this
    interval_cases r <;> norm_num
  · have := Nat.mod_lt x (by norm_num : 11 > 0)
    generalize x % 11 = r at this
    interval_cases r <;> norm_num

/-- If every prime factor of `x ^ 2 + 1` is at most `13`, then `x` is one of 10 values. -/
theorem sq_add_one_smooth {x : ℕ} (h : ∀ p : ℕ, p.Prime → (x ^ 2 + 1) % p = 0 → p ≤ 13) :
    x ∈ ({0, 1, 2, 3, 5, 7, 8, 18, 57, 239} : Finset ℕ) := by
  have hs : Smooth 130 (x ^ 2 + 1) := by
    intro q hq hd
    have := h q hq (Nat.mod_eq_zero_of_dvd hd)
    have h3 := sq_add_one_mod (x := x) (m := 3) (by norm_num)
    have h7 := sq_add_one_mod (x := x) (m := 7) (by norm_num)
    have h11 := sq_add_one_mod (x := x) (m := 11) (by norm_num)
    interval_cases q <;> first | omega | (exfalso; norm_num at hq)
  have h4 := sq_add_one_mod (x := x) (m := 4) (by norm_num)
  obtain ⟨D, y, hDy, hsq⟩ := Nat.sq_mul_squarefree (x ^ 2 + 1)
  have hD : D ∣ 130 := squarefree_dvd hsq (hs.of_dvd (Dvd.intro_left _ hDy))
  have hyN : y ∣ x ^ 2 + 1 := hDy ▸ Dvd.dvd.mul_right (dvd_pow_self y two_ne_zero) D
  have hy2 : ¬ 2 ∣ y := by
    rintro ⟨t, rfl⟩
    apply h4
    rw [← hDy]
    exact Nat.mod_eq_zero_of_dvd ⟨t ^ 2 * D, by ring⟩
  have hys : Smooth 65 y := by
    intro q hq hd
    have h130 := hs q hq (dvd_trans hd hyN)
    have := Nat.le_of_dvd (by norm_num) h130
    interval_cases q <;> omega
  have heq : (x : ℤ) ^ 2 - D * y ^ 2 = -1 := by
    have e' : (y : ℤ) ^ 2 * D = x ^ 2 + 1 := by exact_mod_cast hDy
    linarith
  have hD' : D ∈ Nat.divisors 130 := Nat.mem_divisors.mpr ⟨hD, by norm_num⟩
  rw [show Nat.divisors 130 = {1, 2, 5, 10, 13, 26, 65, 130} by decide] at hD'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hD'
  rcases hD' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hx0 : x = 0 := by
      have hxy : (x : ℤ) < y := by nlinarith
      have : (x : ℤ) ≤ 0 := by nlinarith
      omega
    subst hx0
    simp
  · exact Finset.mem_of_subset (by decide) (blk65_2 (by exact_mod_cast heq) hys)
  · exact Finset.mem_of_subset (by decide) (blk65_5 (by exact_mod_cast heq) hys)
  · exact Finset.mem_of_subset (by decide) (blk65_10 (by exact_mod_cast heq) hys)
  · exact Finset.mem_of_subset (by decide) (blk65_13 (by exact_mod_cast heq) hys)
  · exact Finset.mem_of_subset (by decide) (blk65_26 (by exact_mod_cast heq) hys)
  · exact Finset.mem_of_subset (by decide) (blk65_65 (by exact_mod_cast heq) hys)
  · exact Finset.mem_of_subset (by decide) (blk65_130 (by exact_mod_cast heq) hys)

/-- Solutions of `x ^ 2 - 2 y ^ 2 = ±1` with `y` smooth for `13`. -/
theorem pell_smooth {x y : ℕ} (h : x ^ 2 = 2 * y ^ 2 + 1 ∨ x ^ 2 + 1 = 2 * y ^ 2)
    (hs : ∀ p : ℕ, p.Prime → y % p = 0 → p ≤ 13) :
    y ∈ ({1, 2, 5, 12, 70, 169, 13860} : Finset ℕ) := by
  have hy : 0 < y := by
    rcases Nat.eq_zero_or_pos y with rfl | hy
    · have := hs 17 (by norm_num) (by norm_num)
      omega
    · exact hy
  refine blk30030_2 (x := x) ?_ hy (smooth_30030_of hs)
  rcases h with h | h
  · left
    have : (x : ℤ) ^ 2 = 2 * y ^ 2 + 1 := by exact_mod_cast h
    linarith
  · right
    have : (x : ℤ) ^ 2 + 1 = 2 * y ^ 2 := by exact_mod_cast h
    linarith

end TuringTask
