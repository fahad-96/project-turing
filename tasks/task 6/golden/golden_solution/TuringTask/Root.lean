import Mathlib
import TuringTask.Poly

/-!
# The alternating sum at a root of unity

Let `z` be an element of a field with `z^(2m+1) = 1` and `z^i ≠ 1` for `0 < i ≤ 2m`, and let
`w = z⁻¹`. Evaluating the identity of `TuringTask.altS_even` at `X = z` gives

  `∑_{k=0}^{2m} w^(k(k+1)/2) = ∏_{j=0}^{m-1} (1 - z^(2j+1))`.

The file also contains two elementary facts about finite sums that are used later: a sum of a
periodic function over a full period does not depend on the starting point, and a product
formula for the two "conjugate" sums `∑ w^(c k)` and `∑ u^(c l)` with `u = w⁻¹`.
-/

namespace TuringTask

open Polynomial Finset

section Root

variable {K : Type*} [Field K]

lemma prod_pow_succ (z : K) (k : ℕ) : ∏ j ∈ range k, z ^ (j + 1) = z ^ tri k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [prod_range_succ, ih, tri_succ]
    ring

/-- The value of `[2m, k]` at a root of unity `z` of order `2m+1` is `(-1)^k z^(-k(k+1)/2)`. -/
lemma aeval_gb_mul (m k : ℕ) (hk : k ≤ 2 * m) (z : K) (hz : z ^ (2 * m + 1) = 1)
    (hz' : ∀ i, 0 < i → i ≤ 2 * m → z ^ i ≠ 1) :
    aeval z (gb (2 * m) k) * z ^ tri k = (-1) ^ k := by
  have h := congrArg (aeval z) (gb_mul_EP (2 * m) k hk)
  simp only [EP, map_mul, map_prod, map_sub, map_one, map_pow, aeval_X] at h
  have hP : ∏ i ∈ range k, (1 - z ^ (i + 1)) ≠ 0 := by
    rw [prod_ne_zero_iff]
    intro i hi
    have hi' := mem_range.mp hi
    have h1 := hz' (i + 1) (by omega) (by omega)
    intro h0
    exact h1 (by linear_combination -h0)
  have hterm : ∀ j ∈ range k,
      z ^ (j + 1) * (1 - z ^ (2 * m - k + (k - 1 - j) + 1)) = (-1) * (1 - z ^ (j + 1)) := by
    intro j hj
    have hj' := mem_range.mp hj
    have e : 2 * m - k + (k - 1 - j) + 1 = 2 * m - j := by omega
    have e2 : z ^ (j + 1) * z ^ (2 * m - j) = 1 := by
      rw [← pow_add]
      have e3 : j + 1 + (2 * m - j) = 2 * m + 1 := by omega
      rw [e3, hz]
    rw [e]
    linear_combination -e2
  have hR : z ^ tri k * ∏ j ∈ range k, (1 - z ^ (2 * m - k + j + 1))
      = (-1) ^ k * ∏ i ∈ range k, (1 - z ^ (i + 1)) := by
    rw [← prod_pow_succ z k, ← prod_range_reflect (fun j => 1 - z ^ (2 * m - k + j + 1)) k,
      ← prod_mul_distrib, prod_congr rfl hterm, prod_mul_distrib, prod_const, card_range]
  have h4 : (aeval z (gb (2 * m) k) * z ^ tri k) * ∏ i ∈ range k, (1 - z ^ (i + 1))
      = (-1) ^ k * ∏ i ∈ range k, (1 - z ^ (i + 1)) := by
    rw [← hR, ← h]
    ring
  exact mul_right_cancel₀ hP h4

/-- Evaluation of Gauss's identity at a root of unity of odd order `2m+1`. -/
theorem sum_pow_tri (m : ℕ) (z w : K) (hz : z ^ (2 * m + 1) = 1)
    (hz' : ∀ i, 0 < i → i ≤ 2 * m → z ^ i ≠ 1) (hw : w * z = 1) :
    ∑ k ∈ range (2 * m + 1), w ^ tri k = ∏ j ∈ range m, (1 - z ^ (2 * j + 1)) := by
  have h := congrArg (aeval z) (altS_even m)
  simp only [altS, map_sum, map_mul, map_pow, map_neg, map_one, map_prod, map_sub,
    aeval_X] at h
  rw [← h]
  apply sum_congr rfl
  intro k hk
  have hk' : k ≤ 2 * m := by
    have := mem_range.mp hk
    omega
  have h1 := aeval_gb_mul m k hk' z hz hz'
  have h2 : w ^ tri k * z ^ tri k = 1 := by rw [← mul_pow, hw, one_pow]
  have h3 : ((-1 : K) ^ k) * (-1) ^ k = 1 := by
    rw [← mul_pow]
    simp
  linear_combination (-((-1) ^ k * w ^ tri k)) * h1
    + ((-1) ^ k * aeval z (gb (2 * m) k)) * h2 - w ^ tri k * h3

end Root

section Sums

variable {K : Type*} [Field K]

/-- A sum over a full period does not depend on the starting point. -/
lemma sum_range_shift (n : ℕ) (F : ℕ → K) (hF : ∀ k, F (k + n) = F k) (l : ℕ) :
    ∑ d ∈ range n, F (l + d) = ∑ k ∈ range n, F k := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [← ih]
    have h1 : ∑ d ∈ range (n + 1), F (l + d) = ∑ d ∈ range n, F (l + d) + F (l + n) :=
      sum_range_succ _ _
    have h2 : ∑ d ∈ range (n + 1), F (l + d) = ∑ d ∈ range n, F (l + (d + 1)) + F (l + 0) :=
      sum_range_succ' _ _
    have h3 : ∑ d ∈ range n, F (l + 1 + d) = ∑ d ∈ range n, F (l + (d + 1)) := by
      apply sum_congr rfl
      intro d _
      congr 1
      ring
    rw [h3]
    have h4 : F (l + n) = F (l + 0) := by rw [hF, add_zero]
    linear_combination h1 - h2 + h4

/-- If `x^n = 1` and `x ≠ 1` then `∑_{l<n} x^l = 0`. -/
lemma geom_sum_eq_zero' (n : ℕ) (x : K) (hx : x ^ n = 1) (hx1 : x ≠ 1) :
    ∑ l ∈ range n, x ^ l = 0 := by
  have h := mul_geom_sum x n
  rw [hx, sub_self] at h
  rcases mul_eq_zero.mp h with h0 | h0
  · exact absurd (sub_eq_zero.mp h0) hx1
  · exact h0

/-- Product of two conjugate sums. Here `c` is a "quadratic" exponent:
`c (l + d) = c l + c d + r d l`, with `r` prime to the odd order `n` of `w`. -/
theorem conj_sum_mul (n r : ℕ) (c : ℕ → ℕ) (w u : K) (hn : 0 < n)
    (hw : w ^ n = 1) (hw' : ∀ i, 0 < i → i < n → w ^ i ≠ 1) (hu : u * w = 1)
    (hc : ∀ l d, c (l + d) = c l + c d + r * d * l) (hcn : n ∣ c n)
    (hr : Nat.Coprime r n) (hc0 : c 0 = 0) :
    (∑ k ∈ range n, w ^ c k) * (∑ l ∈ range n, u ^ c l) = n := by
  have hper : ∀ k, w ^ c (k + n) = w ^ c k := by
    intro k
    obtain ⟨t, ht⟩ := hcn
    rw [hc, ht, pow_add, pow_add, pow_mul, hw, one_pow,
      show r * n * k = n * (r * k) by ring, pow_mul, hw, one_pow, mul_one, mul_one]
  have hwi : ∀ i : ℕ, w ^ i = 1 → n ∣ i := by
    intro i hi
    by_contra hnd
    have h1 : w ^ (i % n) = 1 := by
      have h2 : w ^ i = w ^ (i % n) * (w ^ n) ^ (i / n) := by
        rw [← pow_mul, ← pow_add, Nat.mod_add_div]
      rw [h2, hw, one_pow, mul_one] at hi
      exact hi
    have h3 : 0 < i % n := Nat.pos_of_ne_zero (fun h0 => hnd (Nat.dvd_of_mod_eq_zero h0))
    exact hw' (i % n) h3 (Nat.mod_lt _ hn) h1
  have hinner : ∀ d ∈ range n, ∑ l ∈ range n, (w ^ (r * d)) ^ l = if d = 0 then (n : K) else 0 := by
    intro d hd
    have hd' := mem_range.mp hd
    by_cases h0 : d = 0
    · subst h0
      simp
    · rw [if_neg h0]
      apply geom_sum_eq_zero'
      · rw [← pow_mul, mul_comm (r * d) n, pow_mul, hw, one_pow]
      · intro h1
        have h2 : n ∣ r * d := hwi _ h1
        have h3 : n ∣ d := hr.symm.dvd_of_dvd_mul_left h2
        exact h0 (Nat.eq_zero_of_dvd_of_lt h3 hd')
  have hterm : ∀ l d : ℕ, w ^ c (l + d) * u ^ c l = w ^ c d * (w ^ (r * d)) ^ l := by
    intro l d
    have h1 : w ^ c l * u ^ c l = 1 := by rw [← mul_pow, mul_comm, hu, one_pow]
    rw [hc, pow_add, pow_add, ← pow_mul]
    linear_combination (w ^ c d * w ^ (r * d * l)) * h1
  calc (∑ k ∈ range n, w ^ c k) * (∑ l ∈ range n, u ^ c l)
      = ∑ l ∈ range n, (∑ k ∈ range n, w ^ c k) * u ^ c l := by rw [mul_sum]
    _ = ∑ l ∈ range n, ∑ d ∈ range n, w ^ c (l + d) * u ^ c l := by
        apply sum_congr rfl
        intro l _
        rw [← sum_range_shift n (fun k => w ^ c k) hper l, sum_mul]
    _ = ∑ l ∈ range n, ∑ d ∈ range n, w ^ c d * (w ^ (r * d)) ^ l := by
        apply sum_congr rfl
        intro l _
        apply sum_congr rfl
        intro d _
        exact hterm l d
    _ = ∑ d ∈ range n, w ^ c d * ∑ l ∈ range n, (w ^ (r * d)) ^ l := by
        rw [sum_comm]
        apply sum_congr rfl
        intro d _
        rw [mul_sum]
    _ = ∑ d ∈ range n, w ^ c d * (if d = 0 then (n : K) else 0) := by
        apply sum_congr rfl
        intro d hd
        rw [hinner d hd]
    _ = n := by
        rw [sum_eq_single 0]
        · simp [hc0]
        · intro d _ hd
          simp [hd]
        · intro h
          exact absurd (mem_range.mpr hn) h

end Sums

end TuringTask
