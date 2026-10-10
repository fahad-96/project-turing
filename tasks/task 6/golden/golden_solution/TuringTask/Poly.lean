import Mathlib

/-!
# An alternating sum of Gaussian binomial coefficients

In `ℤ[X]` let `gb m k` be the Gaussian binomial coefficient `[m, k]` in the variable `q = X`.
This file proves

  `∑_{k=0}^{2m} (-1)^k [2m, k] = ∏_{j=0}^{m-1} (1 - X^(2j+1))`.
-/

namespace TuringTask

open Polynomial Finset

/-! ### Triangular numbers -/

/-- The triangular number `i (i + 1) / 2`. -/
def tri (i : ℕ) : ℕ := i * (i + 1) / 2

lemma two_mul_tri (i : ℕ) : 2 * tri i = i * (i + 1) := by
  unfold tri
  exact Nat.mul_div_cancel' (Nat.even_mul_succ_self i).two_dvd

lemma tri_succ (i : ℕ) : tri (i + 1) = tri i + (i + 1) := by
  have h1 := two_mul_tri i
  have h2 := two_mul_tri (i + 1)
  nlinarith

@[simp] lemma tri_zero : tri 0 = 0 := rfl

/-! ### The Euler product -/

/-- `EP n = ∏_{i=1}^{n} (1 - X^i)`. -/
noncomputable def EP (n : ℕ) : ℤ[X] := ∏ i ∈ range n, (1 - X ^ (i + 1))

@[simp] lemma EP_zero : EP 0 = 1 := by simp [EP]

lemma EP_succ (n : ℕ) : EP (n + 1) = EP n * (1 - X ^ (n + 1)) := by
  simp [EP, prod_range_succ]

/-! ### Gaussian binomial coefficients -/

/-- The Gaussian binomial coefficient `[m, k]` as a polynomial in `q = X`, defined by the
`q`-Pascal rule `[m+1, k+1] = q^(m-k) [m, k] + [m, k+1]`. -/
noncomputable def gb : ℕ → ℕ → ℤ[X]
  | _, 0 => 1
  | 0, _ + 1 => 0
  | m + 1, k + 1 => X ^ (m - k) * gb m k + gb m (k + 1)

@[simp] lemma gb_zero_right (m : ℕ) : gb m 0 = 1 := by cases m <;> simp [gb]

@[simp] lemma gb_zero_succ (k : ℕ) : gb 0 (k + 1) = 0 := by simp [gb]

lemma gb_succ_succ (m k : ℕ) :
    gb (m + 1) (k + 1) = X ^ (m - k) * gb m k + gb m (k + 1) := by simp [gb]

lemma gb_of_lt : ∀ (m k : ℕ), m < k → gb m k = 0
  | 0, k, h => by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp
  | m + 1, k, h => by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [gb_succ_succ, gb_of_lt m k' (by omega), gb_of_lt m (k' + 1) (by omega)]
    simp

/-- The product formula `[m, k] (q; q)_k = ∏_{j=1}^{k} (1 - q^(m-k+j))`. -/
lemma gb_mul_EP : ∀ (m k : ℕ), k ≤ m →
    gb m k * EP k = ∏ j ∈ range k, (1 - X ^ (m - k + j + 1))
  | 0, k, h => by
    obtain rfl : k = 0 := by omega
    simp
  | m + 1, 0, _ => by simp
  | m + 1, k + 1, h => by
    have hk : k ≤ m := by omega
    rw [gb_succ_succ, EP_succ]
    have ih1 := gb_mul_EP m k hk
    rcases Nat.lt_or_ge k m with hlt | hge
    · have ih2 := gb_mul_EP m (k + 1) hlt
      rw [EP_succ] at ih2
      have e1 : ∏ j ∈ range (k + 1), (1 - (X : ℤ[X]) ^ (m - (k + 1) + j + 1))
          = (1 - X ^ (m - k)) * ∏ j ∈ range k, (1 - X ^ (m - k + j + 1)) := by
        rw [prod_range_succ', mul_comm]
        congr 1
        · congr 2; omega
        · apply prod_congr rfl
          intro j _
          congr 2; omega
      have e2 : ∏ j ∈ range (k + 1), (1 - (X : ℤ[X]) ^ (m + 1 - (k + 1) + j + 1))
          = (∏ j ∈ range k, (1 - X ^ (m - k + j + 1))) * (1 - X ^ (m + 1)) := by
        rw [prod_range_succ]
        congr 1
        · apply prod_congr rfl
          intro j _
          congr 2; omega
        · congr 2; omega
      rw [e2]
      rw [e1] at ih2
      have e3 : (X : ℤ[X]) ^ (m + 1) = X ^ (m - k) * X ^ (k + 1) := by
        rw [← pow_add]; congr 1; omega
      calc (X ^ (m - k) * gb m k + gb m (k + 1)) * (EP k * (1 - X ^ (k + 1)))
          = X ^ (m - k) * (1 - X ^ (k + 1)) * (gb m k * EP k)
            + gb m (k + 1) * (EP k * (1 - X ^ (k + 1))) := by ring
        _ = X ^ (m - k) * (1 - X ^ (k + 1)) * ∏ j ∈ range k, (1 - X ^ (m - k + j + 1))
            + (1 - X ^ (m - k)) * ∏ j ∈ range k, (1 - X ^ (m - k + j + 1)) := by
          rw [ih1, ih2]
        _ = (∏ j ∈ range k, (1 - X ^ (m - k + j + 1))) * (1 - X ^ (m + 1)) := by
          rw [e3]; ring
    · obtain rfl : k = m := by omega
      rw [gb_of_lt k (k + 1) (by omega), add_zero, Nat.sub_self, pow_zero, one_mul]
      rw [← mul_assoc, ih1, prod_range_succ]
      congr 1
      · apply prod_congr rfl
        intro j _
        congr 2; omega
      · congr 2; omega

/-! ### The two Pascal rules -/

lemma EP_ne_zero (k : ℕ) : EP k ≠ 0 := by
  intro h
  have h1 : (EP k).eval 0 = 1 := by
    simp [EP, eval_prod]
  rw [h] at h1
  simp at h1

/-- `(1 - q^(k+1)) [m, k+1] = (1 - q^(m-k)) [m, k]`. -/
lemma gb_ratio (m k : ℕ) :
    (1 - X ^ (k + 1)) * gb m (k + 1) = (1 - X ^ (m - k)) * gb m k := by
  rcases Nat.lt_or_ge k m with hlt | hge
  · have h1 := gb_mul_EP m k hlt.le
    have h2 := gb_mul_EP m (k + 1) hlt
    have e1 : ∏ j ∈ range (k + 1), (1 - (X : ℤ[X]) ^ (m - (k + 1) + j + 1))
        = (1 - X ^ (m - k)) * ∏ j ∈ range k, (1 - X ^ (m - k + j + 1)) := by
      rw [prod_range_succ', mul_comm]
      congr 1
      · congr 2; omega
      · apply prod_congr rfl
        intro j _
        congr 2; omega
    rw [e1, ← h1, EP_succ] at h2
    have h3 : ((1 - X ^ (k + 1)) * gb m (k + 1)) * EP k
        = ((1 - X ^ (m - k)) * gb m k) * EP k := by
      linear_combination h2
    exact mul_right_cancel₀ (EP_ne_zero k) h3
  · rw [gb_of_lt m (k + 1) (by omega)]
    rcases Nat.eq_or_lt_of_le hge with heq | hlt
    · subst heq
      simp
    · rw [gb_of_lt m k hlt]
      simp

/-- The second Pascal rule `[m+1, k+1] = [m, k] + q^(k+1) [m, k+1]`. -/
lemma gb_succ_succ' (m k : ℕ) :
    gb (m + 1) (k + 1) = gb m k + X ^ (k + 1) * gb m (k + 1) := by
  rw [gb_succ_succ]
  linear_combination gb_ratio m k

/-! ### The alternating sum -/

/-- `altS N = ∑_{k=0}^{N} (-1)^k [N, k]`. -/
noncomputable def altS (N : ℕ) : ℤ[X] := ∑ k ∈ range (N + 1), (-1) ^ k * gb N k

/-- `altH N = ∑_{k=0}^{N} (-1)^k q^(N-k) [N, k]`. -/
noncomputable def altH (N : ℕ) : ℤ[X] := ∑ k ∈ range (N + 1), (-1) ^ k * X ^ (N - k) * gb N k

lemma altS_tail (N : ℕ) :
    ∑ k ∈ range (N + 1), (-1 : ℤ[X]) ^ (k + 1) * gb N (k + 1) = altS N - 1 := by
  have h : ∑ k ∈ range (N + 1 + 1), (-1 : ℤ[X]) ^ k * gb N k = altS N := by
    rw [sum_range_succ, gb_of_lt N (N + 1) (by omega)]
    simp [altS]
  rw [sum_range_succ'] at h
  simp only [pow_zero, gb_zero_right, mul_one] at h
  linear_combination h

lemma altS_succ (N : ℕ) : altS (N + 1) = altS N - altH N := by
  have h0 : altS (N + 1)
      = ∑ k ∈ range (N + 1), (-1 : ℤ[X]) ^ (k + 1) * gb (N + 1) (k + 1) + 1 := by
    unfold altS
    rw [sum_range_succ']
    simp
  have h1 : ∑ k ∈ range (N + 1), (-1 : ℤ[X]) ^ (k + 1) * gb (N + 1) (k + 1)
      = ∑ k ∈ range (N + 1), (-1 : ℤ[X]) ^ (k + 1) * gb N (k + 1) - altH N := by
    unfold altH
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro k _
    rw [gb_succ_succ, pow_succ]
    ring
  rw [h0, h1, altS_tail]
  ring

lemma altH_succ (N : ℕ) : altH (N + 1) = X ^ (N + 1) * altS N - altH N := by
  have h0 : altH (N + 1)
      = ∑ k ∈ range (N + 1), (-1 : ℤ[X]) ^ (k + 1) * X ^ (N - k) * gb (N + 1) (k + 1)
        + X ^ (N + 1) := by
    unfold altH
    rw [sum_range_succ']
    simp
  have h1 : ∑ k ∈ range (N + 1), (-1 : ℤ[X]) ^ (k + 1) * X ^ (N - k) * gb (N + 1) (k + 1)
      = X ^ (N + 1) * ∑ k ∈ range (N + 1), (-1 : ℤ[X]) ^ (k + 1) * gb N (k + 1) - altH N := by
    unfold altH
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro k hk
    have hk' : k ≤ N := by
      have := mem_range.mp hk
      omega
    have e : (X : ℤ[X]) ^ (N + 1) = X ^ (N - k) * X ^ (k + 1) := by
      rw [← pow_add]; congr 1; omega
    rw [gb_succ_succ', pow_succ, e]
    ring
  rw [h0, h1, altS_tail]
  ring

lemma altS_add_two (N : ℕ) : altS (N + 2) = (1 - X ^ (N + 1)) * altS N := by
  rw [altS_succ (N + 1), altS_succ N, altH_succ N]
  ring

@[simp] lemma altS_zero : altS 0 = 1 := by
  simp [altS]

/-- Gauss's identity `∑_{k=0}^{2m} (-1)^k [2m, k] = ∏_{j<m} (1 - q^(2j+1))`. -/
theorem altS_even (m : ℕ) : altS (2 * m) = ∏ j ∈ range m, (1 - X ^ (2 * j + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 2 by ring, altS_add_two, ih, prod_range_succ]
    ring

end TuringTask
